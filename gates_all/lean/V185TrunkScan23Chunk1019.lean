import V185TrunkScan23Chunk1018

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_6033310 : List Nat := [4, 3, 1, 3, 1, 1, 3, 1, 1, 1, 4]
def baseStart_6033310 : Nat := 118140960795 + 6033310 * 2 ^ 59
def prefixEnd_6033310 : Nat := 4983230072969 + 3 ^ 40 * 6033310 * 2
def baseEnd_6033310 : Nat := 3097987967577894880578319

theorem tailTrace_6033310 : CollatzResearch.WordTrace tailWord_6033310 prefixEnd_6033310 3097987967577894880578319 := by
  unfold tailWord_6033310
  simp only [CollatzResearch.WordTrace]
  refine ⟨27506611721544469019774173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 146701929181570501438795589 27506611721544469019774173)
  ·
    refine ⟨10314979395579175882415315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27506611721544469019774173 10314979395579175882415315)
    ·
      refine ⟨15472469093368763823622973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10314979395579175882415315 15472469093368763823622973)
      ·
        refine ⟨5802175910013286433858615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15472469093368763823622973 5802175910013286433858615)
        ·
          refine ⟨8703263865019929650787923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5802175910013286433858615 8703263865019929650787923)
          ·
            refine ⟨13054895797529894476181885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8703263865019929650787923 13054895797529894476181885)
            ·
              refine ⟨4895585924073710428568207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13054895797529894476181885 4895585924073710428568207)
              ·
                refine ⟨7343378886110565642852311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4895585924073710428568207 7343378886110565642852311)
                ·
                  refine ⟨11015068329165848464278467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7343378886110565642852311 11015068329165848464278467)
                  ·
                    refine ⟨16522602493748772696417701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11015068329165848464278467 16522602493748772696417701)
                    ·
                      refine ⟨3097987967577894880578319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16522602493748772696417701 3097987967577894880578319)
                      ·
                        rfl

theorem cell23_6033310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 3, 1, 1, 1, 4].length) (baseStart_6033310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6033310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6033310 prefixEnd_6033310 := by exact prefixLift 6033310
  have htrace : WordTrace (prefixWord ++ tailWord_6033310) baseStart_6033310 baseEnd_6033310 := by
    simpa [prefixWord, tailWord_6033310, baseEnd_6033310] using wordTrace_append hprefix tailTrace_6033310
  have hstable : (prefixWord ++ tailWord_6033310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6033310).length < 2 ^ (prefixWord ++ tailWord_6033310).sum := by decide
  have hdescent : baseEnd_6033310 < baseStart_6033310 := by decide
  rcases family_descends (prefixWord ++ tailWord_6033310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6033313 : List Nat := [1, 2, 3, 4, 2, 1, 3, 1, 1, 2, 3]
def baseStart_6033313 : Nat := 118140960795 + 6033313 * 2 ^ 59
def prefixEnd_6033313 : Nat := 4983230072969 + 3 ^ 40 * 6033313 * 2
def baseEnd_6033313 : Nat := 3097989508019858368840805

theorem tailTrace_6033313 : CollatzResearch.WordTrace tailWord_6033313 prefixEnd_6033313 3097989508019858368840805 := by
  unfold tailWord_6033313
  simp only [CollatzResearch.WordTrace]
  refine ⟨220053003191344883670552593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146702002127563255780368395 220053003191344883670552593)
  ·
    refine ⟨165039752393508662752914445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 220053003191344883670552593 165039752393508662752914445)
    ·
      refine ⟨61889907147565748532342917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 165039752393508662752914445 61889907147565748532342917)
      ·
        refine ⟨11604357590168577849814297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 61889907147565748532342917 11604357590168577849814297)
        ·
          refine ⟨8703268192626433387360723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11604357590168577849814297 8703268192626433387360723)
          ·
            refine ⟨13054902288939650081041085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8703268192626433387360723 13054902288939650081041085)
            ·
              refine ⟨4895588358352368780390407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13054902288939650081041085 4895588358352368780390407)
              ·
                refine ⟨7343382537528553170585611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4895588358352368780390407 7343382537528553170585611)
                ·
                  refine ⟨11015073806292829755878417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7343382537528553170585611 11015073806292829755878417)
                  ·
                    refine ⟨8261305354719622316908813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11015073806292829755878417 8261305354719622316908813)
                    ·
                      refine ⟨3097989508019858368840805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8261305354719622316908813 3097989508019858368840805)
                      ·
                        rfl

theorem cell23_6033313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 3, 1, 1, 2, 3].length) (baseStart_6033313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6033313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6033313 prefixEnd_6033313 := by exact prefixLift 6033313
  have htrace : WordTrace (prefixWord ++ tailWord_6033313) baseStart_6033313 baseEnd_6033313 := by
    simpa [prefixWord, tailWord_6033313, baseEnd_6033313] using wordTrace_append hprefix tailTrace_6033313
  have hstable : (prefixWord ++ tailWord_6033313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6033313).length < 2 ^ (prefixWord ++ tailWord_6033313).sum := by decide
  have hdescent : baseEnd_6033313 < baseStart_6033313 := by decide
  rcases family_descends (prefixWord ++ tailWord_6033313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6033342 : List Nat := [4, 2, 1, 1, 1, 3, 1, 1, 1, 8]
def baseStart_6033342 : Nat := 118140960795 + 6033342 * 2 ^ 59
def prefixEnd_6033342 : Nat := 4983230072969 + 3 ^ 40 * 6033342 * 2
def baseEnd_6033342 : Nat := 1032668132986279585126057

theorem tailTrace_6033342 : CollatzResearch.WordTrace tailWord_6033342 prefixEnd_6033342 1032668132986279585126057 := by
  unfold tailWord_6033342
  simp only [CollatzResearch.WordTrace]
  refine ⟨27506757613529977702919785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 146702707272159881082238853 27506757613529977702919785)
  ·
    refine ⟨20630068210147483277189839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27506757613529977702919785 20630068210147483277189839)
    ·
      refine ⟨30945102315221224915784759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20630068210147483277189839 30945102315221224915784759)
      ·
        refine ⟨46417653472831837373677139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30945102315221224915784759 46417653472831837373677139)
        ·
          refine ⟨69626480209247756060515709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46417653472831837373677139 69626480209247756060515709)
          ·
            refine ⟨26109930078467908522693391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69626480209247756060515709 26109930078467908522693391)
            ·
              refine ⟨39164895117701862784040087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26109930078467908522693391 39164895117701862784040087)
              ·
                refine ⟨58747342676552794176060131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39164895117701862784040087 58747342676552794176060131)
                ·
                  refine ⟨88121014014829191264090197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58747342676552794176060131 88121014014829191264090197)
                  ·
                    refine ⟨1032668132986279585126057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 88121014014829191264090197 1032668132986279585126057)
                    ·
                      rfl

theorem cell23_6033342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 1, 1, 8].length) (baseStart_6033342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6033342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6033342 prefixEnd_6033342 := by exact prefixLift 6033342
  have htrace : WordTrace (prefixWord ++ tailWord_6033342) baseStart_6033342 baseEnd_6033342 := by
    simpa [prefixWord, tailWord_6033342, baseEnd_6033342] using wordTrace_append hprefix tailTrace_6033342
  have hstable : (prefixWord ++ tailWord_6033342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6033342).length < 2 ^ (prefixWord ++ tailWord_6033342).sum := by decide
  have hdescent : baseEnd_6033342 < baseStart_6033342 := by decide
  rcases family_descends (prefixWord ++ tailWord_6033342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6033370 : List Nat := [3, 1, 1, 2, 5, 2, 2, 1, 1, 3, 2]
def baseStart_6033370 : Nat := 118140960795 + 6033370 * 2 ^ 59
def prefixEnd_6033370 : Nat := 4983230072969 + 3 ^ 40 * 6033370 * 2
def baseEnd_6033370 : Nat := 3098018776417164645828043

theorem tailTrace_6033370 : CollatzResearch.WordTrace tailWord_6033370 prefixEnd_6033370 3098018776417164645828043 := by
  unfold tailWord_6033370
  simp only [CollatzResearch.WordTrace]
  refine ⟨55013770538034595601344391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146703388101425588270251709 55013770538034595601344391)
  ·
    refine ⟨82520655807051893402016587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55013770538034595601344391 82520655807051893402016587)
    ·
      refine ⟨123780983710577840103024881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82520655807051893402016587 123780983710577840103024881)
      ·
        refine ⟨92835737782933380077268661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123780983710577840103024881 92835737782933380077268661)
        ·
          refine ⟨8703350417150004382243937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 92835737782933380077268661 8703350417150004382243937)
          ·
            refine ⟨6527512812862503286682953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8703350417150004382243937 6527512812862503286682953)
            ·
              refine ⟨4895634609646877465012215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6527512812862503286682953 4895634609646877465012215)
              ·
                refine ⟨7343451914470316197518323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4895634609646877465012215 7343451914470316197518323)
                ·
                  refine ⟨11015177871705474296277485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7343451914470316197518323 11015177871705474296277485)
                  ·
                    refine ⟨4130691701889552861104057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11015177871705474296277485 4130691701889552861104057)
                    ·
                      refine ⟨3098018776417164645828043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4130691701889552861104057 3098018776417164645828043)
                      ·
                        rfl

theorem cell23_6033370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 2, 2, 1, 1, 3, 2].length) (baseStart_6033370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6033370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6033370 prefixEnd_6033370 := by exact prefixLift 6033370
  have htrace : WordTrace (prefixWord ++ tailWord_6033370) baseStart_6033370 baseEnd_6033370 := by
    simpa [prefixWord, tailWord_6033370, baseEnd_6033370] using wordTrace_append hprefix tailTrace_6033370
  have hstable : (prefixWord ++ tailWord_6033370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6033370).length < 2 ^ (prefixWord ++ tailWord_6033370).sum := by decide
  have hdescent : baseEnd_6033370 < baseStart_6033370 := by decide
  rcases family_descends (prefixWord ++ tailWord_6033370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6033383 : List Nat := [1, 1, 5, 2, 3, 1, 1, 1, 4, 2, 2]
def baseStart_6033383 : Nat := 118140960795 + 6033383 * 2 ^ 59
def prefixEnd_6033383 : Nat := 4983230072969 + 3 ^ 40 * 6033383 * 2
def baseEnd_6033383 : Nat := 3098025451665673094965483

theorem tailTrace_6033383 : CollatzResearch.WordTrace tailWord_6033383 prefixEnd_6033383 3098025451665673094965483 := by
  unfold tailWord_6033383
  simp only [CollatzResearch.WordTrace]
  refine ⟨220055556301091285625600803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146703704200727523750400535 220055556301091285625600803)
  ·
    refine ⟨330083334451636928438401205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220055556301091285625600803 330083334451636928438401205)
    ·
      refine ⟨30945312604840962041100113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 330083334451636928438401205 30945312604840962041100113)
      ·
        refine ⟨23208984453630721530825085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30945312604840962041100113 23208984453630721530825085)
        ·
          refine ⟨8703369170111520574059407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23208984453630721530825085 8703369170111520574059407)
          ·
            refine ⟨13055053755167280861089111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8703369170111520574059407 13055053755167280861089111)
            ·
              refine ⟨19582580632750921291633667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13055053755167280861089111 19582580632750921291633667)
              ·
                refine ⟨29373870949126381937450501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19582580632750921291633667 29373870949126381937450501)
                ·
                  refine ⟨5507600802961196613271969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29373870949126381937450501 5507600802961196613271969)
                  ·
                    refine ⟨4130700602220897459953977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5507600802961196613271969 4130700602220897459953977)
                    ·
                      refine ⟨3098025451665673094965483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4130700602220897459953977 3098025451665673094965483)
                      ·
                        rfl

theorem cell23_6033383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 1, 1, 4, 2, 2].length) (baseStart_6033383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6033383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6033383 prefixEnd_6033383 := by exact prefixLift 6033383
  have htrace : WordTrace (prefixWord ++ tailWord_6033383) baseStart_6033383 baseEnd_6033383 := by
    simpa [prefixWord, tailWord_6033383, baseEnd_6033383] using wordTrace_append hprefix tailTrace_6033383
  have hstable : (prefixWord ++ tailWord_6033383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6033383).length < 2 ^ (prefixWord ++ tailWord_6033383).sum := by decide
  have hdescent : baseEnd_6033383 < baseStart_6033383 := by decide
  rcases family_descends (prefixWord ++ tailWord_6033383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6033439 : List Nat := [1, 1, 2, 4, 1, 2, 3, 2, 2, 1, 4]
def baseStart_6033439 : Nat := 118140960795 + 6033439 * 2 ^ 59
def prefixEnd_6033439 : Nat := 4983230072969 + 3 ^ 40 * 6033439 * 2
def baseEnd_6033439 : Nat := 3098054206582324875865225

theorem tailTrace_6033439 : CollatzResearch.WordTrace tailWord_6033439 prefixEnd_6033439 3098054206582324875865225 := by
  unfold tailWord_6033439
  simp only [CollatzResearch.WordTrace]
  refine ⟨220057598788888407189639371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146705065859258938126426247 220057598788888407189639371)
  ·
    refine ⟨330086398183332610784459057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220057598788888407189639371 330086398183332610784459057)
    ·
      refine ⟨247564798637499458088344293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 330086398183332610784459057 247564798637499458088344293)
      ·
        refine ⟨46418399744531148391564555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 247564798637499458088344293 46418399744531148391564555)
        ·
          refine ⟨69627599616796722587346833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46418399744531148391564555 69627599616796722587346833)
          ·
            refine ⟨52220699712597541940510125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69627599616796722587346833 52220699712597541940510125)
            ·
              refine ⟨19582762392224078227691297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52220699712597541940510125 19582762392224078227691297)
              ·
                refine ⟨14687071794168058670768473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19582762392224078227691297 14687071794168058670768473)
                ·
                  refine ⟨11015303845626044003076355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14687071794168058670768473 11015303845626044003076355)
                  ·
                    refine ⟨16522955768439066004614533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11015303845626044003076355 16522955768439066004614533)
                    ·
                      refine ⟨3098054206582324875865225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16522955768439066004614533 3098054206582324875865225)
                      ·
                        rfl

theorem cell23_6033439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 3, 2, 2, 1, 4].length) (baseStart_6033439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6033439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6033439 prefixEnd_6033439 := by exact prefixLift 6033439
  have htrace : WordTrace (prefixWord ++ tailWord_6033439) baseStart_6033439 baseEnd_6033439 := by
    simpa [prefixWord, tailWord_6033439, baseEnd_6033439] using wordTrace_append hprefix tailTrace_6033439
  have hstable : (prefixWord ++ tailWord_6033439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6033439).length < 2 ^ (prefixWord ++ tailWord_6033439).sum := by decide
  have hdescent : baseEnd_6033439 < baseStart_6033439 := by decide
  rcases family_descends (prefixWord ++ tailWord_6033439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6033452 : List Nat := [2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 4]
def baseStart_6033452 : Nat := 118140960795 + 6033452 * 2 ^ 59
def prefixEnd_6033452 : Nat := 4983230072969 + 3 ^ 40 * 6033452 * 2
def baseEnd_6033452 : Nat := 3098060881830833325002665

theorem tailTrace_6033452 : CollatzResearch.WordTrace tailWord_6033452 prefixEnd_6033452 3098060881830833325002665 := by
  unfold tailWord_6033452
  simp only [CollatzResearch.WordTrace]
  refine ⟨110029036468920655204931305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146705381958560873606575073 110029036468920655204931305)
  ·
    refine ⟨82521777351690491403698479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110029036468920655204931305 82521777351690491403698479)
    ·
      refine ⟨123782666027535737105547719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82521777351690491403698479 123782666027535737105547719)
      ·
        refine ⟨185673999041303605658321579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123782666027535737105547719 185673999041303605658321579)
        ·
          refine ⟨278510998561955408487482369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 185673999041303605658321579 278510998561955408487482369)
          ·
            refine ⟨208883248921466556365611777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 278510998561955408487482369 208883248921466556365611777)
            ·
              refine ⟨156662436691099917274208833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 208883248921466556365611777 156662436691099917274208833)
              ·
                refine ⟨117496827518324937955656625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 156662436691099917274208833 117496827518324937955656625)
                ·
                  refine ⟨88122620638743703466742469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 117496827518324937955656625 88122620638743703466742469)
                  ·
                    refine ⟨16522991369764444400014213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 88122620638743703466742469 16522991369764444400014213)
                    ·
                      refine ⟨3098060881830833325002665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16522991369764444400014213 3098060881830833325002665)
                      ·
                        rfl

theorem cell23_6033452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 4].length) (baseStart_6033452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6033452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6033452 prefixEnd_6033452 := by exact prefixLift 6033452
  have htrace : WordTrace (prefixWord ++ tailWord_6033452) baseStart_6033452 baseEnd_6033452 := by
    simpa [prefixWord, tailWord_6033452, baseEnd_6033452] using wordTrace_append hprefix tailTrace_6033452
  have hstable : (prefixWord ++ tailWord_6033452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6033452).length < 2 ^ (prefixWord ++ tailWord_6033452).sum := by decide
  have hdescent : baseEnd_6033452 < baseStart_6033452 := by decide
  rcases family_descends (prefixWord ++ tailWord_6033452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6033482 : List Nat := [3, 1, 2, 1, 1, 2, 1, 2, 1, 1, 8]
def baseStart_6033482 : Nat := 118140960795 + 6033482 * 2 ^ 59
def prefixEnd_6033482 : Nat := 4983230072969 + 3 ^ 40 * 6033482 * 2
def baseEnd_6033482 : Nat := 3098076286250468207627527

theorem tailTrace_6033482 : CollatzResearch.WordTrace tailWord_6033482 prefixEnd_6033482 3098076286250468207627527 := by
  unfold tailWord_6033482
  simp only [CollatzResearch.WordTrace]
  refine ⟨55014791781933156383363675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146706111418488417022303133 55014791781933156383363675)
  ·
    refine ⟨82522187672899734575045513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55014791781933156383363675 82522187672899734575045513)
    ·
      refine ⟨61891640754674800931284135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82522187672899734575045513 61891640754674800931284135)
      ·
        refine ⟨92837461132012201396926203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61891640754674800931284135 92837461132012201396926203)
        ·
          refine ⟨139256191698018302095389305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92837461132012201396926203 139256191698018302095389305)
          ·
            refine ⟨104442143773513726571541979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 139256191698018302095389305 104442143773513726571541979)
            ·
              refine ⟨156663215660270589857312969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104442143773513726571541979 156663215660270589857312969)
              ·
                refine ⟨117497411745202942392984727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 156663215660270589857312969 117497411745202942392984727)
                ·
                  refine ⟨176246117617804413589477091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 117497411745202942392984727 176246117617804413589477091)
                  ·
                    refine ⟨264369176426706620384215637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 176246117617804413589477091 264369176426706620384215637)
                    ·
                      refine ⟨3098076286250468207627527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 264369176426706620384215637 3098076286250468207627527)
                      ·
                        rfl

theorem cell23_6033482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 2, 1, 1, 8].length) (baseStart_6033482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6033482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6033482 prefixEnd_6033482 := by exact prefixLift 6033482
  have htrace : WordTrace (prefixWord ++ tailWord_6033482) baseStart_6033482 baseEnd_6033482 := by
    simpa [prefixWord, tailWord_6033482, baseEnd_6033482] using wordTrace_append hprefix tailTrace_6033482
  have hstable : (prefixWord ++ tailWord_6033482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6033482).length < 2 ^ (prefixWord ++ tailWord_6033482).sum := by decide
  have hdescent : baseEnd_6033482 < baseStart_6033482 := by decide
  rcases family_descends (prefixWord ++ tailWord_6033482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6033500 : List Nat := [2, 2, 4, 1, 1, 2, 4, 2, 1, 4]
def baseStart_6033500 : Nat := 118140960795 + 6033500 * 2 ^ 59
def prefixEnd_6033500 : Nat := 4983230072969 + 3 ^ 40 * 6033500 * 2
def baseEnd_6033500 : Nat := 1032695176300749712400815

theorem tailTrace_6033500 : CollatzResearch.WordTrace tailWord_6033500 prefixEnd_6033500 1032695176300749712400815 := by
  unfold tailWord_6033500
  simp only [CollatzResearch.WordTrace]
  refine ⟨110029911820833707303804977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146706549094444943071739969 110029911820833707303804977)
  ·
    refine ⟨82522433865625280477853733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110029911820833707303804977 82522433865625280477853733)
    ·
      refine ⟨15472956349804740089597575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 82522433865625280477853733 15472956349804740089597575)
      ·
        refine ⟨23209434524707110134396363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15472956349804740089597575 23209434524707110134396363)
        ·
          refine ⟨34814151787060665201594545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23209434524707110134396363 34814151787060665201594545)
          ·
            refine ⟨26110613840295498901195909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34814151787060665201594545 26110613840295498901195909)
            ·
              refine ⟨4895740095055406043974233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26110613840295498901195909 4895740095055406043974233)
              ·
                refine ⟨3671805071291554532980675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4895740095055406043974233 3671805071291554532980675)
                ·
                  refine ⟨5507707606937331799471013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3671805071291554532980675 5507707606937331799471013)
                  ·
                    refine ⟨1032695176300749712400815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5507707606937331799471013 1032695176300749712400815)
                    ·
                      rfl

theorem cell23_6033500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 4, 2, 1, 4].length) (baseStart_6033500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6033500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6033500 prefixEnd_6033500 := by exact prefixLift 6033500
  have htrace : WordTrace (prefixWord ++ tailWord_6033500) baseStart_6033500 baseEnd_6033500 := by
    simpa [prefixWord, tailWord_6033500, baseEnd_6033500] using wordTrace_append hprefix tailTrace_6033500
  have hstable : (prefixWord ++ tailWord_6033500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6033500).length < 2 ^ (prefixWord ++ tailWord_6033500).sum := by decide
  have hdescent : baseEnd_6033500 < baseStart_6033500 := by decide
  rcases family_descends (prefixWord ++ tailWord_6033500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6033509 : List Nat := [1, 3, 1, 3, 2, 2, 1, 2, 3, 5]
def baseStart_6033509 : Nat := 118140960795 + 6033509 * 2 ^ 59
def prefixEnd_6033509 : Nat := 4983230072969 + 3 ^ 40 * 6033509 * 2
def baseEnd_6033509 : Nat := 1032696716742713200663301

theorem tailTrace_6033509 : CollatzResearch.WordTrace tailWord_6033509 prefixEnd_6033509 1032696716742713200663301 := by
  unfold tailWord_6033509
  simp only [CollatzResearch.WordTrace]
  refine ⟨220060151898634809144687581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146706767932423206096458387 220060151898634809144687581)
  ·
    refine ⟨82522556961988053429257843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 220060151898634809144687581 82522556961988053429257843)
    ·
      refine ⟨123783835442982080143886765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82522556961988053429257843 123783835442982080143886765)
      ·
        refine ⟨46418938291118280053957537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 123783835442982080143886765 46418938291118280053957537)
        ·
          refine ⟨34814203718338710040468153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46418938291118280053957537 34814203718338710040468153)
          ·
            refine ⟨26110652788754032530351115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34814203718338710040468153 26110652788754032530351115)
            ·
              refine ⟨39165979183131048795526673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26110652788754032530351115 39165979183131048795526673)
              ·
                refine ⟨29374484387348286596645005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39165979183131048795526673 29374484387348286596645005)
                ·
                  refine ⟨11015431645255607473741877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29374484387348286596645005 11015431645255607473741877)
                  ·
                    refine ⟨1032696716742713200663301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11015431645255607473741877 1032696716742713200663301)
                    ·
                      rfl

theorem cell23_6033509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 2, 3, 5].length) (baseStart_6033509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6033509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6033509 prefixEnd_6033509 := by exact prefixLift 6033509
  have htrace : WordTrace (prefixWord ++ tailWord_6033509) baseStart_6033509 baseEnd_6033509 := by
    simpa [prefixWord, tailWord_6033509, baseEnd_6033509] using wordTrace_append hprefix tailTrace_6033509
  have hstable : (prefixWord ++ tailWord_6033509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6033509).length < 2 ^ (prefixWord ++ tailWord_6033509).sum := by decide
  have hdescent : baseEnd_6033509 < baseStart_6033509 := by decide
  rcases family_descends (prefixWord ++ tailWord_6033509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6033526 : List Nat := [5, 1, 1, 2, 1, 2, 2, 1, 3, 5]
def baseStart_6033526 : Nat := 118140960795 + 6033526 * 2 ^ 59
def prefixEnd_6033526 : Nat := 4983230072969 + 3 ^ 40 * 6033526 * 2
def baseEnd_6033526 : Nat := 1032699626466422011825775

theorem tailTrace_6033526 : CollatzResearch.WordTrace tailWord_6033526 prefixEnd_6033526 1032699626466422011825775 := by
  unfold tailWord_6033526
  simp only [CollatzResearch.WordTrace]
  refine ⟨13753798246223326315503527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 146707181293048814032037621 13753798246223326315503527)
  ·
    refine ⟨20630697369334989473255291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13753798246223326315503527 20630697369334989473255291)
    ·
      refine ⟨30946046054002484209882937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20630697369334989473255291 30946046054002484209882937)
      ·
        refine ⟨23209534540501863157412203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30946046054002484209882937 23209534540501863157412203)
        ·
          refine ⟨34814301810752794736118305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23209534540501863157412203 34814301810752794736118305)
          ·
            refine ⟨26110726358064596052088729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34814301810752794736118305 26110726358064596052088729)
            ·
              refine ⟨19583044768548447039066547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26110726358064596052088729 19583044768548447039066547)
              ·
                refine ⟨29374567152822670558599821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19583044768548447039066547 29374567152822670558599821)
                ·
                  refine ⟨11015462682308501459474933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29374567152822670558599821 11015462682308501459474933)
                  ·
                    refine ⟨1032699626466422011825775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11015462682308501459474933 1032699626466422011825775)
                    ·
                      rfl

theorem cell23_6033526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 2, 1, 3, 5].length) (baseStart_6033526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6033526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6033526 prefixEnd_6033526 := by exact prefixLift 6033526
  have htrace : WordTrace (prefixWord ++ tailWord_6033526) baseStart_6033526 baseEnd_6033526 := by
    simpa [prefixWord, tailWord_6033526, baseEnd_6033526] using wordTrace_append hprefix tailTrace_6033526
  have hstable : (prefixWord ++ tailWord_6033526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6033526).length < 2 ^ (prefixWord ++ tailWord_6033526).sum := by decide
  have hdescent : baseEnd_6033526 < baseStart_6033526 := by decide
  rcases family_descends (prefixWord ++ tailWord_6033526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6033533 : List Nat := [1, 4, 1, 1, 3, 2, 3, 1, 2, 3, 2]
def baseStart_6033533 : Nat := 118140960795 + 6033533 * 2 ^ 59
def prefixEnd_6033533 : Nat := 4983230072969 + 3 ^ 40 * 6033533 * 2
def baseEnd_6033533 : Nat := 3098102473763847508089793

theorem tailTrace_6033533 : CollatzResearch.WordTrace tailWord_6033533 prefixEnd_6033533 3098102473763847508089793 := by
  unfold tailWord_6033533
  simp only [CollatzResearch.WordTrace]
  refine ⟨220061027250547861243561253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146707351500365240829040835 220061027250547861243561253)
  ·
    refine ⟨41261442609477723983167735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 220061027250547861243561253 41261442609477723983167735)
    ·
      refine ⟨61892163914216585974751603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41261442609477723983167735 61892163914216585974751603)
      ·
        refine ⟨92838245871324878962127405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61892163914216585974751603 92838245871324878962127405)
        ·
          refine ⟨34814342201746829610797777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 92838245871324878962127405 34814342201746829610797777)
          ·
            refine ⟨26110756651310122208098333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34814342201746829610797777 26110756651310122208098333)
            ·
              refine ⟨9791533744241295828036875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26110756651310122208098333 9791533744241295828036875)
              ·
                refine ⟨14687300616361943742055313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9791533744241295828036875 14687300616361943742055313)
                ·
                  refine ⟨11015475462271457806541485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14687300616361943742055313 11015475462271457806541485)
                  ·
                    refine ⟨4130803298351796677453057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11015475462271457806541485 4130803298351796677453057)
                    ·
                      refine ⟨3098102473763847508089793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4130803298351796677453057 3098102473763847508089793)
                      ·
                        rfl

theorem cell23_6033533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 3, 1, 2, 3, 2].length) (baseStart_6033533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6033533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6033533 prefixEnd_6033533 := by exact prefixLift 6033533
  have htrace : WordTrace (prefixWord ++ tailWord_6033533) baseStart_6033533 baseEnd_6033533 := by
    simpa [prefixWord, tailWord_6033533, baseEnd_6033533] using wordTrace_append hprefix tailTrace_6033533
  have hstable : (prefixWord ++ tailWord_6033533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6033533).length < 2 ^ (prefixWord ++ tailWord_6033533).sum := by decide
  have hdescent : baseEnd_6033533 < baseStart_6033533 := by decide
  rcases family_descends (prefixWord ++ tailWord_6033533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6033539 : List Nat := [1, 1, 1, 3, 3, 3, 2, 2, 1, 6]
def baseStart_6033539 : Nat := 118140960795 + 6033539 * 2 ^ 59
def prefixEnd_6033539 : Nat := 4983230072969 + 3 ^ 40 * 6033539 * 2
def baseEnd_6033539 : Nat := 1032701851549258161538255

theorem tailTrace_6033539 : CollatzResearch.WordTrace tailWord_6033539 prefixEnd_6033539 1032701851549258161538255 := by
  unfold tailWord_6033539
  simp only [CollatzResearch.WordTrace]
  refine ⟨220061246088526124268279671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146707497392350749512186447 220061246088526124268279671)
  ·
    refine ⟨330091869132789186402419507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220061246088526124268279671 330091869132789186402419507)
    ·
      refine ⟨495137803699183779603629261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 330091869132789186402419507 495137803699183779603629261)
      ·
        refine ⟨185676676387193917351360973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 495137803699183779603629261 185676676387193917351360973)
        ·
          refine ⟨69628753645197719006760365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 185676676387193917351360973 69628753645197719006760365)
          ·
            refine ⟨26110782616949144627535137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69628753645197719006760365 26110782616949144627535137)
            ·
              refine ⟨19583086962711858470651353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26110782616949144627535137 19583086962711858470651353)
              ·
                refine ⟨14687315222033893852988515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19583086962711858470651353 14687315222033893852988515)
                ·
                  refine ⟨22030972833050840779482773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14687315222033893852988515 22030972833050840779482773)
                  ·
                    refine ⟨1032701851549258161538255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22030972833050840779482773 1032701851549258161538255)
                    ·
                      rfl

theorem cell23_6033539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 2, 2, 1, 6].length) (baseStart_6033539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6033539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6033539 prefixEnd_6033539 := by exact prefixLift 6033539
  have htrace : WordTrace (prefixWord ++ tailWord_6033539) baseStart_6033539 baseEnd_6033539 := by
    simpa [prefixWord, tailWord_6033539, baseEnd_6033539] using wordTrace_append hprefix tailTrace_6033539
  have hstable : (prefixWord ++ tailWord_6033539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6033539).length < 2 ^ (prefixWord ++ tailWord_6033539).sum := by decide
  have hdescent : baseEnd_6033539 < baseStart_6033539 := by decide
  rcases family_descends (prefixWord ++ tailWord_6033539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6033540 : List Nat := [2, 3, 2, 1, 2, 1, 4, 3, 1, 1, 3]
def baseStart_6033540 : Nat := 118140960795 + 6033540 * 2 ^ 59
def prefixEnd_6033540 : Nat := 4983230072969 + 3 ^ 40 * 6033540 * 2
def baseEnd_6033540 : Nat := 3098106068128428980702261

theorem tailTrace_6033540 : CollatzResearch.WordTrace tailWord_6033540 prefixEnd_6033540 3098106068128428980702261 := by
  unfold tailWord_6033540
  simp only [CollatzResearch.WordTrace]
  refine ⟨110030641280761250719533037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146707521707681667626044049 110030641280761250719533037)
  ·
    refine ⟨41261490480285469019824889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110030641280761250719533037 41261490480285469019824889)
    ·
      refine ⟨30946117860214101764868667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41261490480285469019824889 30946117860214101764868667)
      ·
        refine ⟨46419176790321152647303001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30946117860214101764868667 46419176790321152647303001)
        ·
          refine ⟨34814382592740864485477251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46419176790321152647303001 34814382592740864485477251)
          ·
            refine ⟨52221573889111296728215877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34814382592740864485477251 52221573889111296728215877)
            ·
              refine ⟨9791545104208368136540477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 52221573889111296728215877 9791545104208368136540477)
              ·
                refine ⟨3671829414078138051202679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9791545104208368136540477 3671829414078138051202679)
                ·
                  refine ⟨5507744121117207076804019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3671829414078138051202679 5507744121117207076804019)
                  ·
                    refine ⟨8261616181675810615206029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5507744121117207076804019 8261616181675810615206029)
                    ·
                      refine ⟨3098106068128428980702261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8261616181675810615206029 3098106068128428980702261)
                      ·
                        rfl

theorem cell23_6033540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 4, 3, 1, 1, 3].length) (baseStart_6033540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6033540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6033540 prefixEnd_6033540 := by exact prefixLift 6033540
  have htrace : WordTrace (prefixWord ++ tailWord_6033540) baseStart_6033540 baseEnd_6033540 := by
    simpa [prefixWord, tailWord_6033540, baseEnd_6033540] using wordTrace_append hprefix tailTrace_6033540
  have hstable : (prefixWord ++ tailWord_6033540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6033540).length < 2 ^ (prefixWord ++ tailWord_6033540).sum := by decide
  have hdescent : baseEnd_6033540 < baseStart_6033540 := by decide
  rcases family_descends (prefixWord ++ tailWord_6033540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6033552 : List Nat := [2, 1, 1, 1, 1, 1, 16]
def baseStart_6033552 : Nat := 118140960795 + 6033552 * 2 ^ 59
def prefixEnd_6033552 : Nat := 4983230072969 + 3 ^ 40 * 6033552 * 2
def baseEnd_6033552 : Nat := 38248299134522011527805

theorem tailTrace_6033552 : CollatzResearch.WordTrace tailWord_6033552 prefixEnd_6033552 38248299134522011527805 := by
  unfold tailWord_6033552
  simp only [CollatzResearch.WordTrace]
  refine ⟨110030860118739513744251455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146707813491652684992335273 110030860118739513744251455)
  ·
    refine ⟨165046290178109270616377183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110030860118739513744251455 165046290178109270616377183)
    ·
      refine ⟨247569435267163905924565775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165046290178109270616377183 247569435267163905924565775)
      ·
        refine ⟨371354152900745858886848663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 247569435267163905924565775 371354152900745858886848663)
        ·
          refine ⟨557031229351118788330272995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 371354152900745858886848663 557031229351118788330272995)
          ·
            refine ⟨835546844026678182495409493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 557031229351118788330272995 835546844026678182495409493)
            ·
              refine ⟨38248299134522011527805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 16 835546844026678182495409493 38248299134522011527805)
              ·
                rfl

theorem cell23_6033552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 16].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 16].length) (baseStart_6033552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6033552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6033552 prefixEnd_6033552 := by exact prefixLift 6033552
  have htrace : WordTrace (prefixWord ++ tailWord_6033552) baseStart_6033552 baseEnd_6033552 := by
    simpa [prefixWord, tailWord_6033552, baseEnd_6033552] using wordTrace_append hprefix tailTrace_6033552
  have hstable : (prefixWord ++ tailWord_6033552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6033552).length < 2 ^ (prefixWord ++ tailWord_6033552).sum := by decide
  have hdescent : baseEnd_6033552 < baseStart_6033552 := by decide
  rcases family_descends (prefixWord ++ tailWord_6033552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6033573 : List Nat := [1, 3, 1, 2, 1, 3, 5, 1, 2, 4]
def baseStart_6033573 : Nat := 118140960795 + 6033573 * 2 ^ 59
def prefixEnd_6033573 : Nat := 4983230072969 + 3 ^ 40 * 6033573 * 2
def baseEnd_6033573 : Nat := 1032707670996675783863203

theorem tailTrace_6033573 : CollatzResearch.WordTrace tailWord_6033573 prefixEnd_6033573 1032707670996675783863203 := by
  unfold tailWord_6033573
  simp only [CollatzResearch.WordTrace]
  refine ⟨220062486170402948075017373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146708324113601965383344915 220062486170402948075017373)
  ·
    refine ⟨82523432313901105528131515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 220062486170402948075017373 82523432313901105528131515)
    ·
      refine ⟨123785148470851658292197273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82523432313901105528131515 123785148470851658292197273)
      ·
        refine ⟨92838861353138743719147955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123785148470851658292197273 92838861353138743719147955)
        ·
          refine ⟨139258292029708115578721933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92838861353138743719147955 139258292029708115578721933)
          ·
            refine ⟨52221859511140543342020725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 139258292029708115578721933 52221859511140543342020725)
            ·
              refine ⟨4895799329169425938314443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 52221859511140543342020725 4895799329169425938314443)
              ·
                refine ⟨7343698993754138907471665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4895799329169425938314443 7343698993754138907471665)
                ·
                  refine ⟨5507774245315604180603749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7343698993754138907471665 5507774245315604180603749)
                  ·
                    refine ⟨1032707670996675783863203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5507774245315604180603749 1032707670996675783863203)
                    ·
                      rfl

theorem cell23_6033573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 5, 1, 2, 4].length) (baseStart_6033573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6033573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6033573 prefixEnd_6033573 := by exact prefixLift 6033573
  have htrace : WordTrace (prefixWord ++ tailWord_6033573) baseStart_6033573 baseEnd_6033573 := by
    simpa [prefixWord, tailWord_6033573, baseEnd_6033573] using wordTrace_append hprefix tailTrace_6033573
  have hstable : (prefixWord ++ tailWord_6033573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6033573).length < 2 ^ (prefixWord ++ tailWord_6033573).sum := by decide
  have hdescent : baseEnd_6033573 < baseStart_6033573 := by decide
  rcases family_descends (prefixWord ++ tailWord_6033573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6033614 : List Nat := [4, 1, 1, 1, 4, 2, 3, 2, 1, 2, 2]
def baseStart_6033614 : Nat := 118140960795 + 6033614 * 2 ^ 59
def prefixEnd_6033614 : Nat := 4983230072969 + 3 ^ 40 * 6033614 * 2
def baseEnd_6033614 : Nat := 3098144065696861691176921

theorem tailTrace_6033614 : CollatzResearch.WordTrace tailWord_6033614 prefixEnd_6033614 3098144065696861691176921 := by
  unfold tailWord_6033614
  simp only [CollatzResearch.WordTrace]
  refine ⟨27507997695406801509657487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 146709321042169608051506597 27507997695406801509657487)
  ·
    refine ⟨41261996543110202264486231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27507997695406801509657487 41261996543110202264486231)
    ·
      refine ⟨61892994814665303396729347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41261996543110202264486231 61892994814665303396729347)
      ·
        refine ⟨92839492221997955095094021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61892994814665303396729347 92839492221997955095094021)
        ·
          refine ⟨17407404791624616580330129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 92839492221997955095094021 17407404791624616580330129)
          ·
            refine ⟨13055553593718462435247597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17407404791624616580330129 13055553593718462435247597)
            ·
              refine ⟨4895832597644423413217849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13055553593718462435247597 4895832597644423413217849)
              ·
                refine ⟨3671874448233317559913387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4895832597644423413217849 3671874448233317559913387)
                ·
                  refine ⟨5507811672349976339870081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3671874448233317559913387 5507811672349976339870081)
                  ·
                    refine ⟨4130858754262482254902561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5507811672349976339870081 4130858754262482254902561)
                    ·
                      refine ⟨3098144065696861691176921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4130858754262482254902561 3098144065696861691176921)
                      ·
                        rfl

theorem cell23_6033614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 3, 2, 1, 2, 2].length) (baseStart_6033614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6033614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6033614 prefixEnd_6033614 := by exact prefixLift 6033614
  have htrace : WordTrace (prefixWord ++ tailWord_6033614) baseStart_6033614 baseEnd_6033614 := by
    simpa [prefixWord, tailWord_6033614, baseEnd_6033614] using wordTrace_append hprefix tailTrace_6033614
  have hstable : (prefixWord ++ tailWord_6033614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6033614).length < 2 ^ (prefixWord ++ tailWord_6033614).sum := by decide
  have hdescent : baseEnd_6033614 < baseStart_6033614 := by decide
  rcases family_descends (prefixWord ++ tailWord_6033614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6033640 : List Nat := [2, 1, 4, 1, 2, 2, 3, 2, 1, 3, 2]
def baseStart_6033640 : Nat := 118140960795 + 6033640 * 2 ^ 59
def prefixEnd_6033640 : Nat := 4983230072969 + 3 ^ 40 * 6033640 * 2
def baseEnd_6033640 : Nat := 3098157416193878589451801

theorem tailTrace_6033640 : CollatzResearch.WordTrace tailWord_6033640 prefixEnd_6033640 3098157416193878589451801 := by
  unfold tailWord_6033640
  simp only [CollatzResearch.WordTrace]
  refine ⟨110032464930580109258853187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146709953240773479011804249 110032464930580109258853187)
  ·
    refine ⟨165048697395870163888279781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110032464930580109258853187 165048697395870163888279781)
    ·
      refine ⟨30946630761725655729052459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 165048697395870163888279781 30946630761725655729052459)
      ·
        refine ⟨46419946142588483593578689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30946630761725655729052459 46419946142588483593578689)
        ·
          refine ⟨34814959606941362695184017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46419946142588483593578689 34814959606941362695184017)
          ·
            refine ⟨26111219705206022021388013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34814959606941362695184017 26111219705206022021388013)
            ·
              refine ⟨9791707389452258258020505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26111219705206022021388013 9791707389452258258020505)
              ·
                refine ⟨7343780542089193693515379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9791707389452258258020505 7343780542089193693515379)
                ·
                  refine ⟨11015670813133790540273069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7343780542089193693515379 11015670813133790540273069)
                  ·
                    refine ⟨4130876554925171452602401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11015670813133790540273069 4130876554925171452602401)
                    ·
                      refine ⟨3098157416193878589451801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4130876554925171452602401 3098157416193878589451801)
                      ·
                        rfl

theorem cell23_6033640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 3, 2, 1, 3, 2].length) (baseStart_6033640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6033640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6033640 prefixEnd_6033640 := by exact prefixLift 6033640
  have htrace : WordTrace (prefixWord ++ tailWord_6033640) baseStart_6033640 baseEnd_6033640 := by
    simpa [prefixWord, tailWord_6033640, baseEnd_6033640] using wordTrace_append hprefix tailTrace_6033640
  have hstable : (prefixWord ++ tailWord_6033640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6033640).length < 2 ^ (prefixWord ++ tailWord_6033640).sum := by decide
  have hdescent : baseEnd_6033640 < baseStart_6033640 := by decide
  rcases family_descends (prefixWord ++ tailWord_6033640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6033693 : List Nat := [1, 4, 2, 3, 2, 1, 1, 2, 7]
def baseStart_6033693 : Nat := 118140960795 + 6033693 * 2 ^ 59
def prefixEnd_6033693 : Nat := 4983230072969 + 3 ^ 40 * 6033693 * 2
def baseEnd_6033693 : Nat := 344242736740951875787673

theorem tailTrace_6033693 : CollatzResearch.WordTrace tailWord_6033693 prefixEnd_6033693 344242736740951875787673 := by
  unfold tailWord_6033693
  simp only [CollatzResearch.WordTrace]
  refine ⟨220066862929968208569385733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146711241953312139046257155 220066862929968208569385733)
  ·
    refine ⟨41262536799369039106759825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 220066862929968208569385733 41262536799369039106759825)
    ·
      refine ⟨30946902599526779330069869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41262536799369039106759825 30946902599526779330069869)
      ·
        refine ⟨11605088474822542248776201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30946902599526779330069869 11605088474822542248776201)
        ·
          refine ⟨8703816356116906686582151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11605088474822542248776201 8703816356116906686582151)
          ·
            refine ⟨13055724534175360029873227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8703816356116906686582151 13055724534175360029873227)
            ·
              refine ⟨19583586801263040044809841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13055724534175360029873227 19583586801263040044809841)
              ·
                refine ⟨14687690100947280033607381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19583586801263040044809841 14687690100947280033607381)
                ·
                  refine ⟨344242736740951875787673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14687690100947280033607381 344242736740951875787673)
                  ·
                    rfl

theorem cell23_6033693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 1, 2, 7].length) (baseStart_6033693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6033693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6033693 prefixEnd_6033693 := by exact prefixLift 6033693
  have htrace : WordTrace (prefixWord ++ tailWord_6033693) baseStart_6033693 baseEnd_6033693 := by
    simpa [prefixWord, tailWord_6033693, baseEnd_6033693] using wordTrace_append hprefix tailTrace_6033693
  have hstable : (prefixWord ++ tailWord_6033693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6033693).length < 2 ^ (prefixWord ++ tailWord_6033693).sum := by decide
  have hdescent : baseEnd_6033693 < baseStart_6033693 := by decide
  rcases family_descends (prefixWord ++ tailWord_6033693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6033719 : List Nat := [1, 1, 3, 1, 2, 1, 1, 2, 1, 10]
def baseStart_6033719 : Nat := 118140960795 + 6033719 * 2 ^ 59
def prefixEnd_6033719 : Nat := 4983230072969 + 3 ^ 40 * 6033719 * 2
def baseEnd_6033719 : Nat := 1032732660388527926787979

theorem tailTrace_6033719 : CollatzResearch.WordTrace tailWord_6033719 prefixEnd_6033719 1032732660388527926787979 := by
  unfold tailWord_6033719
  simp only [CollatzResearch.WordTrace]
  refine ⟨220067811227874015009832211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146711874151916010006554807 220067811227874015009832211)
  ·
    refine ⟨330101716841811022514748317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220067811227874015009832211 330101716841811022514748317)
    ·
      refine ⟨123788143815679133443030619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 330101716841811022514748317 123788143815679133443030619)
      ·
        refine ⟨185682215723518700164545929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123788143815679133443030619 185682215723518700164545929)
        ·
          refine ⟨139261661792639025123409447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 185682215723518700164545929 139261661792639025123409447)
          ·
            refine ⟨208892492688958537685114171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139261661792639025123409447 208892492688958537685114171)
            ·
              refine ⟨313338739033437806527671257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 208892492688958537685114171 313338739033437806527671257)
              ·
                refine ⟨235004054275078354895753443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 313338739033437806527671257 235004054275078354895753443)
                ·
                  refine ⟨352506081412617532343630165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 235004054275078354895753443 352506081412617532343630165)
                  ·
                    refine ⟨1032732660388527926787979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 352506081412617532343630165 1032732660388527926787979)
                    ·
                      rfl

theorem cell23_6033719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 2, 1, 10].length) (baseStart_6033719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6033719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6033719 prefixEnd_6033719 := by exact prefixLift 6033719
  have htrace : WordTrace (prefixWord ++ tailWord_6033719) baseStart_6033719 baseEnd_6033719 := by
    simpa [prefixWord, tailWord_6033719, baseEnd_6033719] using wordTrace_append hprefix tailTrace_6033719
  have hstable : (prefixWord ++ tailWord_6033719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6033719).length < 2 ^ (prefixWord ++ tailWord_6033719).sum := by decide
  have hdescent : baseEnd_6033719 < baseStart_6033719 := by decide
  rcases family_descends (prefixWord ++ tailWord_6033719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6033763 : List Nat := [1, 1, 1, 5, 2, 1, 2, 3, 2, 2, 3]
def baseStart_6033763 : Nat := 118140960795 + 6033763 * 2 ^ 59
def prefixEnd_6033763 : Nat := 4983230072969 + 3 ^ 40 * 6033763 * 2
def baseEnd_6033763 : Nat := 3098220574314381608213735

theorem tailTrace_6033763 : CollatzResearch.WordTrace tailWord_6033763 prefixEnd_6033763 3098220574314381608213735 := by
  unfold tailWord_6033763
  simp only [CollatzResearch.WordTrace]
  refine ⟨220069416039714610524433943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146712944026476407016289295 220069416039714610524433943)
  ·
    refine ⟨330104124059571915786650915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220069416039714610524433943 330104124059571915786650915)
    ·
      refine ⟨495156186089357873679976373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 330104124059571915786650915 495156186089357873679976373)
      ·
        refine ⟨46420892445877300657497785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 495156186089357873679976373 46420892445877300657497785)
        ·
          refine ⟨34815669334407975493123339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46420892445877300657497785 34815669334407975493123339)
          ·
            refine ⟨52223504001611963239685009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34815669334407975493123339 52223504001611963239685009)
            ·
              refine ⟨39167628001208972429763757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52223504001611963239685009 39167628001208972429763757)
              ·
                refine ⟨14687860500453364661161409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39167628001208972429763757 14687860500453364661161409)
                ·
                  refine ⟨11015895375340023495871057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14687860500453364661161409 11015895375340023495871057)
                  ·
                    refine ⟨8261921531505017621903293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11015895375340023495871057 8261921531505017621903293)
                    ·
                      refine ⟨3098220574314381608213735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8261921531505017621903293 3098220574314381608213735)
                      ·
                        rfl

theorem cell23_6033763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 3, 2, 2, 3].length) (baseStart_6033763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6033763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6033763 prefixEnd_6033763 := by exact prefixLift 6033763
  have htrace : WordTrace (prefixWord ++ tailWord_6033763) baseStart_6033763 baseEnd_6033763 := by
    simpa [prefixWord, tailWord_6033763, baseEnd_6033763] using wordTrace_append hprefix tailTrace_6033763
  have hstable : (prefixWord ++ tailWord_6033763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6033763).length < 2 ^ (prefixWord ++ tailWord_6033763).sum := by decide
  have hdescent : baseEnd_6033763 < baseStart_6033763 := by decide
  rcases family_descends (prefixWord ++ tailWord_6033763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6033787 : List Nat := [1, 1, 1, 1, 1, 8, 3, 2, 1, 4]
def baseStart_6033787 : Nat := 118140960795 + 6033787 * 2 ^ 59
def prefixEnd_6033787 : Nat := 4983230072969 + 3 ^ 40 * 6033787 * 2
def baseEnd_6033787 : Nat := 1032744299283363171437875

theorem tailTrace_6033787 : CollatzResearch.WordTrace tailWord_6033787 prefixEnd_6033787 1032744299283363171437875 := by
  unfold tailWord_6033787
  simp only [CollatzResearch.WordTrace]
  refine ⟨220070291391627662623307615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146713527594418441748871743 220070291391627662623307615)
  ·
    refine ⟨330105437087441493934961423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220070291391627662623307615 330105437087441493934961423)
    ·
      refine ⟨495158155631162240902442135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 330105437087441493934961423 495158155631162240902442135)
      ·
        refine ⟨742737233446743361353663203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 495158155631162240902442135 742737233446743361353663203)
        ·
          refine ⟨1114105850170115042030494805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 742737233446743361353663203 1114105850170115042030494805)
          ·
            refine ⟨13055927931681035648794861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1114105850170115042030494805 13055927931681035648794861)
            ·
              refine ⟨4895972974380388368298073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13055927931681035648794861 4895972974380388368298073)
              ·
                refine ⟨3671979730785291276223555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4895972974380388368298073 3671979730785291276223555)
                ·
                  refine ⟨5507969596177936914335333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3671979730785291276223555 5507969596177936914335333)
                  ·
                    refine ⟨1032744299283363171437875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5507969596177936914335333 1032744299283363171437875)
                    ·
                      rfl

theorem cell23_6033787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 3, 2, 1, 4].length) (baseStart_6033787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6033787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6033787 prefixEnd_6033787 := by exact prefixLift 6033787
  have htrace : WordTrace (prefixWord ++ tailWord_6033787) baseStart_6033787 baseEnd_6033787 := by
    simpa [prefixWord, tailWord_6033787, baseEnd_6033787] using wordTrace_append hprefix tailTrace_6033787
  have hstable : (prefixWord ++ tailWord_6033787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6033787).length < 2 ^ (prefixWord ++ tailWord_6033787).sum := by decide
  have hdescent : baseEnd_6033787 < baseStart_6033787 := by decide
  rcases family_descends (prefixWord ++ tailWord_6033787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6033833 : List Nat := [1, 2, 1, 1, 1, 1, 3, 7, 1, 1, 4]
def baseStart_6033833 : Nat := 118140960795 + 6033833 * 2 ^ 59
def prefixEnd_6033833 : Nat := 4983230072969 + 3 ^ 40 * 6033833 * 2
def baseEnd_6033833 : Nat := 3098256517960196334338413

theorem tailTrace_6033833 : CollatzResearch.WordTrace tailWord_6033833 prefixEnd_6033833 3098256517960196334338413 := by
  unfold tailWord_6033833
  simp only [CollatzResearch.WordTrace]
  refine ⟨220071969149461012479482153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146714646099640674986321435 220071969149461012479482153)
  ·
    refine ⟨165053976862095759359611615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 220071969149461012479482153 165053976862095759359611615)
    ·
      refine ⟨247580965293143639039417423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165053976862095759359611615 247580965293143639039417423)
      ·
        refine ⟨371371447939715458559126135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 247580965293143639039417423 371371447939715458559126135)
        ·
          refine ⟨557057171909573187838689203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 371371447939715458559126135 557057171909573187838689203)
          ·
            refine ⟨835585757864359781758033805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 557057171909573187838689203 835585757864359781758033805)
            ·
              refine ⟨313344659199134918159262677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 835585757864359781758033805 313344659199134918159262677)
              ·
                refine ⟨7344015449979724644357719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 313344659199134918159262677 7344015449979724644357719)
                ·
                  refine ⟨11016023174969586966536579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7344015449979724644357719 11016023174969586966536579)
                  ·
                    refine ⟨16524034762454380449804869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11016023174969586966536579 16524034762454380449804869)
                    ·
                      refine ⟨3098256517960196334338413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16524034762454380449804869 3098256517960196334338413)
                      ·
                        rfl

theorem cell23_6033833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 7, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 7, 1, 1, 4].length) (baseStart_6033833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6033833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6033833 prefixEnd_6033833 := by exact prefixLift 6033833
  have htrace : WordTrace (prefixWord ++ tailWord_6033833) baseStart_6033833 baseEnd_6033833 := by
    simpa [prefixWord, tailWord_6033833, baseEnd_6033833] using wordTrace_append hprefix tailTrace_6033833
  have hstable : (prefixWord ++ tailWord_6033833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6033833).length < 2 ^ (prefixWord ++ tailWord_6033833).sum := by decide
  have hdescent : baseEnd_6033833 < baseStart_6033833 := by decide
  rcases family_descends (prefixWord ++ tailWord_6033833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6033834 : List Nat := [3, 1, 6, 1, 1, 1, 2, 2, 6]
def baseStart_6033834 : Nat := 118140960795 + 6033834 * 2 ^ 59
def prefixEnd_6033834 : Nat := 4983230072969 + 3 ^ 40 * 6033834 * 2
def baseEnd_6033834 : Nat := 344250781271205647825101

theorem tailTrace_6033834 : CollatzResearch.WordTrace tailWord_6033834 prefixEnd_6033834 344250781271205647825101 := by
  unfold tailWord_6033834
  simp only [CollatzResearch.WordTrace]
  refine ⟨55018001405614347412567139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146714670414971593100179037 55018001405614347412567139)
  ·
    refine ⟨82527002108421521118850709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55018001405614347412567139 82527002108421521118850709)
    ·
      refine ⟨3868453223832258802446127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 82527002108421521118850709 3868453223832258802446127)
      ·
        refine ⟨5802679835748388203669191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3868453223832258802446127 5802679835748388203669191)
        ·
          refine ⟨8704019753622582305503787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5802679835748388203669191 8704019753622582305503787)
          ·
            refine ⟨13056029630433873458255681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8704019753622582305503787 13056029630433873458255681)
            ·
              refine ⟨9792022222825405093691761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13056029630433873458255681 9792022222825405093691761)
              ·
                refine ⟨7344016667119053820268821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9792022222825405093691761 7344016667119053820268821)
                ·
                  refine ⟨344250781271205647825101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7344016667119053820268821 344250781271205647825101)
                  ·
                    rfl

theorem cell23_6033834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 2, 2, 6].length) (baseStart_6033834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6033834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6033834 prefixEnd_6033834 := by exact prefixLift 6033834
  have htrace : WordTrace (prefixWord ++ tailWord_6033834) baseStart_6033834 baseEnd_6033834 := by
    simpa [prefixWord, tailWord_6033834, baseEnd_6033834] using wordTrace_append hprefix tailTrace_6033834
  have hstable : (prefixWord ++ tailWord_6033834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6033834).length < 2 ^ (prefixWord ++ tailWord_6033834).sum := by decide
  have hdescent : baseEnd_6033834 < baseStart_6033834 := by decide
  rcases family_descends (prefixWord ++ tailWord_6033834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6033850 : List Nat := [3, 1, 1, 1, 2, 1, 1, 2, 7, 2, 2]
def baseStart_6033850 : Nat := 118140960795 + 6033850 * 2 ^ 59
def prefixEnd_6033850 : Nat := 4983230072969 + 3 ^ 40 * 6033850 * 2
def baseEnd_6033850 : Nat := 3098265247131322767825835

theorem tailTrace_6033850 : CollatzResearch.WordTrace tailWord_6033850 prefixEnd_6033850 3098265247131322767825835 := by
  unfold tailWord_6033850
  simp only [CollatzResearch.WordTrace]
  refine ⟨55018147297599856095712751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146715059460266282921900669 55018147297599856095712751)
  ·
    refine ⟨82527220946399784143569127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55018147297599856095712751 82527220946399784143569127)
    ·
      refine ⟨123790831419599676215353691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82527220946399784143569127 123790831419599676215353691)
      ·
        refine ⟨185686247129399514323030537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123790831419599676215353691 185686247129399514323030537)
        ·
          refine ⟨139264685347049635742272903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 185686247129399514323030537 139264685347049635742272903)
          ·
            refine ⟨208897028020574453613409355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139264685347049635742272903 208897028020574453613409355)
            ·
              refine ⟨313345542030861680420114033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 208897028020574453613409355 313345542030861680420114033)
              ·
                refine ⟨235009156523146260315085525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 313345542030861680420114033 235009156523146260315085525)
                ·
                  refine ⟨5508027106011240476134817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 235009156523146260315085525 5508027106011240476134817)
                  ·
                    refine ⟨4131020329508430357101113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5508027106011240476134817 4131020329508430357101113)
                    ·
                      refine ⟨3098265247131322767825835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4131020329508430357101113 3098265247131322767825835)
                      ·
                        rfl

theorem cell23_6033850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 2, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 2, 7, 2, 2].length) (baseStart_6033850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6033850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6033850 prefixEnd_6033850 := by exact prefixLift 6033850
  have htrace : WordTrace (prefixWord ++ tailWord_6033850) baseStart_6033850 baseEnd_6033850 := by
    simpa [prefixWord, tailWord_6033850, baseEnd_6033850] using wordTrace_append hprefix tailTrace_6033850
  have hstable : (prefixWord ++ tailWord_6033850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6033850).length < 2 ^ (prefixWord ++ tailWord_6033850).sum := by decide
  have hdescent : baseEnd_6033850 < baseStart_6033850 := by decide
  rcases family_descends (prefixWord ++ tailWord_6033850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6033863 : List Nat := [1, 1, 4, 1, 1, 4, 1, 3, 1, 2, 4]
def baseStart_6033863 : Nat := 118140960795 + 6033863 * 2 ^ 59
def prefixEnd_6033863 : Nat := 4983230072969 + 3 ^ 40 * 6033863 * 2
def baseEnd_6033863 : Nat := 3098271922379831216963275

theorem tailTrace_6033863 : CollatzResearch.WordTrace tailWord_6033863 prefixEnd_6033863 3098271922379831216963275 := by
  unfold tailWord_6033863
  simp only [CollatzResearch.WordTrace]
  refine ⟨220073063339352327603074243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146715375559568218402049495 220073063339352327603074243)
  ·
    refine ⟨330109595009028491404611365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220073063339352327603074243 330109595009028491404611365)
    ·
      refine ⟨61895549064192842138364631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 330109595009028491404611365 61895549064192842138364631)
      ·
        refine ⟨92843323596289263207546947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61895549064192842138364631 92843323596289263207546947)
        ·
          refine ⟨139264985394433894811320421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92843323596289263207546947 139264985394433894811320421)
          ·
            refine ⟨26112184761456355277122579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 139264985394433894811320421 26112184761456355277122579)
            ·
              refine ⟨39168277142184532915683869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26112184761456355277122579 39168277142184532915683869)
              ·
                refine ⟨14688103928319199843381451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39168277142184532915683869 14688103928319199843381451)
                ·
                  refine ⟨22032155892478799765072177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14688103928319199843381451 22032155892478799765072177)
                  ·
                    refine ⟨16524116919359099823804133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22032155892478799765072177 16524116919359099823804133)
                    ·
                      refine ⟨3098271922379831216963275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16524116919359099823804133 3098271922379831216963275)
                      ·
                        rfl

theorem cell23_6033863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 3, 1, 2, 4].length) (baseStart_6033863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6033863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6033863 prefixEnd_6033863 := by exact prefixLift 6033863
  have htrace : WordTrace (prefixWord ++ tailWord_6033863) baseStart_6033863 baseEnd_6033863 := by
    simpa [prefixWord, tailWord_6033863, baseEnd_6033863] using wordTrace_append hprefix tailTrace_6033863
  have hstable : (prefixWord ++ tailWord_6033863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6033863).length < 2 ^ (prefixWord ++ tailWord_6033863).sum := by decide
  have hdescent : baseEnd_6033863 < baseStart_6033863 := by decide
  rcases family_descends (prefixWord ++ tailWord_6033863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6033870 : List Nat := [4, 1, 1, 1, 2, 1, 1, 6, 1, 2, 3]
def baseStart_6033870 : Nat := 118140960795 + 6033870 * 2 ^ 59
def prefixEnd_6033870 : Nat := 4983230072969 + 3 ^ 40 * 6033870 * 2
def baseEnd_6033870 : Nat := 3098275516744412689575743

theorem tailTrace_6033870 : CollatzResearch.WordTrace tailWord_6033870 prefixEnd_6033870 3098275516744412689575743 := by
  unfold tailWord_6033870
  simp only [CollatzResearch.WordTrace]
  refine ⟨27509164831290870974822383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 146715545766884645199052709 27509164831290870974822383)
  ·
    refine ⟨41263747246936306462233575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27509164831290870974822383 41263747246936306462233575)
    ·
      refine ⟨61895620870404459693350363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41263747246936306462233575 61895620870404459693350363)
      ·
        refine ⟨92843431305606689540025545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61895620870404459693350363 92843431305606689540025545)
        ·
          refine ⟨69632573479205017155019159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92843431305606689540025545 69632573479205017155019159)
          ·
            refine ⟨104448860218807525732528739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69632573479205017155019159 104448860218807525732528739)
            ·
              refine ⟨156673290328211288598793109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104448860218807525732528739 156673290328211288598793109)
              ·
                refine ⟨7344060484134904153068427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 156673290328211288598793109 7344060484134904153068427)
                ·
                  refine ⟨11016090726202356229602641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7344060484134904153068427 11016090726202356229602641)
                  ·
                    refine ⟨8262068044651767172201981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11016090726202356229602641 8262068044651767172201981)
                    ·
                      refine ⟨3098275516744412689575743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8262068044651767172201981 3098275516744412689575743)
                      ·
                        rfl

theorem cell23_6033870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 6, 1, 2, 3].length) (baseStart_6033870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6033870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6033870 prefixEnd_6033870 := by exact prefixLift 6033870
  have htrace : WordTrace (prefixWord ++ tailWord_6033870) baseStart_6033870 baseEnd_6033870 := by
    simpa [prefixWord, tailWord_6033870, baseEnd_6033870] using wordTrace_append hprefix tailTrace_6033870
  have hstable : (prefixWord ++ tailWord_6033870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6033870).length < 2 ^ (prefixWord ++ tailWord_6033870).sum := by decide
  have hdescent : baseEnd_6033870 < baseStart_6033870 := by decide
  rcases family_descends (prefixWord ++ tailWord_6033870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6033887 : List Nat := [1, 1, 2, 3, 3, 2, 4, 1, 1, 2, 3]
def baseStart_6033887 : Nat := 118140960795 + 6033887 * 2 ^ 59
def prefixEnd_6033887 : Nat := 4983230072969 + 3 ^ 40 * 6033887 * 2
def baseEnd_6033887 : Nat := 3098284245915539123063165

theorem tailTrace_6033887 : CollatzResearch.WordTrace tailWord_6033887 prefixEnd_6033887 3098284245915539123063165 := by
  unfold tailWord_6033887
  simp only [CollatzResearch.WordTrace]
  refine ⟨220073938691265379701947915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146715959127510253134631943 220073938691265379701947915)
  ·
    refine ⟨330110908036898069552921873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220073938691265379701947915 330110908036898069552921873)
    ·
      refine ⟨247583181027673552164691405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 330110908036898069552921873 247583181027673552164691405)
      ·
        refine ⟨92843692885377582061759277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 247583181027673552164691405 92843692885377582061759277)
        ·
          refine ⟨34816384832016593273159729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 92843692885377582061759277 34816384832016593273159729)
          ·
            refine ⟨26112288624012444954869797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34816384832016593273159729 26112288624012444954869797)
            ·
              refine ⟨4896054117002333429038087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26112288624012444954869797 4896054117002333429038087)
              ·
                refine ⟨7344081175503500143557131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4896054117002333429038087 7344081175503500143557131)
                ·
                  refine ⟨11016121763255250215335697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7344081175503500143557131 11016121763255250215335697)
                  ·
                    refine ⟨8262091322441437661501773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11016121763255250215335697 8262091322441437661501773)
                    ·
                      refine ⟨3098284245915539123063165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8262091322441437661501773 3098284245915539123063165)
                      ·
                        rfl

theorem cell23_6033887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 4, 1, 1, 2, 3].length) (baseStart_6033887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6033887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6033887 prefixEnd_6033887 := by exact prefixLift 6033887
  have htrace : WordTrace (prefixWord ++ tailWord_6033887) baseStart_6033887 baseEnd_6033887 := by
    simpa [prefixWord, tailWord_6033887, baseEnd_6033887] using wordTrace_append hprefix tailTrace_6033887
  have hstable : (prefixWord ++ tailWord_6033887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6033887).length < 2 ^ (prefixWord ++ tailWord_6033887).sum := by decide
  have hdescent : baseEnd_6033887 < baseStart_6033887 := by decide
  rcases family_descends (prefixWord ++ tailWord_6033887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6033900 : List Nat := [2, 2, 1, 1, 2, 1, 5, 1, 4, 1, 3]
def baseStart_6033900 : Nat := 118140960795 + 6033900 * 2 ^ 59
def prefixEnd_6033900 : Nat := 4983230072969 + 3 ^ 40 * 6033900 * 2
def baseEnd_6033900 : Nat := 3098290921164047572200605

theorem tailTrace_6033900 : CollatzResearch.WordTrace tailWord_6033900 prefixEnd_6033900 3098290921164047572200605 := by
  unfold tailWord_6033900
  simp only [CollatzResearch.WordTrace]
  refine ⟨110037206420109141461085577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146716275226812188614780769 110037206420109141461085577)
  ·
    refine ⟨82527904815081856095814183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110037206420109141461085577 82527904815081856095814183)
    ·
      refine ⟨123791857222622784143721275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82527904815081856095814183 123791857222622784143721275)
      ·
        refine ⟨185687785833934176215581913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123791857222622784143721275 185687785833934176215581913)
        ·
          refine ⟨139265839375450632161686435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 185687785833934176215581913 139265839375450632161686435)
          ·
            refine ⟨208898759063175948242529653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139265839375450632161686435 208898759063175948242529653)
            ·
              refine ⟨19584258662172745147737155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 208898759063175948242529653 19584258662172745147737155)
              ·
                refine ⟨29376387993259117721605733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19584258662172745147737155 29376387993259117721605733)
                ·
                  refine ⟨5508072748736084572801075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29376387993259117721605733 5508072748736084572801075)
                  ·
                    refine ⟨8262109123104126859201613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5508072748736084572801075 8262109123104126859201613)
                    ·
                      refine ⟨3098290921164047572200605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8262109123104126859201613 3098290921164047572200605)
                      ·
                        rfl

theorem cell23_6033900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 4, 1, 3].length) (baseStart_6033900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6033900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6033900 prefixEnd_6033900 := by exact prefixLift 6033900
  have htrace : WordTrace (prefixWord ++ tailWord_6033900) baseStart_6033900 baseEnd_6033900 := by
    simpa [prefixWord, tailWord_6033900, baseEnd_6033900] using wordTrace_append hprefix tailTrace_6033900
  have hstable : (prefixWord ++ tailWord_6033900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6033900).length < 2 ^ (prefixWord ++ tailWord_6033900).sum := by decide
  have hdescent : baseEnd_6033900 < baseStart_6033900 := by decide
  rcases family_descends (prefixWord ++ tailWord_6033900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6033901 : List Nat := [1, 5, 1, 3, 1, 1, 2, 4, 1, 2, 2]
def baseStart_6033901 : Nat := 118140960795 + 6033901 * 2 ^ 59
def prefixEnd_6033901 : Nat := 4983230072969 + 3 ^ 40 * 6033901 * 2
def baseEnd_6033901 : Nat := 3098291434644702068288101

theorem tailTrace_6033901 : CollatzResearch.WordTrace tailWord_6033901 prefixEnd_6033901 3098291434644702068288101 := by
  unfold tailWord_6033901
  simp only [CollatzResearch.WordTrace]
  refine ⟨220074449313214660092957557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146716299542143106728638371 220074449313214660092957557)
  ·
    refine ⟨20631979623113874383714771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 220074449313214660092957557 20631979623113874383714771)
    ·
      refine ⟨30947969434670811575572157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20631979623113874383714771 30947969434670811575572157)
      ·
        refine ⟨11605488538001554340839559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30947969434670811575572157 11605488538001554340839559)
        ·
          refine ⟨17408232807002331511259339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11605488538001554340839559 17408232807002331511259339)
          ·
            refine ⟨26112349210503497266889009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17408232807002331511259339 26112349210503497266889009)
            ·
              refine ⟨19584261907877622950166757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26112349210503497266889009 19584261907877622950166757)
              ·
                refine ⟨3672049107727054303156267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19584261907877622950166757 3672049107727054303156267)
                ·
                  refine ⟨5508073661590581454734401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3672049107727054303156267 5508073661590581454734401)
                  ·
                    refine ⟨4131055246192936091050801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5508073661590581454734401 4131055246192936091050801)
                    ·
                      refine ⟨3098291434644702068288101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4131055246192936091050801 3098291434644702068288101)
                      ·
                        rfl

theorem cell23_6033901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 2, 4, 1, 2, 2].length) (baseStart_6033901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6033901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6033901 prefixEnd_6033901 := by exact prefixLift 6033901
  have htrace : WordTrace (prefixWord ++ tailWord_6033901) baseStart_6033901 baseEnd_6033901 := by
    simpa [prefixWord, tailWord_6033901, baseEnd_6033901] using wordTrace_append hprefix tailTrace_6033901
  have hstable : (prefixWord ++ tailWord_6033901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6033901).length < 2 ^ (prefixWord ++ tailWord_6033901).sum := by decide
  have hdescent : baseEnd_6033901 < baseStart_6033901 := by decide
  rcases family_descends (prefixWord ++ tailWord_6033901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6033957 : List Nat := [1, 3, 1, 2, 2, 1, 4, 1, 4, 2, 2]
def baseStart_6033957 : Nat := 118140960795 + 6033957 * 2 ^ 59
def prefixEnd_6033957 : Nat := 4983230072969 + 3 ^ 40 * 6033957 * 2
def baseEnd_6033957 : Nat := 3098320189561353849187843

theorem tailTrace_6033957 : CollatzResearch.WordTrace tailWord_6033957 prefixEnd_6033957 3098320189561353849187843 := by
  unfold tailWord_6033957
  simp only [CollatzResearch.WordTrace]
  refine ⟨220076491801011781656996125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146717661200674521104664083 220076491801011781656996125)
  ·
    refine ⟨82528684425379418121373547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 220076491801011781656996125 82528684425379418121373547)
    ·
      refine ⟨123793026638069127182060321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82528684425379418121373547 123793026638069127182060321)
      ·
        refine ⟨92844769978551845386545241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123793026638069127182060321 92844769978551845386545241)
        ·
          refine ⟨69633577483913884039908931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92844769978551845386545241 69633577483913884039908931)
          ·
            refine ⟨104450366225870826059863397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69633577483913884039908931 104450366225870826059863397)
            ·
              refine ⟨19584443667350779886224387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 104450366225870826059863397 19584443667350779886224387)
              ·
                refine ⟨29376665501026169829336581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19584443667350779886224387 29376665501026169829336581)
                ·
                  refine ⟨5508124781442406843000609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29376665501026169829336581 5508124781442406843000609)
                  ·
                    refine ⟨4131093586081805132250457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5508124781442406843000609 4131093586081805132250457)
                    ·
                      refine ⟨3098320189561353849187843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4131093586081805132250457 3098320189561353849187843)
                      ·
                        rfl

theorem cell23_6033957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 4, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 4, 1, 4, 2, 2].length) (baseStart_6033957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6033957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6033957 prefixEnd_6033957 := by exact prefixLift 6033957
  have htrace : WordTrace (prefixWord ++ tailWord_6033957) baseStart_6033957 baseEnd_6033957 := by
    simpa [prefixWord, tailWord_6033957, baseEnd_6033957] using wordTrace_append hprefix tailTrace_6033957
  have hstable : (prefixWord ++ tailWord_6033957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6033957).length < 2 ^ (prefixWord ++ tailWord_6033957).sum := by decide
  have hdescent : baseEnd_6033957 < baseStart_6033957 := by decide
  rcases family_descends (prefixWord ++ tailWord_6033957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6034023 : List Nat := [1, 1, 5, 1, 1, 1, 1, 2, 2, 8]
def baseStart_6034023 : Nat := 118140960795 + 6034023 * 2 ^ 59
def prefixEnd_6034023 : Nat := 4983230072969 + 3 ^ 40 * 6034023 * 2
def baseEnd_6034023 : Nat := 1032784693094850196987513

theorem tailTrace_6034023 : CollatzResearch.WordTrace tailWord_6034023 prefixEnd_6034023 1032784693094850196987513 := by
  unfold tailWord_6034023
  simp only [CollatzResearch.WordTrace]
  refine ⟨220078899018772674928898723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146719266012515116619265815 220078899018772674928898723)
  ·
    refine ⟨330118348528159012393348085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220078899018772674928898723 330118348528159012393348085)
    ·
      refine ⟨30948595174514907411876383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 330118348528159012393348085 30948595174514907411876383)
      ·
        refine ⟨46422892761772361117814575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30948595174514907411876383 46422892761772361117814575)
        ·
          refine ⟨69634339142658541676721863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46422892761772361117814575 69634339142658541676721863)
          ·
            refine ⟨104451508713987812515082795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69634339142658541676721863 104451508713987812515082795)
            ·
              refine ⟨156677263070981718772624193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104451508713987812515082795 156677263070981718772624193)
              ·
                refine ⟨117507947303236289079468145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 156677263070981718772624193 117507947303236289079468145)
                ·
                  refine ⟨88130960477427216809601109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 117507947303236289079468145 88130960477427216809601109)
                  ·
                    refine ⟨1032784693094850196987513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 88130960477427216809601109 1032784693094850196987513)
                    ·
                      rfl

theorem cell23_6034023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 2, 2, 8].length) (baseStart_6034023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6034023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6034023 prefixEnd_6034023 := by exact prefixLift 6034023
  have htrace : WordTrace (prefixWord ++ tailWord_6034023) baseStart_6034023 baseEnd_6034023 := by
    simpa [prefixWord, tailWord_6034023, baseEnd_6034023] using wordTrace_append hprefix tailTrace_6034023
  have hstable : (prefixWord ++ tailWord_6034023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6034023).length < 2 ^ (prefixWord ++ tailWord_6034023).sum := by decide
  have hdescent : baseEnd_6034023 < baseStart_6034023 := by decide
  rcases family_descends (prefixWord ++ tailWord_6034023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6034040 : List Nat := [2, 1, 2, 1, 1, 1, 2, 6, 3, 4]
def baseStart_6034040 : Nat := 118140960795 + 6034040 * 2 ^ 59
def prefixEnd_6034040 : Nat := 4983230072969 + 3 ^ 40 * 6034040 * 2
def baseEnd_6034040 : Nat := 1032787602818559008149987

theorem tailTrace_6034040 : CollatzResearch.WordTrace tailWord_6034040 prefixEnd_6034040 1032787602818559008149987 := by
  unfold tailWord_6034040
  simp only [CollatzResearch.WordTrace]
  refine ⟨110039759529855543416133787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146719679373140724554845049 110039759529855543416133787)
  ·
    refine ⟨165059639294783315124200681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110039759529855543416133787 165059639294783315124200681)
    ·
      refine ⟨123794729471087486343150511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 165059639294783315124200681 123794729471087486343150511)
      ·
        refine ⟨185692094206631229514725767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123794729471087486343150511 185692094206631229514725767)
        ·
          refine ⟨278538141309946844272088651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 185692094206631229514725767 278538141309946844272088651)
          ·
            refine ⟨417807211964920266408132977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 278538141309946844272088651 417807211964920266408132977)
            ·
              refine ⟨313355408973690199806099733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 417807211964920266408132977 313355408973690199806099733)
              ·
                refine ⟨14688534795641728115910925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 313355408973690199806099733 14688534795641728115910925)
                ·
                  refine ⟨5508200548365648043466597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14688534795641728115910925 5508200548365648043466597)
                  ·
                    refine ⟨1032787602818559008149987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5508200548365648043466597 1032787602818559008149987)
                    ·
                      rfl

theorem cell23_6034040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 6, 3, 4].length) (baseStart_6034040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6034040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6034040 prefixEnd_6034040 := by exact prefixLift 6034040
  have htrace : WordTrace (prefixWord ++ tailWord_6034040) baseStart_6034040 baseEnd_6034040 := by
    simpa [prefixWord, tailWord_6034040, baseEnd_6034040] using wordTrace_append hprefix tailTrace_6034040
  have hstable : (prefixWord ++ tailWord_6034040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6034040).length < 2 ^ (prefixWord ++ tailWord_6034040).sum := by decide
  have hdescent : baseEnd_6034040 < baseStart_6034040 := by decide
  rcases family_descends (prefixWord ++ tailWord_6034040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6034043 : List Nat := [1, 1, 1, 1, 1, 4, 2, 1, 1, 6, 4]
def baseStart_6034043 : Nat := 118140960795 + 6034043 * 2 ^ 59
def prefixEnd_6034043 : Nat := 4983230072969 + 3 ^ 40 * 6034043 * 2
def baseEnd_6034043 : Nat := 3098364348897640512712447

theorem tailTrace_6034043 : CollatzResearch.WordTrace tailWord_6034043 prefixEnd_6034043 3098364348897640512712447 := by
  unfold tailWord_6034043
  simp only [CollatzResearch.WordTrace]
  refine ⟨220079628478700218344626783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146719752319133478896417855 220079628478700218344626783)
  ·
    refine ⟨330119442718050327516940175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220079628478700218344626783 330119442718050327516940175)
    ·
      refine ⟨495179164077075491275410263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 330119442718050327516940175 495179164077075491275410263)
      ·
        refine ⟨742768746115613236913115395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 495179164077075491275410263 742768746115613236913115395)
        ·
          refine ⟨1114153119173419855369673093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 742768746115613236913115395 1114153119173419855369673093)
          ·
            refine ⟨208903709845016222881813705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1114153119173419855369673093 208903709845016222881813705)
            ·
              refine ⟨156677782383762167161360279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 208903709845016222881813705 156677782383762167161360279)
              ·
                refine ⟨235016673575643250742040419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 156677782383762167161360279 235016673575643250742040419)
                ·
                  refine ⟨352525010363464876113060629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 235016673575643250742040419 352525010363464876113060629)
                  ·
                    refine ⟨16524609860787416067799717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 352525010363464876113060629 16524609860787416067799717)
                    ·
                      refine ⟨3098364348897640512712447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16524609860787416067799717 3098364348897640512712447)
                      ·
                        rfl

theorem cell23_6034043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 1, 1, 6, 4].length) (baseStart_6034043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6034043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6034043 prefixEnd_6034043 := by exact prefixLift 6034043
  have htrace : WordTrace (prefixWord ++ tailWord_6034043) baseStart_6034043 baseEnd_6034043 := by
    simpa [prefixWord, tailWord_6034043, baseEnd_6034043] using wordTrace_append hprefix tailTrace_6034043
  have hstable : (prefixWord ++ tailWord_6034043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6034043).length < 2 ^ (prefixWord ++ tailWord_6034043).sum := by decide
  have hdescent : baseEnd_6034043 < baseStart_6034043 := by decide
  rcases family_descends (prefixWord ++ tailWord_6034043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6034073 : List Nat := [1, 2, 1, 2, 1, 2, 3, 1, 1, 1, 8]
def baseStart_6034073 : Nat := 118140960795 + 6034073 * 2 ^ 59
def prefixEnd_6034073 : Nat := 4983230072969 + 3 ^ 40 * 6034073 * 2
def baseEnd_6034073 : Nat := 3098379753317275395337309

theorem tailTrace_6034073 : CollatzResearch.WordTrace tailWord_6034073 prefixEnd_6034073 3098379753317275395337309 := by
  unfold tailWord_6034073
  simp only [CollatzResearch.WordTrace]
  refine ⟨220080722668591533468218873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146720481779061022312145915 220080722668591533468218873)
  ·
    refine ⟨165060542001443650101164155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 220080722668591533468218873 165060542001443650101164155)
    ·
      refine ⟨247590813002165475151746233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165060542001443650101164155 247590813002165475151746233)
      ·
        refine ⟨185693109751624106363809675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 247590813002165475151746233 185693109751624106363809675)
        ·
          refine ⟨278539664627436159545714513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 185693109751624106363809675 278539664627436159545714513)
          ·
            refine ⟨208904748470577119659285885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 278539664627436159545714513 208904748470577119659285885)
            ·
              refine ⟨78339280676466419872232207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 208904748470577119659285885 78339280676466419872232207)
              ·
                refine ⟨117508921014699629808348311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78339280676466419872232207 117508921014699629808348311)
                ·
                  refine ⟨176263381522049444712522467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 117508921014699629808348311 176263381522049444712522467)
                  ·
                    refine ⟨264395072283074167068783701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 176263381522049444712522467 264395072283074167068783701)
                    ·
                      refine ⟨3098379753317275395337309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 264395072283074167068783701 3098379753317275395337309)
                      ·
                        rfl

theorem cell23_6034073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 1, 1, 1, 8].length) (baseStart_6034073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6034073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6034073 prefixEnd_6034073 := by exact prefixLift 6034073
  have htrace : WordTrace (prefixWord ++ tailWord_6034073) baseStart_6034073 baseEnd_6034073 := by
    simpa [prefixWord, tailWord_6034073, baseEnd_6034073] using wordTrace_append hprefix tailTrace_6034073
  have hstable : (prefixWord ++ tailWord_6034073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6034073).length < 2 ^ (prefixWord ++ tailWord_6034073).sum := by decide
  have hdescent : baseEnd_6034073 < baseStart_6034073 := by decide
  rcases family_descends (prefixWord ++ tailWord_6034073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6034083 : List Nat := [1, 1, 1, 4, 1, 1, 2, 1, 2, 9]
def baseStart_6034083 : Nat := 118140960795 + 6034083 * 2 ^ 59
def prefixEnd_6034083 : Nat := 4983230072969 + 3 ^ 40 * 6034083 * 2
def baseEnd_6034083 : Nat := 1032794962707940118737421

theorem tailTrace_6034083 : CollatzResearch.WordTrace tailWord_6034083 prefixEnd_6034083 1032794962707940118737421 := by
  unfold tailWord_6034083
  simp only [CollatzResearch.WordTrace]
  refine ⟨220081087398555305176082903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146720724932370203450721935 220081087398555305176082903)
  ·
    refine ⟨330121631097832957764124355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220081087398555305176082903 330121631097832957764124355)
    ·
      refine ⟨495182446646749436646186533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 330121631097832957764124355 495182446646749436646186533)
      ·
        refine ⟨92846708746265519371159975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 495182446646749436646186533 92846708746265519371159975)
        ·
          refine ⟨139270063119398279056739963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92846708746265519371159975 139270063119398279056739963)
          ·
            refine ⟨208905094679097418585109945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139270063119398279056739963 208905094679097418585109945)
            ·
              refine ⟨156678821009323063938832459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 208905094679097418585109945 156678821009323063938832459)
              ·
                refine ⟨235018231513984595908248689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 156678821009323063938832459 235018231513984595908248689)
                ·
                  refine ⟨176263673635488446931186517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 235018231513984595908248689 176263673635488446931186517)
                  ·
                    refine ⟨1032794962707940118737421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 176263673635488446931186517 1032794962707940118737421)
                    ·
                      rfl

theorem cell23_6034083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 1, 2, 9].length) (baseStart_6034083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6034083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6034083 prefixEnd_6034083 := by exact prefixLift 6034083
  have htrace : WordTrace (prefixWord ++ tailWord_6034083) baseStart_6034083 baseEnd_6034083 := by
    simpa [prefixWord, tailWord_6034083, baseEnd_6034083] using wordTrace_append hprefix tailTrace_6034083
  have hstable : (prefixWord ++ tailWord_6034083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6034083).length < 2 ^ (prefixWord ++ tailWord_6034083).sum := by decide
  have hdescent : baseEnd_6034083 < baseStart_6034083 := by decide
  rcases family_descends (prefixWord ++ tailWord_6034083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6034118 : List Nat := [6, 1, 2, 1, 2, 1, 1, 2, 2, 2, 3]
def baseStart_6034118 : Nat := 118140960795 + 6034118 * 2 ^ 59
def prefixEnd_6034118 : Nat := 4983230072969 + 3 ^ 40 * 6034118 * 2
def baseEnd_6034118 : Nat := 3098402859946727719274603

theorem tailTrace_6034118 : CollatzResearch.WordTrace tailWord_6034118 prefixEnd_6034118 3098402859946727719274603 := by
  unfold tailWord_6034118
  simp only [CollatzResearch.WordTrace]
  refine ⟨6877573873544640817300219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 146721575968952337435738005 6877573873544640817300219)
  ·
    refine ⟨10316360810316961225950329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6877573873544640817300219 10316360810316961225950329)
    ·
      refine ⟨7737270607737720919462747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10316360810316961225950329 7737270607737720919462747)
      ·
        refine ⟨11605905911606581379194121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7737270607737720919462747 11605905911606581379194121)
        ·
          refine ⟨8704429433704936034395591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11605905911606581379194121 8704429433704936034395591)
          ·
            refine ⟨13056644150557404051593387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8704429433704936034395591 13056644150557404051593387)
            ·
              refine ⟨19584966225836106077390081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13056644150557404051593387 19584966225836106077390081)
              ·
                refine ⟨14688724669377079558042561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19584966225836106077390081 14688724669377079558042561)
                ·
                  refine ⟨11016543502032809668531921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14688724669377079558042561 11016543502032809668531921)
                  ·
                    refine ⟨8262407626524607251398941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11016543502032809668531921 8262407626524607251398941)
                    ·
                      refine ⟨3098402859946727719274603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8262407626524607251398941 3098402859946727719274603)
                      ·
                        rfl

theorem cell23_6034118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 1, 2, 2, 2, 3].length) (baseStart_6034118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6034118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6034118 prefixEnd_6034118 := by exact prefixLift 6034118
  have htrace : WordTrace (prefixWord ++ tailWord_6034118) baseStart_6034118 baseEnd_6034118 := by
    simpa [prefixWord, tailWord_6034118, baseEnd_6034118] using wordTrace_append hprefix tailTrace_6034118
  have hstable : (prefixWord ++ tailWord_6034118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6034118).length < 2 ^ (prefixWord ++ tailWord_6034118).sum := by decide
  have hdescent : baseEnd_6034118 < baseStart_6034118 := by decide
  rcases family_descends (prefixWord ++ tailWord_6034118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6034124 : List Nat := [2, 2, 1, 5, 1, 1, 1, 1, 4, 3, 2]
def baseStart_6034124 : Nat := 118140960795 + 6034124 * 2 ^ 59
def prefixEnd_6034124 : Nat := 4983230072969 + 3 ^ 40 * 6034124 * 2
def baseEnd_6034124 : Nat := 3098405940830654695799575

theorem tailTrace_6034124 : CollatzResearch.WordTrace tailWord_6034124 prefixEnd_6034124 3098405940830654695799575 := by
  unfold tailWord_6034124
  simp only [CollatzResearch.WordTrace]
  refine ⟨110041291395703384589162713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146721721860937846118883617 110041291395703384589162713)
  ·
    refine ⟨82530968546777538441872035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110041291395703384589162713 82530968546777538441872035)
    ·
      refine ⟨123796452820166307662808053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82530968546777538441872035 123796452820166307662808053)
      ·
        refine ⟨11605917451890591343388255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 123796452820166307662808053 11605917451890591343388255)
        ·
          refine ⟨17408876177835887015082383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11605917451890591343388255 17408876177835887015082383)
          ·
            refine ⟨26113314266753830522623575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17408876177835887015082383 26113314266753830522623575)
            ·
              refine ⟨39169971400130745783935363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26113314266753830522623575 39169971400130745783935363)
              ·
                refine ⟨58754957100196118675903045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39169971400130745783935363 58754957100196118675903045)
                ·
                  refine ⟨11016554456286772251731821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 58754957100196118675903045 11016554456286772251731821)
                  ·
                    refine ⟨4131207921107539594399433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11016554456286772251731821 4131207921107539594399433)
                    ·
                      refine ⟨3098405940830654695799575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4131207921107539594399433 3098405940830654695799575)
                      ·
                        rfl

theorem cell23_6034124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 1, 4, 3, 2].length) (baseStart_6034124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6034124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6034124 prefixEnd_6034124 := by exact prefixLift 6034124
  have htrace : WordTrace (prefixWord ++ tailWord_6034124) baseStart_6034124 baseEnd_6034124 := by
    simpa [prefixWord, tailWord_6034124, baseEnd_6034124] using wordTrace_append hprefix tailTrace_6034124
  have hstable : (prefixWord ++ tailWord_6034124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6034124).length < 2 ^ (prefixWord ++ tailWord_6034124).sum := by decide
  have hdescent : baseEnd_6034124 < baseStart_6034124 := by decide
  rcases family_descends (prefixWord ++ tailWord_6034124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6034125 : List Nat := [1, 6, 2, 1, 2, 1, 3, 2, 1, 4]
def baseStart_6034125 : Nat := 118140960795 + 6034125 * 2 ^ 59
def prefixEnd_6034125 : Nat := 4983230072969 + 3 ^ 40 * 6034125 * 2
def baseEnd_6034125 : Nat := 1032802151437103063962357

theorem tailTrace_6034125 : CollatzResearch.WordTrace tailWord_6034125 prefixEnd_6034125 1032802151437103063962357 := by
  unfold tailWord_6034125
  simp only [CollatzResearch.WordTrace]
  refine ⟨220082619264403146349111829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146721746176268764232741219 220082619264403146349111829)
  ·
    refine ⟨10316372778018897485114617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 220082619264403146349111829 10316372778018897485114617)
    ·
      refine ⟨7737279583514173113835963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10316372778018897485114617 7737279583514173113835963)
      ·
        refine ⟨11605919375271259670753945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7737279583514173113835963 11605919375271259670753945)
        ·
          refine ⟨8704439531453444753065459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11605919375271259670753945 8704439531453444753065459)
          ·
            refine ⟨13056659297180167129598189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8704439531453444753065459 13056659297180167129598189)
            ·
              refine ⟨4896247236442562673599321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13056659297180167129598189 4896247236442562673599321)
              ·
                refine ⟨3672185427331922005199491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4896247236442562673599321 3672185427331922005199491)
                ·
                  refine ⟨5508278140997883007799237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3672185427331922005199491 5508278140997883007799237)
                  ·
                    refine ⟨1032802151437103063962357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5508278140997883007799237 1032802151437103063962357)
                    ·
                      rfl

theorem cell23_6034125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 3, 2, 1, 4].length) (baseStart_6034125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6034125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6034125 prefixEnd_6034125 := by exact prefixLift 6034125
  have htrace : WordTrace (prefixWord ++ tailWord_6034125) baseStart_6034125 baseEnd_6034125 := by
    simpa [prefixWord, tailWord_6034125, baseEnd_6034125] using wordTrace_append hprefix tailTrace_6034125
  have hstable : (prefixWord ++ tailWord_6034125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6034125).length < 2 ^ (prefixWord ++ tailWord_6034125).sum := by decide
  have hdescent : baseEnd_6034125 < baseStart_6034125 := by decide
  rcases family_descends (prefixWord ++ tailWord_6034125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6034154 : List Nat := [3, 1, 3, 1, 1, 1, 1, 3, 5, 2, 2]
def baseStart_6034154 : Nat := 118140960795 + 6034154 * 2 ^ 59
def prefixEnd_6034154 : Nat := 4983230072969 + 3 ^ 40 * 6034154 * 2
def baseEnd_6034154 : Nat := 3098421345250289578424437

theorem tailTrace_6034154 : CollatzResearch.WordTrace tailWord_6034154 prefixEnd_6034154 3098421345250289578424437 := by
  unfold tailWord_6034154
  simp only [CollatzResearch.WordTrace]
  refine ⟨55020919245324521075479379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146722451320865389534611677 55020919245324521075479379)
  ·
    refine ⟨82531378867986781613219069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55020919245324521075479379 82531378867986781613219069)
    ·
      refine ⟨30949267075495043104957151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82531378867986781613219069 30949267075495043104957151)
      ·
        refine ⟨46423900613242564657435727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30949267075495043104957151 46423900613242564657435727)
        ·
          refine ⟨69635850919863846986153591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46423900613242564657435727 69635850919863846986153591)
          ·
            refine ⟨104453776379795770479230387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69635850919863846986153591 104453776379795770479230387)
            ·
              refine ⟨156680664569693655718845581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104453776379795770479230387 156680664569693655718845581)
              ·
                refine ⟨58755249213635120894567093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 156680664569693655718845581 58755249213635120894567093)
                ·
                  refine ⟨5508304613778292583865665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 58755249213635120894567093 5508304613778292583865665)
                  ·
                    refine ⟨4131228460333719437899249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5508304613778292583865665 4131228460333719437899249)
                    ·
                      refine ⟨3098421345250289578424437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4131228460333719437899249 3098421345250289578424437)
                      ·
                        rfl

theorem cell23_6034154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 3, 5, 2, 2].length) (baseStart_6034154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6034154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6034154 prefixEnd_6034154 := by exact prefixLift 6034154
  have htrace : WordTrace (prefixWord ++ tailWord_6034154) baseStart_6034154 baseEnd_6034154 := by
    simpa [prefixWord, tailWord_6034154, baseEnd_6034154] using wordTrace_append hprefix tailTrace_6034154
  have hstable : (prefixWord ++ tailWord_6034154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6034154).length < 2 ^ (prefixWord ++ tailWord_6034154).sum := by decide
  have hdescent : baseEnd_6034154 < baseStart_6034154 := by decide
  rcases family_descends (prefixWord ++ tailWord_6034154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6034174 : List Nat := [4, 2, 2, 1, 2, 1, 3, 1, 1, 1, 5]
def baseStart_6034174 : Nat := 118140960795 + 6034174 * 2 ^ 59
def prefixEnd_6034174 : Nat := 4983230072969 + 3 ^ 40 * 6034174 * 2
def baseEnd_6034174 : Nat := 3098431614863379500174345

theorem tailTrace_6034174 : CollatzResearch.WordTrace tailWord_6034174 prefixEnd_6034174 3098431614863379500174345 := by
  unfold tailWord_6034174
  simp only [CollatzResearch.WordTrace]
  refine ⟨27510550805153203464705697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 146722937627483751811763717 27510550805153203464705697)
  ·
    refine ⟨20632913103864902598529273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27510550805153203464705697 20632913103864902598529273)
    ·
      refine ⟨15474684827898676948896955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20632913103864902598529273 15474684827898676948896955)
      ·
        refine ⟨23212027241848015423345433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15474684827898676948896955 23212027241848015423345433)
        ·
          refine ⟨17409020431386011567509075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23212027241848015423345433 17409020431386011567509075)
          ·
            refine ⟨26113530647079017351263613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17409020431386011567509075 26113530647079017351263613)
            ·
              refine ⟨9792573992654631506723855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26113530647079017351263613 9792573992654631506723855)
              ·
                refine ⟨14688860988981947260085783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9792573992654631506723855 14688860988981947260085783)
                ·
                  refine ⟨22033291483472920890128675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14688860988981947260085783 22033291483472920890128675)
                  ·
                    refine ⟨33049937225209381335193013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22033291483472920890128675 33049937225209381335193013)
                    ·
                      refine ⟨3098431614863379500174345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33049937225209381335193013 3098431614863379500174345)
                      ·
                        rfl

theorem cell23_6034174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 3, 1, 1, 1, 5].length) (baseStart_6034174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6034174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6034174 prefixEnd_6034174 := by exact prefixLift 6034174
  have htrace : WordTrace (prefixWord ++ tailWord_6034174) baseStart_6034174 baseEnd_6034174 := by
    simpa [prefixWord, tailWord_6034174, baseEnd_6034174] using wordTrace_append hprefix tailTrace_6034174
  have hstable : (prefixWord ++ tailWord_6034174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6034174).length < 2 ^ (prefixWord ++ tailWord_6034174).sum := by decide
  have hdescent : baseEnd_6034174 < baseStart_6034174 := by decide
  rcases family_descends (prefixWord ++ tailWord_6034174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6034200 : List Nat := [2, 1, 2, 3, 1, 1, 1, 2, 1, 4, 5]
def baseStart_6034200 : Nat := 118140960795 + 6034200 * 2 ^ 59
def prefixEnd_6034200 : Nat := 4983230072969 + 3 ^ 40 * 6034200 * 2
def baseEnd_6034200 : Nat := 3098444965360396398449225

theorem tailTrace_6034200 : CollatzResearch.WordTrace tailWord_6034200 prefixEnd_6034200 3098444965360396398449225 := by
  unfold tailWord_6034200
  simp only [CollatzResearch.WordTrace]
  refine ⟨110042677369565717079046027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146723569826087622772061369 110042677369565717079046027)
  ·
    refine ⟨165064016054348575618569041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110042677369565717079046027 165064016054348575618569041)
    ·
      refine ⟨123798012040761431713926781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 165064016054348575618569041 123798012040761431713926781)
      ·
        refine ⟨46424254515285536892722543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 123798012040761431713926781 46424254515285536892722543)
        ·
          refine ⟨69636381772928305339083815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46424254515285536892722543 69636381772928305339083815)
          ·
            refine ⟨104454572659392458008625723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69636381772928305339083815 104454572659392458008625723)
            ·
              refine ⟨156681858989088687012938585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104454572659392458008625723 156681858989088687012938585)
              ·
                refine ⟨117511394241816515259703939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 156681858989088687012938585 117511394241816515259703939)
                ·
                  refine ⟨176267091362724772889555909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 117511394241816515259703939 176267091362724772889555909)
                  ·
                    refine ⟨33050079630510894916791733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 176267091362724772889555909 33050079630510894916791733)
                    ·
                      refine ⟨3098444965360396398449225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33050079630510894916791733 3098444965360396398449225)
                      ·
                        rfl

theorem cell23_6034200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 2, 1, 4, 5].length) (baseStart_6034200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6034200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6034200 prefixEnd_6034200 := by exact prefixLift 6034200
  have htrace : WordTrace (prefixWord ++ tailWord_6034200) baseStart_6034200 baseEnd_6034200 := by
    simpa [prefixWord, tailWord_6034200, baseEnd_6034200] using wordTrace_append hprefix tailTrace_6034200
  have hstable : (prefixWord ++ tailWord_6034200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6034200).length < 2 ^ (prefixWord ++ tailWord_6034200).sum := by decide
  have hdescent : baseEnd_6034200 < baseStart_6034200 := by decide
  rcases family_descends (prefixWord ++ tailWord_6034200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6034204 : List Nat := [2, 2, 3, 1, 1, 4, 2, 1, 1, 3, 3]
def baseStart_6034204 : Nat := 118140960795 + 6034204 * 2 ^ 59
def prefixEnd_6034204 : Nat := 4983230072969 + 3 ^ 40 * 6034204 * 2
def baseEnd_6034204 : Nat := 3098447019283014382799207

theorem tailTrace_6034204 : CollatzResearch.WordTrace tailWord_6034204 prefixEnd_6034204 3098447019283014382799207 := by
  unfold tailWord_6034204
  simp only [CollatzResearch.WordTrace]
  refine ⟨110042750315558471420618833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146723667087411295227491777 110042750315558471420618833)
  ·
    refine ⟨82532062736668853565464125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110042750315558471420618833 82532062736668853565464125)
    ·
      refine ⟨30949523526250820087049047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82532062736668853565464125 30949523526250820087049047)
      ·
        refine ⟨46424285289376230130573571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30949523526250820087049047 46424285289376230130573571)
        ·
          refine ⟨69636427934064345195860357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46424285289376230130573571 69636427934064345195860357)
          ·
            refine ⟨13056830237637064724223817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 69636427934064345195860357 13056830237637064724223817)
            ·
              refine ⟨9792622678227798543167863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13056830237637064724223817 9792622678227798543167863)
              ·
                refine ⟨14688934017341697814751795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9792622678227798543167863 14688934017341697814751795)
                ·
                  refine ⟨22033401026012546722127693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14688934017341697814751795 22033401026012546722127693)
                  ·
                    refine ⟨8262525384754705020797885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22033401026012546722127693 8262525384754705020797885)
                    ·
                      refine ⟨3098447019283014382799207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8262525384754705020797885 3098447019283014382799207)
                      ·
                        rfl

theorem cell23_6034204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 2, 1, 1, 3, 3].length) (baseStart_6034204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6034204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6034204 prefixEnd_6034204 := by exact prefixLift 6034204
  have htrace : WordTrace (prefixWord ++ tailWord_6034204) baseStart_6034204 baseEnd_6034204 := by
    simpa [prefixWord, tailWord_6034204, baseEnd_6034204] using wordTrace_append hprefix tailTrace_6034204
  have hstable : (prefixWord ++ tailWord_6034204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6034204).length < 2 ^ (prefixWord ++ tailWord_6034204).sum := by decide
  have hdescent : baseEnd_6034204 < baseStart_6034204 := by decide
  rcases family_descends (prefixWord ++ tailWord_6034204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6034220 : List Nat := [2, 2, 1, 1, 1, 4, 1, 2, 1, 8]
def baseStart_6034220 : Nat := 118140960795 + 6034220 * 2 ^ 59
def prefixEnd_6034220 : Nat := 4983230072969 + 3 ^ 40 * 6034220 * 2
def baseEnd_6034220 : Nat := 1032818411657828773399711

theorem tailTrace_6034220 : CollatzResearch.WordTrace tailWord_6034220 prefixEnd_6034220 1032818411657828773399711 := by
  unfold tailWord_6034220
  simp only [CollatzResearch.WordTrace]
  refine ⟨110043042099529488786910057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146724056132705985049213409 110043042099529488786910057)
  ·
    refine ⟨82532281574647116590182543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110043042099529488786910057 82532281574647116590182543)
    ·
      refine ⟨123798422361970674885273815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82532281574647116590182543 123798422361970674885273815)
      ·
        refine ⟨185697633542956012327910723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123798422361970674885273815 185697633542956012327910723)
        ·
          refine ⟨278546450314434018491866085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 185697633542956012327910723 278546450314434018491866085)
          ·
            refine ⟨52227459433956378467224891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 278546450314434018491866085 52227459433956378467224891)
            ·
              refine ⟨78341189150934567700837337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52227459433956378467224891 78341189150934567700837337)
              ·
                refine ⟨58755891863200925775628003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 78341189150934567700837337 58755891863200925775628003)
                ·
                  refine ⟨88133837794801388663442005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58755891863200925775628003 88133837794801388663442005)
                  ·
                    refine ⟨1032818411657828773399711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 88133837794801388663442005 1032818411657828773399711)
                    ·
                      rfl

theorem cell23_6034220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 8].length) (baseStart_6034220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6034220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6034220 prefixEnd_6034220 := by exact prefixLift 6034220
  have htrace : WordTrace (prefixWord ++ tailWord_6034220) baseStart_6034220 baseEnd_6034220 := by
    simpa [prefixWord, tailWord_6034220, baseEnd_6034220] using wordTrace_append hprefix tailTrace_6034220
  have hstable : (prefixWord ++ tailWord_6034220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6034220).length < 2 ^ (prefixWord ++ tailWord_6034220).sum := by decide
  have hdescent : baseEnd_6034220 < baseStart_6034220 := by decide
  rcases family_descends (prefixWord ++ tailWord_6034220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6034277 : List Nat := [1, 3, 1, 3, 1, 1, 2, 2, 1, 5, 3]
def baseStart_6034277 : Nat := 118140960795 + 6034277 * 2 ^ 59
def prefixEnd_6034277 : Nat := 4983230072969 + 3 ^ 40 * 6034277 * 2
def baseEnd_6034277 : Nat := 3098484503370792597186371

theorem tailTrace_6034277 : CollatzResearch.WordTrace tailWord_6034277 prefixEnd_6034277 3098484503370792597186371 := by
  unfold tailWord_6034277
  simp only [CollatzResearch.WordTrace]
  refine ⟨220088163159852476308645085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146725442106568317539096723 220088163159852476308645085)
  ·
    refine ⟨82533061184944678615741907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 220088163159852476308645085 82533061184944678615741907)
    ·
      refine ⟨123799591777417017923612861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82533061184944678615741907 123799591777417017923612861)
      ·
        refine ⟨46424846916531381721354823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 123799591777417017923612861 46424846916531381721354823)
        ·
          refine ⟨69637270374797072582032235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46424846916531381721354823 69637270374797072582032235)
          ·
            refine ⟨104455905562195608873048353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69637270374797072582032235 104455905562195608873048353)
            ·
              refine ⟨78341929171646706654786265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 104455905562195608873048353 78341929171646706654786265)
              ·
                refine ⟨58756446878735029991089699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 78341929171646706654786265 58756446878735029991089699)
                ·
                  refine ⟨88134670318102544986634549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58756446878735029991089699 88134670318102544986634549)
                  ·
                    refine ⟨8262625342322113592496989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 88134670318102544986634549 8262625342322113592496989)
                    ·
                      refine ⟨3098484503370792597186371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8262625342322113592496989 3098484503370792597186371)
                      ·
                        rfl

theorem cell23_6034277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 2, 1, 5, 3].length) (baseStart_6034277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6034277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6034277 prefixEnd_6034277 := by exact prefixLift 6034277
  have htrace : WordTrace (prefixWord ++ tailWord_6034277) baseStart_6034277 baseEnd_6034277 := by
    simpa [prefixWord, tailWord_6034277, baseEnd_6034277] using wordTrace_append hprefix tailTrace_6034277
  have hstable : (prefixWord ++ tailWord_6034277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6034277).length < 2 ^ (prefixWord ++ tailWord_6034277).sum := by decide
  have hdescent : baseEnd_6034277 < baseStart_6034277 := by decide
  rcases family_descends (prefixWord ++ tailWord_6034277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6034297 : List Nat := [1, 2, 1, 3, 2, 3, 1, 1, 4, 5]
def baseStart_6034297 : Nat := 118140960795 + 6034297 * 2 ^ 59
def prefixEnd_6034297 : Nat := 4983230072969 + 3 ^ 40 * 6034297 * 2
def baseEnd_6034297 : Nat := 1032831590994627506312093

theorem tailTrace_6034297 : CollatzResearch.WordTrace tailWord_6034297 prefixEnd_6034297 1032831590994627506312093 := by
  unfold tailWord_6034297
  simp only [CollatzResearch.WordTrace]
  refine ⟨220088892619780019724373145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146725928413186679816248763 220088892619780019724373145)
  ·
    refine ⟨165066669464835014793279859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 220088892619780019724373145 165066669464835014793279859)
    ·
      refine ⟨247600004197252522189919789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165066669464835014793279859 247600004197252522189919789)
      ·
        refine ⟨92850001573969695821219921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 247600004197252522189919789 92850001573969695821219921)
        ·
          refine ⟨69637501180477271865914941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92850001573969695821219921 69637501180477271865914941)
          ·
            refine ⟨26114062942678976949718103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69637501180477271865914941 26114062942678976949718103)
            ·
              refine ⟨39171094414018465424577155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26114062942678976949718103 39171094414018465424577155)
              ·
                refine ⟨58756641621027698136865733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39171094414018465424577155 58756641621027698136865733)
                ·
                  refine ⟨11016870303942693400662325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 58756641621027698136865733 11016870303942693400662325)
                  ·
                    refine ⟨1032831590994627506312093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11016870303942693400662325 1032831590994627506312093)
                    ·
                      rfl

theorem cell23_6034297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 1, 4, 5].length) (baseStart_6034297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6034297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6034297 prefixEnd_6034297 := by exact prefixLift 6034297
  have htrace : WordTrace (prefixWord ++ tailWord_6034297) baseStart_6034297 baseEnd_6034297 := by
    simpa [prefixWord, tailWord_6034297, baseEnd_6034297] using wordTrace_append hprefix tailTrace_6034297
  have hstable : (prefixWord ++ tailWord_6034297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6034297).length < 2 ^ (prefixWord ++ tailWord_6034297).sum := by decide
  have hdescent : baseEnd_6034297 < baseStart_6034297 := by decide
  rcases family_descends (prefixWord ++ tailWord_6034297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6034307 : List Nat := [1, 1, 1, 3, 4, 1, 3, 1, 1, 2, 5]
def baseStart_6034307 : Nat := 118140960795 + 6034307 * 2 ^ 59
def prefixEnd_6034307 : Nat := 4983230072969 + 3 ^ 40 * 6034307 * 2
def baseEnd_6034307 : Nat := 3098499907790427479811233

theorem tailTrace_6034307 : CollatzResearch.WordTrace tailWord_6034307 prefixEnd_6034307 3098499907790427479811233 := by
  unfold tailWord_6034307
  simp only [CollatzResearch.WordTrace]
  refine ⟨220089257349743791432237175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146726171566495860954824783 220089257349743791432237175)
  ·
    refine ⟨330133886024615687148355763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220089257349743791432237175 330133886024615687148355763)
    ·
      refine ⟨495200829036923530722533645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 330133886024615687148355763 495200829036923530722533645)
      ·
        refine ⟨185700310888846324020950117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 495200829036923530722533645 185700310888846324020950117)
        ·
          refine ⟨34818808291658685753928147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 185700310888846324020950117 34818808291658685753928147)
          ·
            refine ⟨52228212437488028630892221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34818808291658685753928147 52228212437488028630892221)
            ·
              refine ⟨19585579664058010736584583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52228212437488028630892221 19585579664058010736584583)
              ·
                refine ⟨29378369496087016104876875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19585579664058010736584583 29378369496087016104876875)
                ·
                  refine ⟨44067554244130524157315313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29378369496087016104876875 44067554244130524157315313)
                  ·
                    refine ⟨33050665683097893117986485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 44067554244130524157315313 33050665683097893117986485)
                    ·
                      refine ⟨3098499907790427479811233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33050665683097893117986485 3098499907790427479811233)
                      ·
                        rfl

theorem cell23_6034307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 3, 1, 1, 2, 5].length) (baseStart_6034307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6034307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6034307 prefixEnd_6034307 := by exact prefixLift 6034307
  have htrace : WordTrace (prefixWord ++ tailWord_6034307) baseStart_6034307 baseEnd_6034307 := by
    simpa [prefixWord, tailWord_6034307, baseEnd_6034307] using wordTrace_append hprefix tailTrace_6034307
  have hstable : (prefixWord ++ tailWord_6034307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6034307).length < 2 ^ (prefixWord ++ tailWord_6034307).sum := by decide
  have hdescent : baseEnd_6034307 < baseStart_6034307 := by decide
  rcases family_descends (prefixWord ++ tailWord_6034307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6034388 : List Nat := [2, 4, 1, 2, 1, 4, 1, 1, 2, 2, 3]
def baseStart_6034388 : Nat := 118140960795 + 6034388 * 2 ^ 59
def prefixEnd_6034388 : Nat := 4983230072969 + 3 ^ 40 * 6034388 * 2
def baseEnd_6034388 : Nat := 3098541499723441662898361

theorem tailTrace_6034388 : CollatzResearch.WordTrace tailWord_6034388 prefixEnd_6034388 3098541499723441662898361 := by
  unfold tailWord_6034388
  simp only [CollatzResearch.WordTrace]
  refine ⟨110046105831225171132967909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146728141108300228177290545 110046105831225171132967909)
  ·
    refine ⟨20633644843354719587431483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 110046105831225171132967909 20633644843354719587431483)
    ·
      refine ⟨30950467265032079381147225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20633644843354719587431483 30950467265032079381147225)
      ·
        refine ⟨23212850448774059535860419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30950467265032079381147225 23212850448774059535860419)
        ·
          refine ⟨34819275673161089303790629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23212850448774059535860419 34819275673161089303790629)
          ·
            refine ⟨6528614188717704244460743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34819275673161089303790629 6528614188717704244460743)
            ·
              refine ⟨9792921283076556366691115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6528614188717704244460743 9792921283076556366691115)
              ·
                refine ⟨14689381924614834550036673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9792921283076556366691115 14689381924614834550036673)
                ·
                  refine ⟨11017036443461125912527505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14689381924614834550036673 11017036443461125912527505)
                  ·
                    refine ⟨8262777332595844434395629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11017036443461125912527505 8262777332595844434395629)
                    ·
                      refine ⟨3098541499723441662898361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8262777332595844434395629 3098541499723441662898361)
                      ·
                        rfl

theorem cell23_6034388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 4, 1, 1, 2, 2, 3].length) (baseStart_6034388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6034388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6034388 prefixEnd_6034388 := by exact prefixLift 6034388
  have htrace : WordTrace (prefixWord ++ tailWord_6034388) baseStart_6034388 baseEnd_6034388 := by
    simpa [prefixWord, tailWord_6034388, baseEnd_6034388] using wordTrace_append hprefix tailTrace_6034388
  have hstable : (prefixWord ++ tailWord_6034388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6034388).length < 2 ^ (prefixWord ++ tailWord_6034388).sum := by decide
  have hdescent : baseEnd_6034388 < baseStart_6034388 := by decide
  rcases family_descends (prefixWord ++ tailWord_6034388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6034471 : List Nat := [1, 1, 7, 1, 1, 1, 1, 2, 1, 1, 6]
def baseStart_6034471 : Nat := 118140960795 + 6034471 * 2 ^ 59
def prefixEnd_6034471 : Nat := 4983230072969 + 3 ^ 40 * 6034471 * 2
def baseEnd_6034471 : Nat := 3098584118617764838160479

theorem tailTrace_6034471 : CollatzResearch.WordTrace tailWord_6034471 prefixEnd_6034471 3098584118617764838160479 := by
  unfold tailWord_6034471
  simp only [CollatzResearch.WordTrace]
  refine ⟨220095238921149647441207267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146730159280766431627471511 220095238921149647441207267)
  ·
    refine ⟨330142858381724471161810901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220095238921149647441207267 330142858381724471161810901)
    ·
      refine ⟨7737723243321667292854943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 330142858381724471161810901 7737723243321667292854943)
      ·
        refine ⟨11606584864982500939282415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7737723243321667292854943 11606584864982500939282415)
        ·
          refine ⟨17409877297473751408923623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11606584864982500939282415 17409877297473751408923623)
          ·
            refine ⟨26114815946210627113385435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17409877297473751408923623 26114815946210627113385435)
            ·
              refine ⟨39172223919315940670078153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26114815946210627113385435 39172223919315940670078153)
              ·
                refine ⟨29379167939486955502558615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39172223919315940670078153 29379167939486955502558615)
                ·
                  refine ⟨44068751909230433253837923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29379167939486955502558615 44068751909230433253837923)
                  ·
                    refine ⟨66103127863845649880756885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 44068751909230433253837923 66103127863845649880756885)
                    ·
                      refine ⟨3098584118617764838160479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 66103127863845649880756885 3098584118617764838160479)
                      ·
                        rfl

theorem cell23_6034471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 2, 1, 1, 6].length) (baseStart_6034471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6034471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6034471 prefixEnd_6034471 := by exact prefixLift 6034471
  have htrace : WordTrace (prefixWord ++ tailWord_6034471) baseStart_6034471 baseEnd_6034471 := by
    simpa [prefixWord, tailWord_6034471, baseEnd_6034471] using wordTrace_append hprefix tailTrace_6034471
  have hstable : (prefixWord ++ tailWord_6034471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6034471).length < 2 ^ (prefixWord ++ tailWord_6034471).sum := by decide
  have hdescent : baseEnd_6034471 < baseStart_6034471 := by decide
  rcases family_descends (prefixWord ++ tailWord_6034471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6034526 : List Nat := [4, 4, 1, 1, 1, 2, 1, 4, 1, 2, 2]
def baseStart_6034526 : Nat := 118140960795 + 6034526 * 2 ^ 59
def prefixEnd_6034526 : Nat := 4983230072969 + 3 ^ 40 * 6034526 * 2
def baseEnd_6034526 : Nat := 3098612360053762122972727

theorem tailTrace_6034526 : CollatzResearch.WordTrace tailWord_6034526 prefixEnd_6034526 3098612360053762122972727 := by
  unfold tailWord_6034526
  simp only [CollatzResearch.WordTrace]
  refine ⟨27512155616993798979307429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 146731496623966927889639621 27512155616993798979307429)
  ·
    refine ⟨5158529178186337308620143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27512155616993798979307429 5158529178186337308620143)
    ·
      refine ⟨7737793767279505962930215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5158529178186337308620143 7737793767279505962930215)
      ·
        refine ⟨11606690650919258944395323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7737793767279505962930215 11606690650919258944395323)
        ·
          refine ⟨17410035976378888416592985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11606690650919258944395323 17410035976378888416592985)
          ·
            refine ⟨13057526982284166312444739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17410035976378888416592985 13057526982284166312444739)
            ·
              refine ⟨19586290473426249468667109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13057526982284166312444739 19586290473426249468667109)
              ·
                refine ⟨3672429463767421775375083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19586290473426249468667109 3672429463767421775375083)
                ·
                  refine ⟨5508644195651132663062625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3672429463767421775375083 5508644195651132663062625)
                  ·
                    refine ⟨4131483146738349497296969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5508644195651132663062625 4131483146738349497296969)
                    ·
                      refine ⟨3098612360053762122972727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4131483146738349497296969 3098612360053762122972727)
                      ·
                        rfl

theorem cell23_6034526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 1, 4, 1, 2, 2].length) (baseStart_6034526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6034526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6034526 prefixEnd_6034526 := by exact prefixLift 6034526
  have htrace : WordTrace (prefixWord ++ tailWord_6034526) baseStart_6034526 baseEnd_6034526 := by
    simpa [prefixWord, tailWord_6034526, baseEnd_6034526] using wordTrace_append hprefix tailTrace_6034526
  have hstable : (prefixWord ++ tailWord_6034526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6034526).length < 2 ^ (prefixWord ++ tailWord_6034526).sum := by decide
  have hdescent : baseEnd_6034526 < baseStart_6034526 := by decide
  rcases family_descends (prefixWord ++ tailWord_6034526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6034531 : List Nat := [1, 1, 1, 5, 1, 1, 1, 1, 5, 4, 2]
def baseStart_6034531 : Nat := 118140960795 + 6034531 * 2 ^ 59
def prefixEnd_6034531 : Nat := 4983230072969 + 3 ^ 40 * 6034531 * 2
def baseEnd_6034531 : Nat := 3098614927457034603410203

theorem tailTrace_6034531 : CollatzResearch.WordTrace tailWord_6034531 prefixEnd_6034531 3098614927457034603410203 := by
  unfold tailWord_6034531
  simp only [CollatzResearch.WordTrace]
  refine ⟨220097427300932277688391447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146731618200621518458927631 220097427300932277688391447)
  ·
    refine ⟨330146140951398416532587171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220097427300932277688391447 330146140951398416532587171)
    ·
      refine ⟨495219211427097624798880757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 330146140951398416532587171 495219211427097624798880757)
      ·
        refine ⟨46426801071290402324895071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 495219211427097624798880757 46426801071290402324895071)
        ·
          refine ⟨69640201606935603487342607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46426801071290402324895071 69640201606935603487342607)
          ·
            refine ⟨104460302410403405231013911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69640201606935603487342607 104460302410403405231013911)
            ·
              refine ⟨156690453615605107846520867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104460302410403405231013911 156690453615605107846520867)
              ·
                refine ⟨235035680423407661769781301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 156690453615605107846520867 235035680423407661769781301)
                ·
                  refine ⟨22034595039694468290916997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 235035680423407661769781301 22034595039694468290916997)
                  ·
                    refine ⟨4131486569942712804546937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22034595039694468290916997 4131486569942712804546937)
                    ·
                      refine ⟨3098614927457034603410203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4131486569942712804546937 3098614927457034603410203)
                      ·
                        rfl

theorem cell23_6034531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 1, 5, 4, 2].length) (baseStart_6034531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6034531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6034531 prefixEnd_6034531 := by exact prefixLift 6034531
  have htrace : WordTrace (prefixWord ++ tailWord_6034531) baseStart_6034531 baseEnd_6034531 := by
    simpa [prefixWord, tailWord_6034531, baseEnd_6034531] using wordTrace_append hprefix tailTrace_6034531
  have hstable : (prefixWord ++ tailWord_6034531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6034531).length < 2 ^ (prefixWord ++ tailWord_6034531).sum := by decide
  have hdescent : baseEnd_6034531 < baseStart_6034531 := by decide
  rcases family_descends (prefixWord ++ tailWord_6034531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6034541 : List Nat := [1, 5, 1, 1, 2, 3, 1, 1, 2, 6]
def baseStart_6034541 : Nat := 118140960795 + 6034541 * 2 ^ 59
def prefixEnd_6034541 : Nat := 4983230072969 + 3 ^ 40 * 6034541 * 2
def baseEnd_6034541 : Nat := 1032873354087859854761719

theorem tailTrace_6034541 : CollatzResearch.WordTrace tailWord_6034541 prefixEnd_6034541 1032873354087859854761719 := by
  unfold tailWord_6034541
  simp only [CollatzResearch.WordTrace]
  refine ⟨220097792030896049396255477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146731861353930699597503651 220097792030896049396255477)
  ·
    refine ⟨20634168002896504630898951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 220097792030896049396255477 20634168002896504630898951)
    ·
      refine ⟨30951252004344756946348427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20634168002896504630898951 30951252004344756946348427)
      ·
        refine ⟨46426878006517135419522641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30951252004344756946348427 46426878006517135419522641)
        ·
          refine ⟨34820158504887851564641981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46426878006517135419522641 34820158504887851564641981)
          ·
            refine ⟨13057559439332944336740743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34820158504887851564641981 13057559439332944336740743)
            ·
              refine ⟨19586339158999416505111115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13057559439332944336740743 19586339158999416505111115)
              ·
                refine ⟨29379508738499124757666673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19586339158999416505111115 29379508738499124757666673)
                ·
                  refine ⟨22034631553874343568250005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29379508738499124757666673 22034631553874343568250005)
                  ·
                    refine ⟨1032873354087859854761719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22034631553874343568250005 1032873354087859854761719)
                    ·
                      rfl

theorem cell23_6034541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 1, 1, 2, 6].length) (baseStart_6034541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6034541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6034541 prefixEnd_6034541 := by exact prefixLift 6034541
  have htrace : WordTrace (prefixWord ++ tailWord_6034541) baseStart_6034541 baseEnd_6034541 := by
    simpa [prefixWord, tailWord_6034541, baseEnd_6034541] using wordTrace_append hprefix tailTrace_6034541
  have hstable : (prefixWord ++ tailWord_6034541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6034541).length < 2 ^ (prefixWord ++ tailWord_6034541).sum := by decide
  have hdescent : baseEnd_6034541 < baseStart_6034541 := by decide
  rcases family_descends (prefixWord ++ tailWord_6034541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6034588 : List Nat := [2, 2, 3, 2, 1, 2, 2, 4, 5]
def baseStart_6034588 : Nat := 118140960795 + 6034588 * 2 ^ 59
def prefixEnd_6034588 : Nat := 4983230072969 + 3 ^ 40 * 6034588 * 2
def baseEnd_6034588 : Nat := 344293799539371208933049

theorem tailTrace_6034588 : CollatzResearch.WordTrace tailWord_6034588 prefixEnd_6034588 344293799539371208933049 := by
  unfold tailWord_6034588
  simp only [CollatzResearch.WordTrace]
  refine ⟨110049753130862888211608209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146733004174483850948810945 110049753130862888211608209)
  ·
    refine ⟨82537314848147166158706157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110049753130862888211608209 82537314848147166158706157)
    ·
      refine ⟨30951493068055187309514809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82537314848147166158706157 30951493068055187309514809)
      ·
        refine ⟨23213619801041390482136107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30951493068055187309514809 23213619801041390482136107)
        ·
          refine ⟨34820429701562085723204161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23213619801041390482136107 34820429701562085723204161)
          ·
            refine ⟨26115322276171564292403121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34820429701562085723204161 26115322276171564292403121)
            ·
              refine ⟨19586491707128673219302341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26115322276171564292403121 19586491707128673219302341)
              ·
                refine ⟨3672467195086626228619189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19586491707128673219302341 3672467195086626228619189)
                ·
                  refine ⟨344293799539371208933049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3672467195086626228619189 344293799539371208933049)
                  ·
                    rfl

theorem cell23_6034588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 2, 4, 5].length) (baseStart_6034588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6034588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6034588 prefixEnd_6034588 := by exact prefixLift 6034588
  have htrace : WordTrace (prefixWord ++ tailWord_6034588) baseStart_6034588 baseEnd_6034588 := by
    simpa [prefixWord, tailWord_6034588, baseEnd_6034588] using wordTrace_append hprefix tailTrace_6034588
  have hstable : (prefixWord ++ tailWord_6034588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6034588).length < 2 ^ (prefixWord ++ tailWord_6034588).sum := by decide
  have hdescent : baseEnd_6034588 < baseStart_6034588 := by decide
  rcases family_descends (prefixWord ++ tailWord_6034588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6034599 : List Nat := [1, 1, 6, 2, 1, 2, 3, 1, 2, 2, 2]
def baseStart_6034599 : Nat := 118140960795 + 6034599 * 2 ^ 59
def prefixEnd_6034599 : Nat := 4983230072969 + 3 ^ 40 * 6034599 * 2
def baseEnd_6034599 : Nat := 3098649844141540337359891

theorem tailTrace_6034599 : CollatzResearch.WordTrace tailWord_6034599 prefixEnd_6034599 3098649844141540337359891 := by
  unfold tailWord_6034599
  simp only [CollatzResearch.WordTrace]
  refine ⟨220099907464685925301866851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146733271643123950201244567 220099907464685925301866851)
  ·
    refine ⟨330149861197028887952800277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220099907464685925301866851 330149861197028887952800277)
    ·
      refine ⟨15475774743610729122787513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 330149861197028887952800277 15475774743610729122787513)
      ·
        refine ⟨11606831057708046842090635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15475774743610729122787513 11606831057708046842090635)
        ·
          refine ⟨17410246586562070263135953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11606831057708046842090635 17410246586562070263135953)
          ·
            refine ⟨13057684939921552697351965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17410246586562070263135953 13057684939921552697351965)
            ·
              refine ⟨4896631852470582261506987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13057684939921552697351965 4896631852470582261506987)
              ·
                refine ⟨7344947778705873392260481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4896631852470582261506987 7344947778705873392260481)
                ·
                  refine ⟨5508710834029405044195361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7344947778705873392260481 5508710834029405044195361)
                  ·
                    refine ⟨4131533125522053783146521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5508710834029405044195361 4131533125522053783146521)
                    ·
                      refine ⟨3098649844141540337359891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4131533125522053783146521 3098649844141540337359891)
                      ·
                        rfl

theorem cell23_6034599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 3, 1, 2, 2, 2].length) (baseStart_6034599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6034599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6034599 prefixEnd_6034599 := by exact prefixLift 6034599
  have htrace : WordTrace (prefixWord ++ tailWord_6034599) baseStart_6034599 baseEnd_6034599 := by
    simpa [prefixWord, tailWord_6034599, baseEnd_6034599] using wordTrace_append hprefix tailTrace_6034599
  have hstable : (prefixWord ++ tailWord_6034599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6034599).length < 2 ^ (prefixWord ++ tailWord_6034599).sum := by decide
  have hdescent : baseEnd_6034599 < baseStart_6034599 := by decide
  rcases family_descends (prefixWord ++ tailWord_6034599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6034621 : List Nat := [1, 4, 1, 2, 1, 1, 4, 1, 1, 3, 4]
def baseStart_6034621 : Nat := 118140960795 + 6034621 * 2 ^ 59
def prefixEnd_6034621 : Nat := 4983230072969 + 3 ^ 40 * 6034621 * 2
def baseEnd_6034621 : Nat := 3098661140715939251284789

theorem tailTrace_6034621 : CollatzResearch.WordTrace tailWord_6034621 prefixEnd_6034621 3098661140715939251284789 := by
  unfold tailWord_6034621
  simp only [CollatzResearch.WordTrace]
  refine ⟨220100709870606223059167717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146733806580404148706111811 220100709870606223059167717)
  ·
    refine ⟨41268883100738666823593947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 220100709870606223059167717 41268883100738666823593947)
    ·
      refine ⟨61903324651108000235390921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41268883100738666823593947 61903324651108000235390921)
      ·
        refine ⟨46427493488331000176543191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61903324651108000235390921 46427493488331000176543191)
        ·
          refine ⟨69641240232496500264814787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46427493488331000176543191 69641240232496500264814787)
          ·
            refine ⟨104461860348744750397222181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69641240232496500264814787 104461860348744750397222181)
            ·
              refine ⟨19586598815389640699479159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 104461860348744750397222181 19586598815389640699479159)
              ·
                refine ⟨29379898223084461049218739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19586598815389640699479159 29379898223084461049218739)
                ·
                  refine ⟨44069847334626691573828109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29379898223084461049218739 44069847334626691573828109)
                  ·
                    refine ⟨16526192750485009340185541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 44069847334626691573828109 16526192750485009340185541)
                    ·
                      refine ⟨3098661140715939251284789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16526192750485009340185541 3098661140715939251284789)
                      ·
                        rfl

theorem cell23_6034621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 4, 1, 1, 3, 4].length) (baseStart_6034621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6034621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6034621 prefixEnd_6034621 := by exact prefixLift 6034621
  have htrace : WordTrace (prefixWord ++ tailWord_6034621) baseStart_6034621 baseEnd_6034621 := by
    simpa [prefixWord, tailWord_6034621, baseEnd_6034621] using wordTrace_append hprefix tailTrace_6034621
  have hstable : (prefixWord ++ tailWord_6034621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6034621).length < 2 ^ (prefixWord ++ tailWord_6034621).sum := by decide
  have hdescent : baseEnd_6034621 < baseStart_6034621 := by decide
  rcases family_descends (prefixWord ++ tailWord_6034621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6034631 : List Nat := [1, 1, 4, 1, 1, 1, 1, 4, 5, 4]
def baseStart_6034631 : Nat := 118140960795 + 6034631 * 2 ^ 59
def prefixEnd_6034631 : Nat := 4983230072969 + 3 ^ 40 * 6034631 * 2
def baseEnd_6034631 : Nat := 1032888758507494737386581

theorem tailTrace_6034631 : CollatzResearch.WordTrace tailWord_6034631 prefixEnd_6034631 1032888758507494737386581 := by
  unfold tailWord_6034631
  simp only [CollatzResearch.WordTrace]
  refine ⟨220101074600569994767031747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146734049733713329844687831 220101074600569994767031747)
  ·
    refine ⟨330151611900854992150547621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220101074600569994767031747 330151611900854992150547621)
    ·
      refine ⟨61903427231410311028227679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 330151611900854992150547621 61903427231410311028227679)
      ·
        refine ⟨92855140847115466542341519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61903427231410311028227679 92855140847115466542341519)
        ·
          refine ⟨139282711270673199813512279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92855140847115466542341519 139282711270673199813512279)
          ·
            refine ⟨208924066906009799720268419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139282711270673199813512279 208924066906009799720268419)
            ·
              refine ⟨313386100359014699580402629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 208924066906009799720268419 313386100359014699580402629)
              ·
                refine ⟨58759893817315256171325493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 313386100359014699580402629 58759893817315256171325493)
                ·
                  refine ⟨5508740045373305266061765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 58759893817315256171325493 5508740045373305266061765)
                  ·
                    refine ⟨1032888758507494737386581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5508740045373305266061765 1032888758507494737386581)
                    ·
                      rfl

theorem cell23_6034631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 4, 5, 4].length) (baseStart_6034631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6034631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6034631 prefixEnd_6034631 := by exact prefixLift 6034631
  have htrace : WordTrace (prefixWord ++ tailWord_6034631) baseStart_6034631 baseEnd_6034631 := by
    simpa [prefixWord, tailWord_6034631, baseEnd_6034631] using wordTrace_append hprefix tailTrace_6034631
  have hstable : (prefixWord ++ tailWord_6034631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6034631).length < 2 ^ (prefixWord ++ tailWord_6034631).sum := by decide
  have hdescent : baseEnd_6034631 < baseStart_6034631 := by decide
  rcases family_descends (prefixWord ++ tailWord_6034631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6034698 : List Nat := [3, 1, 2, 2, 1, 1, 1, 2, 3, 5, 2]
def baseStart_6034698 : Nat := 118140960795 + 6034698 * 2 ^ 59
def prefixEnd_6034698 : Nat := 4983230072969 + 3 ^ 40 * 6034698 * 2
def baseEnd_6034698 : Nat := 3098700678726335450021935

theorem tailTrace_6034698 : CollatzResearch.WordTrace tailWord_6034698 prefixEnd_6034698 3098700678726335450021935 := by
  unfold tailWord_6034698
  simp only [CollatzResearch.WordTrace]
  refine ⟨55025879572831816302430187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146735678860884843473147165 55025879572831816302430187)
  ·
    refine ⟨82538819359247724453645281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55025879572831816302430187 82538819359247724453645281)
    ·
      refine ⟨61904114519435793340233961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82538819359247724453645281 61904114519435793340233961)
      ·
        refine ⟨46428085889576845005175471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61904114519435793340233961 46428085889576845005175471)
        ·
          refine ⟨69642128834365267507763207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46428085889576845005175471 69642128834365267507763207)
          ·
            refine ⟨104463193251547901261644811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69642128834365267507763207 104463193251547901261644811)
            ·
              refine ⟨156694789877321851892467217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104463193251547901261644811 156694789877321851892467217)
              ·
                refine ⟨117521092407991388919350413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 156694789877321851892467217 117521092407991388919350413)
                ·
                  refine ⟨44070409652996770844756405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 117521092407991388919350413 44070409652996770844756405)
                  ·
                    refine ⟨4131600904968447266695913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 44070409652996770844756405 4131600904968447266695913)
                    ·
                      refine ⟨3098700678726335450021935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4131600904968447266695913 3098700678726335450021935)
                      ·
                        rfl

theorem cell23_6034698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 2, 3, 5, 2].length) (baseStart_6034698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6034698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6034698 prefixEnd_6034698 := by exact prefixLift 6034698
  have htrace : WordTrace (prefixWord ++ tailWord_6034698) baseStart_6034698 baseEnd_6034698 := by
    simpa [prefixWord, tailWord_6034698, baseEnd_6034698] using wordTrace_append hprefix tailTrace_6034698
  have hstable : (prefixWord ++ tailWord_6034698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6034698).length < 2 ^ (prefixWord ++ tailWord_6034698).sum := by decide
  have hdescent : baseEnd_6034698 < baseStart_6034698 := by decide
  rcases family_descends (prefixWord ++ tailWord_6034698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6034722 : List Nat := [3, 3, 1, 1, 4, 1, 1, 2, 3, 1, 3]
def baseStart_6034722 : Nat := 118140960795 + 6034722 * 2 ^ 59
def prefixEnd_6034722 : Nat := 4983230072969 + 3 ^ 40 * 6034722 * 2
def baseEnd_6034722 : Nat := 3098713002262043356121825

theorem tailTrace_6034722 : CollatzResearch.WordTrace tailWord_6034722 prefixEnd_6034722 3098713002262043356121825 := by
  unfold tailWord_6034722
  simp only [CollatzResearch.WordTrace]
  refine ⟨55026098410810079327148605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146736262428826878205729613 55026098410810079327148605)
  ·
    refine ⟨20634786904053779747680727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55026098410810079327148605 20634786904053779747680727)
    ·
      refine ⟨30952180356080669621521091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20634786904053779747680727 30952180356080669621521091)
      ·
        refine ⟨46428270534121004432281637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30952180356080669621521091 46428270534121004432281637)
        ·
          refine ⟨8705300725147688331052807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46428270534121004432281637 8705300725147688331052807)
          ·
            refine ⟨13057951087721532496579211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8705300725147688331052807 13057951087721532496579211)
            ·
              refine ⟨19586926631582298744868817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13057951087721532496579211 19586926631582298744868817)
              ·
                refine ⟨14690194973686724058651613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19586926631582298744868817 14690194973686724058651613)
                ·
                  refine ⟨5508823115132521521994355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14690194973686724058651613 5508823115132521521994355)
                  ·
                    refine ⟨8263234672698782282991533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5508823115132521521994355 8263234672698782282991533)
                    ·
                      refine ⟨3098713002262043356121825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8263234672698782282991533 3098713002262043356121825)
                      ·
                        rfl

theorem cell23_6034722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 1, 2, 3, 1, 3].length) (baseStart_6034722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6034722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6034722 prefixEnd_6034722 := by exact prefixLift 6034722
  have htrace : WordTrace (prefixWord ++ tailWord_6034722) baseStart_6034722 baseEnd_6034722 := by
    simpa [prefixWord, tailWord_6034722, baseEnd_6034722] using wordTrace_append hprefix tailTrace_6034722
  have hstable : (prefixWord ++ tailWord_6034722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6034722).length < 2 ^ (prefixWord ++ tailWord_6034722).sum := by decide
  have hdescent : baseEnd_6034722 < baseStart_6034722 := by decide
  rcases family_descends (prefixWord ++ tailWord_6034722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6034731 : List Nat := [1, 1, 1, 1, 2, 1, 2, 1, 4, 6, 3]
def baseStart_6034731 : Nat := 118140960795 + 6034731 * 2 ^ 59
def prefixEnd_6034731 : Nat := 4983230072969 + 3 ^ 40 * 6034731 * 2
def baseEnd_6034731 : Nat := 3098717623587933820909283

theorem tailTrace_6034731 : CollatzResearch.WordTrace tailWord_6034731 prefixEnd_6034731 3098717623587933820909283 := by
  unfold tailWord_6034731
  simp only [CollatzResearch.WordTrace]
  refine ⟨220104721900207711845672047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146736481266805141230448031 220104721900207711845672047)
  ·
    refine ⟨330157082850311567768508071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220104721900207711845672047 330157082850311567768508071)
    ·
      refine ⟨495235624275467351652762107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 330157082850311567768508071 495235624275467351652762107)
      ·
        refine ⟨742853436413201027479143161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 495235624275467351652762107 742853436413201027479143161)
        ·
          refine ⟨557140077309900770609357371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 742853436413201027479143161 557140077309900770609357371)
          ·
            refine ⟨835710115964851155914036057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 557140077309900770609357371 835710115964851155914036057)
            ·
              refine ⟨626782586973638366935527043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 835710115964851155914036057 626782586973638366935527043)
              ·
                refine ⟨940173880460457550403290565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 626782586973638366935527043 940173880460457550403290565)
                ·
                  refine ⟨176282602586335790700616981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 940173880460457550403290565 176282602586335790700616981)
                  ·
                    refine ⟨8263246996234490189091421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 176282602586335790700616981 8263246996234490189091421)
                    ·
                      refine ⟨3098717623587933820909283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8263246996234490189091421 3098717623587933820909283)
                      ·
                        rfl

theorem cell23_6034731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 4, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 4, 6, 3].length) (baseStart_6034731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6034731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6034731 prefixEnd_6034731 := by exact prefixLift 6034731
  have htrace : WordTrace (prefixWord ++ tailWord_6034731) baseStart_6034731 baseEnd_6034731 := by
    simpa [prefixWord, tailWord_6034731, baseEnd_6034731] using wordTrace_append hprefix tailTrace_6034731
  have hstable : (prefixWord ++ tailWord_6034731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6034731).length < 2 ^ (prefixWord ++ tailWord_6034731).sum := by decide
  have hdescent : baseEnd_6034731 < baseStart_6034731 := by decide
  rcases family_descends (prefixWord ++ tailWord_6034731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6034738 : List Nat := [3, 2, 1, 1, 4, 1, 2, 2, 1, 6]
def baseStart_6034738 : Nat := 118140960795 + 6034738 * 2 ^ 59
def prefixEnd_6034738 : Nat := 4983230072969 + 3 ^ 40 * 6034738 * 2
def baseEnd_6034738 : Nat := 1032907072650838431173917

theorem tailTrace_6034738 : CollatzResearch.WordTrace tailWord_6034738 prefixEnd_6034738 1032907072650838431173917 := by
  unfold tailWord_6034738
  simp only [CollatzResearch.WordTrace]
  refine ⟨55026244302795588010294217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146736651474121568027451245 55026244302795588010294217)
  ·
    refine ⟨41269683227096691007720663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55026244302795588010294217 41269683227096691007720663)
    ·
      refine ⟨61904524840645036511580995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41269683227096691007720663 61904524840645036511580995)
      ·
        refine ⟨92856787260967554767371493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61904524840645036511580995 92856787260967554767371493)
        ·
          refine ⟨17410647611431416518882155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 92856787260967554767371493 17410647611431416518882155)
          ·
            refine ⟨26115971417147124778323233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17410647611431416518882155 26115971417147124778323233)
            ·
              refine ⟨19586978562860343583742425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26115971417147124778323233 19586978562860343583742425)
              ·
                refine ⟨14690233922145257687806819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19586978562860343583742425 14690233922145257687806819)
                ·
                  refine ⟨22035350883217886531710229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14690233922145257687806819 22035350883217886531710229)
                  ·
                    refine ⟨1032907072650838431173917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22035350883217886531710229 1032907072650838431173917)
                    ·
                      rfl

theorem cell23_6034738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 2, 2, 1, 6].length) (baseStart_6034738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6034738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6034738 prefixEnd_6034738 := by exact prefixLift 6034738
  have htrace : WordTrace (prefixWord ++ tailWord_6034738) baseStart_6034738 baseEnd_6034738 := by
    simpa [prefixWord, tailWord_6034738, baseEnd_6034738] using wordTrace_append hprefix tailTrace_6034738
  have hstable : (prefixWord ++ tailWord_6034738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6034738).length < 2 ^ (prefixWord ++ tailWord_6034738).sum := by decide
  have hdescent : baseEnd_6034738 < baseStart_6034738 := by decide
  rcases family_descends (prefixWord ++ tailWord_6034738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6034751 : List Nat := [1, 1, 2, 2, 4, 3, 10]
def baseStart_6034751 : Nat := 118140960795 + 6034751 * 2 ^ 59
def prefixEnd_6034751 : Nat := 4983230072969 + 3 ^ 40 * 6034751 * 2
def baseEnd_6034751 : Nat := 38255899916062021514311

theorem tailTrace_6034751 : CollatzResearch.WordTrace tailWord_6034751 prefixEnd_6034751 38255899916062021514311 := by
  unfold tailWord_6034751
  simp only [CollatzResearch.WordTrace]
  refine ⟨220105451360135255261400107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146736967573423503507600071 220105451360135255261400107)
  ·
    refine ⟨330158177040202882892100161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220105451360135255261400107 330158177040202882892100161)
    ·
      refine ⟨247618632780152162169075121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 330158177040202882892100161 247618632780152162169075121)
      ·
        refine ⟨185713974585114121626806341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 247618632780152162169075121 185713974585114121626806341)
        ·
          refine ⟨34821370234708897805026189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 185713974585114121626806341 34821370234708897805026189)
          ·
            refine ⟨13058013838015836676884821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34821370234708897805026189 13058013838015836676884821)
            ·
              refine ⟨38255899916062021514311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 13058013838015836676884821 38255899916062021514311)
              ·
                rfl

theorem cell23_6034751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 10].length) (baseStart_6034751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6034751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6034751 prefixEnd_6034751 := by exact prefixLift 6034751
  have htrace : WordTrace (prefixWord ++ tailWord_6034751) baseStart_6034751 baseEnd_6034751 := by
    simpa [prefixWord, tailWord_6034751, baseEnd_6034751] using wordTrace_append hprefix tailTrace_6034751
  have hstable : (prefixWord ++ tailWord_6034751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6034751).length < 2 ^ (prefixWord ++ tailWord_6034751).sum := by decide
  have hdescent : baseEnd_6034751 < baseStart_6034751 := by decide
  rcases family_descends (prefixWord ++ tailWord_6034751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6034772 : List Nat := [2, 4, 1, 1, 2, 1, 5, 1, 2, 4]
def baseStart_6034772 : Nat := 118140960795 + 6034772 * 2 ^ 59
def prefixEnd_6034772 : Nat := 4983230072969 + 3 ^ 40 * 6034772 * 2
def baseEnd_6034772 : Nat := 1032912892098256053498865

theorem tailTrace_6034772 : CollatzResearch.WordTrace tailWord_6034772 prefixEnd_6034772 1032912892098256053498865 := by
  unfold tailWord_6034772
  simp only [CollatzResearch.WordTrace]
  refine ⟨110053108646529587923957285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146737478195372783898609713 110053108646529587923957285)
  ·
    refine ⟨20634957871224297735741991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 110053108646529587923957285 20634957871224297735741991)
    ·
      refine ⟨30952436806836446603612987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20634957871224297735741991 30952436806836446603612987)
      ·
        refine ⟨46428655210254669905419481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30952436806836446603612987 46428655210254669905419481)
        ·
          refine ⟨34821491407691002429064611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46428655210254669905419481 34821491407691002429064611)
          ·
            refine ⟨52232237111536503643596917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34821491407691002429064611 52232237111536503643596917)
            ·
              refine ⟨4896772229206547216587211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 52232237111536503643596917 4896772229206547216587211)
              ·
                refine ⟨7345158343809820824880817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4896772229206547216587211 7345158343809820824880817)
                ·
                  refine ⟨5508868757857365618660613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7345158343809820824880817 5508868757857365618660613)
                  ·
                    refine ⟨1032912892098256053498865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5508868757857365618660613 1032912892098256053498865)
                    ·
                      rfl

theorem cell23_6034772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 5, 1, 2, 4].length) (baseStart_6034772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6034772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6034772 prefixEnd_6034772 := by exact prefixLift 6034772
  have htrace : WordTrace (prefixWord ++ tailWord_6034772) baseStart_6034772 baseEnd_6034772 := by
    simpa [prefixWord, tailWord_6034772, baseEnd_6034772] using wordTrace_append hprefix tailTrace_6034772
  have hstable : (prefixWord ++ tailWord_6034772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6034772).length < 2 ^ (prefixWord ++ tailWord_6034772).sum := by decide
  have hdescent : baseEnd_6034772 < baseStart_6034772 := by decide
  rcases family_descends (prefixWord ++ tailWord_6034772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6034775 : List Nat := [1, 1, 3, 2, 3, 4, 1, 1, 1, 2, 4]
def baseStart_6034775 : Nat := 118140960795 + 6034775 * 2 ^ 59
def prefixEnd_6034775 : Nat := 4983230072969 + 3 ^ 40 * 6034775 * 2
def baseEnd_6034775 : Nat := 3098740216736731648759081

theorem tailTrace_6034775 : CollatzResearch.WordTrace tailWord_6034775 prefixEnd_6034775 3098740216736731648759081 := by
  unfold tailWord_6034775
  simp only [CollatzResearch.WordTrace]
  refine ⟨220106326712048307360273779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146737551141365538240182519 220106326712048307360273779)
  ·
    refine ⟨330159490068072461040410669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220106326712048307360273779 330159490068072461040410669)
    ·
      refine ⟨123809808775527172890154001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 330159490068072461040410669 123809808775527172890154001)
      ·
        refine ⟨92857356581645379667615501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123809808775527172890154001 92857356581645379667615501)
        ·
          refine ⟨34821508718117017375355813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 92857356581645379667615501 34821508718117017375355813)
          ·
            refine ⟨6529032884646940757879215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34821508718117017375355813 6529032884646940757879215)
            ·
              refine ⟨9793549326970411136818823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6529032884646940757879215 9793549326970411136818823)
              ·
                refine ⟨14690323990455616705228235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9793549326970411136818823 14690323990455616705228235)
                ·
                  refine ⟨22035485985683425057842353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14690323990455616705228235 22035485985683425057842353)
                  ·
                    refine ⟨16526614489262568793381765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22035485985683425057842353 16526614489262568793381765)
                    ·
                      refine ⟨3098740216736731648759081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16526614489262568793381765 3098740216736731648759081)
                      ·
                        rfl

theorem cell23_6034775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 4, 1, 1, 1, 2, 4].length) (baseStart_6034775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6034775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6034775 prefixEnd_6034775 := by exact prefixLift 6034775
  have htrace : WordTrace (prefixWord ++ tailWord_6034775) baseStart_6034775 baseEnd_6034775 := by
    simpa [prefixWord, tailWord_6034775, baseEnd_6034775] using wordTrace_append hprefix tailTrace_6034775
  have hstable : (prefixWord ++ tailWord_6034775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6034775).length < 2 ^ (prefixWord ++ tailWord_6034775).sum := by decide
  have hdescent : baseEnd_6034775 < baseStart_6034775 := by decide
  rcases family_descends (prefixWord ++ tailWord_6034775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6034796 : List Nat := [2, 2, 1, 1, 5, 3, 1, 3, 1, 2, 2]
def baseStart_6034796 : Nat := 118140960795 + 6034796 * 2 ^ 59
def prefixEnd_6034796 : Nat := 4983230072969 + 3 ^ 40 * 6034796 * 2
def baseEnd_6034796 : Nat := 3098750999830476066596485

theorem tailTrace_6034796 : CollatzResearch.WordTrace tailWord_6034796 prefixEnd_6034796 3098750999830476066596485 := by
  unfold tailWord_6034796
  simp only [CollatzResearch.WordTrace]
  refine ⟨110053546322486113973394121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146738061763314818631192161 110053546322486113973394121)
  ·
    refine ⟨82540159741864585480045591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110053546322486113973394121 82540159741864585480045591)
    ·
      refine ⟨123810239612796878220068387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82540159741864585480045591 123810239612796878220068387)
      ·
        refine ⟨185715359419195317330102581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123810239612796878220068387 185715359419195317330102581)
        ·
          refine ⟨17410814945549560999697117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 185715359419195317330102581 17410814945549560999697117)
          ·
            refine ⟨6529055604581085374886419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17410814945549560999697117 6529055604581085374886419)
            ·
              refine ⟨9793583406871628062329629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6529055604581085374886419 9793583406871628062329629)
              ·
                refine ⟨3672593777576860523373611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9793583406871628062329629 3672593777576860523373611)
                ·
                  refine ⟨5508890666365290785060417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3672593777576860523373611 5508890666365290785060417)
                  ·
                    refine ⟨4131667999773968088795313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5508890666365290785060417 4131667999773968088795313)
                    ·
                      refine ⟨3098750999830476066596485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4131667999773968088795313 3098750999830476066596485)
                      ·
                        rfl

theorem cell23_6034796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 3, 1, 3, 1, 2, 2].length) (baseStart_6034796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6034796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6034796 prefixEnd_6034796 := by exact prefixLift 6034796
  have htrace : WordTrace (prefixWord ++ tailWord_6034796) baseStart_6034796 baseEnd_6034796 := by
    simpa [prefixWord, tailWord_6034796, baseEnd_6034796] using wordTrace_append hprefix tailTrace_6034796
  have hstable : (prefixWord ++ tailWord_6034796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6034796).length < 2 ^ (prefixWord ++ tailWord_6034796).sum := by decide
  have hdescent : baseEnd_6034796 < baseStart_6034796 := by decide
  rcases family_descends (prefixWord ++ tailWord_6034796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6034869 : List Nat := [1, 3, 3, 2, 2, 1, 1, 4, 2, 2, 2]
def baseStart_6034869 : Nat := 118140960795 + 6034869 * 2 ^ 59
def prefixEnd_6034869 : Nat := 4983230072969 + 3 ^ 40 * 6034869 * 2
def baseEnd_6034869 : Nat := 3098788483918254280983649

theorem tailTrace_6034869 : CollatzResearch.WordTrace tailWord_6034869 prefixEnd_6034869 3098788483918254280983649 := by
  unfold tailWord_6034869
  simp only [CollatzResearch.WordTrace]
  refine ⟨220109755173707761414195661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146739836782471840942797107 220109755173707761414195661)
  ·
    refine ⟨82541158190140410530323373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 220109755173707761414195661 82541158190140410530323373)
    ·
      refine ⟨30952934321302653948871265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82541158190140410530323373 30952934321302653948871265)
      ·
        refine ⟨23214700740976990461653449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30952934321302653948871265 23214700740976990461653449)
        ·
          refine ⟨17411025555732742846240087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23214700740976990461653449 17411025555732742846240087)
          ·
            refine ⟨26116538333599114269360131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17411025555732742846240087 26116538333599114269360131)
            ·
              refine ⟨39174807500398671404040197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26116538333599114269360131 39174807500398671404040197)
              ·
                refine ⟨7345276406324750888257537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39174807500398671404040197 7345276406324750888257537)
                ·
                  refine ⟨5508957304743563166193153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7345276406324750888257537 5508957304743563166193153)
                  ·
                    refine ⟨4131717978557672374644865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5508957304743563166193153 4131717978557672374644865)
                    ·
                      refine ⟨3098788483918254280983649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4131717978557672374644865 3098788483918254280983649)
                      ·
                        rfl

theorem cell23_6034869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 4, 2, 2, 2].length) (baseStart_6034869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6034869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6034869 prefixEnd_6034869 := by exact prefixLift 6034869
  have htrace : WordTrace (prefixWord ++ tailWord_6034869) baseStart_6034869 baseEnd_6034869 := by
    simpa [prefixWord, tailWord_6034869, baseEnd_6034869] using wordTrace_append hprefix tailTrace_6034869
  have hstable : (prefixWord ++ tailWord_6034869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6034869).length < 2 ^ (prefixWord ++ tailWord_6034869).sum := by decide
  have hdescent : baseEnd_6034869 < baseStart_6034869 := by decide
  rcases family_descends (prefixWord ++ tailWord_6034869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6034878 : List Nat := [4, 2, 1, 1, 1, 1, 1, 1, 2, 1, 8]
def baseStart_6034878 : Nat := 118140960795 + 6034878 * 2 ^ 59
def prefixEnd_6034878 : Nat := 4983230072969 + 3 ^ 40 * 6034878 * 2
def baseEnd_6034878 : Nat := 3098793105244144745771107

theorem tailTrace_6034878 : CollatzResearch.WordTrace tailWord_6034878 prefixEnd_6034878 3098793105244144745771107 := by
  unfold tailWord_6034878
  simp only [CollatzResearch.WordTrace]
  refine ⟨27513760428834394493909161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 146740055620450103967515525 27513760428834394493909161)
  ·
    refine ⟨20635320321625795870431871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27513760428834394493909161 20635320321625795870431871)
    ·
      refine ⟨30952980482438693805647807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20635320321625795870431871 30952980482438693805647807)
      ·
        refine ⟨46429470723658040708471711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30952980482438693805647807 46429470723658040708471711)
        ·
          refine ⟨69644206085487061062707567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46429470723658040708471711 69644206085487061062707567)
          ·
            refine ⟨104466309128230591594061351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69644206085487061062707567 104466309128230591594061351)
            ·
              refine ⟨156699463692345887391092027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104466309128230591594061351 156699463692345887391092027)
              ·
                refine ⟨235049195538518831086638041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 156699463692345887391092027 235049195538518831086638041)
                ·
                  refine ⟨176286896653889123314978531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 235049195538518831086638041 176286896653889123314978531)
                  ·
                    refine ⟨264430344980833684972467797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 176286896653889123314978531 264430344980833684972467797)
                    ·
                      refine ⟨3098793105244144745771107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 264430344980833684972467797 3098793105244144745771107)
                      ·
                        rfl

theorem cell23_6034878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 1, 2, 1, 8].length) (baseStart_6034878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6034878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6034878 prefixEnd_6034878 := by exact prefixLift 6034878
  have htrace : WordTrace (prefixWord ++ tailWord_6034878) baseStart_6034878 baseEnd_6034878 := by
    simpa [prefixWord, tailWord_6034878, baseEnd_6034878] using wordTrace_append hprefix tailTrace_6034878
  have hstable : (prefixWord ++ tailWord_6034878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6034878).length < 2 ^ (prefixWord ++ tailWord_6034878).sum := by decide
  have hdescent : baseEnd_6034878 < baseStart_6034878 := by decide
  rcases family_descends (prefixWord ++ tailWord_6034878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6034888 : List Nat := [2, 1, 3, 1, 3, 1, 2, 2, 1, 7]
def baseStart_6034888 : Nat := 118140960795 + 6034888 * 2 ^ 59
def prefixEnd_6034888 : Nat := 4983230072969 + 3 ^ 40 * 6034888 * 2
def baseEnd_6034888 : Nat := 1032932746683563235548687

theorem tailTrace_6034888 : CollatzResearch.WordTrace tailWord_6034888 prefixEnd_6034888 1032932746683563235548687 := by
  unfold tailWord_6034888
  simp only [CollatzResearch.WordTrace]
  refine ⟨110055224080319463829568659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146740298773759285106091545 110055224080319463829568659)
  ·
    refine ⟨165082836120479195744352989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110055224080319463829568659 165082836120479195744352989)
    ·
      refine ⟨61906063545179698404132371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 165082836120479195744352989 61906063545179698404132371)
      ·
        refine ⟨92859095317769547606198557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61906063545179698404132371 92859095317769547606198557)
        ·
          refine ⟨34822160744163580352324459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 92859095317769547606198557 34822160744163580352324459)
          ·
            refine ⟨52233241116245370528486689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34822160744163580352324459 52233241116245370528486689)
            ·
              refine ⟨39174930837184027896365017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52233241116245370528486689 39174930837184027896365017)
              ·
                refine ⟨29381198127888020922273763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39174930837184027896365017 29381198127888020922273763)
                ·
                  refine ⟨44071797191832031383410645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29381198127888020922273763 44071797191832031383410645)
                  ·
                    refine ⟨1032932746683563235548687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 44071797191832031383410645 1032932746683563235548687)
                    ·
                      rfl

theorem cell23_6034888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 2, 1, 7].length) (baseStart_6034888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6034888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6034888 prefixEnd_6034888 := by exact prefixLift 6034888
  have htrace : WordTrace (prefixWord ++ tailWord_6034888) baseStart_6034888 baseEnd_6034888 := by
    simpa [prefixWord, tailWord_6034888, baseEnd_6034888] using wordTrace_append hprefix tailTrace_6034888
  have hstable : (prefixWord ++ tailWord_6034888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6034888).length < 2 ^ (prefixWord ++ tailWord_6034888).sum := by decide
  have hdescent : baseEnd_6034888 < baseStart_6034888 := by decide
  rcases family_descends (prefixWord ++ tailWord_6034888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6034905 : List Nat := [1, 2, 1, 2, 4, 2, 3, 1, 2, 5]
def baseStart_6034905 : Nat := 118140960795 + 6034905 * 2 ^ 59
def prefixEnd_6034905 : Nat := 4983230072969 + 3 ^ 40 * 6034905 * 2
def baseEnd_6034905 : Nat := 1032935656407272046711161

theorem tailTrace_6034905 : CollatzResearch.WordTrace tailWord_6034905 prefixEnd_6034905 1032935656407272046711161 := by
  unfold tailWord_6034905
  simp only [CollatzResearch.WordTrace]
  refine ⟨220111068201577339562506169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146740712134384893041670779 220111068201577339562506169)
  ·
    refine ⟨165083301151183004671879627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 220111068201577339562506169 165083301151183004671879627)
    ·
      refine ⟨247624951726774507007819441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165083301151183004671879627 247624951726774507007819441)
      ·
        refine ⟨185718713795080880255864581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 247624951726774507007819441 185718713795080880255864581)
        ·
          refine ⟨34822258836577665047974609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 185718713795080880255864581 34822258836577665047974609)
          ·
            refine ⟨26116694127433248785980957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34822258836577665047974609 26116694127433248785980957)
            ·
              refine ⟨9793760297787468294742859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26116694127433248785980957 9793760297787468294742859)
              ·
                refine ⟨14690640446681202442114289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9793760297787468294742859 14690640446681202442114289)
                ·
                  refine ⟨11017980335010901831585717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14690640446681202442114289 11017980335010901831585717)
                  ·
                    refine ⟨1032935656407272046711161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11017980335010901831585717 1032935656407272046711161)
                    ·
                      rfl

theorem cell23_6034905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 3, 1, 2, 5].length) (baseStart_6034905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6034905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6034905 prefixEnd_6034905 := by exact prefixLift 6034905
  have htrace : WordTrace (prefixWord ++ tailWord_6034905) baseStart_6034905 baseEnd_6034905 := by
    simpa [prefixWord, tailWord_6034905, baseEnd_6034905] using wordTrace_append hprefix tailTrace_6034905
  have hstable : (prefixWord ++ tailWord_6034905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6034905).length < 2 ^ (prefixWord ++ tailWord_6034905).sum := by decide
  have hdescent : baseEnd_6034905 < baseStart_6034905 := by decide
  rcases family_descends (prefixWord ++ tailWord_6034905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6034938 : List Nat := [3, 1, 1, 1, 1, 2, 3, 2, 2, 1, 6]
def baseStart_6034938 : Nat := 118140960795 + 6034938 * 2 ^ 59
def prefixEnd_6034938 : Nat := 4983230072969 + 3 ^ 40 * 6034938 * 2
def baseEnd_6034938 : Nat := 3098823914083414511020831

theorem tailTrace_6034938 : CollatzResearch.WordTrace tailWord_6034938 prefixEnd_6034938 3098823914083414511020831 := by
  unfold tailWord_6034938
  simp only [CollatzResearch.WordTrace]
  refine ⟨55028067952614446549614367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146741514540305190798971645 55028067952614446549614367)
  ·
    refine ⟨82542101928921669824421551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55028067952614446549614367 82542101928921669824421551)
    ·
      refine ⟨123813152893382504736632327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82542101928921669824421551 123813152893382504736632327)
      ·
        refine ⟨185719729340073757104948491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123813152893382504736632327 185719729340073757104948491)
        ·
          refine ⟨278579594010110635657422737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 185719729340073757104948491 278579594010110635657422737)
          ·
            refine ⟨208934695507582976743067053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 278579594010110635657422737 208934695507582976743067053)
            ·
              refine ⟨78350510815343616278650145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 208934695507582976743067053 78350510815343616278650145)
              ·
                refine ⟨58762883111507712208987609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 78350510815343616278650145 58762883111507712208987609)
                ·
                  refine ⟨44072162333630784156740707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 58762883111507712208987609 44072162333630784156740707)
                  ·
                    refine ⟨66108243500446176235111061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 44072162333630784156740707 66108243500446176235111061)
                    ·
                      refine ⟨3098823914083414511020831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 66108243500446176235111061 3098823914083414511020831)
                      ·
                        rfl

theorem cell23_6034938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 2, 2, 1, 6].length) (baseStart_6034938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6034938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6034938 prefixEnd_6034938 := by exact prefixLift 6034938
  have htrace : WordTrace (prefixWord ++ tailWord_6034938) baseStart_6034938 baseEnd_6034938 := by
    simpa [prefixWord, tailWord_6034938, baseEnd_6034938] using wordTrace_append hprefix tailTrace_6034938
  have hstable : (prefixWord ++ tailWord_6034938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6034938).length < 2 ^ (prefixWord ++ tailWord_6034938).sum := by decide
  have hdescent : baseEnd_6034938 < baseStart_6034938 := by decide
  rcases family_descends (prefixWord ++ tailWord_6034938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6034985 : List Nat := [1, 2, 1, 1, 1, 1, 1, 1, 1, 11, 2]
def baseStart_6034985 : Nat := 118140960795 + 6034985 * 2 ^ 59
def prefixEnd_6034985 : Nat := 4983230072969 + 3 ^ 40 * 6034985 * 2
def baseEnd_6034985 : Nat := 3098848047674175827133115

theorem tailTrace_6034985 : CollatzResearch.WordTrace tailWord_6034985 prefixEnd_6034985 3098848047674175827133115 := by
  unfold tailWord_6034985
  simp only [CollatzResearch.WordTrace]
  refine ⟨220113986041287513225418409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146742657360858342150278939 220113986041287513225418409)
  ·
    refine ⟨165085489530965634919063807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 220113986041287513225418409 165085489530965634919063807)
    ·
      refine ⟨247628234296448452378595711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165085489530965634919063807 247628234296448452378595711)
      ·
        refine ⟨371442351444672678567893567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 247628234296448452378595711 371442351444672678567893567)
        ·
          refine ⟨557163527167009017851840351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 371442351444672678567893567 557163527167009017851840351)
          ·
            refine ⟨835745290750513526777760527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 557163527167009017851840351 835745290750513526777760527)
            ·
              refine ⟨1253617936125770290166640791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 835745290750513526777760527 1253617936125770290166640791)
              ·
                refine ⟨1880426904188655435249961187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1253617936125770290166640791 1880426904188655435249961187)
                ·
                  refine ⟨2820640356282983152874941781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1880426904188655435249961187 2820640356282983152874941781)
                  ·
                    refine ⟨4131797396898901102844153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 2820640356282983152874941781 4131797396898901102844153)
                    ·
                      refine ⟨3098848047674175827133115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4131797396898901102844153 3098848047674175827133115)
                      ·
                        rfl

theorem cell23_6034985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 11, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 11, 2].length) (baseStart_6034985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6034985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6034985 prefixEnd_6034985 := by exact prefixLift 6034985
  have htrace : WordTrace (prefixWord ++ tailWord_6034985) baseStart_6034985 baseEnd_6034985 := by
    simpa [prefixWord, tailWord_6034985, baseEnd_6034985] using wordTrace_append hprefix tailTrace_6034985
  have hstable : (prefixWord ++ tailWord_6034985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6034985).length < 2 ^ (prefixWord ++ tailWord_6034985).sum := by decide
  have hdescent : baseEnd_6034985 < baseStart_6034985 := by decide
  rcases family_descends (prefixWord ++ tailWord_6034985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6034986 : List Nat := [3, 1, 4, 1, 1, 1, 5, 2, 1, 4]
def baseStart_6034986 : Nat := 118140960795 + 6034986 * 2 ^ 59
def prefixEnd_6034986 : Nat := 4983230072969 + 3 ^ 40 * 6034986 * 2
def baseEnd_6034986 : Nat := 1032949520384943441073537

theorem tailTrace_6034986 : CollatzResearch.WordTrace tailWord_6034986 prefixEnd_6034986 1032949520384943441073537 := by
  unfold tailWord_6034986
  simp only [CollatzResearch.WordTrace]
  refine ⟨55028505628570972599051203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146742681676189260264136541 55028505628570972599051203)
  ·
    refine ⟨82542758442856458898576805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55028505628570972599051203 82542758442856458898576805)
    ·
      refine ⟨15476767208035586043483151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 82542758442856458898576805 15476767208035586043483151)
      ·
        refine ⟨23215150812053379065224727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15476767208035586043483151 23215150812053379065224727)
        ·
          refine ⟨34822726218080068597837091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23215150812053379065224727 34822726218080068597837091)
          ·
            refine ⟨52234089327120102896755637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34822726218080068597837091 52234089327120102896755637)
            ·
              refine ⟨4896945874417509646570841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 52234089327120102896755637 4896945874417509646570841)
              ·
                refine ⟨3672709405813132234928131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4896945874417509646570841 3672709405813132234928131)
                ·
                  refine ⟨5509064108719698352392197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3672709405813132234928131 5509064108719698352392197)
                  ·
                    refine ⟨1032949520384943441073537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5509064108719698352392197 1032949520384943441073537)
                    ·
                      rfl

theorem cell23_6034986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 5, 2, 1, 4].length) (baseStart_6034986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6034986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6034986 prefixEnd_6034986 := by exact prefixLift 6034986
  have htrace : WordTrace (prefixWord ++ tailWord_6034986) baseStart_6034986 baseEnd_6034986 := by
    simpa [prefixWord, tailWord_6034986, baseEnd_6034986] using wordTrace_append hprefix tailTrace_6034986
  have hstable : (prefixWord ++ tailWord_6034986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6034986).length < 2 ^ (prefixWord ++ tailWord_6034986).sum := by decide
  have hdescent : baseEnd_6034986 < baseStart_6034986 := by decide
  rcases family_descends (prefixWord ++ tailWord_6034986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6034988 : List Nat := [2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 7]
def baseStart_6034988 : Nat := 118140960795 + 6034988 * 2 ^ 59
def prefixEnd_6034988 : Nat := 4983230072969 + 3 ^ 40 * 6034988 * 2
def baseEnd_6034988 : Nat := 3098849588116139315395601

theorem tailTrace_6034988 : CollatzResearch.WordTrace tailWord_6034988 prefixEnd_6034988 3098849588116139315395601 := by
  unfold tailWord_6034988
  simp only [CollatzResearch.WordTrace]
  refine ⟨110057047730138322368888809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146742730306851096491851745 110057047730138322368888809)
  ·
    refine ⟨82542785797603741776666607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110057047730138322368888809 82542785797603741776666607)
    ·
      refine ⟨123814178696405612664999911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82542785797603741776666607 123814178696405612664999911)
      ·
        refine ⟨185721268044608418997499867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123814178696405612664999911 185721268044608418997499867)
        ·
          refine ⟨278581902066912628496249801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 185721268044608418997499867 278581902066912628496249801)
          ·
            refine ⟨208936426550184471372187351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 278581902066912628496249801 208936426550184471372187351)
            ·
              refine ⟨313404639825276707058281027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 208936426550184471372187351 313404639825276707058281027)
              ·
                refine ⟨470106959737915060587421541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 313404639825276707058281027 470106959737915060587421541)
                ·
                  refine ⟨88145054950859073860141539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 470106959737915060587421541 88145054950859073860141539)
                  ·
                    refine ⟨132217582426288610790212309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 88145054950859073860141539 132217582426288610790212309)
                    ·
                      refine ⟨3098849588116139315395601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 132217582426288610790212309 3098849588116139315395601)
                      ·
                        rfl

theorem cell23_6034988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 7].length) (baseStart_6034988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6034988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6034988 prefixEnd_6034988 := by exact prefixLift 6034988
  have htrace : WordTrace (prefixWord ++ tailWord_6034988) baseStart_6034988 baseEnd_6034988 := by
    simpa [prefixWord, tailWord_6034988, baseEnd_6034988] using wordTrace_append hprefix tailTrace_6034988
  have hstable : (prefixWord ++ tailWord_6034988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6034988).length < 2 ^ (prefixWord ++ tailWord_6034988).sum := by decide
  have hdescent : baseEnd_6034988 < baseStart_6034988 := by decide
  rcases family_descends (prefixWord ++ tailWord_6034988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6035002 : List Nat := [3, 1, 1, 1, 3, 2, 1, 2, 4, 3, 2]
def baseStart_6035002 : Nat := 118140960795 + 6035002 * 2 ^ 59
def prefixEnd_6035002 : Nat := 4983230072969 + 3 ^ 40 * 6035002 * 2
def baseEnd_6035002 : Nat := 3098856776845302260620537

theorem tailTrace_6035002 : CollatzResearch.WordTrace tailWord_6035002 prefixEnd_6035002 3098856776845302260620537 := by
  unfold tailWord_6035002
  simp only [CollatzResearch.WordTrace]
  refine ⟨55028651520556481282196815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146743070721483950085858173 55028651520556481282196815)
  ·
    refine ⟨82542977280834721923295223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55028651520556481282196815 82542977280834721923295223)
    ·
      refine ⟨123814465921252082884942835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82542977280834721923295223 123814465921252082884942835)
      ·
        refine ⟨185721698881878124327414253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123814465921252082884942835 185721698881878124327414253)
        ·
          refine ⟨69645637080704296622780345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 185721698881878124327414253 69645637080704296622780345)
          ·
            refine ⟨52234227810528222467085259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69645637080704296622780345 52234227810528222467085259)
            ·
              refine ⟨78351341715792333700627889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52234227810528222467085259 78351341715792333700627889)
              ·
                refine ⟨58763506286844250275470917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 78351341715792333700627889 58763506286844250275470917)
                ·
                  refine ⟨11018157428783296926650797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 58763506286844250275470917 11018157428783296926650797)
                  ·
                    refine ⟨4131809035793736347494049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11018157428783296926650797 4131809035793736347494049)
                    ·
                      refine ⟨3098856776845302260620537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4131809035793736347494049 3098856776845302260620537)
                      ·
                        rfl

theorem cell23_6035002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 2, 4, 3, 2].length) (baseStart_6035002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6035002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6035002 prefixEnd_6035002 := by exact prefixLift 6035002
  have htrace : WordTrace (prefixWord ++ tailWord_6035002) baseStart_6035002 baseEnd_6035002 := by
    simpa [prefixWord, tailWord_6035002, baseEnd_6035002] using wordTrace_append hprefix tailTrace_6035002
  have hstable : (prefixWord ++ tailWord_6035002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6035002).length < 2 ^ (prefixWord ++ tailWord_6035002).sum := by decide
  have hdescent : baseEnd_6035002 < baseStart_6035002 := by decide
  rcases family_descends (prefixWord ++ tailWord_6035002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6035025 : List Nat := [1, 2, 2, 1, 3, 2, 3, 2, 1, 6]
def baseStart_6035025 : Nat := 118140960795 + 6035025 * 2 ^ 59
def prefixEnd_6035025 : Nat := 4983230072969 + 3 ^ 40 * 6035025 * 2
def baseEnd_6035025 : Nat := 1032956195633451890210977

theorem tailTrace_6035025 : CollatzResearch.WordTrace tailWord_6035025 prefixEnd_6035025 1032956195633451890210977 := by
  unfold tailWord_6035025
  simp only [CollatzResearch.WordTrace]
  refine ⟨220115444961142600056874529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146743629974095066704583019 220115444961142600056874529)
  ·
    refine ⟨165086583720856950042655897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 220115444961142600056874529 165086583720856950042655897)
    ·
      refine ⟨123814937790642712531991923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 165086583720856950042655897 123814937790642712531991923)
      ·
        refine ⟨185722406685964068797987885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123814937790642712531991923 185722406685964068797987885)
        ·
          refine ⟨69645902507236525799245457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 185722406685964068797987885 69645902507236525799245457)
          ·
            refine ⟨52234426880427394349434093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69645902507236525799245457 52234426880427394349434093)
            ·
              refine ⟨19587910080160272881037785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52234426880427394349434093 19587910080160272881037785)
              ·
                refine ⟨14690932560120204660778339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19587910080160272881037785 14690932560120204660778339)
                ·
                  refine ⟨22036398840180306991167509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14690932560120204660778339 22036398840180306991167509)
                  ·
                    refine ⟨1032956195633451890210977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22036398840180306991167509 1032956195633451890210977)
                    ·
                      rfl

theorem cell23_6035025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 3, 2, 1, 6].length) (baseStart_6035025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6035025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6035025 prefixEnd_6035025 := by exact prefixLift 6035025
  have htrace : WordTrace (prefixWord ++ tailWord_6035025) baseStart_6035025 baseEnd_6035025 := by
    simpa [prefixWord, tailWord_6035025, baseEnd_6035025] using wordTrace_append hprefix tailTrace_6035025
  have hstable : (prefixWord ++ tailWord_6035025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6035025).length < 2 ^ (prefixWord ++ tailWord_6035025).sum := by decide
  have hdescent : baseEnd_6035025 < baseStart_6035025 := by decide
  rcases family_descends (prefixWord ++ tailWord_6035025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6035037 : List Nat := [1, 4, 4, 2, 2, 1, 2, 2, 1, 4]
def baseStart_6035037 : Nat := 118140960795 + 6035037 * 2 ^ 59
def prefixEnd_6035037 : Nat := 4983230072969 + 3 ^ 40 * 6035037 * 2
def baseEnd_6035037 : Nat := 1032958249556069874560959

theorem tailTrace_6035037 : CollatzResearch.WordTrace tailWord_6035037 prefixEnd_6035037 1032958249556069874560959 := by
  unfold tailWord_6035037
  simp only [CollatzResearch.WordTrace]
  refine ⟨220115882637099126106311365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146743921758066084070874243 220115882637099126106311365)
  ·
    refine ⟨41271727994456086144933381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 220115882637099126106311365 41271727994456086144933381)
    ·
      refine ⟨7738448998960516152175009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41271727994456086144933381 7738448998960516152175009)
      ·
        refine ⟨5803836749220387114131257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7738448998960516152175009 5803836749220387114131257)
        ·
          refine ⟨4352877561915290335598443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5803836749220387114131257 4352877561915290335598443)
          ·
            refine ⟨6529316342872935503397665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4352877561915290335598443 6529316342872935503397665)
            ·
              refine ⟨4896987257154701627548249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6529316342872935503397665 4896987257154701627548249)
              ·
                refine ⟨3672740442866026220661187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4896987257154701627548249 3672740442866026220661187)
                ·
                  refine ⟨5509110664299039330991781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3672740442866026220661187 5509110664299039330991781)
                  ·
                    refine ⟨1032958249556069874560959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5509110664299039330991781 1032958249556069874560959)
                    ·
                      rfl

theorem cell23_6035037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 2, 1, 2, 2, 1, 4].length) (baseStart_6035037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6035037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6035037 prefixEnd_6035037 := by exact prefixLift 6035037
  have htrace : WordTrace (prefixWord ++ tailWord_6035037) baseStart_6035037 baseEnd_6035037 := by
    simpa [prefixWord, tailWord_6035037, baseEnd_6035037] using wordTrace_append hprefix tailTrace_6035037
  have hstable : (prefixWord ++ tailWord_6035037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6035037).length < 2 ^ (prefixWord ++ tailWord_6035037).sum := by decide
  have hdescent : baseEnd_6035037 < baseStart_6035037 := by decide
  rcases family_descends (prefixWord ++ tailWord_6035037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6035043 : List Nat := [1, 1, 1, 5, 1, 5, 2, 2, 1, 1, 3]
def baseStart_6035043 : Nat := 118140960795 + 6035043 * 2 ^ 59
def prefixEnd_6035043 : Nat := 4983230072969 + 3 ^ 40 * 6035043 * 2
def baseEnd_6035043 : Nat := 3098877829552136600207849

theorem tailTrace_6035043 : CollatzResearch.WordTrace tailWord_6035043 prefixEnd_6035043 3098877829552136600207849 := by
  unfold tailWord_6035043
  simp only [CollatzResearch.WordTrace]
  refine ⟨220116101475077389131029783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146744067650051592754019855 220116101475077389131029783)
  ·
    refine ⟨330174152212616083696544675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220116101475077389131029783 330174152212616083696544675)
    ·
      refine ⟨495261228318924125544817013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 330174152212616083696544675 495261228318924125544817013)
      ·
        refine ⟨46430740154899136769826595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 495261228318924125544817013 46430740154899136769826595)
        ·
          refine ⟨69646110232348705154739893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46430740154899136769826595 69646110232348705154739893)
          ·
            refine ⟨6529322834282691108256865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 69646110232348705154739893 6529322834282691108256865)
            ·
              refine ⟨4896992125712018331192649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6529322834282691108256865 4896992125712018331192649)
              ·
                refine ⟨3672744094284013748394487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4896992125712018331192649 3672744094284013748394487)
                ·
                  refine ⟨5509116141426020622591731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3672744094284013748394487 5509116141426020622591731)
                  ·
                    refine ⟨8263674212139030933887597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5509116141426020622591731 8263674212139030933887597)
                    ·
                      refine ⟨3098877829552136600207849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8263674212139030933887597 3098877829552136600207849)
                      ·
                        rfl

theorem cell23_6035043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 5, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 5, 2, 2, 1, 1, 3].length) (baseStart_6035043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6035043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6035043 prefixEnd_6035043 := by exact prefixLift 6035043
  have htrace : WordTrace (prefixWord ++ tailWord_6035043) baseStart_6035043 baseEnd_6035043 := by
    simpa [prefixWord, tailWord_6035043, baseEnd_6035043] using wordTrace_append hprefix tailTrace_6035043
  have hstable : (prefixWord ++ tailWord_6035043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6035043).length < 2 ^ (prefixWord ++ tailWord_6035043).sum := by decide
  have hdescent : baseEnd_6035043 < baseStart_6035043 := by decide
  rcases family_descends (prefixWord ++ tailWord_6035043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6035086 : List Nat := [4, 1, 1, 3, 1, 2, 4, 1, 1, 2, 3]
def baseStart_6035086 : Nat := 118140960795 + 6035086 * 2 ^ 59
def prefixEnd_6035086 : Nat := 4983230072969 + 3 ^ 40 * 6035086 * 2
def baseEnd_6035086 : Nat := 3098899909220279931970151

theorem tailTrace_6035086 : CollatzResearch.WordTrace tailWord_6035086 prefixEnd_6035086 3098899909220279931970151 := by
  unfold tailWord_6035086
  simp only [CollatzResearch.WordTrace]
  refine ⟨27514708726740200934355639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 146745113209281071649896741 27514708726740200934355639)
  ·
    refine ⟨41272063090110301401533459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27514708726740200934355639 41272063090110301401533459)
    ·
      refine ⟨61908094635165452102300189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41272063090110301401533459 61908094635165452102300189)
      ·
        refine ⟨23215535488187044538362571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61908094635165452102300189 23215535488187044538362571)
        ·
          refine ⟨34823303232280566807543857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23215535488187044538362571 34823303232280566807543857)
          ·
            refine ⟨26117477424210425105657893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34823303232280566807543857 26117477424210425105657893)
            ·
              refine ⟨4897027017039454707310855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26117477424210425105657893 4897027017039454707310855)
              ·
                refine ⟨7345540525559182060966283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4897027017039454707310855 7345540525559182060966283)
                ·
                  refine ⟨11018310788338773091449425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7345540525559182060966283 11018310788338773091449425)
                  ·
                    refine ⟨8263733091254079818587069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11018310788338773091449425 8263733091254079818587069)
                    ·
                      refine ⟨3098899909220279931970151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8263733091254079818587069 3098899909220279931970151)
                      ·
                        rfl

theorem cell23_6035086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 4, 1, 1, 2, 3].length) (baseStart_6035086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6035086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6035086 prefixEnd_6035086 := by exact prefixLift 6035086
  have htrace : WordTrace (prefixWord ++ tailWord_6035086) baseStart_6035086 baseEnd_6035086 := by
    simpa [prefixWord, tailWord_6035086, baseEnd_6035086] using wordTrace_append hprefix tailTrace_6035086
  have hstable : (prefixWord ++ tailWord_6035086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6035086).length < 2 ^ (prefixWord ++ tailWord_6035086).sum := by decide
  have hdescent : baseEnd_6035086 < baseStart_6035086 := by decide
  rcases family_descends (prefixWord ++ tailWord_6035086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6035162 : List Nat := [3, 1, 1, 2, 2, 3, 3, 1, 7]
def baseStart_6035162 : Nat := 118140960795 + 6035162 * 2 ^ 59
def prefixEnd_6035162 : Nat := 4983230072969 + 3 ^ 40 * 6035162 * 2
def baseEnd_6035162 : Nat := 344326548194446848291089

theorem tailTrace_6035162 : CollatzResearch.WordTrace tailWord_6035162 prefixEnd_6035162 344326548194446848291089 := by
  unfold tailWord_6035162
  simp only [CollatzResearch.WordTrace]
  refine ⟨55030110440411568113652935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146746961174430848303074493 55030110440411568113652935)
  ·
    refine ⟨82545165660617352170479403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55030110440411568113652935 82545165660617352170479403)
    ·
      refine ⟨123817748490926028255719105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82545165660617352170479403 123817748490926028255719105)
      ·
        refine ⟨92863311368194521191789329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123817748490926028255719105 92863311368194521191789329)
        ·
          refine ⟨69647483526145890893841997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92863311368194521191789329 69647483526145890893841997)
          ·
            refine ⟨26117806322304709085190749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69647483526145890893841997 26117806322304709085190749)
            ·
              refine ⟨9794177370864265906946531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26117806322304709085190749 9794177370864265906946531)
              ·
                refine ⟨14691266056296398860419797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9794177370864265906946531 14691266056296398860419797)
                ·
                  refine ⟨344326548194446848291089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14691266056296398860419797 344326548194446848291089)
                  ·
                    rfl

theorem cell23_6035162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 3, 1, 7].length) (baseStart_6035162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6035162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6035162 prefixEnd_6035162 := by exact prefixLift 6035162
  have htrace : WordTrace (prefixWord ++ tailWord_6035162) baseStart_6035162 baseEnd_6035162 := by
    simpa [prefixWord, tailWord_6035162, baseEnd_6035162] using wordTrace_append hprefix tailTrace_6035162
  have hstable : (prefixWord ++ tailWord_6035162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6035162).length < 2 ^ (prefixWord ++ tailWord_6035162).sum := by decide
  have hdescent : baseEnd_6035162 < baseStart_6035162 := by decide
  rcases family_descends (prefixWord ++ tailWord_6035162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6035172 : List Nat := [2, 3, 1, 1, 1, 3, 2, 1, 1, 5, 3]
def baseStart_6035172 : Nat := 118140960795 + 6035172 * 2 ^ 59
def prefixEnd_6035172 : Nat := 4983230072969 + 3 ^ 40 * 6035172 * 2
def baseEnd_6035172 : Nat := 3098944068556566595494755

theorem tailTrace_6035172 : CollatzResearch.WordTrace tailWord_6035172 prefixEnd_6035172 3098944068556566595494755 := by
  unfold tailWord_6035172
  simp only [CollatzResearch.WordTrace]
  refine ⟨110060403245805022081237885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146747204327740029441650513 110060403245805022081237885)
  ·
    refine ⟨41272651217176883280464207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110060403245805022081237885 41272651217176883280464207)
    ·
      refine ⟨61908976825765324920696311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41272651217176883280464207 61908976825765324920696311)
      ·
        refine ⟨92863465238647987381044467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61908976825765324920696311 92863465238647987381044467)
        ·
          refine ⟨139295197857971981071566701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92863465238647987381044467 139295197857971981071566701)
          ·
            refine ⟨52235699196739492901837513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 139295197857971981071566701 52235699196739492901837513)
            ·
              refine ⟨39176774397554619676378135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52235699196739492901837513 39176774397554619676378135)
              ·
                refine ⟨58765161596331929514567203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39176774397554619676378135 58765161596331929514567203)
                ·
                  refine ⟨88147742394497894271850805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58765161596331929514567203 88147742394497894271850805)
                  ·
                    refine ⟨8263850849484177587986013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 88147742394497894271850805 8263850849484177587986013)
                    ·
                      refine ⟨3098944068556566595494755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8263850849484177587986013 3098944068556566595494755)
                      ·
                        rfl

theorem cell23_6035172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 1, 1, 5, 3].length) (baseStart_6035172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6035172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6035172 prefixEnd_6035172 := by exact prefixLift 6035172
  have htrace : WordTrace (prefixWord ++ tailWord_6035172) baseStart_6035172 baseEnd_6035172 := by
    simpa [prefixWord, tailWord_6035172, baseEnd_6035172] using wordTrace_append hprefix tailTrace_6035172
  have hstable : (prefixWord ++ tailWord_6035172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6035172).length < 2 ^ (prefixWord ++ tailWord_6035172).sum := by decide
  have hdescent : baseEnd_6035172 < baseStart_6035172 := by decide
  rcases family_descends (prefixWord ++ tailWord_6035172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6035246 : List Nat := [4, 1, 3, 2, 2, 1, 1, 1, 1, 3, 4]
def baseStart_6035246 : Nat := 118140960795 + 6035246 * 2 ^ 59
def prefixEnd_6035246 : Nat := 4983230072969 + 3 ^ 40 * 6035246 * 2
def baseEnd_6035246 : Nat := 3098982066124999305969415

theorem tailTrace_6035246 : CollatzResearch.WordTrace tailWord_6035246 prefixEnd_6035246 3098982066124999305969415 := by
  unfold tailWord_6035246
  simp only [CollatzResearch.WordTrace]
  refine ⟨27515438186667744350083699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 146749003662227969867113061 27515438186667744350083699)
  ·
    refine ⟨41273157280001616525125549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27515438186667744350083699 41273157280001616525125549)
    ·
      refine ⟨15477433980000606196922081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41273157280001616525125549 15477433980000606196922081)
      ·
        refine ⟨11608075485000454647691561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15477433980000606196922081 11608075485000454647691561)
        ·
          refine ⟨8706056613750340985768671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11608075485000454647691561 8706056613750340985768671)
          ·
            refine ⟨13059084920625511478653007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8706056613750340985768671 13059084920625511478653007)
            ·
              refine ⟨19588627380938267217979511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13059084920625511478653007 19588627380938267217979511)
              ·
                refine ⟨29382941071407400826969267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19588627380938267217979511 29382941071407400826969267)
                ·
                  refine ⟨44074411607111101240453901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29382941071407400826969267 44074411607111101240453901)
                  ·
                    refine ⟨16527904352666662965170213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 44074411607111101240453901 16527904352666662965170213)
                    ·
                      refine ⟨3098982066124999305969415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16527904352666662965170213 3098982066124999305969415)
                      ·
                        rfl

theorem cell23_6035246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 1, 1, 1, 3, 4].length) (baseStart_6035246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6035246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6035246 prefixEnd_6035246 := by exact prefixLift 6035246
  have htrace : WordTrace (prefixWord ++ tailWord_6035246) baseStart_6035246 baseEnd_6035246 := by
    simpa [prefixWord, tailWord_6035246, baseEnd_6035246] using wordTrace_append hprefix tailTrace_6035246
  have hstable : (prefixWord ++ tailWord_6035246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6035246).length < 2 ^ (prefixWord ++ tailWord_6035246).sum := by decide
  have hdescent : baseEnd_6035246 < baseStart_6035246 := by decide
  rcases family_descends (prefixWord ++ tailWord_6035246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6035249 : List Nat := [1, 2, 2, 3, 2, 3, 1, 1, 1, 4, 3]
def baseStart_6035249 : Nat := 118140960795 + 6035249 * 2 ^ 59
def prefixEnd_6035249 : Nat := 4983230072969 + 3 ^ 40 * 6035249 * 2
def baseEnd_6035249 : Nat := 3098983606566962794231901

theorem tailTrace_6035249 : CollatzResearch.WordTrace tailWord_6035249 prefixEnd_6035249 3098983606566962794231901 := by
  unfold tailWord_6035249
  simp only [CollatzResearch.WordTrace]
  refine ⟨220123614912331086313028801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146749076608220724208685867 220123614912331086313028801)
  ·
    refine ⟨165092711184248314734771601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 220123614912331086313028801 165092711184248314734771601)
    ·
      refine ⟨123819533388186236051078701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 165092711184248314734771601 123819533388186236051078701)
      ·
        refine ⟨46432325020569838519154513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 123819533388186236051078701 46432325020569838519154513)
        ·
          refine ⟨34824243765427378889365885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46432325020569838519154513 34824243765427378889365885)
          ·
            refine ⟨13059091412035267083512207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34824243765427378889365885 13059091412035267083512207)
            ·
              refine ⟨19588637118052900625268311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13059091412035267083512207 19588637118052900625268311)
              ·
                refine ⟨29382955677079350937902467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19588637118052900625268311 29382955677079350937902467)
                ·
                  refine ⟨44074433515619026406853701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29382955677079350937902467 44074433515619026406853701)
                  ·
                    refine ⟨8263956284178567451285069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 44074433515619026406853701 8263956284178567451285069)
                    ·
                      refine ⟨3098983606566962794231901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8263956284178567451285069 3098983606566962794231901)
                      ·
                        rfl

theorem cell23_6035249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 1, 1, 1, 4, 3].length) (baseStart_6035249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6035249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6035249 prefixEnd_6035249 := by exact prefixLift 6035249
  have htrace : WordTrace (prefixWord ++ tailWord_6035249) baseStart_6035249 baseEnd_6035249 := by
    simpa [prefixWord, tailWord_6035249, baseEnd_6035249] using wordTrace_append hprefix tailTrace_6035249
  have hstable : (prefixWord ++ tailWord_6035249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6035249).length < 2 ^ (prefixWord ++ tailWord_6035249).sum := by decide
  have hdescent : baseEnd_6035249 < baseStart_6035249 := by decide
  rcases family_descends (prefixWord ++ tailWord_6035249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6035256 : List Nat := [2, 1, 2, 1, 3, 3, 1, 5, 1, 4]
def baseStart_6035256 : Nat := 118140960795 + 6035256 * 2 ^ 59
def prefixEnd_6035256 : Nat := 4983230072969 + 3 ^ 40 * 6035256 * 2
def baseEnd_6035256 : Nat := 1032995733643848088948123

theorem tailTrace_6035256 : CollatzResearch.WordTrace tailWord_6035256 prefixEnd_6035256 1032995733643848088948123 := by
  unfold tailWord_6035256
  simp only [CollatzResearch.WordTrace]
  refine ⟨110061935111652863254266811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146749246815537151005689081 110061935111652863254266811)
  ·
    refine ⟨165092902667479294881400217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110061935111652863254266811 165092902667479294881400217)
    ·
      refine ⟨123819677000609471161050163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 165092902667479294881400217 123819677000609471161050163)
      ·
        refine ⟨185729515500914206741575245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123819677000609471161050163 185729515500914206741575245)
        ·
          refine ⟨69648568312842827528090717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 185729515500914206741575245 69648568312842827528090717)
          ·
            refine ⟨26118213117316060323034019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69648568312842827528090717 26118213117316060323034019)
            ·
              refine ⟨39177319675974090484551029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26118213117316060323034019 39177319675974090484551029)
              ·
                refine ⟨3672873719622570982926659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 39177319675974090484551029 3672873719622570982926659)
                ·
                  refine ⟨5509310579433856474389989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3672873719622570982926659 5509310579433856474389989)
                  ·
                    refine ⟨1032995733643848088948123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5509310579433856474389989 1032995733643848088948123)
                    ·
                      rfl

theorem cell23_6035256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 5, 1, 4].length) (baseStart_6035256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6035256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6035256 prefixEnd_6035256 := by exact prefixLift 6035256
  have htrace : WordTrace (prefixWord ++ tailWord_6035256) baseStart_6035256 baseEnd_6035256 := by
    simpa [prefixWord, tailWord_6035256, baseEnd_6035256] using wordTrace_append hprefix tailTrace_6035256
  have hstable : (prefixWord ++ tailWord_6035256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6035256).length < 2 ^ (prefixWord ++ tailWord_6035256).sum := by decide
  have hdescent : baseEnd_6035256 < baseStart_6035256 := by decide
  rcases family_descends (prefixWord ++ tailWord_6035256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6035272 : List Nat := [2, 1, 3, 1, 1, 4, 1, 1, 1, 2, 6]
def baseStart_6035272 : Nat := 118140960795 + 6035272 * 2 ^ 59
def prefixEnd_6035272 : Nat := 4983230072969 + 3 ^ 40 * 6035272 * 2
def baseEnd_6035272 : Nat := 3098995416622016204244295

theorem tailTrace_6035272 : CollatzResearch.WordTrace tailWord_6035272 prefixEnd_6035272 3098995416622016204244295 := by
  unfold tailWord_6035272
  simp only [CollatzResearch.WordTrace]
  refine ⟨110062226895623880620558035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146749635860831840827410713 110062226895623880620558035)
  ·
    refine ⟨165093340343435820930837053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110062226895623880620558035 165093340343435820930837053)
    ·
      refine ⟨61910002628788432849063895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 165093340343435820930837053 61910002628788432849063895)
      ·
        refine ⟨92865003943182649273595843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61910002628788432849063895 92865003943182649273595843)
        ·
          refine ⟨139297505914773973910393765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92865003943182649273595843 139297505914773973910393765)
          ·
            refine ⟨26118282359020120108198831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 139297505914773973910393765 26118282359020120108198831)
            ·
              refine ⟨39177423538530180162298247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26118282359020120108198831 39177423538530180162298247)
              ·
                refine ⟨58766135307795270243447371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39177423538530180162298247 58766135307795270243447371)
                ·
                  refine ⟨88149202961692905365171057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58766135307795270243447371 88149202961692905365171057)
                  ·
                    refine ⟨66111902221269679023878293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 88149202961692905365171057 66111902221269679023878293)
                    ·
                      refine ⟨3098995416622016204244295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 66111902221269679023878293 3098995416622016204244295)
                      ·
                        rfl

theorem cell23_6035272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 1, 1, 2, 6].length) (baseStart_6035272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6035272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6035272 prefixEnd_6035272 := by exact prefixLift 6035272
  have htrace : WordTrace (prefixWord ++ tailWord_6035272) baseStart_6035272 baseEnd_6035272 := by
    simpa [prefixWord, tailWord_6035272, baseEnd_6035272] using wordTrace_append hprefix tailTrace_6035272
  have hstable : (prefixWord ++ tailWord_6035272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6035272).length < 2 ^ (prefixWord ++ tailWord_6035272).sum := by decide
  have hdescent : baseEnd_6035272 < baseStart_6035272 := by decide
  rcases family_descends (prefixWord ++ tailWord_6035272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6035289 : List Nat := [1, 2, 1, 2, 2, 3, 1, 1, 3, 5, 2]
def baseStart_6035289 : Nat := 118140960795 + 6035289 * 2 ^ 59
def prefixEnd_6035289 : Nat := 4983230072969 + 3 ^ 40 * 6035289 * 2
def baseEnd_6035289 : Nat := 3099004145793142637731717

theorem tailTrace_6035289 : CollatzResearch.WordTrace tailWord_6035289 prefixEnd_6035289 3099004145793142637731717 := by
  unfold tailWord_6035289
  simp only [CollatzResearch.WordTrace]
  refine ⟨220125073832186173144484921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146750049221457448762989947 220125073832186173144484921)
  ·
    refine ⟨165093805374139629858363691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 220125073832186173144484921 165093805374139629858363691)
    ·
      refine ⟨247640708061209444787545537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165093805374139629858363691 247640708061209444787545537)
      ·
        refine ⟨185730531045907083590659153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 247640708061209444787545537 185730531045907083590659153)
        ·
          refine ⟨139297898284430312692994365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 185730531045907083590659153 139297898284430312692994365)
          ·
            refine ⟨52236711856661367259872887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 139297898284430312692994365 52236711856661367259872887)
            ·
              refine ⟨78355067784992050889809331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52236711856661367259872887 78355067784992050889809331)
              ·
                refine ⟨117532601677488076334713997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78355067784992050889809331 117532601677488076334713997)
                ·
                  refine ⟨44074725629058028625517749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 117532601677488076334713997 44074725629058028625517749)
                  ·
                    refine ⟨4132005527724190183642289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 44074725629058028625517749 4132005527724190183642289)
                    ·
                      refine ⟨3099004145793142637731717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4132005527724190183642289 3099004145793142637731717)
                      ·
                        rfl

theorem cell23_6035289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 1, 3, 5, 2].length) (baseStart_6035289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6035289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6035289 prefixEnd_6035289 := by exact prefixLift 6035289
  have htrace : WordTrace (prefixWord ++ tailWord_6035289) baseStart_6035289 baseEnd_6035289 := by
    simpa [prefixWord, tailWord_6035289, baseEnd_6035289] using wordTrace_append hprefix tailTrace_6035289
  have hstable : (prefixWord ++ tailWord_6035289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6035289).length < 2 ^ (prefixWord ++ tailWord_6035289).sum := by decide
  have hdescent : baseEnd_6035289 < baseStart_6035289 := by decide
  rcases family_descends (prefixWord ++ tailWord_6035289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6035296 : List Nat := [2, 1, 1, 3, 3, 2, 2, 2, 3, 1, 3]
def baseStart_6035296 : Nat := 118140960795 + 6035296 * 2 ^ 59
def prefixEnd_6035296 : Nat := 4983230072969 + 3 ^ 40 * 6035296 * 2
def baseEnd_6035296 : Nat := 3099007740157724110344185

theorem tailTrace_6035296 : CollatzResearch.WordTrace tailWord_6035296 prefixEnd_6035296 3099007740157724110344185 := by
  unfold tailWord_6035296
  simp only [CollatzResearch.WordTrace]
  refine ⟨110062664571580406669994871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146750219428773875559993161 110062664571580406669994871)
  ·
    refine ⟨165093996857370610004992307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110062664571580406669994871 165093996857370610004992307)
    ·
      refine ⟨247640995286055915007488461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165093996857370610004992307 247640995286055915007488461)
      ·
        refine ⟨92865373232270968127808173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 247640995286055915007488461 92865373232270968127808173)
        ·
          refine ⟨34824514962101613047928065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 92865373232270968127808173 34824514962101613047928065)
          ·
            refine ⟨26118386221576209785946049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34824514962101613047928065 26118386221576209785946049)
            ·
              refine ⟨19588789666182157339459537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26118386221576209785946049 19588789666182157339459537)
              ·
                refine ⟨14691592249636618004594653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19588789666182157339459537 14691592249636618004594653)
                ·
                  refine ⟨5509347093613731751722995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14691592249636618004594653 5509347093613731751722995)
                  ·
                    refine ⟨8264020640420597627584493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5509347093613731751722995 8264020640420597627584493)
                    ·
                      refine ⟨3099007740157724110344185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8264020640420597627584493 3099007740157724110344185)
                      ·
                        rfl

theorem cell23_6035296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 2, 2, 3, 1, 3].length) (baseStart_6035296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6035296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6035296 prefixEnd_6035296 := by exact prefixLift 6035296
  have htrace : WordTrace (prefixWord ++ tailWord_6035296) baseStart_6035296 baseEnd_6035296 := by
    simpa [prefixWord, tailWord_6035296, baseEnd_6035296] using wordTrace_append hprefix tailTrace_6035296
  have hstable : (prefixWord ++ tailWord_6035296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6035296).length < 2 ^ (prefixWord ++ tailWord_6035296).sum := by decide
  have hdescent : baseEnd_6035296 < baseStart_6035296 := by decide
  rcases family_descends (prefixWord ++ tailWord_6035296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6035312 : List Nat := [2, 1, 1, 1, 4, 1, 1, 3, 3, 6]
def baseStart_6035312 : Nat := 118140960795 + 6035312 * 2 ^ 59
def prefixEnd_6035312 : Nat := 4983230072969 + 3 ^ 40 * 6035312 * 2
def baseEnd_6035312 : Nat := 1033005318616065349248037

theorem tailTrace_6035312 : CollatzResearch.WordTrace tailWord_6035312 prefixEnd_6035312 1033005318616065349248037 := by
  unfold tailWord_6035312
  simp only [CollatzResearch.WordTrace]
  refine ⟨110062956355551424036286095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146750608474068565381714793 110062956355551424036286095)
  ·
    refine ⟨165094434533327136054429143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110062956355551424036286095 165094434533327136054429143)
    ·
      refine ⟨247641651799990704081643715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165094434533327136054429143 247641651799990704081643715)
      ·
        refine ⟨371462477699986056122465573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 247641651799990704081643715 371462477699986056122465573)
        ·
          refine ⟨69649214568747385522962295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 371462477699986056122465573 69649214568747385522962295)
          ·
            refine ⟨104473821853121078284443443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69649214568747385522962295 104473821853121078284443443)
            ·
              refine ⟨156710732779681617426665165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104473821853121078284443443 156710732779681617426665165)
              ·
                refine ⟨58766524792380606534999437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 156710732779681617426665165 58766524792380606534999437)
                ·
                  refine ⟨22037446797142727450624789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 58766524792380606534999437 22037446797142727450624789)
                  ·
                    refine ⟨1033005318616065349248037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22037446797142727450624789 1033005318616065349248037)
                    ·
                      rfl

theorem cell23_6035312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 3, 3, 6].length) (baseStart_6035312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6035312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6035312 prefixEnd_6035312 := by exact prefixLift 6035312
  have htrace : WordTrace (prefixWord ++ tailWord_6035312) baseStart_6035312 baseEnd_6035312 := by
    simpa [prefixWord, tailWord_6035312, baseEnd_6035312] using wordTrace_append hprefix tailTrace_6035312
  have hstable : (prefixWord ++ tailWord_6035312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6035312).length < 2 ^ (prefixWord ++ tailWord_6035312).sum := by decide
  have hdescent : baseEnd_6035312 < baseStart_6035312 := by decide
  rcases family_descends (prefixWord ++ tailWord_6035312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6035339 : List Nat := [1, 1, 1, 1, 4, 2, 1, 4, 3, 2, 3]
def baseStart_6035339 : Nat := 118140960795 + 6035339 * 2 ^ 59
def prefixEnd_6035339 : Nat := 4983230072969 + 3 ^ 40 * 6035339 * 2
def baseEnd_6035339 : Nat := 3099029819825867442106487

theorem tailTrace_6035339 : CollatzResearch.WordTrace tailWord_6035339 prefixEnd_6035339 3099029819825867442106487 := by
  unfold tailWord_6035339
  simp only [CollatzResearch.WordTrace]
  refine ⟨220126897482005031683805071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146751264988003354455870047 220126897482005031683805071)
  ·
    refine ⟨330190346223007547525707607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220126897482005031683805071 330190346223007547525707607)
    ·
      refine ⟨495285519334511321288561411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 330190346223007547525707607 495285519334511321288561411)
      ·
        refine ⟨742928279001766981932842117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 495285519334511321288561411 742928279001766981932842117)
        ·
          refine ⟨139299052312831309112407897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 742928279001766981932842117 139299052312831309112407897)
          ·
            refine ⟨104474289234623481834305923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 139299052312831309112407897 104474289234623481834305923)
            ·
              refine ⟨156711433851935222751458885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104474289234623481834305923 156711433851935222751458885)
              ·
                refine ⟨29383393847237854265898541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 156711433851935222751458885 29383393847237854265898541)
                ·
                  refine ⟨11018772692714195349711953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29383393847237854265898541 11018772692714195349711953)
                  ·
                    refine ⟨8264079519535646512283965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11018772692714195349711953 8264079519535646512283965)
                    ·
                      refine ⟨3099029819825867442106487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8264079519535646512283965 3099029819825867442106487)
                      ·
                        rfl

theorem cell23_6035339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 4, 3, 2, 3].length) (baseStart_6035339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6035339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6035339 prefixEnd_6035339 := by exact prefixLift 6035339
  have htrace : WordTrace (prefixWord ++ tailWord_6035339) baseStart_6035339 baseEnd_6035339 := by
    simpa [prefixWord, tailWord_6035339, baseEnd_6035339] using wordTrace_append hprefix tailTrace_6035339
  have hstable : (prefixWord ++ tailWord_6035339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6035339).length < 2 ^ (prefixWord ++ tailWord_6035339).sum := by decide
  have hdescent : baseEnd_6035339 < baseStart_6035339 := by decide
  rcases family_descends (prefixWord ++ tailWord_6035339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6035349 : List Nat := [1, 3, 2, 1, 1, 3, 2, 3, 1, 2, 4]
def baseStart_6035349 : Nat := 118140960795 + 6035349 * 2 ^ 59
def prefixEnd_6035349 : Nat := 4983230072969 + 3 ^ 40 * 6035349 * 2
def baseEnd_6035349 : Nat := 3099034954632412402981441

theorem tailTrace_6035349 : CollatzResearch.WordTrace tailWord_6035349 prefixEnd_6035349 3099034954632412402981441 := by
  unfold tailWord_6035349
  simp only [CollatzResearch.WordTrace]
  refine ⟨220127262211968803391669101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146751508141312535594446067 220127262211968803391669101)
  ·
    refine ⟨82547723329488301271875913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 220127262211968803391669101 82547723329488301271875913)
    ·
      refine ⟨61910792497116225953906935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82547723329488301271875913 61910792497116225953906935)
      ·
        refine ⟨92866188745674338930860403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61910792497116225953906935 92866188745674338930860403)
        ·
          refine ⟨139299283118511508396290605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92866188745674338930860403 139299283118511508396290605)
          ·
            refine ⟨52237231169441815648608977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 139299283118511508396290605 52237231169441815648608977)
            ·
              refine ⟨39177923377081361736456733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52237231169441815648608977 39177923377081361736456733)
              ·
                refine ⟨14691721266405510651171275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39177923377081361736456733 14691721266405510651171275)
                ·
                  refine ⟨22037581899608265976756913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14691721266405510651171275 22037581899608265976756913)
                  ·
                    refine ⟨16528186424706199482567685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22037581899608265976756913 16528186424706199482567685)
                    ·
                      refine ⟨3099034954632412402981441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16528186424706199482567685 3099034954632412402981441)
                      ·
                        rfl

theorem cell23_6035349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 3, 1, 2, 4].length) (baseStart_6035349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6035349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6035349 prefixEnd_6035349 := by exact prefixLift 6035349
  have htrace : WordTrace (prefixWord ++ tailWord_6035349) baseStart_6035349 baseEnd_6035349 := by
    simpa [prefixWord, tailWord_6035349, baseEnd_6035349] using wordTrace_append hprefix tailTrace_6035349
  have hstable : (prefixWord ++ tailWord_6035349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6035349).length < 2 ^ (prefixWord ++ tailWord_6035349).sum := by decide
  have hdescent : baseEnd_6035349 < baseStart_6035349 := by decide
  rcases family_descends (prefixWord ++ tailWord_6035349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6035350 : List Nat := [5, 3, 1, 1, 2, 1, 1, 1, 3, 5]
def baseStart_6035350 : Nat := 118140960795 + 6035350 * 2 ^ 59
def prefixEnd_6035350 : Nat := 4983230072969 + 3 ^ 40 * 6035350 * 2
def baseEnd_6035350 : Nat := 1033011822704355633022979

theorem tailTrace_6035350 : CollatzResearch.WordTrace tailWord_6035350 prefixEnd_6035350 1033011822704355633022979 := by
  unfold tailWord_6035350
  simp only [CollatzResearch.WordTrace]
  refine ⟨13757956167810323785153469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 146751532456643453708303669 13757956167810323785153469)
  ·
    refine ⟨5159233562928871419432551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13757956167810323785153469 5159233562928871419432551)
    ·
      refine ⟨7738850344393307129148827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5159233562928871419432551 7738850344393307129148827)
      ·
        refine ⟨11608275516589960693723241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7738850344393307129148827 11608275516589960693723241)
        ·
          refine ⟨8706206637442470520292431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11608275516589960693723241 8706206637442470520292431)
          ·
            refine ⟨13059309956163705780438647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8706206637442470520292431 13059309956163705780438647)
            ·
              refine ⟨19588964934245558670657971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13059309956163705780438647 19588964934245558670657971)
              ·
                refine ⟨29383447401368338005986957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19588964934245558670657971 29383447401368338005986957)
                ·
                  refine ⟨11018792775513126752245109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29383447401368338005986957 11018792775513126752245109)
                  ·
                    refine ⟨1033011822704355633022979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11018792775513126752245109 1033011822704355633022979)
                    ·
                      rfl

theorem cell23_6035350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 1, 1, 3, 5].length) (baseStart_6035350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6035350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6035350 prefixEnd_6035350 := by exact prefixLift 6035350
  have htrace : WordTrace (prefixWord ++ tailWord_6035350) baseStart_6035350 baseEnd_6035350 := by
    simpa [prefixWord, tailWord_6035350, baseEnd_6035350] using wordTrace_append hprefix tailTrace_6035350
  have hstable : (prefixWord ++ tailWord_6035350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6035350).length < 2 ^ (prefixWord ++ tailWord_6035350).sum := by decide
  have hdescent : baseEnd_6035350 < baseStart_6035350 := by decide
  rcases family_descends (prefixWord ++ tailWord_6035350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6035372 : List Nat := [2, 2, 1, 1, 1, 1, 2, 1, 3, 9]
def baseStart_6035372 : Nat := 118140960795 + 6035372 * 2 ^ 59
def prefixEnd_6035372 : Nat := 4983230072969 + 3 ^ 40 * 6035372 * 2
def baseEnd_6035372 : Nat := 1033015588229155270997945

theorem tailTrace_6035372 : CollatzResearch.WordTrace tailWord_6035372 prefixEnd_6035372 1033015588229155270997945 := by
  unfold tailWord_6035372
  simp only [CollatzResearch.WordTrace]
  refine ⟨110064050545442739159878185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146752067393923652213170913 110064050545442739159878185)
  ·
    refine ⟨82548037909082054369908639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110064050545442739159878185 82548037909082054369908639)
    ·
      refine ⟨123822056863623081554862959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82548037909082054369908639 123822056863623081554862959)
      ·
        refine ⟨185733085295434622332294439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123822056863623081554862959 185733085295434622332294439)
        ·
          refine ⟨278599627943151933498441659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 185733085295434622332294439 278599627943151933498441659)
          ·
            refine ⟨417899441914727900247662489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 278599627943151933498441659 417899441914727900247662489)
            ·
              refine ⟨313424581436045925185746867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 417899441914727900247662489 313424581436045925185746867)
              ·
                refine ⟨470136872154068887778620301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 313424581436045925185746867 470136872154068887778620301)
                ·
                  refine ⟨176301327057775832916982613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 470136872154068887778620301 176301327057775832916982613)
                  ·
                    refine ⟨1033015588229155270997945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 176301327057775832916982613 1033015588229155270997945)
                    ·
                      rfl

theorem cell23_6035372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 9].length) (baseStart_6035372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6035372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6035372 prefixEnd_6035372 := by exact prefixLift 6035372
  have htrace : WordTrace (prefixWord ++ tailWord_6035372) baseStart_6035372 baseEnd_6035372 := by
    simpa [prefixWord, tailWord_6035372, baseEnd_6035372] using wordTrace_append hprefix tailTrace_6035372
  have hstable : (prefixWord ++ tailWord_6035372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6035372).length < 2 ^ (prefixWord ++ tailWord_6035372).sum := by decide
  have hdescent : baseEnd_6035372 < baseStart_6035372 := by decide
  rcases family_descends (prefixWord ++ tailWord_6035372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6035389 : List Nat := [1, 4, 1, 2, 3, 1, 1, 1, 2, 7]
def baseStart_6035389 : Nat := 118140960795 + 6035389 * 2 ^ 59
def prefixEnd_6035389 : Nat := 4983230072969 + 3 ^ 40 * 6035389 * 2
def baseEnd_6035389 : Nat := 1033018497952864082160419

theorem tailTrace_6035389 : CollatzResearch.WordTrace tailWord_6035389 prefixEnd_6035389 1033018497952864082160419 := by
  unfold tailWord_6035389
  simp only [CollatzResearch.WordTrace]
  refine ⟨220128721131823890223125221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146752480754549260148750147 220128721131823890223125221)
  ·
    refine ⟨41274135212216979416835979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 220128721131823890223125221 41274135212216979416835979)
    ·
      refine ⟨61911202818325469125253969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41274135212216979416835979 61911202818325469125253969)
      ·
        refine ⟨46433402113744101843940477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61911202818325469125253969 46433402113744101843940477)
        ·
          refine ⟨17412525792654038191477679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46433402113744101843940477 17412525792654038191477679)
          ·
            refine ⟨26118788688981057287216519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17412525792654038191477679 26118788688981057287216519)
            ·
              refine ⟨39178183033471585930824779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26118788688981057287216519 39178183033471585930824779)
              ·
                refine ⟨58767274550207378896237169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39178183033471585930824779 58767274550207378896237169)
                ·
                  refine ⟨44075455912655534172177877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 58767274550207378896237169 44075455912655534172177877)
                  ·
                    refine ⟨1033018497952864082160419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 44075455912655534172177877 1033018497952864082160419)
                    ·
                      rfl

theorem cell23_6035389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 1, 2, 7].length) (baseStart_6035389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6035389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6035389 prefixEnd_6035389 := by exact prefixLift 6035389
  have htrace : WordTrace (prefixWord ++ tailWord_6035389) baseStart_6035389 baseEnd_6035389 := by
    simpa [prefixWord, tailWord_6035389, baseEnd_6035389] using wordTrace_append hprefix tailTrace_6035389
  have hstable : (prefixWord ++ tailWord_6035389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6035389).length < 2 ^ (prefixWord ++ tailWord_6035389).sum := by decide
  have hdescent : baseEnd_6035389 < baseStart_6035389 := by decide
  rcases family_descends (prefixWord ++ tailWord_6035389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6035413 : List Nat := [1, 3, 2, 3, 2, 1, 2, 1, 3, 3, 2]
def baseStart_6035413 : Nat := 118140960795 + 6035413 * 2 ^ 59
def prefixEnd_6035413 : Nat := 4983230072969 + 3 ^ 40 * 6035413 * 2
def baseEnd_6035413 : Nat := 3099067817394300152581147

theorem tailTrace_6035413 : CollatzResearch.WordTrace tailWord_6035413 prefixEnd_6035413 3099067817394300152581147 := by
  unfold tailWord_6035413
  simp only [CollatzResearch.WordTrace]
  refine ⟨220129596483736942321998893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146753064322491294881332595 220129596483736942321998893)
  ·
    refine ⟨82548598681401353370749585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 220129596483736942321998893 82548598681401353370749585)
    ·
      refine ⟨61911449011051015028062189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82548598681401353370749585 61911449011051015028062189)
      ·
        refine ⟨23216793379144130635523321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61911449011051015028062189 23216793379144130635523321)
        ·
          refine ⟨17412595034358097976642491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23216793379144130635523321 17412595034358097976642491)
          ·
            refine ⟨26118892551537146964963737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17412595034358097976642491 26118892551537146964963737)
            ·
              refine ⟨19589169413652860223722803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26118892551537146964963737 19589169413652860223722803)
              ·
                refine ⟨29383754120479290335584205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19589169413652860223722803 29383754120479290335584205)
                ·
                  refine ⟨11018907795179733875844077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29383754120479290335584205 11018907795179733875844077)
                  ·
                    refine ⟨4132090423192400203441529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11018907795179733875844077 4132090423192400203441529)
                    ·
                      refine ⟨3099067817394300152581147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4132090423192400203441529 3099067817394300152581147)
                      ·
                        rfl

theorem cell23_6035413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 2, 1, 3, 3, 2].length) (baseStart_6035413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6035413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6035413 prefixEnd_6035413 := by exact prefixLift 6035413
  have htrace : WordTrace (prefixWord ++ tailWord_6035413) baseStart_6035413 baseEnd_6035413 := by
    simpa [prefixWord, tailWord_6035413, baseEnd_6035413] using wordTrace_append hprefix tailTrace_6035413
  have hstable : (prefixWord ++ tailWord_6035413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6035413).length < 2 ^ (prefixWord ++ tailWord_6035413).sum := by decide
  have hdescent : baseEnd_6035413 < baseStart_6035413 := by decide
  rcases family_descends (prefixWord ++ tailWord_6035413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6035439 : List Nat := [1, 1, 2, 1, 4, 2, 1, 1, 4, 2, 4]
def baseStart_6035439 : Nat := 118140960795 + 6035439 * 2 ^ 59
def prefixEnd_6035439 : Nat := 4983230072969 + 3 ^ 40 * 6035439 * 2
def baseEnd_6035439 : Nat := 3099081167891317050856027

theorem tailTrace_6035439 : CollatzResearch.WordTrace tailWord_6035439 prefixEnd_6035439 3099081167891317050856027 := by
  unfold tailWord_6035439
  simp only [CollatzResearch.WordTrace]
  refine ⟨220130544781642748762445371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146753696521095165841630247 220130544781642748762445371)
  ·
    refine ⟨330195817172464123143668057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220130544781642748762445371 330195817172464123143668057)
    ·
      refine ⟨247646862879348092357751043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 330195817172464123143668057 247646862879348092357751043)
      ·
        refine ⟨371470294319022138536626565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 247646862879348092357751043 371470294319022138536626565)
        ·
          refine ⟨69650680184816650975617481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 371470294319022138536626565 69650680184816650975617481)
          ·
            refine ⟨52238010138612488231713111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69650680184816650975617481 52238010138612488231713111)
            ·
              refine ⟨78357015207918732347569667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52238010138612488231713111 78357015207918732347569667)
              ·
                refine ⟨117535522811878098521354501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78357015207918732347569667 117535522811878098521354501)
                ·
                  refine ⟨22037910527227143472753969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 117535522811878098521354501 22037910527227143472753969)
                  ·
                    refine ⟨16528432895420357604565477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22037910527227143472753969 16528432895420357604565477)
                    ·
                      refine ⟨3099081167891317050856027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16528432895420357604565477 3099081167891317050856027)
                      ·
                        rfl

theorem cell23_6035439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 1, 4, 2, 4].length) (baseStart_6035439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6035439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6035439 prefixEnd_6035439 := by exact prefixLift 6035439
  have htrace : WordTrace (prefixWord ++ tailWord_6035439) baseStart_6035439 baseEnd_6035439 := by
    simpa [prefixWord, tailWord_6035439, baseEnd_6035439] using wordTrace_append hprefix tailTrace_6035439
  have hstable : (prefixWord ++ tailWord_6035439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6035439).length < 2 ^ (prefixWord ++ tailWord_6035439).sum := by decide
  have hdescent : baseEnd_6035439 < baseStart_6035439 := by decide
  rcases family_descends (prefixWord ++ tailWord_6035439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6035449 : List Nat := [1, 2, 1, 3, 1, 4, 1, 3, 7]
def baseStart_6035449 : Nat := 118140960795 + 6035449 * 2 ^ 59
def prefixEnd_6035449 : Nat := 4983230072969 + 3 ^ 40 * 6035449 * 2
def baseEnd_6035449 : Nat := 344342922521984667970109

theorem tailTrace_6035449 : CollatzResearch.WordTrace tailWord_6035449 prefixEnd_6035449 344342922521984667970109 := by
  unfold tailWord_6035449
  simp only [CollatzResearch.WordTrace]
  refine ⟨220130909511606520470309401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146753939674404346980206267 220130909511606520470309401)
  ·
    refine ⟨165098182133704890352732051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 220130909511606520470309401 165098182133704890352732051)
    ·
      refine ⟨247647273200557335529098077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165098182133704890352732051 247647273200557335529098077)
      ·
        refine ⟨92867727450209000823411779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 247647273200557335529098077 92867727450209000823411779)
        ·
          refine ⟨139301591175313501235117669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92867727450209000823411779 139301591175313501235117669)
          ·
            refine ⟨26119048345371281481584563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 139301591175313501235117669 26119048345371281481584563)
            ·
              refine ⟨39178572518056922222376845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26119048345371281481584563 39178572518056922222376845)
              ·
                refine ⟨14691964694271345833391317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39178572518056922222376845 14691964694271345833391317)
                ·
                  refine ⟨344342922521984667970109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14691964694271345833391317 344342922521984667970109)
                  ·
                    rfl

theorem cell23_6035449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 3, 7].length) (baseStart_6035449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6035449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6035449 prefixEnd_6035449 := by exact prefixLift 6035449
  have htrace : WordTrace (prefixWord ++ tailWord_6035449) baseStart_6035449 baseEnd_6035449 := by
    simpa [prefixWord, tailWord_6035449, baseEnd_6035449] using wordTrace_append hprefix tailTrace_6035449
  have hstable : (prefixWord ++ tailWord_6035449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6035449).length < 2 ^ (prefixWord ++ tailWord_6035449).sum := by decide
  have hdescent : baseEnd_6035449 < baseStart_6035449 := by decide
  rcases family_descends (prefixWord ++ tailWord_6035449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6035499 : List Nat := [1, 1, 1, 1, 2, 1, 4, 2, 3, 3, 4]
def baseStart_6035499 : Nat := 118140960795 + 6035499 * 2 ^ 59
def prefixEnd_6035499 : Nat := 4983230072969 + 3 ^ 40 * 6035499 * 2
def baseEnd_6035499 : Nat := 3099111976730586816105751

theorem tailTrace_6035499 : CollatzResearch.WordTrace tailWord_6035499 prefixEnd_6035499 3099111976730586816105751 := by
  unfold tailWord_6035499
  simp only [CollatzResearch.WordTrace]
  refine ⟨220132733161425379009629551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146755155440950252673086367 220132733161425379009629551)
  ·
    refine ⟨330199099742138068514444327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220132733161425379009629551 330199099742138068514444327)
    ·
      refine ⟨495298649613207102771666491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 330199099742138068514444327 495298649613207102771666491)
      ·
        refine ⟨742947974419810654157499737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 495298649613207102771666491 742947974419810654157499737)
        ·
          refine ⟨557210980814857990618124803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 742947974419810654157499737 557210980814857990618124803)
          ·
            refine ⟨835816471222286985927187205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 557210980814857990618124803 835816471222286985927187205)
            ·
              refine ⟨156715588354178809861347601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 835816471222286985927187205 156715588354178809861347601)
              ·
                refine ⟨117536691265634107396010701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 156715588354178809861347601 117536691265634107396010701)
                ·
                  refine ⟨44076259224612790273504013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 117536691265634107396010701 44076259224612790273504013)
                  ·
                    refine ⟨16528597209229796352564005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 44076259224612790273504013 16528597209229796352564005)
                    ·
                      refine ⟨3099111976730586816105751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16528597209229796352564005 3099111976730586816105751)
                      ·
                        rfl

theorem cell23_6035499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 2, 3, 3, 4].length) (baseStart_6035499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6035499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6035499 prefixEnd_6035499 := by exact prefixLift 6035499
  have htrace : WordTrace (prefixWord ++ tailWord_6035499) baseStart_6035499 baseEnd_6035499 := by
    simpa [prefixWord, tailWord_6035499, baseEnd_6035499] using wordTrace_append hprefix tailTrace_6035499
  have hstable : (prefixWord ++ tailWord_6035499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6035499).length < 2 ^ (prefixWord ++ tailWord_6035499).sum := by decide
  have hdescent : baseEnd_6035499 < baseStart_6035499 := by decide
  rcases family_descends (prefixWord ++ tailWord_6035499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6035506 : List Nat := [3, 2, 1, 1, 2, 4, 1, 1, 1, 2, 5]
def baseStart_6035506 : Nat := 118140960795 + 6035506 * 2 ^ 59
def prefixEnd_6035506 : Nat := 4983230072969 + 3 ^ 40 * 6035506 * 2
def baseEnd_6035506 : Nat := 3099115571095168288718219

theorem tailTrace_6035506 : CollatzResearch.WordTrace tailWord_6035506 prefixEnd_6035506 3099115571095168288718219 := by
  unfold tailWord_6035506
  simp only [CollatzResearch.WordTrace]
  refine ⟨55033247118100004801283593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146755325648266679470089581 55033247118100004801283593)
  ·
    refine ⟨41274935338575003600962695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55033247118100004801283593 41274935338575003600962695)
    ·
      refine ⟨61912403007862505401444043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41274935338575003600962695 61912403007862505401444043)
      ·
        refine ⟨92868604511793758102166065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61912403007862505401444043 92868604511793758102166065)
        ·
          refine ⟨69651453383845318576624549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92868604511793758102166065 69651453383845318576624549)
          ·
            refine ⟨13059647509470997233117103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 69651453383845318576624549 13059647509470997233117103)
            ·
              refine ⟨19589471264206495849675655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13059647509470997233117103 19589471264206495849675655)
              ·
                refine ⟨29384206896309743774513483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19589471264206495849675655 29384206896309743774513483)
                ·
                  refine ⟨44076310344464615661770225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29384206896309743774513483 44076310344464615661770225)
                  ·
                    refine ⟨33057232758348461746327669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 44076310344464615661770225 33057232758348461746327669)
                    ·
                      refine ⟨3099115571095168288718219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33057232758348461746327669 3099115571095168288718219)
                      ·
                        rfl

theorem cell23_6035506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 1, 1, 1, 2, 5].length) (baseStart_6035506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6035506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6035506 prefixEnd_6035506 := by exact prefixLift 6035506
  have htrace : WordTrace (prefixWord ++ tailWord_6035506) baseStart_6035506 baseEnd_6035506 := by
    simpa [prefixWord, tailWord_6035506, baseEnd_6035506] using wordTrace_append hprefix tailTrace_6035506
  have hstable : (prefixWord ++ tailWord_6035506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6035506).length < 2 ^ (prefixWord ++ tailWord_6035506).sum := by decide
  have hdescent : baseEnd_6035506 < baseStart_6035506 := by decide
  rcases family_descends (prefixWord ++ tailWord_6035506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6035516 : List Nat := [2, 2, 2, 2, 2, 1, 1, 2, 4, 1, 4]
def baseStart_6035516 : Nat := 118140960795 + 6035516 * 2 ^ 59
def prefixEnd_6035516 : Nat := 4983230072969 + 3 ^ 40 * 6035516 * 2
def baseEnd_6035516 : Nat := 3099120705901713249593173

theorem tailTrace_6035516 : CollatzResearch.WordTrace tailWord_6035516 prefixEnd_6035516 3099120705901713249593173 := by
  unfold tailWord_6035516
  simp only [CollatzResearch.WordTrace]
  refine ⟨110066676601181895456499201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146755568801575860608665601 110066676601181895456499201)
  ·
    refine ⟨82550007450886421592374401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110066676601181895456499201 82550007450886421592374401)
    ·
      refine ⟨61912505588164816194280801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82550007450886421592374401 61912505588164816194280801)
      ·
        refine ⟨46434379191123612145710601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61912505588164816194280801 46434379191123612145710601)
        ·
          refine ⟨34825784393342709109282951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46434379191123612145710601 34825784393342709109282951)
          ·
            refine ⟨52238676590014063663924427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34825784393342709109282951 52238676590014063663924427)
            ·
              refine ⟨78358014885021095495886641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52238676590014063663924427 78358014885021095495886641)
              ·
                refine ⟨58768511163765821621914981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 78358014885021095495886641 58768511163765821621914981)
                ·
                  refine ⟨11019095843206091554109059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 58768511163765821621914981 11019095843206091554109059)
                  ·
                    refine ⟨16528643764809137331163589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11019095843206091554109059 16528643764809137331163589)
                    ·
                      refine ⟨3099120705901713249593173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16528643764809137331163589 3099120705901713249593173)
                      ·
                        rfl

theorem cell23_6035516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 2, 4, 1, 4].length) (baseStart_6035516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6035516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6035516 prefixEnd_6035516 := by exact prefixLift 6035516
  have htrace : WordTrace (prefixWord ++ tailWord_6035516) baseStart_6035516 baseEnd_6035516 := by
    simpa [prefixWord, tailWord_6035516, baseEnd_6035516] using wordTrace_append hprefix tailTrace_6035516
  have hstable : (prefixWord ++ tailWord_6035516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6035516).length < 2 ^ (prefixWord ++ tailWord_6035516).sum := by decide
  have hdescent : baseEnd_6035516 < baseStart_6035516 := by decide
  rcases family_descends (prefixWord ++ tailWord_6035516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6035556 : List Nat := [2, 3, 1, 1, 2, 1, 3, 4, 6]
def baseStart_6035556 : Nat := 118140960795 + 6035556 * 2 ^ 59
def prefixEnd_6035556 : Nat := 4983230072969 + 3 ^ 40 * 6035556 * 2
def baseEnd_6035556 : Nat := 344349027236432565899221

theorem tailTrace_6035556 : CollatzResearch.WordTrace tailWord_6035556 prefixEnd_6035556 344349027236432565899221 := by
  unfold tailWord_6035556
  simp only [CollatzResearch.WordTrace]
  refine ⟨110067406061109438872227261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146756541414812585162969681 110067406061109438872227261)
  ·
    refine ⟨41275277272916039577085223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110067406061109438872227261 41275277272916039577085223)
    ·
      refine ⟨61912915909374059365627835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41275277272916039577085223 61912915909374059365627835)
      ·
        refine ⟨92869373864061089048441753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61912915909374059365627835 92869373864061089048441753)
        ·
          refine ⟨69652030398045816786331315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92869373864061089048441753 69652030398045816786331315)
          ·
            refine ⟨104478045597068725179496973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69652030398045816786331315 104478045597068725179496973)
            ·
              refine ⟨39179267098900771942311365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 104478045597068725179496973 39179267098900771942311365)
              ·
                refine ⟨7346112581043894739183381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39179267098900771942311365 7346112581043894739183381)
                ·
                  refine ⟨344349027236432565899221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7346112581043894739183381 344349027236432565899221)
                  ·
                    rfl

theorem cell23_6035556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 4, 6].length) (baseStart_6035556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6035556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6035556 prefixEnd_6035556 := by exact prefixLift 6035556
  have htrace : WordTrace (prefixWord ++ tailWord_6035556) baseStart_6035556 baseEnd_6035556 := by
    simpa [prefixWord, tailWord_6035556, baseEnd_6035556] using wordTrace_append hprefix tailTrace_6035556
  have hstable : (prefixWord ++ tailWord_6035556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6035556).length < 2 ^ (prefixWord ++ tailWord_6035556).sum := by decide
  have hdescent : baseEnd_6035556 < baseStart_6035556 := by decide
  rcases family_descends (prefixWord ++ tailWord_6035556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6035593 : List Nat := [1, 2, 1, 1, 4, 2, 3, 1, 1, 5, 2]
def baseStart_6035593 : Nat := 118140960795 + 6035593 * 2 ^ 59
def prefixEnd_6035593 : Nat := 4983230072969 + 3 ^ 40 * 6035593 * 2
def baseEnd_6035593 : Nat := 3099160243912109448330319

theorem tailTrace_6035593 : CollatzResearch.WordTrace tailWord_6035593 prefixEnd_6035593 3099160243912109448330319 := by
  unfold tailWord_6035593
  simp only [CollatzResearch.WordTrace]
  refine ⟨220136161623084833063551433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146757441082056555375700955 220136161623084833063551433)
  ·
    refine ⟨165102121217313624797663575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 220136161623084833063551433 165102121217313624797663575)
    ·
      refine ⟨247653181825970437196495363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165102121217313624797663575 247653181825970437196495363)
      ·
        refine ⟨371479772738955655794743045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 247653181825970437196495363 371479772738955655794743045)
        ·
          refine ⟨69652457388554185461514321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 371479772738955655794743045 69652457388554185461514321)
          ·
            refine ⟨52239343041415639096135741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69652457388554185461514321 52239343041415639096135741)
            ·
              refine ⟨19589753640530864661050903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52239343041415639096135741 19589753640530864661050903)
              ·
                refine ⟨29384630460796296991576355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19589753640530864661050903 29384630460796296991576355)
                ·
                  refine ⟨44076945691194445487364533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29384630460796296991576355 44076945691194445487364533)
                  ·
                    refine ⟨4132213658549479264440425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 44076945691194445487364533 4132213658549479264440425)
                    ·
                      refine ⟨3099160243912109448330319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4132213658549479264440425 3099160243912109448330319)
                      ·
                        rfl

theorem cell23_6035593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 3, 1, 1, 5, 2].length) (baseStart_6035593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6035593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6035593 prefixEnd_6035593 := by exact prefixLift 6035593
  have htrace : WordTrace (prefixWord ++ tailWord_6035593) baseStart_6035593 baseEnd_6035593 := by
    simpa [prefixWord, tailWord_6035593, baseEnd_6035593] using wordTrace_append hprefix tailTrace_6035593
  have hstable : (prefixWord ++ tailWord_6035593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6035593).length < 2 ^ (prefixWord ++ tailWord_6035593).sum := by decide
  have hdescent : baseEnd_6035593 < baseStart_6035593 := by decide
  rcases family_descends (prefixWord ++ tailWord_6035593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6035617 : List Nat := [1, 2, 3, 3, 1, 2, 2, 4, 1, 1, 3]
def baseStart_6035617 : Nat := 118140960795 + 6035617 * 2 ^ 59
def prefixEnd_6035617 : Nat := 4983230072969 + 3 ^ 40 * 6035617 * 2
def baseEnd_6035617 : Nat := 3099172567447817354430209

theorem tailTrace_6035617 : CollatzResearch.WordTrace tailWord_6035617 prefixEnd_6035617 3099172567447817354430209 := by
  unfold tailWord_6035617
  simp only [CollatzResearch.WordTrace]
  refine ⟨220137036974997885162425105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146758024649998590108283403 220137036974997885162425105)
  ·
    refine ⟨165102777731248413871818829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 220137036974997885162425105 165102777731248413871818829)
    ·
      refine ⟨61913541649218155201932061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 165102777731248413871818829 61913541649218155201932061)
      ·
        refine ⟨23217578118456808200724523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61913541649218155201932061 23217578118456808200724523)
        ·
          refine ⟨34826367177685212301086785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23217578118456808200724523 34826367177685212301086785)
          ·
            refine ⟨26119775383263909225815089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34826367177685212301086785 26119775383263909225815089)
            ·
              refine ⟨19589831537447931919361317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26119775383263909225815089 19589831537447931919361317)
              ·
                refine ⟨3673093413271487234880247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19589831537447931919361317 3673093413271487234880247)
                ·
                  refine ⟨5509640119907230852320371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3673093413271487234880247 5509640119907230852320371)
                  ·
                    refine ⟨8264460179860846278480557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5509640119907230852320371 8264460179860846278480557)
                    ·
                      refine ⟨3099172567447817354430209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8264460179860846278480557 3099172567447817354430209)
                      ·
                        rfl

theorem cell23_6035617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 2, 4, 1, 1, 3].length) (baseStart_6035617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6035617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6035617 prefixEnd_6035617 := by exact prefixLift 6035617
  have htrace : WordTrace (prefixWord ++ tailWord_6035617) baseStart_6035617 baseEnd_6035617 := by
    simpa [prefixWord, tailWord_6035617, baseEnd_6035617] using wordTrace_append hprefix tailTrace_6035617
  have hstable : (prefixWord ++ tailWord_6035617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6035617).length < 2 ^ (prefixWord ++ tailWord_6035617).sum := by decide
  have hdescent : baseEnd_6035617 < baseStart_6035617 := by decide
  rcases family_descends (prefixWord ++ tailWord_6035617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6035637 : List Nat := [1, 3, 3, 4, 1, 1, 2, 2, 1, 5]
def baseStart_6035637 : Nat := 118140960795 + 6035637 * 2 ^ 59
def prefixEnd_6035637 : Nat := 4983230072969 + 3 ^ 40 * 6035637 * 2
def baseEnd_6035637 : Nat := 1033060945686969092060039

theorem tailTrace_6035637 : CollatzResearch.WordTrace tailWord_6035637 prefixEnd_6035637 1033060945686969092060039 := by
  unfold tailWord_6035637
  simp only [CollatzResearch.WordTrace]
  refine ⟨220137766434925428578153165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146758510956616952385435443 220137766434925428578153165)
  ·
    refine ⟨82551662413097035716807437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 220137766434925428578153165 82551662413097035716807437)
    ·
      refine ⟨30956873404911388393802789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82551662413097035716807437 30956873404911388393802789)
      ·
        refine ⟨5804413763420885323838023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30956873404911388393802789 5804413763420885323838023)
        ·
          refine ⟨8706620645131327985757035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5804413763420885323838023 8706620645131327985757035)
          ·
            refine ⟨13059930967696991978635553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8706620645131327985757035 13059930967696991978635553)
            ·
              refine ⟨9794948225772743983976665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13059930967696991978635553 9794948225772743983976665)
              ·
                refine ⟨7346211169329557987982499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9794948225772743983976665 7346211169329557987982499)
                ·
                  refine ⟨11019316753994336981973749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7346211169329557987982499 11019316753994336981973749)
                  ·
                    refine ⟨1033060945686969092060039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11019316753994336981973749 1033060945686969092060039)
                    ·
                      rfl

theorem cell23_6035637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 2, 2, 1, 5].length) (baseStart_6035637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6035637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6035637 prefixEnd_6035637 := by exact prefixLift 6035637
  have htrace : WordTrace (prefixWord ++ tailWord_6035637) baseStart_6035637 baseEnd_6035637 := by
    simpa [prefixWord, tailWord_6035637, baseEnd_6035637] using wordTrace_append hprefix tailTrace_6035637
  have hstable : (prefixWord ++ tailWord_6035637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6035637).length < 2 ^ (prefixWord ++ tailWord_6035637).sum := by decide
  have hdescent : baseEnd_6035637 < baseStart_6035637 := by decide
  rcases family_descends (prefixWord ++ tailWord_6035637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6035640 : List Nat := [2, 1, 2, 1, 2, 1, 3, 4, 3, 2, 2]
def baseStart_6035640 : Nat := 118140960795 + 6035640 * 2 ^ 59
def prefixEnd_6035640 : Nat := 4983230072969 + 3 ^ 40 * 6035640 * 2
def baseEnd_6035640 : Nat := 3099184377502870764442603

theorem tailTrace_6035640 : CollatzResearch.WordTrace tailWord_6035640 prefixEnd_6035640 3099184377502870764442603 := by
  unfold tailWord_6035640
  simp only [CollatzResearch.WordTrace]
  refine ⟨110068937926957280045256187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146758583902609706727008249 110068937926957280045256187)
  ·
    refine ⟨165103406890435920067884281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110068937926957280045256187 165103406890435920067884281)
    ·
      refine ⟨123827555167826940050913211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 165103406890435920067884281 123827555167826940050913211)
      ·
        refine ⟨185741332751740410076369817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123827555167826940050913211 185741332751740410076369817)
        ·
          refine ⟨139305999563805307557277363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 185741332751740410076369817 139305999563805307557277363)
          ·
            refine ⟨208958999345707961335916045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139305999563805307557277363 208958999345707961335916045)
            ·
              refine ⟨78359624754640485500968517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 208958999345707961335916045 78359624754640485500968517)
              ·
                refine ⟨14692429641495091031431597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 78359624754640485500968517 14692429641495091031431597)
                ·
                  refine ⟨5509661115560659136786849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14692429641495091031431597 5509661115560659136786849)
                  ·
                    refine ⟨4132245836670494352590137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5509661115560659136786849 4132245836670494352590137)
                    ·
                      refine ⟨3099184377502870764442603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4132245836670494352590137 3099184377502870764442603)
                      ·
                        rfl

theorem cell23_6035640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 4, 3, 2, 2].length) (baseStart_6035640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6035640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6035640 prefixEnd_6035640 := by exact prefixLift 6035640
  have htrace : WordTrace (prefixWord ++ tailWord_6035640) baseStart_6035640 baseEnd_6035640 := by
    simpa [prefixWord, tailWord_6035640, baseEnd_6035640] using wordTrace_append hprefix tailTrace_6035640
  have hstable : (prefixWord ++ tailWord_6035640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6035640).length < 2 ^ (prefixWord ++ tailWord_6035640).sum := by decide
  have hdescent : baseEnd_6035640 < baseStart_6035640 := by decide
  rcases family_descends (prefixWord ++ tailWord_6035640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6035657 : List Nat := [1, 2, 1, 1, 2, 1, 1, 9, 1, 2, 2]
def baseStart_6035657 : Nat := 118140960795 + 6035657 * 2 ^ 59
def prefixEnd_6035657 : Nat := 4983230072969 + 3 ^ 40 * 6035657 * 2
def baseEnd_6035657 : Nat := 3099193106673997197930025

theorem tailTrace_6035657 : CollatzResearch.WordTrace tailWord_6035657 prefixEnd_6035657 3099193106673997197930025 := by
  unfold tailWord_6035657
  simp only [CollatzResearch.WordTrace]
  refine ⟨220138495894852971993881225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146758997263235314662587483 220138495894852971993881225)
  ·
    refine ⟨165103871921139728995410919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 220138495894852971993881225 165103871921139728995410919)
    ·
      refine ⟨247655807881709593493116379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165103871921139728995410919 247655807881709593493116379)
      ·
        refine ⟨371483711822564390239674569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 247655807881709593493116379 371483711822564390239674569)
        ·
          refine ⟨278612783866923292679755927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 371483711822564390239674569 278612783866923292679755927)
          ·
            refine ⟨417919175800384939019633891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 278612783866923292679755927 417919175800384939019633891)
            ·
              refine ⟨626878763700577408529450837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 417919175800384939019633891 626878763700577408529450837)
              ·
                refine ⟨3673117756058070753102251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 626878763700577408529450837 3673117756058070753102251)
                ·
                  refine ⟨5509676634087106129653377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3673117756058070753102251 5509676634087106129653377)
                  ·
                    refine ⟨4132257475565329597240033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5509676634087106129653377 4132257475565329597240033)
                    ·
                      refine ⟨3099193106673997197930025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4132257475565329597240033 3099193106673997197930025)
                      ·
                        rfl

theorem cell23_6035657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 9, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 9, 1, 2, 2].length) (baseStart_6035657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6035657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6035657 prefixEnd_6035657 := by exact prefixLift 6035657
  have htrace : WordTrace (prefixWord ++ tailWord_6035657) baseStart_6035657 baseEnd_6035657 := by
    simpa [prefixWord, tailWord_6035657, baseEnd_6035657] using wordTrace_append hprefix tailTrace_6035657
  have hstable : (prefixWord ++ tailWord_6035657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6035657).length < 2 ^ (prefixWord ++ tailWord_6035657).sum := by decide
  have hdescent : baseEnd_6035657 < baseStart_6035657 := by decide
  rcases family_descends (prefixWord ++ tailWord_6035657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6035670 : List Nat := [5, 2, 1, 2, 1, 1, 1, 2, 1, 1, 6]
def baseStart_6035670 : Nat := 118140960795 + 6035670 * 2 ^ 59
def prefixEnd_6035670 : Nat := 4983230072969 + 3 ^ 40 * 6035670 * 2
def baseEnd_6035670 : Nat := 3099199781922505647067465

theorem tailTrace_6035670 : CollatzResearch.WordTrace tailWord_6035670 prefixEnd_6035670 3099199781922505647067465 := by
  unfold tailWord_6035670
  simp only [CollatzResearch.WordTrace]
  refine ⟨13758685627737867200881529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 146759313362537250142736309 13758685627737867200881529)
  ·
    refine ⟨10319014220803400400661147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13758685627737867200881529 10319014220803400400661147)
    ·
      refine ⟨15478521331205100600991721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10319014220803400400661147 15478521331205100600991721)
      ·
        refine ⟨11608890998403825450743791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15478521331205100600991721 11608890998403825450743791)
        ·
          refine ⟨17413336497605738176115687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11608890998403825450743791 17413336497605738176115687)
          ·
            refine ⟨26120004746408607264173531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17413336497605738176115687 26120004746408607264173531)
            ·
              refine ⟨39180007119612910896260297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26120004746408607264173531 39180007119612910896260297)
              ·
                refine ⟨29385005339709683172195223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39180007119612910896260297 29385005339709683172195223)
                ·
                  refine ⟨44077508009564524758292835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29385005339709683172195223 44077508009564524758292835)
                  ·
                    refine ⟨66116262014346787137439253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 44077508009564524758292835 66116262014346787137439253)
                    ·
                      refine ⟨3099199781922505647067465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 66116262014346787137439253 3099199781922505647067465)
                      ·
                        rfl

theorem cell23_6035670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 2, 1, 1, 6].length) (baseStart_6035670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6035670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6035670 prefixEnd_6035670 := by exact prefixLift 6035670
  have htrace : WordTrace (prefixWord ++ tailWord_6035670) baseStart_6035670 baseEnd_6035670 := by
    simpa [prefixWord, tailWord_6035670, baseEnd_6035670] using wordTrace_append hprefix tailTrace_6035670
  have hstable : (prefixWord ++ tailWord_6035670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6035670).length < 2 ^ (prefixWord ++ tailWord_6035670).sum := by decide
  have hdescent : baseEnd_6035670 < baseStart_6035670 := by decide
  rcases family_descends (prefixWord ++ tailWord_6035670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6035733 : List Nat := [1, 3, 2, 1, 2, 1, 3, 1, 2, 4, 3]
def baseStart_6035733 : Nat := 118140960795 + 6035733 * 2 ^ 59
def prefixEnd_6035733 : Nat := 4983230072969 + 3 ^ 40 * 6035733 * 2
def baseEnd_6035733 : Nat := 3099232131203738900579675

theorem tailTrace_6035733 : CollatzResearch.WordTrace tailWord_6035733 prefixEnd_6035733 3099232131203738900579675 := by
  unfold tailWord_6035733
  simp only [CollatzResearch.WordTrace]
  refine ⟨220141267842577636973647853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146760845228385091315765235 220141267842577636973647853)
  ·
    refine ⟨82552975440966613865117945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 220141267842577636973647853 82552975440966613865117945)
    ·
      refine ⟨61914731580724960398838459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82552975440966613865117945 61914731580724960398838459)
      ·
        refine ⟨92872097371087440598257689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61914731580724960398838459 92872097371087440598257689)
        ·
          refine ⟨69654073028315580448693267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92872097371087440598257689 69654073028315580448693267)
          ·
            refine ⟨104481109542473370673039901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69654073028315580448693267 104481109542473370673039901)
            ·
              refine ⟨39180416078427514002389963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 104481109542473370673039901 39180416078427514002389963)
              ·
                refine ⟨58770624117641271003584945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39180416078427514002389963 58770624117641271003584945)
                ·
                  refine ⟨44077968088230953252688709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 58770624117641271003584945 44077968088230953252688709)
                  ·
                    refine ⟨8264619016543303734879133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 44077968088230953252688709 8264619016543303734879133)
                    ·
                      refine ⟨3099232131203738900579675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8264619016543303734879133 3099232131203738900579675)
                      ·
                        rfl

theorem cell23_6035733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 1, 2, 4, 3].length) (baseStart_6035733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6035733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6035733 prefixEnd_6035733 := by exact prefixLift 6035733
  have htrace : WordTrace (prefixWord ++ tailWord_6035733) baseStart_6035733 baseEnd_6035733 := by
    simpa [prefixWord, tailWord_6035733, baseEnd_6035733] using wordTrace_append hprefix tailTrace_6035733
  have hstable : (prefixWord ++ tailWord_6035733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6035733).length < 2 ^ (prefixWord ++ tailWord_6035733).sum := by decide
  have hdescent : baseEnd_6035733 < baseStart_6035733 := by decide
  rcases family_descends (prefixWord ++ tailWord_6035733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6035743 : List Nat := [1, 1, 2, 4, 3, 1, 1, 1, 1, 4, 4]
def baseStart_6035743 : Nat := 118140960795 + 6035743 * 2 ^ 59
def prefixEnd_6035743 : Nat := 4983230072969 + 3 ^ 40 * 6035743 * 2
def baseEnd_6035743 : Nat := 3099237266010283861454629

theorem tailTrace_6035743 : CollatzResearch.WordTrace tailWord_6035743 prefixEnd_6035743 3099237266010283861454629 := by
  unfold tailWord_6035743
  simp only [CollatzResearch.WordTrace]
  refine ⟨220141632572541408681511883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146761088381694272454341255 220141632572541408681511883)
  ·
    refine ⟨330212448858812113022267825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220141632572541408681511883 330212448858812113022267825)
    ·
      refine ⟨247659336644109084766700869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 330212448858812113022267825 247659336644109084766700869)
      ·
        refine ⟨46436125620770453393756413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 247659336644109084766700869 46436125620770453393756413)
        ·
          refine ⟨17413547107788920022658655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46436125620770453393756413 17413547107788920022658655)
          ·
            refine ⟨26120320661683380033987983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17413547107788920022658655 26120320661683380033987983)
            ·
              refine ⟨39180480992525070050981975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26120320661683380033987983 39180480992525070050981975)
              ·
                refine ⟨58770721488787605076472963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39180480992525070050981975 58770721488787605076472963)
                ·
                  refine ⟨88156082233181407614709445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58770721488787605076472963 88156082233181407614709445)
                  ·
                    refine ⟨16529265418721513927758021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 88156082233181407614709445 16529265418721513927758021)
                    ·
                      refine ⟨3099237266010283861454629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16529265418721513927758021 3099237266010283861454629)
                      ·
                        rfl

theorem cell23_6035743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 1, 1, 4, 4].length) (baseStart_6035743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6035743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6035743 prefixEnd_6035743 := by exact prefixLift 6035743
  have htrace : WordTrace (prefixWord ++ tailWord_6035743) baseStart_6035743 baseEnd_6035743 := by
    simpa [prefixWord, tailWord_6035743, baseEnd_6035743] using wordTrace_append hprefix tailTrace_6035743
  have hstable : (prefixWord ++ tailWord_6035743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6035743).length < 2 ^ (prefixWord ++ tailWord_6035743).sum := by decide
  have hdescent : baseEnd_6035743 < baseStart_6035743 := by decide
  rcases family_descends (prefixWord ++ tailWord_6035743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6035747 : List Nat := [1, 1, 1, 4, 2, 2, 1, 5, 2, 2, 2]
def baseStart_6035747 : Nat := 118140960795 + 6035747 * 2 ^ 59
def prefixEnd_6035747 : Nat := 4983230072969 + 3 ^ 40 * 6035747 * 2
def baseEnd_6035747 : Nat := 3099239319932901845804611

theorem tailTrace_6035747 : CollatzResearch.WordTrace tailWord_6035747 prefixEnd_6035747 3099239319932901845804611 := by
  unfold tailWord_6035747
  simp only [CollatzResearch.WordTrace]
  refine ⟨220141778464526917364657495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146761185643017944909771663 220141778464526917364657495)
  ·
    refine ⟨330212667696790376046986243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220141778464526917364657495 330212667696790376046986243)
    ·
      refine ⟨495319001545185564070479365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 330212667696790376046986243 495319001545185564070479365)
      ·
        refine ⟨92872312789722293263214881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 495319001545185564070479365 92872312789722293263214881)
        ·
          refine ⟨69654234592291719947411161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92872312789722293263214881 69654234592291719947411161)
          ·
            refine ⟨52240675944218789960558371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69654234592291719947411161 52240675944218789960558371)
            ·
              refine ⟨78361013916328184940837557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52240675944218789960558371 78361013916328184940837557)
              ·
                refine ⟨7346345054655767338203521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 78361013916328184940837557 7346345054655767338203521)
                ·
                  refine ⟨5509758790991825503652641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7346345054655767338203521 5509758790991825503652641)
                  ·
                    refine ⟨4132319093243869127739481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5509758790991825503652641 4132319093243869127739481)
                    ·
                      refine ⟨3099239319932901845804611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4132319093243869127739481 3099239319932901845804611)
                      ·
                        rfl

theorem cell23_6035747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 5, 2, 2, 2].length) (baseStart_6035747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6035747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6035747 prefixEnd_6035747 := by exact prefixLift 6035747
  have htrace : WordTrace (prefixWord ++ tailWord_6035747) baseStart_6035747 baseEnd_6035747 := by
    simpa [prefixWord, tailWord_6035747, baseEnd_6035747] using wordTrace_append hprefix tailTrace_6035747
  have hstable : (prefixWord ++ tailWord_6035747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6035747).length < 2 ^ (prefixWord ++ tailWord_6035747).sum := by decide
  have hdescent : baseEnd_6035747 < baseStart_6035747 := by decide
  rcases family_descends (prefixWord ++ tailWord_6035747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6035763 : List Nat := [1, 1, 1, 2, 5, 1, 1, 2, 1, 5, 3]
def baseStart_6035763 : Nat := 118140960795 + 6035763 * 2 ^ 59
def prefixEnd_6035763 : Nat := 4983230072969 + 3 ^ 40 * 6035763 * 2
def baseEnd_6035763 : Nat := 3099247535623373783204537

theorem tailTrace_6035763 : CollatzResearch.WordTrace tailWord_6035763 prefixEnd_6035763 3099247535623373783204537 := by
  unfold tailWord_6035763
  simp only [CollatzResearch.WordTrace]
  refine ⟨220142362032468952097239943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146761574688312634731493295 220142362032468952097239943)
  ·
    refine ⟨330213543048703428145859915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220142362032468952097239943 330213543048703428145859915)
    ·
      refine ⟨495320314573055142218789873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 330213543048703428145859915 495320314573055142218789873)
      ·
        refine ⟨371490235929791356664092405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 495320314573055142218789873 371490235929791356664092405)
        ·
          refine ⟨34827209618417939687258663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 371490235929791356664092405 34827209618417939687258663)
          ·
            refine ⟨52240814427626909530887995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34827209618417939687258663 52240814427626909530887995)
            ·
              refine ⟨78361221641440364296331993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52240814427626909530887995 78361221641440364296331993)
              ·
                refine ⟨58770916231080273222248995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 78361221641440364296331993 58770916231080273222248995)
                ·
                  refine ⟨88156374346620409833373493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58770916231080273222248995 88156374346620409833373493)
                  ·
                    refine ⟨8264660094995663421878765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 88156374346620409833373493 8264660094995663421878765)
                    ·
                      refine ⟨3099247535623373783204537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8264660094995663421878765 3099247535623373783204537)
                      ·
                        rfl

theorem cell23_6035763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 2, 1, 5, 3].length) (baseStart_6035763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6035763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6035763 prefixEnd_6035763 := by exact prefixLift 6035763
  have htrace : WordTrace (prefixWord ++ tailWord_6035763) baseStart_6035763 baseEnd_6035763 := by
    simpa [prefixWord, tailWord_6035763, baseEnd_6035763] using wordTrace_append hprefix tailTrace_6035763
  have hstable : (prefixWord ++ tailWord_6035763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6035763).length < 2 ^ (prefixWord ++ tailWord_6035763).sum := by decide
  have hdescent : baseEnd_6035763 < baseStart_6035763 := by decide
  rcases family_descends (prefixWord ++ tailWord_6035763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6035770 : List Nat := [3, 1, 1, 1, 4, 2, 1, 5, 5]
def baseStart_6035770 : Nat := 118140960795 + 6035770 * 2 ^ 59
def prefixEnd_6035770 : Nat := 4983230072969 + 3 ^ 40 * 6035770 * 2
def baseEnd_6035770 : Nat := 344361236665328361757445

theorem tailTrace_6035770 : CollatzResearch.WordTrace tailWord_6035770 prefixEnd_6035770 344361236665328361757445 := by
  unfold tailWord_6035770
  simp only [CollatzResearch.WordTrace]
  refine ⟨55035654335860898073186191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146761744895629061528496509 55035654335860898073186191)
  ·
    refine ⟨82553481503791347109779287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55035654335860898073186191 82553481503791347109779287)
    ·
      refine ⟨123830222255687020664668931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82553481503791347109779287 123830222255687020664668931)
      ·
        refine ⟨185745333383530530997003397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123830222255687020664668931 185745333383530530997003397)
        ·
          refine ⟨34827250009411974561938137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 185745333383530530997003397 34827250009411974561938137)
          ·
            refine ⟨26120437507058980921453603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34827250009411974561938137 26120437507058980921453603)
            ·
              refine ⟨39180656260588471382180405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26120437507058980921453603 39180656260588471382180405)
              ·
                refine ⟨3673186524430169192079413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 39180656260588471382180405 3673186524430169192079413)
                ·
                  refine ⟨344361236665328361757445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3673186524430169192079413 344361236665328361757445)
                  ·
                    rfl

theorem cell23_6035770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 5, 5].length) (baseStart_6035770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6035770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6035770 prefixEnd_6035770 := by exact prefixLift 6035770
  have htrace : WordTrace (prefixWord ++ tailWord_6035770) baseStart_6035770 baseEnd_6035770 := by
    simpa [prefixWord, tailWord_6035770, baseEnd_6035770] using wordTrace_append hprefix tailTrace_6035770
  have hstable : (prefixWord ++ tailWord_6035770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6035770).length < 2 ^ (prefixWord ++ tailWord_6035770).sum := by decide
  have hdescent : baseEnd_6035770 < baseStart_6035770 := by decide
  rcases family_descends (prefixWord ++ tailWord_6035770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6035783 : List Nat := [1, 1, 4, 1, 2, 2, 2, 1, 4, 5]
def baseStart_6035783 : Nat := 118140960795 + 6035783 * 2 ^ 59
def prefixEnd_6035783 : Nat := 4983230072969 + 3 ^ 40 * 6035783 * 2
def baseEnd_6035783 : Nat := 1033085935078821234984815

theorem tailTrace_6035783 : CollatzResearch.WordTrace tailWord_6035783 prefixEnd_6035783 1033085935078821234984815 := by
  unfold tailWord_6035783
  simp only [CollatzResearch.WordTrace]
  refine ⟨220143091492396495512968003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146762060994930997008645335 220143091492396495512968003)
  ·
    refine ⟨330214637238594743269452005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220143091492396495512968003 330214637238594743269452005)
    ·
      refine ⟨61915244482236514363022251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 330214637238594743269452005 61915244482236514363022251)
      ·
        refine ⟨92872866723354771544533377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61915244482236514363022251 92872866723354771544533377)
        ·
          refine ⟨69654650042516078658400033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92872866723354771544533377 69654650042516078658400033)
          ·
            refine ⟨52240987531887058993800025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69654650042516078658400033 52240987531887058993800025)
            ·
              refine ⟨39180740648915294245350019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52240987531887058993800025 39180740648915294245350019)
              ·
                refine ⟨58771110973372941368025029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39180740648915294245350019 58771110973372941368025029)
                ·
                  refine ⟨11019583307507426506504693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 58771110973372941368025029 11019583307507426506504693)
                  ·
                    refine ⟨1033085935078821234984815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11019583307507426506504693 1033085935078821234984815)
                    ·
                      rfl

theorem cell23_6035783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 1, 4, 5].length) (baseStart_6035783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6035783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6035783 prefixEnd_6035783 := by exact prefixLift 6035783
  have htrace : WordTrace (prefixWord ++ tailWord_6035783) baseStart_6035783 baseEnd_6035783 := by
    simpa [prefixWord, tailWord_6035783, baseEnd_6035783] using wordTrace_append hprefix tailTrace_6035783
  have hstable : (prefixWord ++ tailWord_6035783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6035783).length < 2 ^ (prefixWord ++ tailWord_6035783).sum := by decide
  have hdescent : baseEnd_6035783 < baseStart_6035783 := by decide
  rcases family_descends (prefixWord ++ tailWord_6035783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6035790 : List Nat := [4, 1, 1, 1, 1, 1, 2, 3, 2, 5, 2]
def baseStart_6035790 : Nat := 118140960795 + 6035790 * 2 ^ 59
def prefixEnd_6035790 : Nat := 4983230072969 + 3 ^ 40 * 6035790 * 2
def baseEnd_6035790 : Nat := 3099261399601045177566913

theorem tailTrace_6035790 : CollatzResearch.WordTrace tailWord_6035790 prefixEnd_6035790 3099261399601045177566913 := by
  unfold tailWord_6035790
  simp only [CollatzResearch.WordTrace]
  refine ⟨27517918350421391963559103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 146762231202247423805648549 27517918350421391963559103)
  ·
    refine ⟨41276877525632087945338655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27517918350421391963559103 41276877525632087945338655)
    ·
      refine ⟨61915316288448131918007983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41276877525632087945338655 61915316288448131918007983)
      ·
        refine ⟨92872974432672197877011975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61915316288448131918007983 92872974432672197877011975)
        ·
          refine ⟨139309461649008296815517963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92872974432672197877011975 139309461649008296815517963)
          ·
            refine ⟨208964192473512445223276945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139309461649008296815517963 208964192473512445223276945)
            ·
              refine ⟨156723144355134333917457709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 208964192473512445223276945 156723144355134333917457709)
              ·
                refine ⟨58771179133175375219046641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 156723144355134333917457709 58771179133175375219046641)
                ·
                  refine ⟨44078384349881531414284981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 58771179133175375219046641 44078384349881531414284981)
                  ·
                    refine ⟨4132348532801393570089217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 44078384349881531414284981 4132348532801393570089217)
                    ·
                      refine ⟨3099261399601045177566913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4132348532801393570089217 3099261399601045177566913)
                      ·
                        rfl

theorem cell23_6035790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 3, 2, 5, 2].length) (baseStart_6035790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6035790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6035790 prefixEnd_6035790 := by exact prefixLift 6035790
  have htrace : WordTrace (prefixWord ++ tailWord_6035790) baseStart_6035790 baseEnd_6035790 := by
    simpa [prefixWord, tailWord_6035790, baseEnd_6035790] using wordTrace_append hprefix tailTrace_6035790
  have hstable : (prefixWord ++ tailWord_6035790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6035790).length < 2 ^ (prefixWord ++ tailWord_6035790).sum := by decide
  have hdescent : baseEnd_6035790 < baseStart_6035790 := by decide
  rcases family_descends (prefixWord ++ tailWord_6035790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6035863 : List Nat := [1, 1, 3, 3, 1, 1, 2, 2, 1, 2, 6]
def baseStart_6035863 : Nat := 118140960795 + 6035863 * 2 ^ 59
def prefixEnd_6035863 : Nat := 4983230072969 + 3 ^ 40 * 6035863 * 2
def baseEnd_6035863 : Nat := 3099298883688823391954077

theorem tailTrace_6035863 : CollatzResearch.WordTrace tailWord_6035863 prefixEnd_6035863 3099298883688823391954077 := by
  unfold tailWord_6035863
  simp only [CollatzResearch.WordTrace]
  refine ⟨220146009332106669175880243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146764006221404446117253495 220146009332106669175880243)
  ·
    refine ⟨330219013998160003763820365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220146009332106669175880243 330219013998160003763820365)
    ·
      refine ⟨123832130249310001411432637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 330219013998160003763820365 123832130249310001411432637)
      ·
        refine ⟨46437048843491250529287239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 123832130249310001411432637 46437048843491250529287239)
        ·
          refine ⟨69655573265236875793930859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46437048843491250529287239 69655573265236875793930859)
          ·
            refine ⟨104483359897855313690896289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69655573265236875793930859 104483359897855313690896289)
            ·
              refine ⟨78362519923391485268172217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 104483359897855313690896289 78362519923391485268172217)
              ·
                refine ⟨58771889942543613951129163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 78362519923391485268172217 58771889942543613951129163)
                ·
                  refine ⟨88157834913815420926693745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58771889942543613951129163 88157834913815420926693745)
                  ·
                    refine ⟨66118376185361565695020309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 88157834913815420926693745 66118376185361565695020309)
                    ·
                      refine ⟨3099298883688823391954077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 66118376185361565695020309 3099298883688823391954077)
                      ·
                        rfl

theorem cell23_6035863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 2, 1, 2, 6].length) (baseStart_6035863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6035863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6035863 prefixEnd_6035863 := by exact prefixLift 6035863
  have htrace : WordTrace (prefixWord ++ tailWord_6035863) baseStart_6035863 baseEnd_6035863 := by
    simpa [prefixWord, tailWord_6035863, baseEnd_6035863] using wordTrace_append hprefix tailTrace_6035863
  have hstable : (prefixWord ++ tailWord_6035863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6035863).length < 2 ^ (prefixWord ++ tailWord_6035863).sum := by decide
  have hdescent : baseEnd_6035863 < baseStart_6035863 := by decide
  rcases family_descends (prefixWord ++ tailWord_6035863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6035923 : List Nat := [1, 1, 1, 2, 1, 1, 1, 1, 7, 1, 6]
def baseStart_6035923 : Nat := 118140960795 + 6035923 * 2 ^ 59
def prefixEnd_6035923 : Nat := 4983230072969 + 3 ^ 40 * 6035923 * 2
def baseEnd_6035923 : Nat := 3099329692528093157203801

theorem tailTrace_6035923 : CollatzResearch.WordTrace tailWord_6035923 prefixEnd_6035923 3099329692528093157203801 := by
  unfold tailWord_6035923
  simp only [CollatzResearch.WordTrace]
  refine ⟨220148197711889299423064423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146765465141259532948709615 220148197711889299423064423)
  ·
    refine ⟨330222296567833949134596635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220148197711889299423064423 330222296567833949134596635)
    ·
      refine ⟨495333444851750923701894953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 330222296567833949134596635 495333444851750923701894953)
      ·
        refine ⟨371500083638813192776421215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 495333444851750923701894953 371500083638813192776421215)
        ·
          refine ⟨557250125458219789164631823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 371500083638813192776421215 557250125458219789164631823)
          ·
            refine ⟨835875188187329683746947735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 557250125458219789164631823 835875188187329683746947735)
            ·
              refine ⟨1253812782280994525620421603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 835875188187329683746947735 1253812782280994525620421603)
              ·
                refine ⟨1880719173421491788430632405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1253812782280994525620421603 1880719173421491788430632405)
                ·
                  refine ⟨44079355627066213791342947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1880719173421491788430632405 44079355627066213791342947)
                  ·
                    refine ⟨66119033440599320687014421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 44079355627066213791342947 66119033440599320687014421)
                    ·
                      refine ⟨3099329692528093157203801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 66119033440599320687014421 3099329692528093157203801)
                      ·
                        rfl

theorem cell23_6035923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 7, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 7, 1, 6].length) (baseStart_6035923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6035923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6035923 prefixEnd_6035923 := by exact prefixLift 6035923
  have htrace : WordTrace (prefixWord ++ tailWord_6035923) baseStart_6035923 baseEnd_6035923 := by
    simpa [prefixWord, tailWord_6035923, baseEnd_6035923] using wordTrace_append hprefix tailTrace_6035923
  have hstable : (prefixWord ++ tailWord_6035923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6035923).length < 2 ^ (prefixWord ++ tailWord_6035923).sum := by decide
  have hdescent : baseEnd_6035923 < baseStart_6035923 := by decide
  rcases family_descends (prefixWord ++ tailWord_6035923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6035941 : List Nat := [1, 3, 1, 5, 2, 2, 2, 1, 1, 5]
def baseStart_6035941 : Nat := 118140960795 + 6035941 * 2 ^ 59
def prefixEnd_6035941 : Nat := 4983230072969 + 3 ^ 40 * 6035941 * 2
def baseEnd_6035941 : Nat := 1033112978393291362259573

theorem tailTrace_6035941 : CollatzResearch.WordTrace tailWord_6035941 prefixEnd_6035941 1033112978393291362259573 := by
  unfold tailWord_6035941
  simp only [CollatzResearch.WordTrace]
  refine ⟨220148854225824088497219677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146765902817216058998146451 220148854225824088497219677)
  ·
    refine ⟨82555820334684033186457379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 220148854225824088497219677 82555820334684033186457379)
    ·
      refine ⟨123833730502026049779686069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82555820334684033186457379 123833730502026049779686069)
      ·
        refine ⟨11609412234564942166845569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 123833730502026049779686069 11609412234564942166845569)
        ·
          refine ⟨8707059175923706625134177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11609412234564942166845569 8707059175923706625134177)
          ·
            refine ⟨6530294381942779968850633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8707059175923706625134177 6530294381942779968850633)
            ·
              refine ⟨4897720786457084976637975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6530294381942779968850633 4897720786457084976637975)
              ·
                refine ⟨7346581179685627464956963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4897720786457084976637975 7346581179685627464956963)
                ·
                  refine ⟨11019871769528441197435445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7346581179685627464956963 11019871769528441197435445)
                  ·
                    refine ⟨1033112978393291362259573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11019871769528441197435445 1033112978393291362259573)
                    ·
                      rfl

theorem cell23_6035941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 2, 2, 1, 1, 5].length) (baseStart_6035941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6035941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6035941 prefixEnd_6035941 := by exact prefixLift 6035941
  have htrace : WordTrace (prefixWord ++ tailWord_6035941) baseStart_6035941 baseEnd_6035941 := by
    simpa [prefixWord, tailWord_6035941, baseEnd_6035941] using wordTrace_append hprefix tailTrace_6035941
  have hstable : (prefixWord ++ tailWord_6035941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6035941).length < 2 ^ (prefixWord ++ tailWord_6035941).sum := by decide
  have hdescent : baseEnd_6035941 < baseStart_6035941 := by decide
  rcases family_descends (prefixWord ++ tailWord_6035941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6035944 : List Nat := [2, 1, 4, 1, 1, 3, 4, 1, 1, 1, 4]
def baseStart_6035944 : Nat := 118140960795 + 6035944 * 2 ^ 59
def prefixEnd_6035944 : Nat := 4983230072969 + 3 ^ 40 * 6035944 * 2
def baseEnd_6035944 : Nat := 3099340475621837575041205

theorem tailTrace_6035944 : CollatzResearch.WordTrace tailWord_6035944 prefixEnd_6035944 3099340475621837575041205 := by
  unfold tailWord_6035944
  simp only [CollatzResearch.WordTrace]
  refine ⟨110074481822406610004789443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146765975763208813339719257 110074481822406610004789443)
  ·
    refine ⟨165111722733609915007184165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110074481822406610004789443 165111722733609915007184165)
    ·
      refine ⟨30958448012551859063847031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 165111722733609915007184165 30958448012551859063847031)
      ·
        refine ⟨46437672018827788595770547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30958448012551859063847031 46437672018827788595770547)
        ·
          refine ⟨69656508028241682893655821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46437672018827788595770547 69656508028241682893655821)
          ·
            refine ⟨26121190510590631085120933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69656508028241682893655821 26121190510590631085120933)
            ·
              refine ⟨4897723220735743328460175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26121190510590631085120933 4897723220735743328460175)
              ·
                refine ⟨7346584831103614992690263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4897723220735743328460175 7346584831103614992690263)
                ·
                  refine ⟨11019877246655422489035395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7346584831103614992690263 11019877246655422489035395)
                  ·
                    refine ⟨16529815869983133733553093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11019877246655422489035395 16529815869983133733553093)
                    ·
                      refine ⟨3099340475621837575041205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16529815869983133733553093 3099340475621837575041205)
                      ·
                        rfl

theorem cell23_6035944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 4, 1, 1, 1, 4].length) (baseStart_6035944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6035944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6035944 prefixEnd_6035944 := by exact prefixLift 6035944
  have htrace : WordTrace (prefixWord ++ tailWord_6035944) baseStart_6035944 baseEnd_6035944 := by
    simpa [prefixWord, tailWord_6035944, baseEnd_6035944] using wordTrace_append hprefix tailTrace_6035944
  have hstable : (prefixWord ++ tailWord_6035944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6035944).length < 2 ^ (prefixWord ++ tailWord_6035944).sum := by decide
  have hdescent : baseEnd_6035944 < baseStart_6035944 := by decide
  rcases family_descends (prefixWord ++ tailWord_6035944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6035947 : List Nat := [1, 1, 1, 1, 2, 3, 5, 3, 1, 2, 3]
def baseStart_6035947 : Nat := 118140960795 + 6035947 * 2 ^ 59
def prefixEnd_6035947 : Nat := 4983230072969 + 3 ^ 40 * 6035947 * 2
def baseEnd_6035947 : Nat := 3099342016063801063303691

theorem tailTrace_6035947 : CollatzResearch.WordTrace tailWord_6035947 prefixEnd_6035947 3099342016063801063303691 := by
  unfold tailWord_6035947
  simp only [CollatzResearch.WordTrace]
  refine ⟨220149073063802351521938095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146766048709201567681292063 220149073063802351521938095)
  ·
    refine ⟨330223609595703527282907143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220149073063802351521938095 330223609595703527282907143)
    ·
      refine ⟨495335414393555290924360715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 330223609595703527282907143 495335414393555290924360715)
      ·
        refine ⟨743003121590332936386541073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 495335414393555290924360715 743003121590332936386541073)
        ·
          refine ⟨557252341192749702289905805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 743003121590332936386541073 557252341192749702289905805)
          ·
            refine ⟨208969627947281138358714677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 557252341192749702289905805 208969627947281138358714677)
            ·
              refine ⟨19590902620057606721129501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 208969627947281138358714677 19590902620057606721129501)
              ·
                refine ⟨7346588482521602520423563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19590902620057606721129501 7346588482521602520423563)
                ·
                  refine ⟨11019882723782403780635345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7346588482521602520423563 11019882723782403780635345)
                  ·
                    refine ⟨8264912042836802835476509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11019882723782403780635345 8264912042836802835476509)
                    ·
                      refine ⟨3099342016063801063303691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8264912042836802835476509 3099342016063801063303691)
                      ·
                        rfl

theorem cell23_6035947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 5, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 5, 3, 1, 2, 3].length) (baseStart_6035947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6035947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6035947 prefixEnd_6035947 := by exact prefixLift 6035947
  have htrace : WordTrace (prefixWord ++ tailWord_6035947) baseStart_6035947 baseEnd_6035947 := by
    simpa [prefixWord, tailWord_6035947, baseEnd_6035947] using wordTrace_append hprefix tailTrace_6035947
  have hstable : (prefixWord ++ tailWord_6035947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6035947).length < 2 ^ (prefixWord ++ tailWord_6035947).sum := by decide
  have hdescent : baseEnd_6035947 < baseStart_6035947 := by decide
  rcases family_descends (prefixWord ++ tailWord_6035947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6035950 : List Nat := [4, 1, 2, 1, 2, 3, 10]
def baseStart_6035950 : Nat := 118140960795 + 6035950 * 2 ^ 59
def prefixEnd_6035950 : Nat := 4983230072969 + 3 ^ 40 * 6035950 * 2
def baseEnd_6035950 : Nat := 38263500697602031500817

theorem tailTrace_6035950 : CollatzResearch.WordTrace tailWord_6035950 prefixEnd_6035950 38263500697602031500817 := by
  unfold tailWord_6035950
  simp only [CollatzResearch.WordTrace]
  refine ⟨27518647810348935379287163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 146766121655194322022864869 27518647810348935379287163)
  ·
    refine ⟨41277971715523403068930745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27518647810348935379287163 41277971715523403068930745)
    ·
      refine ⟨30958478786642552301698059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41277971715523403068930745 30958478786642552301698059)
      ·
        refine ⟨46437718179963828452547089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30958478786642552301698059 46437718179963828452547089)
        ·
          refine ⟨34828288634972871339410317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46437718179963828452547089 34828288634972871339410317)
          ·
            refine ⟨13060608238114826752278869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34828288634972871339410317 13060608238114826752278869)
            ·
              refine ⟨38263500697602031500817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 13060608238114826752278869 38263500697602031500817)
              ·
                rfl

theorem cell23_6035950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 10].length) (baseStart_6035950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6035950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6035950 prefixEnd_6035950 := by exact prefixLift 6035950
  have htrace : WordTrace (prefixWord ++ tailWord_6035950) baseStart_6035950 baseEnd_6035950 := by
    simpa [prefixWord, tailWord_6035950, baseEnd_6035950] using wordTrace_append hprefix tailTrace_6035950
  have hstable : (prefixWord ++ tailWord_6035950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6035950).length < 2 ^ (prefixWord ++ tailWord_6035950).sum := by decide
  have hdescent : baseEnd_6035950 < baseStart_6035950 := by decide
  rcases family_descends (prefixWord ++ tailWord_6035950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6035954 : List Nat := [3, 2, 1, 4, 2, 1, 1, 1, 4, 4]
def baseStart_6035954 : Nat := 118140960795 + 6035954 * 2 ^ 59
def prefixEnd_6035954 : Nat := 4983230072969 + 3 ^ 40 * 6035954 * 2
def baseEnd_6035954 : Nat := 1033115203476127511972053

theorem tailTrace_6035954 : CollatzResearch.WordTrace tailWord_6035954 prefixEnd_6035954 1033115203476127511972053 := by
  unfold tailWord_6035954
  simp only [CollatzResearch.WordTrace]
  refine ⟨55037332093694247929360729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146766218916517994478295277 55037332093694247929360729)
  ·
    refine ⟨41277999070270685947020547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55037332093694247929360729 41277999070270685947020547)
    ·
      refine ⟨61916998605406028920530821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41277999070270685947020547 61916998605406028920530821)
      ·
        refine ⟨11609437238513630422599529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 61916998605406028920530821 11609437238513630422599529)
        ·
          refine ⟨8707077928885222816949647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11609437238513630422599529 8707077928885222816949647)
          ·
            refine ⟨13060616893327834225424471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8707077928885222816949647 13060616893327834225424471)
            ·
              refine ⟨19590925339991751338136707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13060616893327834225424471 19590925339991751338136707)
              ·
                refine ⟨29386388009987627007205061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19590925339991751338136707 29386388009987627007205061)
                ·
                  refine ⟨5509947751872680063850949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29386388009987627007205061 5509947751872680063850949)
                  ·
                    refine ⟨1033115203476127511972053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5509947751872680063850949 1033115203476127511972053)
                    ·
                      rfl

theorem cell23_6035954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 1, 1, 4, 4].length) (baseStart_6035954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6035954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6035954 prefixEnd_6035954 := by exact prefixLift 6035954
  have htrace : WordTrace (prefixWord ++ tailWord_6035954) baseStart_6035954 baseEnd_6035954 := by
    simpa [prefixWord, tailWord_6035954, baseEnd_6035954] using wordTrace_append hprefix tailTrace_6035954
  have hstable : (prefixWord ++ tailWord_6035954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6035954).length < 2 ^ (prefixWord ++ tailWord_6035954).sum := by decide
  have hdescent : baseEnd_6035954 < baseStart_6035954 := by decide
  rcases family_descends (prefixWord ++ tailWord_6035954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6035961 : List Nat := [1, 2, 1, 3, 1, 2, 4, 4, 1, 2, 2]
def baseStart_6035961 : Nat := 118140960795 + 6035961 * 2 ^ 59
def prefixEnd_6035961 : Nat := 4983230072969 + 3 ^ 40 * 6035961 * 2
def baseEnd_6035961 : Nat := 3099349204792964008528627

theorem tailTrace_6035961 : CollatzResearch.WordTrace tailWord_6035961 prefixEnd_6035961 3099349204792964008528627 := by
  unfold tailWord_6035961
  simp only [CollatzResearch.WordTrace]
  refine ⟨220149583685751631912947737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146766389123834421275298491 220149583685751631912947737)
  ·
    refine ⟨165112187764313723934710803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 220149583685751631912947737 165112187764313723934710803)
    ·
      refine ⟨247668281646470585902066205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165112187764313723934710803 247668281646470585902066205)
      ·
        refine ⟨92875605617426469713274827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 247668281646470585902066205 92875605617426469713274827)
        ·
          refine ⟨139313408426139704569912241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92875605617426469713274827 139313408426139704569912241)
          ·
            refine ⟨104485056319604778427434181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 139313408426139704569912241 104485056319604778427434181)
            ·
              refine ⟨19590948059925895955143909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 104485056319604778427434181 19590948059925895955143909)
              ·
                refine ⟨3673302761236105491589483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19590948059925895955143909 3673302761236105491589483)
                ·
                  refine ⟨5509954141854158237384225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3673302761236105491589483 5509954141854158237384225)
                  ·
                    refine ⟨4132465606390618678038169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5509954141854158237384225 4132465606390618678038169)
                    ·
                      refine ⟨3099349204792964008528627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4132465606390618678038169 3099349204792964008528627)
                      ·
                        rfl

theorem cell23_6035961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 4, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 4, 4, 1, 2, 2].length) (baseStart_6035961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6035961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6035961 prefixEnd_6035961 := by exact prefixLift 6035961
  have htrace : WordTrace (prefixWord ++ tailWord_6035961) baseStart_6035961 baseEnd_6035961 := by
    simpa [prefixWord, tailWord_6035961, baseEnd_6035961] using wordTrace_append hprefix tailTrace_6035961
  have hstable : (prefixWord ++ tailWord_6035961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6035961).length < 2 ^ (prefixWord ++ tailWord_6035961).sum := by decide
  have hdescent : baseEnd_6035961 < baseStart_6035961 := by decide
  rcases family_descends (prefixWord ++ tailWord_6035961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6036028 : List Nat := [2, 2, 2, 2, 3, 3, 2, 1, 2, 1, 3]
def baseStart_6036028 : Nat := 118140960795 + 6036028 * 2 ^ 59
def prefixEnd_6036028 : Nat := 4983230072969 + 3 ^ 40 * 6036028 * 2
def baseEnd_6036028 : Nat := 3099383607996815246390819

theorem tailTrace_6036028 : CollatzResearch.WordTrace tailWord_6036028 prefixEnd_6036028 3099383607996815246390819 := by
  unfold tailWord_6036028
  simp only [CollatzResearch.WordTrace]
  refine ⟨110076013688254451177818369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146768018251005934903757825 110076013688254451177818369)
  ·
    refine ⟨82557010266190838383363777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110076013688254451177818369 82557010266190838383363777)
    ·
      refine ⟨61917757699643128787522833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82557010266190838383363777 61917757699643128787522833)
      ·
        refine ⟨46438318274732346590642125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61917757699643128787522833 46438318274732346590642125)
        ·
          refine ⟨17414369353024629971490797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46438318274732346590642125 17414369353024629971490797)
          ·
            refine ⟨6530388507384236239309049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17414369353024629971490797 6530388507384236239309049)
            ·
              refine ⟨4897791380538177179481787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6530388507384236239309049 4897791380538177179481787)
              ·
                refine ⟨7346687070807265769222681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4897791380538177179481787 7346687070807265769222681)
                ·
                  refine ⟨5510015303105449326917011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7346687070807265769222681 5510015303105449326917011)
                  ·
                    refine ⟨8265022954658173990375517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5510015303105449326917011 8265022954658173990375517)
                    ·
                      refine ⟨3099383607996815246390819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8265022954658173990375517 3099383607996815246390819)
                      ·
                        rfl

theorem cell23_6036028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 3, 2, 1, 2, 1, 3].length) (baseStart_6036028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6036028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6036028 prefixEnd_6036028 := by exact prefixLift 6036028
  have htrace : WordTrace (prefixWord ++ tailWord_6036028) baseStart_6036028 baseEnd_6036028 := by
    simpa [prefixWord, tailWord_6036028, baseEnd_6036028] using wordTrace_append hprefix tailTrace_6036028
  have hstable : (prefixWord ++ tailWord_6036028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6036028).length < 2 ^ (prefixWord ++ tailWord_6036028).sum := by decide
  have hdescent : baseEnd_6036028 < baseStart_6036028 := by decide
  rcases family_descends (prefixWord ++ tailWord_6036028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6036038 : List Nat := [6, 1, 1, 1, 2, 2, 1, 1, 3, 3, 2]
def baseStart_6036038 : Nat := 118140960795 + 6036038 * 2 ^ 59
def prefixEnd_6036038 : Nat := 4983230072969 + 3 ^ 40 * 6036038 * 2
def baseEnd_6036038 : Nat := 3099388742803360207265773

theorem tailTrace_6036038 : CollatzResearch.WordTrace tailWord_6036038 prefixEnd_6036038 3099388742803360207265773 := by
  unfold tailWord_6036038
  simp only [CollatzResearch.WordTrace]
  refine ⟨6879762253327271064484399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 146768261404315116042333845 6879762253327271064484399)
  ·
    refine ⟨10319643379990906596726599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6879762253327271064484399 10319643379990906596726599)
    ·
      refine ⟨15479465069986359895089899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10319643379990906596726599 15479465069986359895089899)
      ·
        refine ⟨23219197604979539842634849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15479465069986359895089899 23219197604979539842634849)
        ·
          refine ⟨17414398203734654881976137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23219197604979539842634849 17414398203734654881976137)
          ·
            refine ⟨13060798652800991161482103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17414398203734654881976137 13060798652800991161482103)
            ·
              refine ⟨19591197979201486742223155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13060798652800991161482103 19591197979201486742223155)
              ·
                refine ⟨29386796968802230113334733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19591197979201486742223155 29386796968802230113334733)
                ·
                  refine ⟨11020048863300836292500525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29386796968802230113334733 11020048863300836292500525)
                  ·
                    refine ⟨4132518323737813609687697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11020048863300836292500525 4132518323737813609687697)
                    ·
                      refine ⟨3099388742803360207265773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4132518323737813609687697 3099388742803360207265773)
                      ·
                        rfl

theorem cell23_6036038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 1, 1, 3, 3, 2].length) (baseStart_6036038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6036038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6036038 prefixEnd_6036038 := by exact prefixLift 6036038
  have htrace : WordTrace (prefixWord ++ tailWord_6036038) baseStart_6036038 baseEnd_6036038 := by
    simpa [prefixWord, tailWord_6036038, baseEnd_6036038] using wordTrace_append hprefix tailTrace_6036038
  have hstable : (prefixWord ++ tailWord_6036038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6036038).length < 2 ^ (prefixWord ++ tailWord_6036038).sum := by decide
  have hdescent : baseEnd_6036038 < baseStart_6036038 := by decide
  rcases family_descends (prefixWord ++ tailWord_6036038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6036040 : List Nat := [2, 1, 3, 1, 1, 1, 1, 6, 7]
def baseStart_6036040 : Nat := 118140960795 + 6036040 * 2 ^ 59
def prefixEnd_6036040 : Nat := 4983230072969 + 3 ^ 40 * 6036040 * 2
def baseEnd_6036040 : Nat := 344376641084963244382307

theorem tailTrace_6036040 : CollatzResearch.WordTrace tailWord_6036040 prefixEnd_6036040 344376641084963244382307 := by
  unfold tailWord_6036040
  simp only [CollatzResearch.WordTrace]
  refine ⟨110076232526232714202536787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146768310034976952270049049 110076232526232714202536787)
  ·
    refine ⟨165114348789349071303805181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110076232526232714202536787 165114348789349071303805181)
    ·
      refine ⟨61917880796005901738926943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 165114348789349071303805181 61917880796005901738926943)
      ·
        refine ⟨92876821194008852608390415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61917880796005901738926943 92876821194008852608390415)
        ·
          refine ⟨139315231791013278912585623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92876821194008852608390415 139315231791013278912585623)
          ·
            refine ⟨208972847686519918368878435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139315231791013278912585623 208972847686519918368878435)
            ·
              refine ⟨313459271529779877553317653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 208972847686519918368878435 313459271529779877553317653)
              ·
                refine ⟨14693403352958431760311765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 313459271529779877553317653 14693403352958431760311765)
                ·
                  refine ⟨344376641084963244382307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14693403352958431760311765 344376641084963244382307)
                  ·
                    rfl

theorem cell23_6036040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 6, 7].length) (baseStart_6036040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6036040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6036040 prefixEnd_6036040 := by exact prefixLift 6036040
  have htrace : WordTrace (prefixWord ++ tailWord_6036040) baseStart_6036040 baseEnd_6036040 := by
    simpa [prefixWord, tailWord_6036040, baseEnd_6036040] using wordTrace_append hprefix tailTrace_6036040
  have hstable : (prefixWord ++ tailWord_6036040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6036040).length < 2 ^ (prefixWord ++ tailWord_6036040).sum := by decide
  have hdescent : baseEnd_6036040 < baseStart_6036040 := by decide
  rcases family_descends (prefixWord ++ tailWord_6036040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6036062 : List Nat := [4, 4, 1, 2, 1, 1, 2, 2, 2, 1, 3]
def baseStart_6036062 : Nat := 118140960795 + 6036062 * 2 ^ 59
def prefixEnd_6036062 : Nat := 4983230072969 + 3 ^ 40 * 6036062 * 2
def baseEnd_6036062 : Nat := 3099401066339068113365663

theorem tailTrace_6036062 : CollatzResearch.WordTrace tailWord_6036062 prefixEnd_6036062 3099401066339068113365663 := by
  unfold tailWord_6036062
  simp only [CollatzResearch.WordTrace]
  refine ⟨27519158432298215770296805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 146768844972257150774916293 27519158432298215770296805)
  ·
    refine ⟨5159842206055915456930651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27519158432298215770296805 5159842206055915456930651)
    ·
      refine ⟨7739763309083873185395977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5159842206055915456930651 7739763309083873185395977)
      ·
        refine ⟨5804822481812904889046983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7739763309083873185395977 5804822481812904889046983)
        ·
          refine ⟨8707233722719357333570475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5804822481812904889046983 8707233722719357333570475)
          ·
            refine ⟨13060850584079036000355713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8707233722719357333570475 13060850584079036000355713)
            ·
              refine ⟨9795637938059277000266785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13060850584079036000355713 9795637938059277000266785)
              ·
                refine ⟨7346728453544457750200089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9795637938059277000266785 7346728453544457750200089)
                ·
                  refine ⟨5510046340158343312650067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7346728453544457750200089 5510046340158343312650067)
                  ·
                    refine ⟨8265069510237514968975101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5510046340158343312650067 8265069510237514968975101)
                    ·
                      refine ⟨3099401066339068113365663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8265069510237514968975101 3099401066339068113365663)
                      ·
                        rfl

theorem cell23_6036062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 2, 2, 2, 1, 3].length) (baseStart_6036062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6036062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6036062 prefixEnd_6036062 := by exact prefixLift 6036062
  have htrace : WordTrace (prefixWord ++ tailWord_6036062) baseStart_6036062 baseEnd_6036062 := by
    simpa [prefixWord, tailWord_6036062, baseEnd_6036062] using wordTrace_append hprefix tailTrace_6036062
  have hstable : (prefixWord ++ tailWord_6036062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6036062).length < 2 ^ (prefixWord ++ tailWord_6036062).sum := by decide
  have hdescent : baseEnd_6036062 < baseStart_6036062 := by decide
  rcases family_descends (prefixWord ++ tailWord_6036062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6036067 : List Nat := [1, 1, 1, 5, 1, 2, 2, 2, 2, 3, 3]
def baseStart_6036067 : Nat := 118140960795 + 6036067 * 2 ^ 59
def prefixEnd_6036067 : Nat := 4983230072969 + 3 ^ 40 * 6036067 * 2
def baseEnd_6036067 : Nat := 3099403633742340593803139

theorem tailTrace_6036067 : CollatzResearch.WordTrace tailWord_6036067 prefixEnd_6036067 3099403633742340593803139 := by
  unfold tailWord_6036067
  simp only [CollatzResearch.WordTrace]
  refine ⟨220153449823367612016306455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146768966548911741344204303 220153449823367612016306455)
  ·
    refine ⟨330230174735051418024459683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220153449823367612016306455 330230174735051418024459683)
    ·
      refine ⟨495345262102577127036689525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 330230174735051418024459683 495345262102577127036689525)
      ·
        refine ⟨46438618322116605659689643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 495345262102577127036689525 46438618322116605659689643)
        ·
          refine ⟨69657927483174908489534465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46438618322116605659689643 69657927483174908489534465)
          ·
            refine ⟨52243445612381181367150849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69657927483174908489534465 52243445612381181367150849)
            ·
              refine ⟨39182584209285886025363137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52243445612381181367150849 39182584209285886025363137)
              ·
                refine ⟨29386938156964414519022353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39182584209285886025363137 29386938156964414519022353)
                ·
                  refine ⟨22040203617723310889266765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29386938156964414519022353 22040203617723310889266765)
                  ·
                    refine ⟨8265076356646241583475037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22040203617723310889266765 8265076356646241583475037)
                    ·
                      refine ⟨3099403633742340593803139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8265076356646241583475037 3099403633742340593803139)
                      ·
                        rfl

theorem cell23_6036067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 2, 2, 3, 3].length) (baseStart_6036067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6036067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6036067 prefixEnd_6036067 := by exact prefixLift 6036067
  have htrace : WordTrace (prefixWord ++ tailWord_6036067) baseStart_6036067 baseEnd_6036067 := by
    simpa [prefixWord, tailWord_6036067, baseEnd_6036067] using wordTrace_append hprefix tailTrace_6036067
  have hstable : (prefixWord ++ tailWord_6036067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6036067).length < 2 ^ (prefixWord ++ tailWord_6036067).sum := by decide
  have hdescent : baseEnd_6036067 < baseStart_6036067 := by decide
  rcases family_descends (prefixWord ++ tailWord_6036067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6036074 : List Nat := [3, 1, 3, 2, 1, 1, 3, 4, 5]
def baseStart_6036074 : Nat := 118140960795 + 6036074 * 2 ^ 59
def prefixEnd_6036074 : Nat := 4983230072969 + 3 ^ 40 * 6036074 * 2
def baseEnd_6036074 : Nat := 344378580900769118490623

theorem tailTrace_6036074 : CollatzResearch.WordTrace tailWord_6036074 prefixEnd_6036074 344378580900769118490623 := by
  unfold tailWord_6036074
  simp only [CollatzResearch.WordTrace]
  refine ⟨55038426283585563052952819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146769136756228168141207517 55038426283585563052952819)
  ·
    refine ⟨82557639425378344579429229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55038426283585563052952819 82557639425378344579429229)
    ·
      refine ⟨30959114784516879217285961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82557639425378344579429229 30959114784516879217285961)
      ·
        refine ⟨23219336088387659412964471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30959114784516879217285961 23219336088387659412964471)
        ·
          refine ⟨34829004132581489119446707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23219336088387659412964471 34829004132581489119446707)
          ·
            refine ⟨52243506198872233679170061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34829004132581489119446707 52243506198872233679170061)
            ·
              refine ⟨19591314824577087629688773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52243506198872233679170061 19591314824577087629688773)
              ·
                refine ⟨3673371529608203930566645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19591314824577087629688773 3673371529608203930566645)
                ·
                  refine ⟨344378580900769118490623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3673371529608203930566645 344378580900769118490623)
                  ·
                    rfl

theorem cell23_6036074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 3, 4, 5].length) (baseStart_6036074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6036074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6036074 prefixEnd_6036074 := by exact prefixLift 6036074
  have htrace : WordTrace (prefixWord ++ tailWord_6036074) baseStart_6036074 baseEnd_6036074 := by
    simpa [prefixWord, tailWord_6036074, baseEnd_6036074] using wordTrace_append hprefix tailTrace_6036074
  have hstable : (prefixWord ++ tailWord_6036074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6036074).length < 2 ^ (prefixWord ++ tailWord_6036074).sum := by decide
  have hdescent : baseEnd_6036074 < baseStart_6036074 := by decide
  rcases family_descends (prefixWord ++ tailWord_6036074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6036107 : List Nat := [1, 1, 1, 1, 4, 1, 2, 5, 2, 1, 4]
def baseStart_6036107 : Nat := 118140960795 + 6036107 * 2 ^ 59
def prefixEnd_6036107 : Nat := 4983230072969 + 3 ^ 40 * 6036107 * 2
def baseEnd_6036107 : Nat := 3099424172968520437302955

theorem tailTrace_6036107 : CollatzResearch.WordTrace tailWord_6036107 prefixEnd_6036107 3099424172968520437302955 := by
  unfold tailWord_6036107
  simp only [CollatzResearch.WordTrace]
  refine ⟨220154908743222698847762575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146769939162148465898508383 220154908743222698847762575)
  ·
    refine ⟨330232363114834048271643863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220154908743222698847762575 330232363114834048271643863)
    ·
      refine ⟨495348544672251072407465795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 330232363114834048271643863 495348544672251072407465795)
      ·
        refine ⟨743022817008376608611198693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 495348544672251072407465795 743022817008376608611198693)
        ·
          refine ⟨139316778189070614114599755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 743022817008376608611198693 139316778189070614114599755)
          ·
            refine ⟨208975167283605921171899633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139316778189070614114599755 208975167283605921171899633)
            ·
              refine ⟨156731375462704440878924725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 208975167283605921171899633 156731375462704440878924725)
              ·
                refine ⟨14693566449628541332399193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 156731375462704440878924725 14693566449628541332399193)
                ·
                  refine ⟨11020174837221405999299395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14693566449628541332399193 11020174837221405999299395)
                  ·
                    refine ⟨16530262255832108998949093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11020174837221405999299395 16530262255832108998949093)
                    ·
                      refine ⟨3099424172968520437302955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16530262255832108998949093 3099424172968520437302955)
                      ·
                        rfl

theorem cell23_6036107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 5, 2, 1, 4].length) (baseStart_6036107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6036107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6036107 prefixEnd_6036107 := by exact prefixLift 6036107
  have htrace : WordTrace (prefixWord ++ tailWord_6036107) baseStart_6036107 baseEnd_6036107 := by
    simpa [prefixWord, tailWord_6036107, baseEnd_6036107] using wordTrace_append hprefix tailTrace_6036107
  have hstable : (prefixWord ++ tailWord_6036107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6036107).length < 2 ^ (prefixWord ++ tailWord_6036107).sum := by decide
  have hdescent : baseEnd_6036107 < baseStart_6036107 := by decide
  rcases family_descends (prefixWord ++ tailWord_6036107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6036141 : List Nat := [1, 5, 2, 1, 1, 2, 2, 1, 2, 4, 2]
def baseStart_6036141 : Nat := 118140960795 + 6036141 * 2 ^ 59
def prefixEnd_6036141 : Nat := 4983230072969 + 3 ^ 40 * 6036141 * 2
def baseEnd_6036141 : Nat := 3099441631310773304277799

theorem tailTrace_6036141 : CollatzResearch.WordTrace tailWord_6036141 prefixEnd_6036141 3099441631310773304277799 := by
  unfold tailWord_6036141
  simp only [CollatzResearch.WordTrace]
  refine ⟨220156148825099522654500277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146770765883399681769666851 220156148825099522654500277)
  ·
    refine ⟨20639638952353080248859401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 220156148825099522654500277 20639638952353080248859401)
    ·
      refine ⟨15479729214264810186644551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20639638952353080248859401 15479729214264810186644551)
      ·
        refine ⟨23219593821397215279966827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15479729214264810186644551 23219593821397215279966827)
        ·
          refine ⟨34829390732095822919950241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23219593821397215279966827 34829390732095822919950241)
          ·
            refine ⟨26122043049071867189962681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34829390732095822919950241 26122043049071867189962681)
            ·
              refine ⟨19591532286803900392472011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26122043049071867189962681 19591532286803900392472011)
              ·
                refine ⟨29387298430205850588708017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19591532286803900392472011 29387298430205850588708017)
                ·
                  refine ⟨22040473822654387941531013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29387298430205850588708017 22040473822654387941531013)
                  ·
                    refine ⟨4132588841747697739037065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22040473822654387941531013 4132588841747697739037065)
                    ·
                      refine ⟨3099441631310773304277799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4132588841747697739037065 3099441631310773304277799)
                      ·
                        rfl

theorem cell23_6036141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 2, 1, 2, 4, 2].length) (baseStart_6036141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6036141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6036141 prefixEnd_6036141 := by exact prefixLift 6036141
  have htrace : WordTrace (prefixWord ++ tailWord_6036141) baseStart_6036141 baseEnd_6036141 := by
    simpa [prefixWord, tailWord_6036141, baseEnd_6036141] using wordTrace_append hprefix tailTrace_6036141
  have hstable : (prefixWord ++ tailWord_6036141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6036141).length < 2 ^ (prefixWord ++ tailWord_6036141).sum := by decide
  have hdescent : baseEnd_6036141 < baseStart_6036141 := by decide
  rcases family_descends (prefixWord ++ tailWord_6036141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6036168 : List Nat := [2, 1, 3, 1, 2, 5, 1, 3, 1, 4]
def baseStart_6036168 : Nat := 118140960795 + 6036168 * 2 ^ 59
def prefixEnd_6036168 : Nat := 4983230072969 + 3 ^ 40 * 6036168 * 2
def baseEnd_6036168 : Nat := 1033151831762814899546725

theorem tailTrace_6036168 : CollatzResearch.WordTrace tailWord_6036168 prefixEnd_6036168 1033151831762814899546725 := by
  unfold tailWord_6036168
  simp only [CollatzResearch.WordTrace]
  refine ⟨110078566798000853132866579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146771422397334470843822105 110078566798000853132866579)
  ·
    refine ⟨165117850197001279699299869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110078566798000853132866579 165117850197001279699299869)
    ·
      refine ⟨61919193823875479887237451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 165117850197001279699299869 61919193823875479887237451)
      ·
        refine ⟨92878790735813219830856177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61919193823875479887237451 92878790735813219830856177)
        ·
          refine ⟨69659093051859914873142133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92878790735813219830856177 69659093051859914873142133)
          ·
            refine ⟨6530539973611867019357075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 69659093051859914873142133 6530539973611867019357075)
            ·
              refine ⟨9795809960417800529035613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6530539973611867019357075 9795809960417800529035613)
              ·
                refine ⟨3673428735156675198388355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9795809960417800529035613 3673428735156675198388355)
                ·
                  refine ⟨5510143102735012797582533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3673428735156675198388355 5510143102735012797582533)
                  ·
                    refine ⟨1033151831762814899546725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5510143102735012797582533 1033151831762814899546725)
                    ·
                      rfl

theorem cell23_6036168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 5, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 5, 1, 3, 1, 4].length) (baseStart_6036168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6036168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6036168 prefixEnd_6036168 := by exact prefixLift 6036168
  have htrace : WordTrace (prefixWord ++ tailWord_6036168) baseStart_6036168 baseEnd_6036168 := by
    simpa [prefixWord, tailWord_6036168, baseEnd_6036168] using wordTrace_append hprefix tailTrace_6036168
  have hstable : (prefixWord ++ tailWord_6036168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6036168).length < 2 ^ (prefixWord ++ tailWord_6036168).sum := by decide
  have hdescent : baseEnd_6036168 < baseStart_6036168 := by decide
  rcases family_descends (prefixWord ++ tailWord_6036168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6036191 : List Nat := [1, 1, 2, 3, 2, 3, 3, 1, 3, 1, 3]
def baseStart_6036191 : Nat := 118140960795 + 6036191 * 2 ^ 59
def prefixEnd_6036191 : Nat := 4983230072969 + 3 ^ 40 * 6036191 * 2
def baseEnd_6036191 : Nat := 3099467305343498108652569

theorem tailTrace_6036191 : CollatzResearch.WordTrace tailWord_6036191 prefixEnd_6036191 3099467305343498108652569 := by
  unfold tailWord_6036191
  simp only [CollatzResearch.WordTrace]
  refine ⟨220157972474918381193820427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146771981649945587462546951 220157972474918381193820427)
  ·
    refine ⟨330236958712377571790730641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220157972474918381193820427 330236958712377571790730641)
    ·
      refine ⟨247677719034283178843047981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 330236958712377571790730641 247677719034283178843047981)
      ·
        refine ⟨92879144637856192066142993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 247677719034283178843047981 92879144637856192066142993)
        ·
          refine ⟨69659358478392144049607245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92879144637856192066142993 69659358478392144049607245)
          ·
            refine ⟨26122259429397054018602717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69659358478392144049607245 26122259429397054018602717)
            ·
              refine ⟨9795847286023895256976019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26122259429397054018602717 9795847286023895256976019)
              ·
                refine ⟨14693770929035842885464029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9795847286023895256976019 14693770929035842885464029)
                ·
                  refine ⟨5510164098388441082049011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14693770929035842885464029 5510164098388441082049011)
                  ·
                    refine ⟨8265246147582661623073517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5510164098388441082049011 8265246147582661623073517)
                    ·
                      refine ⟨3099467305343498108652569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8265246147582661623073517 3099467305343498108652569)
                      ·
                        rfl

theorem cell23_6036191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 3, 1, 3, 1, 3].length) (baseStart_6036191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6036191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6036191 prefixEnd_6036191 := by exact prefixLift 6036191
  have htrace : WordTrace (prefixWord ++ tailWord_6036191) baseStart_6036191 baseEnd_6036191 := by
    simpa [prefixWord, tailWord_6036191, baseEnd_6036191] using wordTrace_append hprefix tailTrace_6036191
  have hstable : (prefixWord ++ tailWord_6036191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6036191).length < 2 ^ (prefixWord ++ tailWord_6036191).sum := by decide
  have hdescent : baseEnd_6036191 < baseStart_6036191 := by decide
  rcases family_descends (prefixWord ++ tailWord_6036191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6036217 : List Nat := [1, 2, 1, 3, 1, 1, 1, 4, 3, 1, 5]
def baseStart_6036217 : Nat := 118140960795 + 6036217 * 2 ^ 59
def prefixEnd_6036217 : Nat := 4983230072969 + 3 ^ 40 * 6036217 * 2
def baseEnd_6036217 : Nat := 3099480655840515006927449

theorem tailTrace_6036217 : CollatzResearch.WordTrace tailWord_6036217 prefixEnd_6036217 3099480655840515006927449 := by
  unfold tailWord_6036217
  simp only [CollatzResearch.WordTrace]
  refine ⟨220158920772824187634266905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146772613848549458422844603 220158920772824187634266905)
  ·
    refine ⟨165119190579618140725700179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 220158920772824187634266905 165119190579618140725700179)
    ·
      refine ⟨247678785869427211088550269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165119190579618140725700179 247678785869427211088550269)
      ·
        refine ⟨92879544701035204158206351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 247678785869427211088550269 92879544701035204158206351)
        ·
          refine ⟨139319317051552806237309527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92879544701035204158206351 139319317051552806237309527)
          ·
            refine ⟨208978975577329209355964291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139319317051552806237309527 208978975577329209355964291)
            ·
              refine ⟨313468463365993814033946437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 208978975577329209355964291 313468463365993814033946437)
              ·
                refine ⟨58775336881123840131364957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 313468463365993814033946437 58775336881123840131364957)
                ·
                  refine ⟨22040751330421440049261859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 58775336881123840131364957 22040751330421440049261859)
                  ·
                    refine ⟨33061126995632160073892789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22040751330421440049261859 33061126995632160073892789)
                    ·
                      refine ⟨3099480655840515006927449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33061126995632160073892789 3099480655840515006927449)
                      ·
                        rfl

theorem cell23_6036217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 4, 3, 1, 5].length) (baseStart_6036217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6036217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6036217 prefixEnd_6036217 := by exact prefixLift 6036217
  have htrace : WordTrace (prefixWord ++ tailWord_6036217) baseStart_6036217 baseEnd_6036217 := by
    simpa [prefixWord, tailWord_6036217, baseEnd_6036217] using wordTrace_append hprefix tailTrace_6036217
  have hstable : (prefixWord ++ tailWord_6036217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6036217).length < 2 ^ (prefixWord ++ tailWord_6036217).sum := by decide
  have hdescent : baseEnd_6036217 < baseStart_6036217 := by decide
  rcases family_descends (prefixWord ++ tailWord_6036217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6036242 : List Nat := [3, 2, 4, 1, 2, 1, 1, 4, 1, 1, 3]
def baseStart_6036242 : Nat := 118140960795 + 6036242 * 2 ^ 59
def prefixEnd_6036242 : Nat := 4983230072969 + 3 ^ 40 * 6036242 * 2
def baseEnd_6036242 : Nat := 3099493492856877409114835

theorem tailTrace_6036242 : CollatzResearch.WordTrace tailWord_6036242 prefixEnd_6036242 3099493492856877409114835 := by
  unfold tailWord_6036242
  simp only [CollatzResearch.WordTrace]
  refine ⟨55039958149433404225981745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146773221731822411269284653 55039958149433404225981745)
  ·
    refine ⟨41279968612075053169486309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55039958149433404225981745 41279968612075053169486309)
    ·
      refine ⟨7739994114764072469278683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41279968612075053169486309 7739994114764072469278683)
      ·
        refine ⟨11609991172146108703918025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7739994114764072469278683 11609991172146108703918025)
        ·
          refine ⟨8707493379109581527938519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11609991172146108703918025 8707493379109581527938519)
          ·
            refine ⟨13061240068664372291907779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8707493379109581527938519 13061240068664372291907779)
            ·
              refine ⟨19591860102996558437861669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13061240068664372291907779 19591860102996558437861669)
              ·
                refine ⟨3673473769311854707099063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19591860102996558437861669 3673473769311854707099063)
                ·
                  refine ⟨5510210653967782060648595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3673473769311854707099063 5510210653967782060648595)
                  ·
                    refine ⟨8265315980951673090972893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5510210653967782060648595 8265315980951673090972893)
                    ·
                      refine ⟨3099493492856877409114835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8265315980951673090972893 3099493492856877409114835)
                      ·
                        rfl

theorem cell23_6036242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 1, 4, 1, 1, 3].length) (baseStart_6036242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6036242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6036242 prefixEnd_6036242 := by exact prefixLift 6036242
  have htrace : WordTrace (prefixWord ++ tailWord_6036242) baseStart_6036242 baseEnd_6036242 := by
    simpa [prefixWord, tailWord_6036242, baseEnd_6036242] using wordTrace_append hprefix tailTrace_6036242
  have hstable : (prefixWord ++ tailWord_6036242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6036242).length < 2 ^ (prefixWord ++ tailWord_6036242).sum := by decide
  have hdescent : baseEnd_6036242 < baseStart_6036242 := by decide
  rcases family_descends (prefixWord ++ tailWord_6036242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6036269 : List Nat := [1, 5, 3, 2, 2, 1, 1, 1, 2, 3, 2]
def baseStart_6036269 : Nat := 118140960795 + 6036269 * 2 ^ 59
def prefixEnd_6036269 : Nat := 4983230072969 + 3 ^ 40 * 6036269 * 2
def baseEnd_6036269 : Nat := 3099507356834548803477211

theorem tailTrace_6036269 : CollatzResearch.WordTrace tailWord_6036269 prefixEnd_6036269 3099507356834548803477211 := by
  unfold tailWord_6036269
  simp only [CollatzResearch.WordTrace]
  refine ⟨220160817368635800515159861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146773878245757200343439907 220160817368635800515159861)
  ·
    refine ⟨20640076628309606298296237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 220160817368635800515159861 20640076628309606298296237)
    ·
      refine ⟨7740028735616102361861089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20640076628309606298296237 7740028735616102361861089)
      ·
        refine ⟨5805021551712076771395817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7740028735616102361861089 5805021551712076771395817)
        ·
          refine ⟨4353766163784057578546863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5805021551712076771395817 4353766163784057578546863)
          ·
            refine ⟨6530649245676086367820295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4353766163784057578546863 6530649245676086367820295)
            ·
              refine ⟨9795973868514129551730443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6530649245676086367820295 9795973868514129551730443)
              ·
                refine ⟨14693960802771194327595665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9795973868514129551730443 14693960802771194327595665)
                ·
                  refine ⟨11020470602078395745696749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14693960802771194327595665 11020470602078395745696749)
                  ·
                    refine ⟨4132676475779398404636281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11020470602078395745696749 4132676475779398404636281)
                    ·
                      refine ⟨3099507356834548803477211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4132676475779398404636281 3099507356834548803477211)
                      ·
                        rfl

theorem cell23_6036269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 2, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 2, 1, 1, 1, 2, 3, 2].length) (baseStart_6036269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6036269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6036269 prefixEnd_6036269 := by exact prefixLift 6036269
  have htrace : WordTrace (prefixWord ++ tailWord_6036269) baseStart_6036269 baseEnd_6036269 := by
    simpa [prefixWord, tailWord_6036269, baseEnd_6036269] using wordTrace_append hprefix tailTrace_6036269
  have hstable : (prefixWord ++ tailWord_6036269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6036269).length < 2 ^ (prefixWord ++ tailWord_6036269).sum := by decide
  have hdescent : baseEnd_6036269 < baseStart_6036269 := by decide
  rcases family_descends (prefixWord ++ tailWord_6036269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6036282 : List Nat := [3, 1, 1, 1, 6, 1, 2, 3, 1, 2, 2]
def baseStart_6036282 : Nat := 118140960795 + 6036282 * 2 ^ 59
def prefixEnd_6036282 : Nat := 4983230072969 + 3 ^ 40 * 6036282 * 2
def baseEnd_6036282 : Nat := 3099514032083057252614651

theorem tailTrace_6036282 : CollatzResearch.WordTrace tailWord_6036282 prefixEnd_6036282 3099514032083057252614651 := by
  unfold tailWord_6036282
  simp only [CollatzResearch.WordTrace]
  refine ⟨55040322879397175933845775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146774194345059135823588733 55040322879397175933845775)
  ·
    refine ⟨82560484319095763900768663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55040322879397175933845775 82560484319095763900768663)
    ·
      refine ⟨123840726478643645851152995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82560484319095763900768663 123840726478643645851152995)
      ·
        refine ⟨185761089717965468776729493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123840726478643645851152995 185761089717965468776729493)
        ·
          refine ⟨8707551080529631348909195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 185761089717965468776729493 8707551080529631348909195)
          ·
            refine ⟨13061326620794447023363793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8707551080529631348909195 13061326620794447023363793)
            ·
              refine ⟨9795994965595835267522845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13061326620794447023363793 9795994965595835267522845)
              ·
                refine ⟨3673498112098438225321067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9795994965595835267522845 3673498112098438225321067)
                ·
                  refine ⟨5510247168147657337981601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3673498112098438225321067 5510247168147657337981601)
                  ·
                    refine ⟨4132685376110743003486201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5510247168147657337981601 4132685376110743003486201)
                    ·
                      refine ⟨3099514032083057252614651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4132685376110743003486201 3099514032083057252614651)
                      ·
                        rfl

theorem cell23_6036282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 2, 3, 1, 2, 2].length) (baseStart_6036282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6036282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6036282 prefixEnd_6036282 := by exact prefixLift 6036282
  have htrace : WordTrace (prefixWord ++ tailWord_6036282) baseStart_6036282 baseEnd_6036282 := by
    simpa [prefixWord, tailWord_6036282, baseEnd_6036282] using wordTrace_append hprefix tailTrace_6036282
  have hstable : (prefixWord ++ tailWord_6036282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6036282).length < 2 ^ (prefixWord ++ tailWord_6036282).sum := by decide
  have hdescent : baseEnd_6036282 < baseStart_6036282 := by decide
  rcases family_descends (prefixWord ++ tailWord_6036282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6036292 : List Nat := [2, 3, 4, 2, 1, 2, 1, 2, 2, 4]
def baseStart_6036292 : Nat := 118140960795 + 6036292 * 2 ^ 59
def prefixEnd_6036292 : Nat := 4983230072969 + 3 ^ 40 * 6036292 * 2
def baseEnd_6036292 : Nat := 1033173055629867404496535

theorem tailTrace_6036292 : CollatzResearch.WordTrace tailWord_6036292 prefixEnd_6036292 1033173055629867404496535 := by
  unfold tailWord_6036292
  simp only [CollatzResearch.WordTrace]
  refine ⟨110080828123776237721623565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146774437498368316962164753 110080828123776237721623565)
  ·
    refine ⟨41280310546416089145608837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110080828123776237721623565 41280310546416089145608837)
    ·
      refine ⟨7740058227453016714801657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41280310546416089145608837 7740058227453016714801657)
      ·
        refine ⟨5805043670589762536101243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7740058227453016714801657 5805043670589762536101243)
        ·
          refine ⟨8707565505884643804151865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5805043670589762536101243 8707565505884643804151865)
          ·
            refine ⟨6530674129413482853113899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8707565505884643804151865 6530674129413482853113899)
            ·
              refine ⟨9796011194120224279670849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6530674129413482853113899 9796011194120224279670849)
              ·
                refine ⟨7347008395590168209753137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9796011194120224279670849 7347008395590168209753137)
                ·
                  refine ⟨5510256296692626157314853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7347008395590168209753137 5510256296692626157314853)
                  ·
                    refine ⟨1033173055629867404496535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5510256296692626157314853 1033173055629867404496535)
                    ·
                      rfl

theorem cell23_6036292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 2, 1, 2, 2, 4].length) (baseStart_6036292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6036292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6036292 prefixEnd_6036292 := by exact prefixLift 6036292
  have htrace : WordTrace (prefixWord ++ tailWord_6036292) baseStart_6036292 baseEnd_6036292 := by
    simpa [prefixWord, tailWord_6036292, baseEnd_6036292] using wordTrace_append hprefix tailTrace_6036292
  have hstable : (prefixWord ++ tailWord_6036292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6036292).length < 2 ^ (prefixWord ++ tailWord_6036292).sum := by decide
  have hdescent : baseEnd_6036292 < baseStart_6036292 := by decide
  rcases family_descends (prefixWord ++ tailWord_6036292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6036314 : List Nat := [3, 1, 1, 2, 1, 4, 2, 1, 2, 6]
def baseStart_6036314 : Nat := 118140960795 + 6036314 * 2 ^ 59
def prefixEnd_6036314 : Nat := 4983230072969 + 3 ^ 40 * 6036314 * 2
def baseEnd_6036314 : Nat := 1033176821154667042471501

theorem tailTrace_6036314 : CollatzResearch.WordTrace tailWord_6036314 prefixEnd_6036314 1033176821154667042471501 := by
  unfold tailWord_6036314
  simp only [CollatzResearch.WordTrace]
  refine ⟨55040614663368193300136999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146774972435648515467031997 55040614663368193300136999)
  ·
    refine ⟨82560921995052289950205499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55040614663368193300136999 82560921995052289950205499)
    ·
      refine ⟨123841382992578434925308249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82560921995052289950205499 123841382992578434925308249)
      ·
        refine ⟨92881037244433826193981187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123841382992578434925308249 92881037244433826193981187)
        ·
          refine ⟨139321555866650739290971781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92881037244433826193981187 139321555866650739290971781)
          ·
            refine ⟨26122791724997013617057209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 139321555866650739290971781 26122791724997013617057209)
            ·
              refine ⟨19592093793747760212792907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26122791724997013617057209 19592093793747760212792907)
              ·
                refine ⟨29388140690621640319189361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19592093793747760212792907 29388140690621640319189361)
                ·
                  refine ⟨22041105517966230239392021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29388140690621640319189361 22041105517966230239392021)
                  ·
                    refine ⟨1033176821154667042471501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22041105517966230239392021 1033176821154667042471501)
                    ·
                      rfl

theorem cell23_6036314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 2, 1, 2, 6].length) (baseStart_6036314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6036314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6036314 prefixEnd_6036314 := by exact prefixLift 6036314
  have htrace : WordTrace (prefixWord ++ tailWord_6036314) baseStart_6036314 baseEnd_6036314 := by
    simpa [prefixWord, tailWord_6036314, baseEnd_6036314] using wordTrace_append hprefix tailTrace_6036314
  have hstable : (prefixWord ++ tailWord_6036314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6036314).length < 2 ^ (prefixWord ++ tailWord_6036314).sum := by decide
  have hdescent : baseEnd_6036314 < baseStart_6036314 := by decide
  rcases family_descends (prefixWord ++ tailWord_6036314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6036321 : List Nat := [1, 2, 3, 1, 1, 1, 2, 5, 1, 4, 2]
def baseStart_6036321 : Nat := 118140960795 + 6036321 * 2 ^ 59
def prefixEnd_6036321 : Nat := 4983230072969 + 3 ^ 40 * 6036321 * 2
def baseEnd_6036321 : Nat := 3099534057828582600026971

theorem tailTrace_6036321 : CollatzResearch.WordTrace tailWord_6036321 prefixEnd_6036321 3099534057828582600026971 := by
  unfold tailWord_6036321
  simp only [CollatzResearch.WordTrace]
  refine ⟨220162713964447413396052817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146775142642964942264035211 220162713964447413396052817)
  ·
    refine ⟨165122035473335560047039613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 220162713964447413396052817 165122035473335560047039613)
    ·
      refine ⟨61920763302500835017639855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 165122035473335560047039613 61920763302500835017639855)
      ·
        refine ⟨92881144953751252526459783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61920763302500835017639855 92881144953751252526459783)
        ·
          refine ⟨139321717430626878789689675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92881144953751252526459783 139321717430626878789689675)
          ·
            refine ⟨208982576145940318184534513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139321717430626878789689675 208982576145940318184534513)
            ·
              refine ⟨156736932109455238638400885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 208982576145940318184534513 156736932109455238638400885)
              ·
                refine ⟨14694087385261428622350083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 156736932109455238638400885 14694087385261428622350083)
                ·
                  refine ⟨22041131077892142933525125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14694087385261428622350083 22041131077892142933525125)
                  ·
                    refine ⟨4132712077104776800035961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22041131077892142933525125 4132712077104776800035961)
                    ·
                      refine ⟨3099534057828582600026971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4132712077104776800035961 3099534057828582600026971)
                      ·
                        rfl

theorem cell23_6036321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 5, 1, 4, 2].length) (baseStart_6036321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6036321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6036321 prefixEnd_6036321 := by exact prefixLift 6036321
  have htrace : WordTrace (prefixWord ++ tailWord_6036321) baseStart_6036321 baseEnd_6036321 := by
    simpa [prefixWord, tailWord_6036321, baseEnd_6036321] using wordTrace_append hprefix tailTrace_6036321
  have hstable : (prefixWord ++ tailWord_6036321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6036321).length < 2 ^ (prefixWord ++ tailWord_6036321).sum := by decide
  have hdescent : baseEnd_6036321 < baseStart_6036321 := by decide
  rcases family_descends (prefixWord ++ tailWord_6036321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6036338 : List Nat := [3, 2, 1, 2, 1, 1, 3, 2, 4, 2, 2]
def baseStart_6036338 : Nat := 118140960795 + 6036338 * 2 ^ 59
def prefixEnd_6036338 : Nat := 4983230072969 + 3 ^ 40 * 6036338 * 2
def baseEnd_6036338 : Nat := 3099542786999709033514393

theorem tailTrace_6036338 : CollatzResearch.WordTrace tailWord_6036338 prefixEnd_6036338 3099542786999709033514393 := by
  unfold tailWord_6036338
  simp only [CollatzResearch.WordTrace]
  refine ⟨55040833501346456324855417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146775556003590550199614445 55040833501346456324855417)
  ·
    refine ⟨41280625126009842243641563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55040833501346456324855417 41280625126009842243641563)
    ·
      refine ⟨61920937689014763365462345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41280625126009842243641563 61920937689014763365462345)
      ·
        refine ⟨46440703266761072524096759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61920937689014763365462345 46440703266761072524096759)
        ·
          refine ⟨69661054900141608786145139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46440703266761072524096759 69661054900141608786145139)
          ·
            refine ⟨104491582350212413179217709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69661054900141608786145139 104491582350212413179217709)
            ·
              refine ⟨39184343381329654942206641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 104491582350212413179217709 39184343381329654942206641)
              ·
                refine ⟨29388257535997241206654981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39184343381329654942206641 29388257535997241206654981)
                ·
                  refine ⟨5510298287999482726247809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29388257535997241206654981 5510298287999482726247809)
                  ·
                    refine ⟨4132723715999612044685857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5510298287999482726247809 4132723715999612044685857)
                    ·
                      refine ⟨3099542786999709033514393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4132723715999612044685857 3099542786999709033514393)
                      ·
                        rfl

theorem cell23_6036338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 2, 4, 2, 2].length) (baseStart_6036338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6036338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6036338 prefixEnd_6036338 := by exact prefixLift 6036338
  have htrace : WordTrace (prefixWord ++ tailWord_6036338) baseStart_6036338 baseEnd_6036338 := by
    simpa [prefixWord, tailWord_6036338, baseEnd_6036338] using wordTrace_append hprefix tailTrace_6036338
  have hstable : (prefixWord ++ tailWord_6036338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6036338).length < 2 ^ (prefixWord ++ tailWord_6036338).sum := by decide
  have hdescent : baseEnd_6036338 < baseStart_6036338 := by decide
  rcases family_descends (prefixWord ++ tailWord_6036338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6036341 : List Nat := [1, 3, 4, 1, 1, 3, 1, 1, 2, 1, 5]
def baseStart_6036341 : Nat := 118140960795 + 6036341 * 2 ^ 59
def prefixEnd_6036341 : Nat := 4983230072969 + 3 ^ 40 * 6036341 * 2
def baseEnd_6036341 : Nat := 3099544327441672521776879

theorem tailTrace_6036341 : CollatzResearch.WordTrace tailWord_6036341 prefixEnd_6036341 3099544327441672521776879 := by
  unfold tailWord_6036341
  simp only [CollatzResearch.WordTrace]
  refine ⟨220163443424374956811780877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146775628949583304541187251 220163443424374956811780877)
  ·
    refine ⟨82561291284140608804417829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 220163443424374956811780877 82561291284140608804417829)
    ·
      refine ⟨15480242115776364150828343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 82561291284140608804417829 15480242115776364150828343)
      ·
        refine ⟨23220363173664546226242515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15480242115776364150828343 23220363173664546226242515)
        ·
          refine ⟨34830544760496819339363773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23220363173664546226242515 34830544760496819339363773)
          ·
            refine ⟨13061454285186307252261415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34830544760496819339363773 13061454285186307252261415)
            ·
              refine ⟨19592181427779460878392123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13061454285186307252261415 19592181427779460878392123)
              ·
                refine ⟨29388272141669191317588185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19592181427779460878392123 29388272141669191317588185)
                ·
                  refine ⟨22041204106251893488191139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29388272141669191317588185 22041204106251893488191139)
                  ·
                    refine ⟨33061806159377840232286709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22041204106251893488191139 33061806159377840232286709)
                    ·
                      refine ⟨3099544327441672521776879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33061806159377840232286709 3099544327441672521776879)
                      ·
                        rfl

theorem cell23_6036341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 1, 1, 2, 1, 5].length) (baseStart_6036341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6036341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6036341 prefixEnd_6036341 := by exact prefixLift 6036341
  have htrace : WordTrace (prefixWord ++ tailWord_6036341) baseStart_6036341 baseEnd_6036341 := by
    simpa [prefixWord, tailWord_6036341, baseEnd_6036341] using wordTrace_append hprefix tailTrace_6036341
  have hstable : (prefixWord ++ tailWord_6036341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6036341).length < 2 ^ (prefixWord ++ tailWord_6036341).sum := by decide
  have hdescent : baseEnd_6036341 < baseStart_6036341 := by decide
  rcases family_descends (prefixWord ++ tailWord_6036341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6036361 : List Nat := [1, 2, 1, 1, 5, 4, 1, 1, 7]
def baseStart_6036361 : Nat := 118140960795 + 6036361 * 2 ^ 59
def prefixEnd_6036361 : Nat := 4983230072969 + 3 ^ 40 * 6036361 * 2
def baseEnd_6036361 : Nat := 344394955228306938169643

theorem tailTrace_6036361 : CollatzResearch.WordTrace tailWord_6036361 prefixEnd_6036361 344394955228306938169643 := by
  unfold tailWord_6036361
  simp only [CollatzResearch.WordTrace]
  refine ⟨220164172884302500227508937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146776115256201666818339291 220164172884302500227508937)
  ·
    refine ⟨165123129663226875170631703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 220164172884302500227508937 165123129663226875170631703)
    ·
      refine ⟨247684694494840312755947555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165123129663226875170631703 247684694494840312755947555)
      ·
        refine ⟨371527041742260469133921333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 247684694494840312755947555 371527041742260469133921333)
        ·
          refine ⟨34830660163336918981305125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 371527041742260469133921333 34830660163336918981305125)
          ·
            refine ⟨6530748780625672308994711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34830660163336918981305125 6530748780625672308994711)
            ·
              refine ⟨9796123170938508463492067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6530748780625672308994711 9796123170938508463492067)
              ·
                refine ⟨14694184756407762695238101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9796123170938508463492067 14694184756407762695238101)
                ·
                  refine ⟨344394955228306938169643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14694184756407762695238101 344394955228306938169643)
                  ·
                    rfl

theorem cell23_6036361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 4, 1, 1, 7].length) (baseStart_6036361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6036361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6036361 prefixEnd_6036361 := by exact prefixLift 6036361
  have htrace : WordTrace (prefixWord ++ tailWord_6036361) baseStart_6036361 baseEnd_6036361 := by
    simpa [prefixWord, tailWord_6036361, baseEnd_6036361] using wordTrace_append hprefix tailTrace_6036361
  have hstable : (prefixWord ++ tailWord_6036361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6036361).length < 2 ^ (prefixWord ++ tailWord_6036361).sum := by decide
  have hdescent : baseEnd_6036361 < baseStart_6036361 := by decide
  rcases family_descends (prefixWord ++ tailWord_6036361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6036428 : List Nat := [2, 2, 1, 4, 1, 1, 3, 1, 2, 4, 2]
def baseStart_6036428 : Nat := 118140960795 + 6036428 * 2 ^ 59
def prefixEnd_6036428 : Nat := 4983230072969 + 3 ^ 40 * 6036428 * 2
def baseEnd_6036428 : Nat := 3099589000258613681388979

theorem tailTrace_6036428 : CollatzResearch.WordTrace tailWord_6036428 prefixEnd_6036428 3099589000258613681388979 := by
  unfold tailWord_6036428
  simp only [CollatzResearch.WordTrace]
  refine ⟨110083308287529885335098969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146777744383373180446798625 110083308287529885335098969)
  ·
    refine ⟨82562481215647414001324227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110083308287529885335098969 82562481215647414001324227)
    ·
      refine ⟨123843721823471121001986341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82562481215647414001324227 123843721823471121001986341)
      ·
        refine ⟨23220697841900835187872439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 123843721823471121001986341 23220697841900835187872439)
        ·
          refine ⟨34831046762851252781808659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23220697841900835187872439 34831046762851252781808659)
          ·
            refine ⟨52246570144276879172712989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34831046762851252781808659 52246570144276879172712989)
            ·
              refine ⟨19592463804103829689767371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52246570144276879172712989 19592463804103829689767371)
              ·
                refine ⟨29388695706155744534651057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19592463804103829689767371 29388695706155744534651057)
                ·
                  refine ⟨22041521779616808400988293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29388695706155744534651057 22041521779616808400988293)
                  ·
                    refine ⟨4132785333678151575185305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22041521779616808400988293 4132785333678151575185305)
                    ·
                      refine ⟨3099589000258613681388979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4132785333678151575185305 3099589000258613681388979)
                      ·
                        rfl

theorem cell23_6036428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 3, 1, 2, 4, 2].length) (baseStart_6036428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6036428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6036428 prefixEnd_6036428 := by exact prefixLift 6036428
  have htrace : WordTrace (prefixWord ++ tailWord_6036428) baseStart_6036428 baseEnd_6036428 := by
    simpa [prefixWord, tailWord_6036428, baseEnd_6036428] using wordTrace_append hprefix tailTrace_6036428
  have hstable : (prefixWord ++ tailWord_6036428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6036428).length < 2 ^ (prefixWord ++ tailWord_6036428).sum := by decide
  have hdescent : baseEnd_6036428 < baseStart_6036428 := by decide
  rcases family_descends (prefixWord ++ tailWord_6036428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6036445 : List Nat := [1, 4, 3, 1, 2, 3, 1, 1, 2, 1, 4]
def baseStart_6036445 : Nat := 118140960795 + 6036445 * 2 ^ 59
def prefixEnd_6036445 : Nat := 4983230072969 + 3 ^ 40 * 6036445 * 2
def baseEnd_6036445 : Nat := 3099597729429740114876401

theorem tailTrace_6036445 : CollatzResearch.WordTrace tailWord_6036445 prefixEnd_6036445 3099597729429740114876401 := by
  unfold tailWord_6036445
  simp only [CollatzResearch.WordTrace]
  refine ⟨220167236615998182573566789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146778157743998788382377859 220167236615998182573566789)
  ·
    refine ⟨41281356865499659232543773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 220167236615998182573566789 41281356865499659232543773)
    ·
      refine ⟨15480508824562372212203915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41281356865499659232543773 15480508824562372212203915)
      ·
        refine ⟨23220763236843558318305873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15480508824562372212203915 23220763236843558318305873)
        ·
          refine ⟨17415572427632668738729405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23220763236843558318305873 17415572427632668738729405)
          ·
            refine ⟨6530839660362250777023527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17415572427632668738729405 6530839660362250777023527)
            ·
              refine ⟨9796259490543376165535291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6530839660362250777023527 9796259490543376165535291)
              ·
                refine ⟨14694389235815064248302937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9796259490543376165535291 14694389235815064248302937)
                ·
                  refine ⟨11020791926861298186227203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14694389235815064248302937 11020791926861298186227203)
                  ·
                    refine ⟨16531187890291947279340805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11020791926861298186227203 16531187890291947279340805)
                    ·
                      refine ⟨3099597729429740114876401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16531187890291947279340805 3099597729429740114876401)
                      ·
                        rfl

theorem cell23_6036445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 3, 1, 1, 2, 1, 4].length) (baseStart_6036445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6036445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6036445 prefixEnd_6036445 := by exact prefixLift 6036445
  have htrace : WordTrace (prefixWord ++ tailWord_6036445) baseStart_6036445 baseEnd_6036445 := by
    simpa [prefixWord, tailWord_6036445, baseEnd_6036445] using wordTrace_append hprefix tailTrace_6036445
  have hstable : (prefixWord ++ tailWord_6036445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6036445).length < 2 ^ (prefixWord ++ tailWord_6036445).sum := by decide
  have hdescent : baseEnd_6036445 < baseStart_6036445 := by decide
  rcases family_descends (prefixWord ++ tailWord_6036445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6036455 : List Nat := [1, 1, 5, 2, 2, 1, 1, 5, 1, 4]
def baseStart_6036455 : Nat := 118140960795 + 6036455 * 2 ^ 59
def prefixEnd_6036455 : Nat := 4983230072969 + 3 ^ 40 * 6036455 * 2
def baseEnd_6036455 : Nat := 1033200954745428358583785

theorem tailTrace_6036455 : CollatzResearch.WordTrace tailWord_6036455 prefixEnd_6036455 1033200954745428358583785 := by
  unfold tailWord_6036455
  simp only [CollatzResearch.WordTrace]
  refine ⟨220167601345961954281430819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146778400897307969520953879 220167601345961954281430819)
  ·
    refine ⟨330251402018942931422146229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220167601345961954281430819 330251402018942931422146229)
    ·
      refine ⟨30961068939275899820826209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 330251402018942931422146229 30961068939275899820826209)
      ·
        refine ⟨23220801704456924865619657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30961068939275899820826209 23220801704456924865619657)
        ·
          refine ⟨17415601278342693649214743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23220801704456924865619657 17415601278342693649214743)
          ·
            refine ⟨26123401917514040473822115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17415601278342693649214743 26123401917514040473822115)
            ·
              refine ⟨39185102876271060710733173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26123401917514040473822115 39185102876271060710733173)
              ·
                refine ⟨3673603394650411941631235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 39185102876271060710733173 3673603394650411941631235)
                ·
                  refine ⟨5510405091975617912446853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3673603394650411941631235 5510405091975617912446853)
                  ·
                    refine ⟨1033200954745428358583785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5510405091975617912446853 1033200954745428358583785)
                    ·
                      rfl

theorem cell23_6036455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 5, 1, 4].length) (baseStart_6036455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6036455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6036455 prefixEnd_6036455 := by exact prefixLift 6036455
  have htrace : WordTrace (prefixWord ++ tailWord_6036455) baseStart_6036455 baseEnd_6036455 := by
    simpa [prefixWord, tailWord_6036455, baseEnd_6036455] using wordTrace_append hprefix tailTrace_6036455
  have hstable : (prefixWord ++ tailWord_6036455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6036455).length < 2 ^ (prefixWord ++ tailWord_6036455).sum := by decide
  have hdescent : baseEnd_6036455 < baseStart_6036455 := by decide
  rcases family_descends (prefixWord ++ tailWord_6036455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6036488 : List Nat := [2, 1, 3, 2, 1, 3, 1, 2, 1, 5, 2]
def baseStart_6036488 : Nat := 118140960795 + 6036488 * 2 ^ 59
def prefixEnd_6036488 : Nat := 4983230072969 + 3 ^ 40 * 6036488 * 2
def baseEnd_6036488 : Nat := 3099619809097883446638703

theorem tailTrace_6036488 : CollatzResearch.WordTrace tailWord_6036488 prefixEnd_6036488 3099619809097883446638703 := by
  unfold tailWord_6036488
  simp only [CollatzResearch.WordTrace]
  refine ⟨110084402477421200458691059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146779203303228267278254745 110084402477421200458691059)
  ·
    refine ⟨165126603716131800688036589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110084402477421200458691059 165126603716131800688036589)
    ·
      refine ⟨61922476393549425258013721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 165126603716131800688036589 61922476393549425258013721)
      ·
        refine ⟨46441857295162068943510291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61922476393549425258013721 46441857295162068943510291)
        ·
          refine ⟨69662785942743103415265437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46441857295162068943510291 69662785942743103415265437)
          ·
            refine ⟨26123544728528663780724539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69662785942743103415265437 26123544728528663780724539)
            ·
              refine ⟨39185317092792995671086809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26123544728528663780724539 39185317092792995671086809)
              ·
                refine ⟨29388987819594746753315107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39185317092792995671086809 29388987819594746753315107)
                ·
                  refine ⟨44083481729392120129972661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29388987819594746753315107 44083481729392120129972661)
                  ·
                    refine ⟨4132826412130511262184937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 44083481729392120129972661 4132826412130511262184937)
                    ·
                      refine ⟨3099619809097883446638703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4132826412130511262184937 3099619809097883446638703)
                      ·
                        rfl

theorem cell23_6036488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 2, 1, 5, 2].length) (baseStart_6036488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6036488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6036488 prefixEnd_6036488 := by exact prefixLift 6036488
  have htrace : WordTrace (prefixWord ++ tailWord_6036488) baseStart_6036488 baseEnd_6036488 := by
    simpa [prefixWord, tailWord_6036488, baseEnd_6036488] using wordTrace_append hprefix tailTrace_6036488
  have hstable : (prefixWord ++ tailWord_6036488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6036488).length < 2 ^ (prefixWord ++ tailWord_6036488).sum := by decide
  have hdescent : baseEnd_6036488 < baseStart_6036488 := by decide
  rcases family_descends (prefixWord ++ tailWord_6036488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6036522 : List Nat := [3, 1, 4, 1, 3, 1, 1, 2, 2, 3, 2]
def baseStart_6036522 : Nat := 118140960795 + 6036522 * 2 ^ 59
def prefixEnd_6036522 : Nat := 4983230072969 + 3 ^ 40 * 6036522 * 2
def baseEnd_6036522 : Nat := 3099637267440136313613547

theorem tailTrace_6036522 : CollatzResearch.WordTrace tailWord_6036522 prefixEnd_6036522 3099637267440136313613547 := by
  unfold tailWord_6036522
  simp only [CollatzResearch.WordTrace]
  refine ⟨55042511259179806181029955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146780030024479483149413213 55042511259179806181029955)
  ·
    refine ⟨82563766888769709271544933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55042511259179806181029955 82563766888769709271544933)
    ·
      refine ⟨15480706291644320488414675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 82563766888769709271544933 15480706291644320488414675)
      ·
        refine ⟨23221059437466480732622013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15480706291644320488414675 23221059437466480732622013)
        ·
          refine ⟨8707897289049930274733255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23221059437466480732622013 8707897289049930274733255)
          ·
            refine ⟨13061845933574895412099883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8707897289049930274733255 13061845933574895412099883)
            ·
              refine ⟨19592768900362343118149825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13061845933574895412099883 19592768900362343118149825)
              ·
                refine ⟨14694576675271757338612369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19592768900362343118149825 14694576675271757338612369)
                ·
                  refine ⟨11020932506453818003959277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14694576675271757338612369 11020932506453818003959277)
                  ·
                    refine ⟨4132849689920181751484729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11020932506453818003959277 4132849689920181751484729)
                    ·
                      refine ⟨3099637267440136313613547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4132849689920181751484729 3099637267440136313613547)
                      ·
                        rfl

theorem cell23_6036522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 1, 2, 2, 3, 2].length) (baseStart_6036522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6036522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6036522 prefixEnd_6036522 := by exact prefixLift 6036522
  have htrace : WordTrace (prefixWord ++ tailWord_6036522) baseStart_6036522 baseEnd_6036522 := by
    simpa [prefixWord, tailWord_6036522, baseEnd_6036522] using wordTrace_append hprefix tailTrace_6036522
  have hstable : (prefixWord ++ tailWord_6036522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6036522).length < 2 ^ (prefixWord ++ tailWord_6036522).sum := by decide
  have hdescent : baseEnd_6036522 < baseStart_6036522 := by decide
  rcases family_descends (prefixWord ++ tailWord_6036522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6036528 : List Nat := [2, 1, 1, 1, 2, 4, 2, 4, 2, 4]
def baseStart_6036528 : Nat := 118140960795 + 6036528 * 2 ^ 59
def prefixEnd_6036528 : Nat := 4983230072969 + 3 ^ 40 * 6036528 * 2
def baseEnd_6036528 : Nat := 1033213449441354430046173

theorem tailTrace_6036528 : CollatzResearch.WordTrace tailWord_6036528 prefixEnd_6036528 1033213449441354430046173 := by
  unfold tailWord_6036528
  simp only [CollatzResearch.WordTrace]
  refine ⟨110085131937348743874419119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146780175916464991832558825 110085131937348743874419119)
  ·
    refine ⟨165127697906023115811628679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110085131937348743874419119 165127697906023115811628679)
    ·
      refine ⟨247691546859034673717443019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165127697906023115811628679 247691546859034673717443019)
      ·
        refine ⟨371537320288552010576164529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 247691546859034673717443019 371537320288552010576164529)
        ·
          refine ⟨278652990216414007932123397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 371537320288552010576164529 278652990216414007932123397)
          ·
            refine ⟨52247435665577626487273137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 278652990216414007932123397 52247435665577626487273137)
            ·
              refine ⟨39185576749183219865454853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52247435665577626487273137 39185576749183219865454853)
              ·
                refine ⟨7347295640471853724772785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39185576749183219865454853 7347295640471853724772785)
                ·
                  refine ⟨5510471730353890293579589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7347295640471853724772785 5510471730353890293579589)
                  ·
                    refine ⟨1033213449441354430046173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5510471730353890293579589 1033213449441354430046173)
                    ·
                      rfl

theorem cell23_6036528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 4, 2, 4].length) (baseStart_6036528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6036528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6036528 prefixEnd_6036528 := by exact prefixLift 6036528
  have htrace : WordTrace (prefixWord ++ tailWord_6036528) baseStart_6036528 baseEnd_6036528 := by
    simpa [prefixWord, tailWord_6036528, baseEnd_6036528] using wordTrace_append hprefix tailTrace_6036528
  have hstable : (prefixWord ++ tailWord_6036528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6036528).length < 2 ^ (prefixWord ++ tailWord_6036528).sum := by decide
  have hdescent : baseEnd_6036528 < baseStart_6036528 := by decide
  rcases family_descends (prefixWord ++ tailWord_6036528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6036541 : List Nat := [1, 4, 1, 3, 1, 2, 1, 10]
def baseStart_6036541 : Nat := 118140960795 + 6036541 * 2 ^ 59
def prefixEnd_6036541 : Nat := 4983230072969 + 3 ^ 40 * 6036541 * 2
def baseEnd_6036541 : Nat := 114801741613798953306517

theorem tailTrace_6036541 : CollatzResearch.WordTrace tailWord_6036541 prefixEnd_6036541 114801741613798953306517 := by
  unfold tailWord_6036541
  simp only [CollatzResearch.WordTrace]
  refine ⟨220170738023650390969061477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146780492015766927312707651 220170738023650390969061477)
  ·
    refine ⟨41282013379434448306699027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 220170738023650390969061477 41282013379434448306699027)
    ·
      refine ⟨61923020069151672460048541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41282013379434448306699027 61923020069151672460048541)
      ·
        refine ⟨23221132525931877172518203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61923020069151672460048541 23221132525931877172518203)
        ·
          refine ⟨34831698788897815758777305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23221132525931877172518203 34831698788897815758777305)
          ·
            refine ⟨26123774091673361819082979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34831698788897815758777305 26123774091673361819082979)
            ·
              refine ⟨39185661137510042728624469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26123774091673361819082979 39185661137510042728624469)
              ·
                refine ⟨114801741613798953306517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 39185661137510042728624469 114801741613798953306517)
                ·
                  rfl

theorem cell23_6036541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 10].length) (baseStart_6036541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6036541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6036541 prefixEnd_6036541 := by exact prefixLift 6036541
  have htrace : WordTrace (prefixWord ++ tailWord_6036541) baseStart_6036541 baseEnd_6036541 := by
    simpa [prefixWord, tailWord_6036541, baseEnd_6036541] using wordTrace_append hprefix tailTrace_6036541
  have hstable : (prefixWord ++ tailWord_6036541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6036541).length < 2 ^ (prefixWord ++ tailWord_6036541).sum := by decide
  have hdescent : baseEnd_6036541 < baseStart_6036541 := by decide
  rcases family_descends (prefixWord ++ tailWord_6036541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6036568 : List Nat := [2, 1, 2, 2, 1, 3, 3, 2, 1, 3, 3]
def baseStart_6036568 : Nat := 118140960795 + 6036568 * 2 ^ 59
def prefixEnd_6036568 : Nat := 4983230072969 + 3 ^ 40 * 6036568 * 2
def baseEnd_6036568 : Nat := 3099660887550243133638335

theorem tailTrace_6036568 : CollatzResearch.WordTrace tailWord_6036568 prefixEnd_6036568 3099660887550243133638335 := by
  unfold tailWord_6036568
  simp only [CollatzResearch.WordTrace]
  refine ⟨110085861397276287290147179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146781148529701716386862905 110085861397276287290147179)
  ·
    refine ⟨165128792095914430935220769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110085861397276287290147179 165128792095914430935220769)
    ·
      refine ⟨123846594071935823201415577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 165128792095914430935220769 123846594071935823201415577)
      ·
        refine ⟨92884945553951867401061683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123846594071935823201415577 92884945553951867401061683)
        ·
          refine ⟨139327418330927801101592525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92884945553951867401061683 139327418330927801101592525)
          ·
            refine ⟨52247781874097925413097197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 139327418330927801101592525 52247781874097925413097197)
            ·
              refine ⟨19592918202786722029911449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52247781874097925413097197 19592918202786722029911449)
              ·
                refine ⟨14694688652090041522433587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19592918202786722029911449 14694688652090041522433587)
                ·
                  refine ⟨22042032978135062283650381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14694688652090041522433587 22042032978135062283650381)
                  ·
                    refine ⟨8265762366800648356368893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22042032978135062283650381 8265762366800648356368893)
                    ·
                      refine ⟨3099660887550243133638335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8265762366800648356368893 3099660887550243133638335)
                      ·
                        rfl

theorem cell23_6036568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 3, 2, 1, 3, 3].length) (baseStart_6036568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6036568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6036568 prefixEnd_6036568 := by exact prefixLift 6036568
  have htrace : WordTrace (prefixWord ++ tailWord_6036568) baseStart_6036568 baseEnd_6036568 := by
    simpa [prefixWord, tailWord_6036568, baseEnd_6036568] using wordTrace_append hprefix tailTrace_6036568
  have hstable : (prefixWord ++ tailWord_6036568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6036568).length < 2 ^ (prefixWord ++ tailWord_6036568).sum := by decide
  have hdescent : baseEnd_6036568 < baseStart_6036568 := by decide
  rcases family_descends (prefixWord ++ tailWord_6036568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6036572 : List Nat := [2, 2, 4, 1, 1, 1, 5, 1, 1, 2, 3]
def baseStart_6036572 : Nat := 118140960795 + 6036572 * 2 ^ 59
def prefixEnd_6036572 : Nat := 4983230072969 + 3 ^ 40 * 6036572 * 2
def baseEnd_6036572 : Nat := 3099662941472861117988317

theorem tailTrace_6036572 : CollatzResearch.WordTrace tailWord_6036572 prefixEnd_6036572 3099662941472861117988317 := by
  unfold tailWord_6036572
  simp only [CollatzResearch.WordTrace]
  refine ⟨110085934343269041631719985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146781245791025388842293313 110085934343269041631719985)
  ·
    refine ⟨82564450757451781223789989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110085934343269041631719985 82564450757451781223789989)
    ·
      refine ⟨15480834517022208979460623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 82564450757451781223789989 15480834517022208979460623)
      ·
        refine ⟨23221251775533313469190935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15480834517022208979460623 23221251775533313469190935)
        ·
          refine ⟨34831877663299970203786403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23221251775533313469190935 34831877663299970203786403)
          ·
            refine ⟨52247816494949955305679605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34831877663299970203786403 52247816494949955305679605)
            ·
              refine ⟨4898232796401558309907463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 52247816494949955305679605 4898232796401558309907463)
              ·
                refine ⟨7347349194602337464861195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4898232796401558309907463 7347349194602337464861195)
                ·
                  refine ⟨11021023791903506197291793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7347349194602337464861195 11021023791903506197291793)
                  ·
                    refine ⟨8265767843927629647968845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11021023791903506197291793 8265767843927629647968845)
                    ·
                      refine ⟨3099662941472861117988317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8265767843927629647968845 3099662941472861117988317)
                      ·
                        rfl

theorem cell23_6036572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 5, 1, 1, 2, 3].length) (baseStart_6036572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6036572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6036572 prefixEnd_6036572 := by exact prefixLift 6036572
  have htrace : WordTrace (prefixWord ++ tailWord_6036572) baseStart_6036572 baseEnd_6036572 := by
    simpa [prefixWord, tailWord_6036572, baseEnd_6036572] using wordTrace_append hprefix tailTrace_6036572
  have hstable : (prefixWord ++ tailWord_6036572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6036572).length < 2 ^ (prefixWord ++ tailWord_6036572).sum := by decide
  have hdescent : baseEnd_6036572 < baseStart_6036572 := by decide
  rcases family_descends (prefixWord ++ tailWord_6036572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6036585 : List Nat := [1, 2, 1, 1, 1, 6, 1, 4, 2, 1, 3]
def baseStart_6036585 : Nat := 118140960795 + 6036585 * 2 ^ 59
def prefixEnd_6036585 : Nat := 4983230072969 + 3 ^ 40 * 6036585 * 2
def baseEnd_6036585 : Nat := 3099669616721369567125757

theorem tailTrace_6036585 : CollatzResearch.WordTrace tailWord_6036585 prefixEnd_6036585 3099669616721369567125757 := by
  unfold tailWord_6036585
  simp only [CollatzResearch.WordTrace]
  refine ⟨220172342835490986483663209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146781561890327324322442139 220172342835490986483663209)
  ·
    refine ⟨165129257126618239862747407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 220172342835490986483663209 165129257126618239862747407)
    ·
      refine ⟨247693885689927359794121111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165129257126618239862747407 247693885689927359794121111)
      ·
        refine ⟨371540828534891039691181667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 247693885689927359794121111 371540828534891039691181667)
        ·
          refine ⟨557311242802336559536772501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 371540828534891039691181667 557311242802336559536772501)
          ·
            refine ⟨26123964506359526228286211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 557311242802336559536772501 26123964506359526228286211)
            ·
              refine ⟨39185946759539289342429317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26123964506359526228286211 39185946759539289342429317)
              ·
                refine ⟨7347365017413616751705497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39185946759539289342429317 7347365017413616751705497)
                ·
                  refine ⟨5510523763060212563779123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7347365017413616751705497 5510523763060212563779123)
                  ·
                    refine ⟨8265785644590318845668685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5510523763060212563779123 8265785644590318845668685)
                    ·
                      refine ⟨3099669616721369567125757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8265785644590318845668685 3099669616721369567125757)
                      ·
                        rfl

theorem cell23_6036585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 4, 2, 1, 3].length) (baseStart_6036585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6036585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6036585 prefixEnd_6036585 := by exact prefixLift 6036585
  have htrace : WordTrace (prefixWord ++ tailWord_6036585) baseStart_6036585 baseEnd_6036585 := by
    simpa [prefixWord, tailWord_6036585, baseEnd_6036585] using wordTrace_append hprefix tailTrace_6036585
  have hstable : (prefixWord ++ tailWord_6036585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6036585).length < 2 ^ (prefixWord ++ tailWord_6036585).sum := by decide
  have hdescent : baseEnd_6036585 < baseStart_6036585 := by decide
  rcases family_descends (prefixWord ++ tailWord_6036585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6036586 : List Nat := [3, 1, 3, 2, 2, 1, 4, 2, 1, 2, 2]
def baseStart_6036586 : Nat := 118140960795 + 6036586 * 2 ^ 59
def prefixEnd_6036586 : Nat := 4983230072969 + 3 ^ 40 * 6036586 * 2
def baseEnd_6036586 : Nat := 3099670130202024063213253

theorem tailTrace_6036586 : CollatzResearch.WordTrace tailWord_6036586 prefixEnd_6036586 3099670130202024063213253 := by
  unfold tailWord_6036586
  simp only [CollatzResearch.WordTrace]
  refine ⟨55043094827121840913612403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146781586205658242436299741 55043094827121840913612403)
  ·
    refine ⟨82564642240682761370418605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55043094827121840913612403 82564642240682761370418605)
    ·
      refine ⟨30961740840256035513906977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82564642240682761370418605 30961740840256035513906977)
      ·
        refine ⟨23221305630192026635430233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30961740840256035513906977 23221305630192026635430233)
        ·
          refine ⟨17415979222644019976572675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23221305630192026635430233 17415979222644019976572675)
          ·
            refine ⟨26123968833966029964859013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17415979222644019976572675 26123968833966029964859013)
            ·
              refine ⟨4898244156368630618411065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26123968833966029964859013 4898244156368630618411065)
              ·
                refine ⟨3673683117276472963808299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4898244156368630618411065 3673683117276472963808299)
                ·
                  refine ⟨5510524675914709445712449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3673683117276472963808299 5510524675914709445712449)
                  ·
                    refine ⟨4132893506936032084284337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5510524675914709445712449 4132893506936032084284337)
                    ·
                      refine ⟨3099670130202024063213253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4132893506936032084284337 3099670130202024063213253)
                      ·
                        rfl

theorem cell23_6036586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 4, 2, 1, 2, 2].length) (baseStart_6036586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6036586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6036586 prefixEnd_6036586 := by exact prefixLift 6036586
  have htrace : WordTrace (prefixWord ++ tailWord_6036586) baseStart_6036586 baseEnd_6036586 := by
    simpa [prefixWord, tailWord_6036586, baseEnd_6036586] using wordTrace_append hprefix tailTrace_6036586
  have hstable : (prefixWord ++ tailWord_6036586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6036586).length < 2 ^ (prefixWord ++ tailWord_6036586).sum := by decide
  have hdescent : baseEnd_6036586 < baseStart_6036586 := by decide
  rcases family_descends (prefixWord ++ tailWord_6036586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6036591 : List Nat := [1, 1, 2, 1, 3, 3, 1, 1, 1, 5, 4]
def baseStart_6036591 : Nat := 118140960795 + 6036591 * 2 ^ 59
def prefixEnd_6036591 : Nat := 4983230072969 + 3 ^ 40 * 6036591 * 2
def baseEnd_6036591 : Nat := 3099672697605296543650729

theorem tailTrace_6036591 : CollatzResearch.WordTrace tailWord_6036591 prefixEnd_6036591 3099672697605296543650729 := by
  unfold tailWord_6036591
  simp only [CollatzResearch.WordTrace]
  refine ⟨220172561673469249508381627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146781707782312833005587751 220172561673469249508381627)
  ·
    refine ⟨330258842510203874262572441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220172561673469249508381627 330258842510203874262572441)
    ·
      refine ⟨247694131882652905696929331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 330258842510203874262572441 247694131882652905696929331)
      ·
        refine ⟨371541197823979358545393997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 247694131882652905696929331 371541197823979358545393997)
        ·
          refine ⟨139327949183992259454522749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 371541197823979358545393997 139327949183992259454522749)
          ·
            refine ⟨52247980943997097295446031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 139327949183992259454522749 52247980943997097295446031)
            ·
              refine ⟨78371971415995645943169047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52247980943997097295446031 78371971415995645943169047)
              ·
                refine ⟨117557957123993468914753571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78371971415995645943169047 117557957123993468914753571)
                ·
                  refine ⟨176336935685990203372130357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 117557957123993468914753571 176336935685990203372130357)
                  ·
                    refine ⟨16531587720561581566137221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 176336935685990203372130357 16531587720561581566137221)
                    ·
                      refine ⟨3099672697605296543650729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16531587720561581566137221 3099672697605296543650729)
                      ·
                        rfl

theorem cell23_6036591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 1, 1, 5, 4].length) (baseStart_6036591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6036591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6036591 prefixEnd_6036591 := by exact prefixLift 6036591
  have htrace : WordTrace (prefixWord ++ tailWord_6036591) baseStart_6036591 baseEnd_6036591 := by
    simpa [prefixWord, tailWord_6036591, baseEnd_6036591] using wordTrace_append hprefix tailTrace_6036591
  have hstable : (prefixWord ++ tailWord_6036591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6036591).length < 2 ^ (prefixWord ++ tailWord_6036591).sum := by decide
  have hdescent : baseEnd_6036591 < baseStart_6036591 := by decide
  rcases family_descends (prefixWord ++ tailWord_6036591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6036681 : List Nat := [1, 2, 1, 1, 2, 1, 1, 2, 2, 2, 8]
def baseStart_6036681 : Nat := 118140960795 + 6036681 * 2 ^ 59
def prefixEnd_6036681 : Nat := 4983230072969 + 3 ^ 40 * 6036681 * 2
def baseEnd_6036681 : Nat := 3099718910864201191525315

theorem tailTrace_6036681 : CollatzResearch.WordTrace tailWord_6036681 prefixEnd_6036681 3099718910864201191525315 := by
  unfold tailWord_6036681
  simp only [CollatzResearch.WordTrace]
  refine ⟨220175844243143194879157897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146783896162095463252771931 220175844243143194879157897)
  ·
    refine ⟨165131883182357396159368423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 220175844243143194879157897 165131883182357396159368423)
    ·
      refine ⟨247697824773536094239052635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165131883182357396159368423 247697824773536094239052635)
      ·
        refine ⟨371546737160304141358578953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 247697824773536094239052635 371546737160304141358578953)
        ·
          refine ⟨278660052870228106018934215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 371546737160304141358578953 278660052870228106018934215)
          ·
            refine ⟨417990079305342159028401323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 278660052870228106018934215 417990079305342159028401323)
            ·
              refine ⟨626985118958013238542601985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 417990079305342159028401323 626985118958013238542601985)
              ·
                refine ⟨470238839218509928906951489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 626985118958013238542601985 470238839218509928906951489)
                ·
                  refine ⟨352679129413882446680213617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 470238839218509928906951489 352679129413882446680213617)
                  ·
                    refine ⟨264509347060411835010160213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 352679129413882446680213617 264509347060411835010160213)
                    ·
                      refine ⟨3099718910864201191525315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 264509347060411835010160213 3099718910864201191525315)
                      ·
                        rfl

theorem cell23_6036681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 2, 2, 2, 8].length) (baseStart_6036681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6036681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6036681 prefixEnd_6036681 := by exact prefixLift 6036681
  have htrace : WordTrace (prefixWord ++ tailWord_6036681) baseStart_6036681 baseEnd_6036681 := by
    simpa [prefixWord, tailWord_6036681, baseEnd_6036681] using wordTrace_append hprefix tailTrace_6036681
  have hstable : (prefixWord ++ tailWord_6036681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6036681).length < 2 ^ (prefixWord ++ tailWord_6036681).sum := by decide
  have hdescent : baseEnd_6036681 < baseStart_6036681 := by decide
  rcases family_descends (prefixWord ++ tailWord_6036681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6036682 : List Nat := [3, 1, 2, 1, 3, 4, 1, 3, 5]
def baseStart_6036682 : Nat := 118140960795 + 6036682 * 2 ^ 59
def prefixEnd_6036682 : Nat := 4983230072969 + 3 ^ 40 * 6036682 * 2
def baseEnd_6036682 : Nat := 344413269371650631956979

theorem tailTrace_6036682 : CollatzResearch.WordTrace tailWord_6036682 prefixEnd_6036682 344413269371650631956979 := by
  unfold tailWord_6036682
  simp only [CollatzResearch.WordTrace]
  refine ⟨55043970179034893012486075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146783920477426381366629533 55043970179034893012486075)
  ·
    refine ⟨82565955268552339518729113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55043970179034893012486075 82565955268552339518729113)
    ·
      refine ⟨61924466451414254639046835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82565955268552339518729113 61924466451414254639046835)
      ·
        refine ⟨92886699677121381958570253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61924466451414254639046835 92886699677121381958570253)
        ·
          refine ⟨34832512378920518234463845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 92886699677121381958570253 34832512378920518234463845)
          ·
            refine ⟨6531096071047597168961971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34832512378920518234463845 6531096071047597168961971)
            ·
              refine ⟨9796644106571395753442957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6531096071047597168961971 9796644106571395753442957)
              ·
                refine ⟨3673741539964273407541109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9796644106571395753442957 3673741539964273407541109)
                ·
                  refine ⟨344413269371650631956979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3673741539964273407541109 344413269371650631956979)
                  ·
                    rfl

theorem cell23_6036682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 4, 1, 3, 5].length) (baseStart_6036682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6036682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6036682 prefixEnd_6036682 := by exact prefixLift 6036682
  have htrace : WordTrace (prefixWord ++ tailWord_6036682) baseStart_6036682 baseEnd_6036682 := by
    simpa [prefixWord, tailWord_6036682, baseEnd_6036682] using wordTrace_append hprefix tailTrace_6036682
  have hstable : (prefixWord ++ tailWord_6036682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6036682).length < 2 ^ (prefixWord ++ tailWord_6036682).sum := by decide
  have hdescent : baseEnd_6036682 < baseStart_6036682 := by decide
  rcases family_descends (prefixWord ++ tailWord_6036682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6036691 : List Nat := [1, 1, 1, 2, 1, 1, 1, 4, 1, 10]
def baseStart_6036691 : Nat := 118140960795 + 6036691 * 2 ^ 59
def prefixEnd_6036691 : Nat := 4983230072969 + 3 ^ 40 * 6036691 * 2
def baseEnd_6036691 : Nat := 1033241348556915384133423

theorem tailTrace_6036691 : CollatzResearch.WordTrace tailWord_6036691 prefixEnd_6036691 1033241348556915384133423 := by
  unfold tailWord_6036691
  simp only [CollatzResearch.WordTrace]
  refine ⟨220176208973106966587021927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146784139315404644391347951 220176208973106966587021927)
  ·
    refine ⟨330264313459660449880532891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220176208973106966587021927 330264313459660449880532891)
    ·
      refine ⟨495396470189490674820799337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 330264313459660449880532891 495396470189490674820799337)
      ·
        refine ⟨371547352642118006115599503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 495396470189490674820799337 371547352642118006115599503)
        ·
          refine ⟨557321028963177009173399255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 371547352642118006115599503 557321028963177009173399255)
          ·
            refine ⟨835981543444765513760098883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 557321028963177009173399255 835981543444765513760098883)
            ·
              refine ⟨1253972315167148270640148325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 835981543444765513760098883 1253972315167148270640148325)
              ·
                refine ⟨235119809093840300745027811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1253972315167148270640148325 235119809093840300745027811)
                ·
                  refine ⟨352679713640760451117541717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 235119809093840300745027811 352679713640760451117541717)
                  ·
                    refine ⟨1033241348556915384133423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 352679713640760451117541717 1033241348556915384133423)
                    ·
                      rfl

theorem cell23_6036691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 4, 1, 10].length) (baseStart_6036691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6036691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6036691 prefixEnd_6036691 := by exact prefixLift 6036691
  have htrace : WordTrace (prefixWord ++ tailWord_6036691) baseStart_6036691 baseEnd_6036691 := by
    simpa [prefixWord, tailWord_6036691, baseEnd_6036691] using wordTrace_append hprefix tailTrace_6036691
  have hstable : (prefixWord ++ tailWord_6036691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6036691).length < 2 ^ (prefixWord ++ tailWord_6036691).sum := by decide
  have hdescent : baseEnd_6036691 < baseStart_6036691 := by decide
  rcases family_descends (prefixWord ++ tailWord_6036691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6036732 : List Nat := [2, 2, 2, 1, 5, 1, 2, 1, 2, 1, 4]
def baseStart_6036732 : Nat := 118140960795 + 6036732 * 2 ^ 59
def prefixEnd_6036732 : Nat := 4983230072969 + 3 ^ 40 * 6036732 * 2
def baseEnd_6036732 : Nat := 3099745098377580491987581

theorem tailTrace_6036732 : CollatzResearch.WordTrace tailWord_6036732 prefixEnd_6036732 3099745098377580491987581 := by
  unfold tailWord_6036732
  simp only [CollatzResearch.WordTrace]
  refine ⟨110088852182979215294632225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146785136243972287059509633 110088852182979215294632225)
  ·
    refine ⟨82566639137234411470974169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110088852182979215294632225 82566639137234411470974169)
    ·
      refine ⟨61924979352925808603230627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82566639137234411470974169 61924979352925808603230627)
      ·
        refine ⟨92887469029388712904845941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61924979352925808603230627 92887469029388712904845941)
        ·
          refine ⟨8708200221505191834829307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 92887469029388712904845941 8708200221505191834829307)
          ·
            refine ⟨13062300332257787752243961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8708200221505191834829307 13062300332257787752243961)
            ·
              refine ⟨9796725249193340814182971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13062300332257787752243961 9796725249193340814182971)
              ·
                refine ⟨14695087873790011221274457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9796725249193340814182971 14695087873790011221274457)
                ·
                  refine ⟨11021315905342508415955843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14695087873790011221274457 11021315905342508415955843)
                  ·
                    refine ⟨16531973858013762623933765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11021315905342508415955843 16531973858013762623933765)
                    ·
                      refine ⟨3099745098377580491987581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16531973858013762623933765 3099745098377580491987581)
                      ·
                        rfl

theorem cell23_6036732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 2, 1, 2, 1, 4].length) (baseStart_6036732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6036732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6036732 prefixEnd_6036732 := by exact prefixLift 6036732
  have htrace : WordTrace (prefixWord ++ tailWord_6036732) baseStart_6036732 baseEnd_6036732 := by
    simpa [prefixWord, tailWord_6036732, baseEnd_6036732] using wordTrace_append hprefix tailTrace_6036732
  have hstable : (prefixWord ++ tailWord_6036732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6036732).length < 2 ^ (prefixWord ++ tailWord_6036732).sum := by decide
  have hdescent : baseEnd_6036732 < baseStart_6036732 := by decide
  rcases family_descends (prefixWord ++ tailWord_6036732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6036735 : List Nat := [1, 1, 2, 2, 1, 5, 1, 3, 2, 2, 3]
def baseStart_6036735 : Nat := 118140960795 + 6036735 * 2 ^ 59
def prefixEnd_6036735 : Nat := 4983230072969 + 3 ^ 40 * 6036735 * 2
def baseEnd_6036735 : Nat := 3099746638819543980250067

theorem tailTrace_6036735 : CollatzResearch.WordTrace tailWord_6036735 prefixEnd_6036735 3099746638819543980250067 := by
  unfold tailWord_6036735
  simp only [CollatzResearch.WordTrace]
  refine ⟨220177813784947562101623659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146785209189965041401082439 220177813784947562101623659)
  ·
    refine ⟨330266720677421343152435489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220177813784947562101623659 330266720677421343152435489)
    ·
      refine ⟨247700040508066007364326617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 330266720677421343152435489 247700040508066007364326617)
      ·
        refine ⟨185775030381049505523244963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 247700040508066007364326617 185775030381049505523244963)
        ·
          refine ⟨278662545571574258284867445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 185775030381049505523244963 278662545571574258284867445)
          ·
            refine ⟨26124613647335086714206323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 278662545571574258284867445 26124613647335086714206323)
            ·
              refine ⟨39186920471002630071309485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26124613647335086714206323 39186920471002630071309485)
              ·
                refine ⟨14695095176625986276741057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39186920471002630071309485 14695095176625986276741057)
                ·
                  refine ⟨11021321382469489707555793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14695095176625986276741057 11021321382469489707555793)
                  ·
                    refine ⟨8265991036852117280666845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11021321382469489707555793 8265991036852117280666845)
                    ·
                      refine ⟨3099746638819543980250067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8265991036852117280666845 3099746638819543980250067)
                      ·
                        rfl

theorem cell23_6036735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 3, 2, 2, 3].length) (baseStart_6036735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6036735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6036735 prefixEnd_6036735 := by exact prefixLift 6036735
  have htrace : WordTrace (prefixWord ++ tailWord_6036735) baseStart_6036735 baseEnd_6036735 := by
    simpa [prefixWord, tailWord_6036735, baseEnd_6036735] using wordTrace_append hprefix tailTrace_6036735
  have hstable : (prefixWord ++ tailWord_6036735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6036735).length < 2 ^ (prefixWord ++ tailWord_6036735).sum := by decide
  have hdescent : baseEnd_6036735 < baseStart_6036735 := by decide
  rcases family_descends (prefixWord ++ tailWord_6036735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6036766 : List Nat := [4, 3, 2, 1, 2, 1, 1, 1, 2, 4, 2]
def baseStart_6036766 : Nat := 118140960795 + 6036766 * 2 ^ 59
def prefixEnd_6036766 : Nat := 4983230072969 + 3 ^ 40 * 6036766 * 2
def baseEnd_6036766 : Nat := 3099762556719833358962425

theorem tailTrace_6036766 : CollatzResearch.WordTrace tailWord_6036766 prefixEnd_6036766 3099762556719833358962425 := by
  unfold tailWord_6036766
  simp only [CollatzResearch.WordTrace]
  refine ⟨27522368055979406799500269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 146785962965223502930668101 27522368055979406799500269)
  ·
    refine ⟨10320888020992277549812601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27522368055979406799500269 10320888020992277549812601)
    ·
      refine ⟨7740666015744208162359451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10320888020992277549812601 7740666015744208162359451)
      ·
        refine ⟨11610999023616312243539177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7740666015744208162359451 11610999023616312243539177)
        ·
          refine ⟨8708249267712234182654383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11610999023616312243539177 8708249267712234182654383)
          ·
            refine ⟨13062373901568351273981575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8708249267712234182654383 13062373901568351273981575)
            ·
              refine ⟨19593560852352526910972363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13062373901568351273981575 19593560852352526910972363)
              ·
                refine ⟨29390341278528790366458545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19593560852352526910972363 29390341278528790366458545)
                ·
                  refine ⟨22042755958896592774843909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29390341278528790366458545 22042755958896592774843909)
                  ·
                    refine ⟨4133016742293111145283233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22042755958896592774843909 4133016742293111145283233)
                    ·
                      refine ⟨3099762556719833358962425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4133016742293111145283233 3099762556719833358962425)
                      ·
                        rfl

theorem cell23_6036766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 1, 1, 2, 4, 2].length) (baseStart_6036766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6036766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6036766 prefixEnd_6036766 := by exact prefixLift 6036766
  have htrace : WordTrace (prefixWord ++ tailWord_6036766) baseStart_6036766 baseEnd_6036766 := by
    simpa [prefixWord, tailWord_6036766, baseEnd_6036766] using wordTrace_append hprefix tailTrace_6036766
  have hstable : (prefixWord ++ tailWord_6036766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6036766).length < 2 ^ (prefixWord ++ tailWord_6036766).sum := by decide
  have hdescent : baseEnd_6036766 < baseStart_6036766 := by decide
  rcases family_descends (prefixWord ++ tailWord_6036766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6036785 : List Nat := [1, 2, 2, 3, 3, 1, 2, 1, 3, 5]
def baseStart_6036785 : Nat := 118140960795 + 6036785 * 2 ^ 59
def prefixEnd_6036785 : Nat := 4983230072969 + 3 ^ 40 * 6036785 * 2
def baseEnd_6036785 : Nat := 1033257437617422928208279

theorem tailTrace_6036785 : CollatzResearch.WordTrace tailWord_6036785 prefixEnd_6036785 1033257437617422928208279 := by
  unfold tailWord_6036785
  simp only [CollatzResearch.WordTrace]
  refine ⟨220179637434766420640943809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146786424956510947093962539 220179637434766420640943809)
  ·
    refine ⟨165134728076074815480707857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 220179637434766420640943809 165134728076074815480707857)
    ·
      refine ⟨123851046057056111610530893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 165134728076074815480707857 123851046057056111610530893)
      ·
        refine ⟨46444142271396041853949085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 123851046057056111610530893 46444142271396041853949085)
        ·
          refine ⟨17416553351773515695230907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46444142271396041853949085 17416553351773515695230907)
          ·
            refine ⟨26124830027660273542846361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17416553351773515695230907 26124830027660273542846361)
            ·
              refine ⟨19593622520745205157134771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26124830027660273542846361 19593622520745205157134771)
              ·
                refine ⟨29390433781117807735702157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19593622520745205157134771 29390433781117807735702157)
                ·
                  refine ⟨11021412667919177900888309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29390433781117807735702157 11021412667919177900888309)
                  ·
                    refine ⟨1033257437617422928208279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11021412667919177900888309 1033257437617422928208279)
                    ·
                      rfl

theorem cell23_6036785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 2, 1, 3, 5].length) (baseStart_6036785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6036785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6036785 prefixEnd_6036785 := by exact prefixLift 6036785
  have htrace : WordTrace (prefixWord ++ tailWord_6036785) baseStart_6036785 baseEnd_6036785 := by
    simpa [prefixWord, tailWord_6036785, baseEnd_6036785] using wordTrace_append hprefix tailTrace_6036785
  have hstable : (prefixWord ++ tailWord_6036785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6036785).length < 2 ^ (prefixWord ++ tailWord_6036785).sum := by decide
  have hdescent : baseEnd_6036785 < baseStart_6036785 := by decide
  rcases family_descends (prefixWord ++ tailWord_6036785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6036799 : List Nat := [1, 1, 2, 2, 4, 2, 1, 5, 1, 1, 3]
def baseStart_6036799 : Nat := 118140960795 + 6036799 * 2 ^ 59
def prefixEnd_6036799 : Nat := 4983230072969 + 3 ^ 40 * 6036799 * 2
def baseEnd_6036799 : Nat := 3099779501581431729849773

theorem tailTrace_6036799 : CollatzResearch.WordTrace tailWord_6036799 prefixEnd_6036799 3099779501581431729849773 := by
  unfold tailWord_6036799
  simp only [CollatzResearch.WordTrace]
  refine ⟨220180148056715701031953451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146786765371143800687968967 220180148056715701031953451)
  ·
    refine ⟨330270222085073551547930177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220180148056715701031953451 330270222085073551547930177)
    ·
      refine ⟨247702666563805163660947633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 330270222085073551547930177 247702666563805163660947633)
      ·
        refine ⟨185776999922853872745710725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 247702666563805163660947633 185776999922853872745710725)
        ·
          refine ⟨34833187485535101139820761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 185776999922853872745710725 34833187485535101139820761)
          ·
            refine ⟨26124890614151325854865571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34833187485535101139820761 26124890614151325854865571)
            ·
              refine ⟨39187335921226988782298357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26124890614151325854865571 39187335921226988782298357)
              ·
                refine ⟨3673812742615030198340471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 39187335921226988782298357 3673812742615030198340471)
                ·
                  refine ⟨5510719113922545297510707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3673812742615030198340471 5510719113922545297510707)
                  ·
                    refine ⟨8266078670883817946266061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5510719113922545297510707 8266078670883817946266061)
                    ·
                      refine ⟨3099779501581431729849773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8266078670883817946266061 3099779501581431729849773)
                      ·
                        rfl

theorem cell23_6036799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 5, 1, 1, 3].length) (baseStart_6036799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6036799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6036799 prefixEnd_6036799 := by exact prefixLift 6036799
  have htrace : WordTrace (prefixWord ++ tailWord_6036799) baseStart_6036799 baseEnd_6036799 := by
    simpa [prefixWord, tailWord_6036799, baseEnd_6036799] using wordTrace_append hprefix tailTrace_6036799
  have hstable : (prefixWord ++ tailWord_6036799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6036799).length < 2 ^ (prefixWord ++ tailWord_6036799).sum := by decide
  have hdescent : baseEnd_6036799 < baseStart_6036799 := by decide
  rcases family_descends (prefixWord ++ tailWord_6036799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6036805 : List Nat := [1, 3, 1, 1, 1, 2, 1, 2, 1, 8, 2]
def baseStart_6036805 : Nat := 118140960795 + 6036805 * 2 ^ 59
def prefixEnd_6036805 : Nat := 4983230072969 + 3 ^ 40 * 6036805 * 2
def baseEnd_6036805 : Nat := 3099782582465358706374745

theorem tailTrace_6036805 : CollatzResearch.WordTrace tailWord_6036805 prefixEnd_6036805 3099782582465358706374745 := by
  unfold tailWord_6036805
  simp only [CollatzResearch.WordTrace]
  refine ⟨220180366894693964056671869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146786911263129309371114579 220180366894693964056671869)
  ·
    refine ⟨82567637585510236521251951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 220180366894693964056671869 82567637585510236521251951)
    ·
      refine ⟨123851456378265354781877927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82567637585510236521251951 123851456378265354781877927)
      ·
        refine ⟨185777184567398032172816891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123851456378265354781877927 185777184567398032172816891)
        ·
          refine ⟨278665776851097048259225337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 185777184567398032172816891 278665776851097048259225337)
          ·
            refine ⟨208999332638322786194419003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 278665776851097048259225337 208999332638322786194419003)
            ·
              refine ⟨313498998957484179291628505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 208999332638322786194419003 313498998957484179291628505)
              ·
                refine ⟨235124249218113134468721379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 313498998957484179291628505 235124249218113134468721379)
                ·
                  refine ⟨352686373827169701703082069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 235124249218113134468721379 352686373827169701703082069)
                  ·
                    refine ⟨4133043443287144941832993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 352686373827169701703082069 4133043443287144941832993)
                    ·
                      refine ⟨3099782582465358706374745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4133043443287144941832993 3099782582465358706374745)
                      ·
                        rfl

theorem cell23_6036805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 2, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 2, 1, 8, 2].length) (baseStart_6036805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6036805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6036805 prefixEnd_6036805 := by exact prefixLift 6036805
  have htrace : WordTrace (prefixWord ++ tailWord_6036805) baseStart_6036805 baseEnd_6036805 := by
    simpa [prefixWord, tailWord_6036805, baseEnd_6036805] using wordTrace_append hprefix tailTrace_6036805
  have hstable : (prefixWord ++ tailWord_6036805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6036805).length < 2 ^ (prefixWord ++ tailWord_6036805).sum := by decide
  have hdescent : baseEnd_6036805 < baseStart_6036805 := by decide
  rcases family_descends (prefixWord ++ tailWord_6036805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6036825 : List Nat := [1, 2, 1, 2, 2, 2, 2, 1, 5, 2, 3]
def baseStart_6036825 : Nat := 118140960795 + 6036825 * 2 ^ 59
def prefixEnd_6036825 : Nat := 4983230072969 + 3 ^ 40 * 6036825 * 2
def baseEnd_6036825 : Nat := 3099792852078448628124653

theorem tailTrace_6036825 : CollatzResearch.WordTrace tailWord_6036825 prefixEnd_6036825 3099792852078448628124653 := by
  unfold tailWord_6036825
  simp only [CollatzResearch.WordTrace]
  refine ⟨220181096354621507472399929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146787397569747671648266619 220181096354621507472399929)
  ·
    refine ⟨165135822265966130604299947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 220181096354621507472399929 165135822265966130604299947)
    ·
      refine ⟨247703733398949195906449921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165135822265966130604299947 247703733398949195906449921)
      ·
        refine ⟨185777800049211896929837441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 247703733398949195906449921 185777800049211896929837441)
        ·
          refine ⟨139333350036908922697378081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 185777800049211896929837441 139333350036908922697378081)
          ·
            refine ⟨104500012527681692023033561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 139333350036908922697378081 104500012527681692023033561)
            ·
              refine ⟨78375009395761269017275171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 104500012527681692023033561 78375009395761269017275171)
              ·
                refine ⟨117562514093641903525912757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78375009395761269017275171 117562514093641903525912757)
                ·
                  refine ⟨11021485696278928455554321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 117562514093641903525912757 11021485696278928455554321)
                  ·
                    refine ⟨8266114272209196341665741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11021485696278928455554321 8266114272209196341665741)
                    ·
                      refine ⟨3099792852078448628124653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8266114272209196341665741 3099792852078448628124653)
                      ·
                        rfl

theorem cell23_6036825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 1, 5, 2, 3].length) (baseStart_6036825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6036825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6036825 prefixEnd_6036825 := by exact prefixLift 6036825
  have htrace : WordTrace (prefixWord ++ tailWord_6036825) baseStart_6036825 baseEnd_6036825 := by
    simpa [prefixWord, tailWord_6036825, baseEnd_6036825] using wordTrace_append hprefix tailTrace_6036825
  have hstable : (prefixWord ++ tailWord_6036825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6036825).length < 2 ^ (prefixWord ++ tailWord_6036825).sum := by decide
  have hdescent : baseEnd_6036825 < baseStart_6036825 := by decide
  rcases family_descends (prefixWord ++ tailWord_6036825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6036832 : List Nat := [2, 1, 1, 3, 4, 3, 1, 1, 1, 6]
def baseStart_6036832 : Nat := 118140960795 + 6036832 * 2 ^ 59
def prefixEnd_6036832 : Nat := 4983230072969 + 3 ^ 40 * 6036832 * 2
def baseEnd_6036832 : Nat := 1033265482147676700245707

theorem tailTrace_6036832 : CollatzResearch.WordTrace tailWord_6036832 prefixEnd_6036832 1033265482147676700245707 := by
  unfold tailWord_6036832
  simp only [CollatzResearch.WordTrace]
  refine ⟨110090675832798073833952375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146787567777064098445269833 110090675832798073833952375)
  ·
    refine ⟨165136013749197110750928563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110090675832798073833952375 165136013749197110750928563)
    ·
      refine ⟨247704020623795666126392845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165136013749197110750928563 247704020623795666126392845)
      ·
        refine ⟨92889007733923374797397317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 247704020623795666126392845 92889007733923374797397317)
        ·
          refine ⟨17416688950110632774511997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 92889007733923374797397317 17416688950110632774511997)
          ·
            refine ⟨6531258356291487290441999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17416688950110632774511997 6531258356291487290441999)
            ·
              refine ⟨9796887534437230935662999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6531258356291487290441999 9796887534437230935662999)
              ·
                refine ⟨14695331301655846403494499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9796887534437230935662999 14695331301655846403494499)
                ·
                  refine ⟨22042996952483769605241749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14695331301655846403494499 22042996952483769605241749)
                  ·
                    refine ⟨1033265482147676700245707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22042996952483769605241749 1033265482147676700245707)
                    ·
                      rfl

theorem cell23_6036832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 3, 1, 1, 1, 6].length) (baseStart_6036832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6036832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6036832 prefixEnd_6036832 := by exact prefixLift 6036832
  have htrace : WordTrace (prefixWord ++ tailWord_6036832) baseStart_6036832 baseEnd_6036832 := by
    simpa [prefixWord, tailWord_6036832, baseEnd_6036832] using wordTrace_append hprefix tailTrace_6036832
  have hstable : (prefixWord ++ tailWord_6036832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6036832).length < 2 ^ (prefixWord ++ tailWord_6036832).sum := by decide
  have hdescent : baseEnd_6036832 < baseStart_6036832 := by decide
  rcases family_descends (prefixWord ++ tailWord_6036832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6036835 : List Nat := [1, 1, 1, 5, 2, 3, 1, 1, 1, 1, 6]
def baseStart_6036835 : Nat := 118140960795 + 6036835 * 2 ^ 59
def prefixEnd_6036835 : Nat := 4983230072969 + 3 ^ 40 * 6036835 * 2
def baseEnd_6036835 : Nat := 3099797986884993588999607

theorem tailTrace_6036835 : CollatzResearch.WordTrace tailWord_6036835 prefixEnd_6036835 3099797986884993588999607 := by
  unfold tailWord_6036835
  simp only [CollatzResearch.WordTrace]
  refine ⟨220181461084585279180263959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146787640723056852786842639 220181461084585279180263959)
  ·
    refine ⟨330272191626877918770395939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220181461084585279180263959 330272191626877918770395939)
    ·
      refine ⟨495408287440316878155593909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 330272191626877918770395939 495408287440316878155593909)
      ·
        refine ⟨46444526947529707327086929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 495408287440316878155593909 46444526947529707327086929)
        ·
          refine ⟨34833395210647280495315197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46444526947529707327086929 34833395210647280495315197)
          ·
            refine ⟨13062523203992730185743199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34833395210647280495315197 13062523203992730185743199)
            ·
              refine ⟨19593784805989095278614799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13062523203992730185743199 19593784805989095278614799)
              ·
                refine ⟨29390677208983642917922199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19593784805989095278614799 29390677208983642917922199)
                ·
                  refine ⟨44086015813475464376883299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29390677208983642917922199 44086015813475464376883299)
                  ·
                    refine ⟨66129023720213196565324949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 44086015813475464376883299 66129023720213196565324949)
                    ·
                      refine ⟨3099797986884993588999607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 66129023720213196565324949 3099797986884993588999607)
                      ·
                        rfl

theorem cell23_6036835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 1, 1, 1, 1, 6].length) (baseStart_6036835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6036835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6036835 prefixEnd_6036835 := by exact prefixLift 6036835
  have htrace : WordTrace (prefixWord ++ tailWord_6036835) baseStart_6036835 baseEnd_6036835 := by
    simpa [prefixWord, tailWord_6036835, baseEnd_6036835] using wordTrace_append hprefix tailTrace_6036835
  have hstable : (prefixWord ++ tailWord_6036835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6036835).length < 2 ^ (prefixWord ++ tailWord_6036835).sum := by decide
  have hdescent : baseEnd_6036835 < baseStart_6036835 := by decide
  rcases family_descends (prefixWord ++ tailWord_6036835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6036839 : List Nat := [1, 1, 5, 1, 4, 1, 2, 2, 1, 1, 4]
def baseStart_6036839 : Nat := 118140960795 + 6036839 * 2 ^ 59
def prefixEnd_6036839 : Nat := 4983230072969 + 3 ^ 40 * 6036839 * 2
def baseEnd_6036839 : Nat := 3099800040807611573349589

theorem tailTrace_6036839 : CollatzResearch.WordTrace tailWord_6036839 prefixEnd_6036839 3099800040807611573349589 := by
  unfold tailWord_6036839
  simp only [CollatzResearch.WordTrace]
  refine ⟨220181606976570787863409571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146787737984380525242273047 220181606976570787863409571)
  ·
    refine ⟨330272410464856181795114357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220181606976570787863409571 330272410464856181795114357)
    ·
      refine ⟨30963038481080267043291971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 330272410464856181795114357 30963038481080267043291971)
      ·
        refine ⟨46444557721620400564937957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30963038481080267043291971 46444557721620400564937957)
        ·
          refine ⟨8708354572803825105925867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46444557721620400564937957 8708354572803825105925867)
          ·
            refine ⟨13062531859205737658888801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8708354572803825105925867 13062531859205737658888801)
            ·
              refine ⟨9796898894404303244166601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13062531859205737658888801 9796898894404303244166601)
              ·
                refine ⟨7347674170803227433124951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9796898894404303244166601 7347674170803227433124951)
                ·
                  refine ⟨11021511256204841149687427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7347674170803227433124951 11021511256204841149687427)
                  ·
                    refine ⟨16532266884307261724531141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11021511256204841149687427 16532266884307261724531141)
                    ·
                      refine ⟨3099800040807611573349589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16532266884307261724531141 3099800040807611573349589)
                      ·
                        rfl

theorem cell23_6036839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 2, 2, 1, 1, 4].length) (baseStart_6036839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6036839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6036839 prefixEnd_6036839 := by exact prefixLift 6036839
  have htrace : WordTrace (prefixWord ++ tailWord_6036839) baseStart_6036839 baseEnd_6036839 := by
    simpa [prefixWord, tailWord_6036839, baseEnd_6036839] using wordTrace_append hprefix tailTrace_6036839
  have hstable : (prefixWord ++ tailWord_6036839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6036839).length < 2 ^ (prefixWord ++ tailWord_6036839).sum := by decide
  have hdescent : baseEnd_6036839 < baseStart_6036839 := by decide
  rcases family_descends (prefixWord ++ tailWord_6036839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6036845 : List Nat := [1, 5, 1, 1, 1, 4, 1, 9]
def baseStart_6036845 : Nat := 118140960795 + 6036845 * 2 ^ 59
def prefixEnd_6036845 : Nat := 4983230072969 + 3 ^ 40 * 6036845 * 2
def baseEnd_6036845 : Nat := 114807523025612538884243

theorem tailTrace_6036845 : CollatzResearch.WordTrace tailWord_6036845 prefixEnd_6036845 114807523025612538884243 := by
  unfold tailWord_6036845
  simp only [CollatzResearch.WordTrace]
  refine ⟨220181825814549050888127989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146787883876366033925418659 220181825814549050888127989)
  ·
    refine ⟨20642046170113973520761999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 220181825814549050888127989 20642046170113973520761999)
    ·
      refine ⟨30963069255170960281142999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20642046170113973520761999 30963069255170960281142999)
      ·
        refine ⟨46444603882756440421714499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30963069255170960281142999 46444603882756440421714499)
        ·
          refine ⟨69666905824134660632571749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46444603882756440421714499 69666905824134660632571749)
          ·
            refine ⟨13062544842025248868607203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 69666905824134660632571749 13062544842025248868607203)
            ·
              refine ⟨19593817263037873302910805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13062544842025248868607203 19593817263037873302910805)
              ·
                refine ⟨114807523025612538884243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 19593817263037873302910805 114807523025612538884243)
                ·
                  rfl

theorem cell23_6036845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 1, 9].length) (baseStart_6036845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6036845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6036845 prefixEnd_6036845 := by exact prefixLift 6036845
  have htrace : WordTrace (prefixWord ++ tailWord_6036845) baseStart_6036845 baseEnd_6036845 := by
    simpa [prefixWord, tailWord_6036845, baseEnd_6036845] using wordTrace_append hprefix tailTrace_6036845
  have hstable : (prefixWord ++ tailWord_6036845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6036845).length < 2 ^ (prefixWord ++ tailWord_6036845).sum := by decide
  have hdescent : baseEnd_6036845 < baseStart_6036845 := by decide
  rcases family_descends (prefixWord ++ tailWord_6036845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6036855 : List Nat := [1, 1, 3, 1, 1, 2, 4, 1, 3, 3, 3]
def baseStart_6036855 : Nat := 118140960795 + 6036855 * 2 ^ 59
def prefixEnd_6036855 : Nat := 4983230072969 + 3 ^ 40 * 6036855 * 2
def baseEnd_6036855 : Nat := 3099808256498083510749515

theorem tailTrace_6036855 : CollatzResearch.WordTrace tailWord_6036855 prefixEnd_6036855 3099808256498083510749515 := by
  unfold tailWord_6036855
  simp only [CollatzResearch.WordTrace]
  refine ⟨220182190544512822595992019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146788127029675215063994679 220182190544512822595992019)
  ·
    refine ⟨330273285816769233893988029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220182190544512822595992019 330273285816769233893988029)
    ·
      refine ⟨123852482181288462710245511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 330273285816769233893988029 123852482181288462710245511)
      ·
        refine ⟨185778723271932694065368267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123852482181288462710245511 185778723271932694065368267)
        ·
          refine ⟨278668084907899041098052401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 185778723271932694065368267 278668084907899041098052401)
          ·
            refine ⟨209001063680924280823539301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 278668084907899041098052401 209001063680924280823539301)
            ·
              refine ⟨39187699440173302654413619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 209001063680924280823539301 39187699440173302654413619)
              ·
                refine ⟨58781549160259953981620429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39187699440173302654413619 58781549160259953981620429)
                ·
                  refine ⟨22043080935097482743107661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 58781549160259953981620429 22043080935097482743107661)
                  ·
                    refine ⟨8266155350661556028665373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22043080935097482743107661 8266155350661556028665373)
                    ·
                      refine ⟨3099808256498083510749515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8266155350661556028665373 3099808256498083510749515)
                      ·
                        rfl

theorem cell23_6036855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 1, 3, 3, 3].length) (baseStart_6036855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6036855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6036855 prefixEnd_6036855 := by exact prefixLift 6036855
  have htrace : WordTrace (prefixWord ++ tailWord_6036855) baseStart_6036855 baseEnd_6036855 := by
    simpa [prefixWord, tailWord_6036855, baseEnd_6036855] using wordTrace_append hprefix tailTrace_6036855
  have hstable : (prefixWord ++ tailWord_6036855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6036855).length < 2 ^ (prefixWord ++ tailWord_6036855).sum := by decide
  have hdescent : baseEnd_6036855 < baseStart_6036855 := by decide
  rcases family_descends (prefixWord ++ tailWord_6036855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6036873 : List Nat := [1, 2, 1, 1, 8, 1, 1, 1, 3, 2, 2]
def baseStart_6036873 : Nat := 118140960795 + 6036873 * 2 ^ 59
def prefixEnd_6036873 : Nat := 4983230072969 + 3 ^ 40 * 6036873 * 2
def baseEnd_6036873 : Nat := 3099817499149864440324433

theorem tailTrace_6036873 : CollatzResearch.WordTrace tailWord_6036873 prefixEnd_6036873 3099817499149864440324433 := by
  unfold tailWord_6036873
  simp only [CollatzResearch.WordTrace]
  refine ⟨220182847058447611670147273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146788564705631741113431515 220182847058447611670147273)
  ·
    refine ⟨165137135293835708752610455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 220182847058447611670147273 165137135293835708752610455)
    ·
      refine ⟨247705702940753563128915683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165137135293835708752610455 247705702940753563128915683)
      ·
        refine ⟨371558554411130344693373525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 247705702940753563128915683 371558554411130344693373525)
        ·
          refine ⟨4354201809505433726875471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 371558554411130344693373525 4354201809505433726875471)
          ·
            refine ⟨6531302714258150590313207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4354201809505433726875471 6531302714258150590313207)
            ·
              refine ⟨9796954071387225885469811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6531302714258150590313207 9796954071387225885469811)
              ·
                refine ⟨14695431107080838828204717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9796954071387225885469811 14695431107080838828204717)
                ·
                  refine ⟨5510786665155314560576769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14695431107080838828204717 5510786665155314560576769)
                  ·
                    refine ⟨4133089998866485920432577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5510786665155314560576769 4133089998866485920432577)
                    ·
                      refine ⟨3099817499149864440324433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4133089998866485920432577 3099817499149864440324433)
                      ·
                        rfl

theorem cell23_6036873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 8, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 8, 1, 1, 1, 3, 2, 2].length) (baseStart_6036873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6036873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6036873 prefixEnd_6036873 := by exact prefixLift 6036873
  have htrace : WordTrace (prefixWord ++ tailWord_6036873) baseStart_6036873 baseEnd_6036873 := by
    simpa [prefixWord, tailWord_6036873, baseEnd_6036873] using wordTrace_append hprefix tailTrace_6036873
  have hstable : (prefixWord ++ tailWord_6036873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6036873).length < 2 ^ (prefixWord ++ tailWord_6036873).sum := by decide
  have hdescent : baseEnd_6036873 < baseStart_6036873 := by decide
  rcases family_descends (prefixWord ++ tailWord_6036873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6036889 : List Nat := [1, 2, 1, 2, 1, 6, 1, 3, 2, 1, 3]
def baseStart_6036889 : Nat := 118140960795 + 6036889 * 2 ^ 59
def prefixEnd_6036889 : Nat := 4983230072969 + 3 ^ 40 * 6036889 * 2
def baseEnd_6036889 : Nat := 3099825714840336377724359

theorem tailTrace_6036889 : CollatzResearch.WordTrace tailWord_6036889 prefixEnd_6036889 3099825714840336377724359 := by
  unfold tailWord_6036889
  simp only [CollatzResearch.WordTrace]
  refine ⟨220183430626389646402729721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146788953750926430935153147 220183430626389646402729721)
  ·
    refine ⟨165137572969792234802047291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 220183430626389646402729721 165137572969792234802047291)
    ·
      refine ⟨247706359454688352203070937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165137572969792234802047291 247706359454688352203070937)
      ·
        refine ⟨185779769591016264152303203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 247706359454688352203070937 185779769591016264152303203)
        ·
          refine ⟨278669654386524396228454805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 185779769591016264152303203 278669654386524396228454805)
          ·
            refine ⟨13062640049368331073208819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 278669654386524396228454805 13062640049368331073208819)
            ·
              refine ⟨19593960074052496609813229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13062640049368331073208819 19593960074052496609813229)
              ·
                refine ⟨7347735027769686228679961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19593960074052496609813229 7347735027769686228679961)
                ·
                  refine ⟨5510801270827264671509971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7347735027769686228679961 5510801270827264671509971)
                  ·
                    refine ⟨8266201906240897007264957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5510801270827264671509971 8266201906240897007264957)
                    ·
                      refine ⟨3099825714840336377724359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8266201906240897007264957 3099825714840336377724359)
                      ·
                        rfl

theorem cell23_6036889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 1, 3, 2, 1, 3].length) (baseStart_6036889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6036889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6036889 prefixEnd_6036889 := by exact prefixLift 6036889
  have htrace : WordTrace (prefixWord ++ tailWord_6036889) baseStart_6036889 baseEnd_6036889 := by
    simpa [prefixWord, tailWord_6036889, baseEnd_6036889] using wordTrace_append hprefix tailTrace_6036889
  have hstable : (prefixWord ++ tailWord_6036889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6036889).length < 2 ^ (prefixWord ++ tailWord_6036889).sum := by decide
  have hdescent : baseEnd_6036889 < baseStart_6036889 := by decide
  rcases family_descends (prefixWord ++ tailWord_6036889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6036915 : List Nat := [1, 1, 1, 2, 3, 1, 1, 2, 4, 4, 3]
def baseStart_6036915 : Nat := 118140960795 + 6036915 * 2 ^ 59
def prefixEnd_6036915 : Nat := 4983230072969 + 3 ^ 40 * 6036915 * 2
def baseEnd_6036915 : Nat := 3099839065337353275999239

theorem tailTrace_6036915 : CollatzResearch.WordTrace tailWord_6036915 prefixEnd_6036915 3099839065337353275999239 := by
  unfold tailWord_6036915
  simp only [CollatzResearch.WordTrace]
  refine ⟨220184378924295452843176199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146789585949530301895450799 220184378924295452843176199)
  ·
    refine ⟨330276568386443179264764299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220184378924295452843176199 330276568386443179264764299)
    ·
      refine ⟨495414852579664768897146449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 330276568386443179264764299 495414852579664768897146449)
      ·
        refine ⟨371561139434748576672859837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 495414852579664768897146449 371561139434748576672859837)
        ·
          refine ⟨139335427288030716252322439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 371561139434748576672859837 139335427288030716252322439)
          ·
            refine ⟨209003140932046074378483659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139335427288030716252322439 209003140932046074378483659)
            ·
              refine ⟨313504711398069111567725489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 209003140932046074378483659 313504711398069111567725489)
              ·
                refine ⟨235128533548551833675794117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 313504711398069111567725489 235128533548551833675794117)
                ·
                  refine ⟨44086600040353468814211397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 235128533548551833675794117 44086600040353468814211397)
                  ·
                    refine ⟨8266237507566275402664637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 44086600040353468814211397 8266237507566275402664637)
                    ·
                      refine ⟨3099839065337353275999239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8266237507566275402664637 3099839065337353275999239)
                      ·
                        rfl

theorem cell23_6036915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 2, 4, 4, 3].length) (baseStart_6036915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6036915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6036915 prefixEnd_6036915 := by exact prefixLift 6036915
  have htrace : WordTrace (prefixWord ++ tailWord_6036915) baseStart_6036915 baseEnd_6036915 := by
    simpa [prefixWord, tailWord_6036915, baseEnd_6036915] using wordTrace_append hprefix tailTrace_6036915
  have hstable : (prefixWord ++ tailWord_6036915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6036915).length < 2 ^ (prefixWord ++ tailWord_6036915).sum := by decide
  have hdescent : baseEnd_6036915 < baseStart_6036915 := by decide
  rcases family_descends (prefixWord ++ tailWord_6036915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6036930 : List Nat := [3, 5, 2, 1, 2, 1, 1, 8]
def baseStart_6036930 : Nat := 118140960795 + 6036930 * 2 ^ 59
def prefixEnd_6036930 : Nat := 4983230072969 + 3 ^ 40 * 6036930 * 2
def baseEnd_6036930 : Nat := 114809139538784100641173

theorem tailTrace_6036930 : CollatzResearch.WordTrace tailWord_6036930 prefixEnd_6036930 114809139538784100641173 := by
  unfold tailWord_6036930
  simp only [CollatzResearch.WordTrace]
  refine ⟨55046231504810277601243061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146789950679494073603314829 55046231504810277601243061)
  ·
    refine ⟨5160584203575963525116537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 55046231504810277601243061 5160584203575963525116537)
    ·
      refine ⟨3870438152681972643837403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5160584203575963525116537 3870438152681972643837403)
      ·
        refine ⟨5805657229022958965756105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3870438152681972643837403 5805657229022958965756105)
        ·
          refine ⟨4354242921767219224317079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5805657229022958965756105 4354242921767219224317079)
          ·
            refine ⟨6531364382650828836475619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4354242921767219224317079 6531364382650828836475619)
            ·
              refine ⟨9797046573976243254713429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6531364382650828836475619 9797046573976243254713429)
              ·
                refine ⟨114809139538784100641173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9797046573976243254713429 114809139538784100641173)
                ·
                  rfl

theorem cell23_6036930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 2, 1, 1, 8].length) (baseStart_6036930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6036930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6036930 prefixEnd_6036930 := by exact prefixLift 6036930
  have htrace : WordTrace (prefixWord ++ tailWord_6036930) baseStart_6036930 baseEnd_6036930 := by
    simpa [prefixWord, tailWord_6036930, baseEnd_6036930] using wordTrace_append hprefix tailTrace_6036930
  have hstable : (prefixWord ++ tailWord_6036930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6036930).length < 2 ^ (prefixWord ++ tailWord_6036930).sum := by decide
  have hdescent : baseEnd_6036930 < baseStart_6036930 := by decide
  rcases family_descends (prefixWord ++ tailWord_6036930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6036935 : List Nat := [1, 1, 4, 1, 1, 3, 2, 3, 7]
def baseStart_6036935 : Nat := 118140960795 + 6036935 * 2 ^ 59
def prefixEnd_6036935 : Nat := 4983230072969 + 3 ^ 40 * 6036935 * 2
def baseEnd_6036935 : Nat := 344427703883382577527683

theorem tailTrace_6036935 : CollatzResearch.WordTrace tailWord_6036935 prefixEnd_6036935 344427703883382577527683 := by
  unfold tailWord_6036935
  simp only [CollatzResearch.WordTrace]
  refine ⟨220185108384222996258904259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146790072256148664172602839 220185108384222996258904259)
  ·
    refine ⟨330277662576334494388356389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220185108384222996258904259 330277662576334494388356389)
    ·
      refine ⟨61927061733062717697816823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 330277662576334494388356389 61927061733062717697816823)
      ·
        refine ⟨92890592599594076546725235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61927061733062717697816823 92890592599594076546725235)
        ·
          refine ⟨139335888899391114820087853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92890592599594076546725235 139335888899391114820087853)
          ·
            refine ⟨52250958337271668057532945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 139335888899391114820087853 52250958337271668057532945)
            ·
              refine ⟨39188218752953751043149709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52250958337271668057532945 39188218752953751043149709)
              ·
                refine ⟨14695582032357656641181141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39188218752953751043149709 14695582032357656641181141)
                ·
                  refine ⟨344427703883382577527683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14695582032357656641181141 344427703883382577527683)
                  ·
                    rfl

theorem cell23_6036935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 3, 7].length) (baseStart_6036935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6036935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6036935 prefixEnd_6036935 := by exact prefixLift 6036935
  have htrace : WordTrace (prefixWord ++ tailWord_6036935) baseStart_6036935 baseEnd_6036935 := by
    simpa [prefixWord, tailWord_6036935, baseEnd_6036935] using wordTrace_append hprefix tailTrace_6036935
  have hstable : (prefixWord ++ tailWord_6036935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6036935).length < 2 ^ (prefixWord ++ tailWord_6036935).sum := by decide
  have hdescent : baseEnd_6036935 < baseStart_6036935 := by decide
  rcases family_descends (prefixWord ++ tailWord_6036935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6036972 : List Nat := [2, 2, 1, 1, 2, 1, 2, 2, 1, 7, 2]
def baseStart_6036972 : Nat := 118140960795 + 6036972 * 2 ^ 59
def prefixEnd_6036972 : Nat := 4983230072969 + 3 ^ 40 * 6036972 * 2
def baseEnd_6036972 : Nat := 3099868333734659552986477

theorem tailTrace_6036972 : CollatzResearch.WordTrace tailWord_6036972 prefixEnd_6036972 3099868333734659552986477 := by
  unfold tailWord_6036972
  simp only [CollatzResearch.WordTrace]
  refine ⟨110093228942544475789000585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146790971923392634385334113 110093228942544475789000585)
  ·
    refine ⟨82569921706908356841750439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110093228942544475789000585 82569921706908356841750439)
    ·
      refine ⟨123854882560362535262625659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82569921706908356841750439 123854882560362535262625659)
      ·
        refine ⟨185782323840543802893938489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123854882560362535262625659 185782323840543802893938489)
        ·
          refine ⟨139336742880407852170453867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 185782323840543802893938489 139336742880407852170453867)
          ·
            refine ⟨209005114320611778255680801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139336742880407852170453867 209005114320611778255680801)
            ·
              refine ⟨156753835740458833691760601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 209005114320611778255680801 156753835740458833691760601)
              ·
                refine ⟨117565376805344125268820451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 156753835740458833691760601 117565376805344125268820451)
                ·
                  refine ⟨176348065208016187903230677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 117565376805344125268820451 176348065208016187903230677)
                  ·
                    refine ⟨4133157778312879403981969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 176348065208016187903230677 4133157778312879403981969)
                    ·
                      refine ⟨3099868333734659552986477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4133157778312879403981969 3099868333734659552986477)
                      ·
                        rfl

theorem cell23_6036972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 7, 2].length) (baseStart_6036972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6036972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6036972 prefixEnd_6036972 := by exact prefixLift 6036972
  have htrace : WordTrace (prefixWord ++ tailWord_6036972) baseStart_6036972 baseEnd_6036972 := by
    simpa [prefixWord, tailWord_6036972, baseEnd_6036972] using wordTrace_append hprefix tailTrace_6036972
  have hstable : (prefixWord ++ tailWord_6036972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6036972).length < 2 ^ (prefixWord ++ tailWord_6036972).sum := by decide
  have hdescent : baseEnd_6036972 < baseStart_6036972 := by decide
  rcases family_descends (prefixWord ++ tailWord_6036972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6036975 : List Nat := [1, 1, 2, 1, 4, 1, 2, 1, 3, 2, 5]
def baseStart_6036975 : Nat := 118140960795 + 6036975 * 2 ^ 59
def prefixEnd_6036975 : Nat := 4983230072969 + 3 ^ 40 * 6036975 * 2
def baseEnd_6036975 : Nat := 3099869874176623041248963

theorem tailTrace_6036975 : CollatzResearch.WordTrace tailWord_6036975 prefixEnd_6036975 3099869874176623041248963 := by
  unfold tailWord_6036975
  simp only [CollatzResearch.WordTrace]
  refine ⟨220186567304078083090360379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146791044869385388726906919 220186567304078083090360379)
  ·
    refine ⟨330279850956117124635540569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220186567304078083090360379 330279850956117124635540569)
    ·
      refine ⟨247709888217087843476655427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 330279850956117124635540569 247709888217087843476655427)
      ·
        refine ⟨371564832325631765214983141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 247709888217087843476655427 371564832325631765214983141)
        ·
          refine ⟨69668406061055955977809339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 371564832325631765214983141 69668406061055955977809339)
          ·
            refine ⟨104502609091583933966714009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69668406061055955977809339 104502609091583933966714009)
            ·
              refine ⟨78376956818687950475035507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 104502609091583933966714009 78376956818687950475035507)
              ·
                refine ⟨117565435228031925712553261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78376956818687950475035507 117565435228031925712553261)
                ·
                  refine ⟨44087038210511972142207473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 117565435228031925712553261 44087038210511972142207473)
                  ·
                    refine ⟨33065278657883979106655605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 44087038210511972142207473 33065278657883979106655605)
                    ·
                      refine ⟨3099869874176623041248963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33065278657883979106655605 3099869874176623041248963)
                      ·
                        rfl

theorem cell23_6036975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 1, 3, 2, 5].length) (baseStart_6036975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6036975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6036975 prefixEnd_6036975 := by exact prefixLift 6036975
  have htrace : WordTrace (prefixWord ++ tailWord_6036975) baseStart_6036975 baseEnd_6036975 := by
    simpa [prefixWord, tailWord_6036975, baseEnd_6036975] using wordTrace_append hprefix tailTrace_6036975
  have hstable : (prefixWord ++ tailWord_6036975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6036975).length < 2 ^ (prefixWord ++ tailWord_6036975).sum := by decide
  have hdescent : baseEnd_6036975 < baseStart_6036975 := by decide
  rcases family_descends (prefixWord ++ tailWord_6036975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6037002 : List Nat := [3, 1, 2, 2, 2, 2, 1, 2, 1, 3, 4]
def baseStart_6037002 : Nat := 118140960795 + 6037002 * 2 ^ 59
def prefixEnd_6037002 : Nat := 4983230072969 + 3 ^ 40 * 6037002 * 2
def baseEnd_6037002 : Nat := 3099883738154294435611339

theorem tailTrace_6037002 : CollatzResearch.WordTrace tailWord_6037002 prefixEnd_6037002 3099883738154294435611339 := by
  unfold tailWord_6037002
  simp only [CollatzResearch.WordTrace]
  refine ⟨55046888018745066675398315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146791701383320177801062173 55046888018745066675398315)
  ·
    refine ⟨82570332028117600013097473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55046888018745066675398315 82570332028117600013097473)
    ·
      refine ⟨61927749021088200009823105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82570332028117600013097473 61927749021088200009823105)
      ·
        refine ⟨46445811765816150007367329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61927749021088200009823105 46445811765816150007367329)
        ·
          refine ⟨34834358824362112505525497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46445811765816150007367329 34834358824362112505525497)
          ·
            refine ⟨26125769118271584379144123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34834358824362112505525497 26125769118271584379144123)
            ·
              refine ⟨39188653677407376568716185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26125769118271584379144123 39188653677407376568716185)
              ·
                refine ⟨29391490258055532426537139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39188653677407376568716185 29391490258055532426537139)
                ·
                  refine ⟨44087235387083298639805709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29391490258055532426537139 44087235387083298639805709)
                  ·
                    refine ⟨16532713270156236989927141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 44087235387083298639805709 16532713270156236989927141)
                    ·
                      refine ⟨3099883738154294435611339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16532713270156236989927141 3099883738154294435611339)
                      ·
                        rfl

theorem cell23_6037002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 2, 1, 3, 4].length) (baseStart_6037002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6037002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6037002 prefixEnd_6037002 := by exact prefixLift 6037002
  have htrace : WordTrace (prefixWord ++ tailWord_6037002) baseStart_6037002 baseEnd_6037002 := by
    simpa [prefixWord, tailWord_6037002, baseEnd_6037002] using wordTrace_append hprefix tailTrace_6037002
  have hstable : (prefixWord ++ tailWord_6037002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6037002).length < 2 ^ (prefixWord ++ tailWord_6037002).sum := by decide
  have hdescent : baseEnd_6037002 < baseStart_6037002 := by decide
  rcases family_descends (prefixWord ++ tailWord_6037002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6037042 : List Nat := [3, 2, 1, 1, 2, 1, 1, 6, 6]
def baseStart_6037042 : Nat := 118140960795 + 6037042 * 2 ^ 59
def prefixEnd_6037042 : Nat := 4983230072969 + 3 ^ 40 * 6037042 * 2
def baseEnd_6037042 : Nat := 344433808597830475456795

theorem tailTrace_6037042 : CollatzResearch.WordTrace tailWord_6037042 prefixEnd_6037042 344433808597830475456795 := by
  unfold tailWord_6037042
  simp only [CollatzResearch.WordTrace]
  refine ⟨55047252748708838383262345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146792673996556902355366253 55047252748708838383262345)
  ·
    refine ⟨41285439561531628787446759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55047252748708838383262345 41285439561531628787446759)
    ·
      refine ⟨61928159342297443181170139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41285439561531628787446759 61928159342297443181170139)
      ·
        refine ⟨92892239013446164771755209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61928159342297443181170139 92892239013446164771755209)
        ·
          refine ⟨69669179260084623578816407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92892239013446164771755209 69669179260084623578816407)
          ·
            refine ⟨104503768890126935368224611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69669179260084623578816407 104503768890126935368224611)
            ·
              refine ⟨156755653335190403052336917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104503768890126935368224611 156755653335190403052336917)
              ·
                refine ⟨7347921250087050143078293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 156755653335190403052336917 7347921250087050143078293)
                ·
                  refine ⟨344433808597830475456795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7347921250087050143078293 344433808597830475456795)
                  ·
                    rfl

theorem cell23_6037042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 6, 6].length) (baseStart_6037042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6037042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6037042 prefixEnd_6037042 := by exact prefixLift 6037042
  have htrace : WordTrace (prefixWord ++ tailWord_6037042) baseStart_6037042 baseEnd_6037042 := by
    simpa [prefixWord, tailWord_6037042, baseEnd_6037042] using wordTrace_append hprefix tailTrace_6037042
  have hstable : (prefixWord ++ tailWord_6037042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6037042).length < 2 ^ (prefixWord ++ tailWord_6037042).sum := by decide
  have hdescent : baseEnd_6037042 < baseStart_6037042 := by decide
  rcases family_descends (prefixWord ++ tailWord_6037042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6037072 : List Nat := [2, 1, 1, 1, 1, 3, 5, 1, 3, 5]
def baseStart_6037072 : Nat := 118140960795 + 6037072 * 2 ^ 59
def prefixEnd_6037072 : Nat := 4983230072969 + 3 ^ 40 * 6037072 * 2
def baseEnd_6037072 : Nat := 1033306560600036387245339

theorem tailTrace_6037072 : CollatzResearch.WordTrace tailWord_6037072 prefixEnd_6037072 1033306560600036387245339 := by
  unfold tailWord_6037072
  simp only [CollatzResearch.WordTrace]
  refine ⟨110095052592363334328320735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146793403456484445771094313 110095052592363334328320735)
  ·
    refine ⟨165142578888545001492481103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110095052592363334328320735 165142578888545001492481103)
    ·
      refine ⟨247713868332817502238721655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165142578888545001492481103 247713868332817502238721655)
      ·
        refine ⟨371570802499226253358082483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 247713868332817502238721655 371570802499226253358082483)
        ·
          refine ⟨557356203748839380037123725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 371570802499226253358082483 557356203748839380037123725)
          ·
            refine ⟨209008576405814767513921397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 557356203748839380037123725 209008576405814767513921397)
            ·
              refine ⟨19594554038045134454430131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 209008576405814767513921397 19594554038045134454430131)
              ·
                refine ⟨29391831057067701681645197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19594554038045134454430131 29391831057067701681645197)
                ·
                  refine ⟨11021936646400388130616949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29391831057067701681645197 11021936646400388130616949)
                  ·
                    refine ⟨1033306560600036387245339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11021936646400388130616949 1033306560600036387245339)
                    ·
                      rfl

theorem cell23_6037072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 5, 1, 3, 5].length) (baseStart_6037072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6037072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6037072 prefixEnd_6037072 := by exact prefixLift 6037072
  have htrace : WordTrace (prefixWord ++ tailWord_6037072) baseStart_6037072 baseEnd_6037072 := by
    simpa [prefixWord, tailWord_6037072, baseEnd_6037072] using wordTrace_append hprefix tailTrace_6037072
  have hstable : (prefixWord ++ tailWord_6037072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6037072).length < 2 ^ (prefixWord ++ tailWord_6037072).sum := by decide
  have hdescent : baseEnd_6037072 < baseStart_6037072 := by decide
  rcases family_descends (prefixWord ++ tailWord_6037072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6037112 : List Nat := [2, 1, 2, 1, 1, 1, 2, 1, 1, 8, 3]
def baseStart_6037112 : Nat := 118140960795 + 6037112 * 2 ^ 59
def prefixEnd_6037112 : Nat := 4983230072969 + 3 ^ 40 * 6037112 * 2
def baseEnd_6037112 : Nat := 3099940221026289005235833

theorem tailTrace_6037112 : CollatzResearch.WordTrace tailWord_6037112 prefixEnd_6037112 3099940221026289005235833 := by
  unfold tailWord_6037112
  simp only [CollatzResearch.WordTrace]
  refine ⟨110095782052290877744048795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146794376069721170325398393 110095782052290877744048795)
  ·
    refine ⟨165143673078436316616073193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110095782052290877744048795 165143673078436316616073193)
    ·
      refine ⟨123857754808827237462054895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 165143673078436316616073193 123857754808827237462054895)
      ·
        refine ⟨185786632213240856193082343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123857754808827237462054895 185786632213240856193082343)
        ·
          refine ⟨278679948319861284289623515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 185786632213240856193082343 278679948319861284289623515)
          ·
            refine ⟨418019922479791926434435273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 278679948319861284289623515 418019922479791926434435273)
            ·
              refine ⟨313514941859843944825826455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 418019922479791926434435273 313514941859843944825826455)
              ·
                refine ⟨470272412789765917238739683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 313514941859843944825826455 470272412789765917238739683)
                ·
                  refine ⟨705408619184648875858109525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 470272412789765917238739683 705408619184648875858109525)
                  ·
                    refine ⟨8266507256070104013962221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 705408619184648875858109525 8266507256070104013962221)
                    ·
                      refine ⟨3099940221026289005235833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8266507256070104013962221 3099940221026289005235833)
                      ·
                        rfl

theorem cell23_6037112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 1, 8, 3].length) (baseStart_6037112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6037112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6037112 prefixEnd_6037112 := by exact prefixLift 6037112
  have htrace : WordTrace (prefixWord ++ tailWord_6037112) baseStart_6037112 baseEnd_6037112 := by
    simpa [prefixWord, tailWord_6037112, baseEnd_6037112] using wordTrace_append hprefix tailTrace_6037112
  have hstable : (prefixWord ++ tailWord_6037112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6037112).length < 2 ^ (prefixWord ++ tailWord_6037112).sum := by decide
  have hdescent : baseEnd_6037112 < baseStart_6037112 := by decide
  rcases family_descends (prefixWord ++ tailWord_6037112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6037129 : List Nat := [1, 2, 1, 1, 4, 1, 4, 1, 3, 2, 3]
def baseStart_6037129 : Nat := 118140960795 + 6037129 * 2 ^ 59
def prefixEnd_6037129 : Nat := 4983230072969 + 3 ^ 40 * 6037129 * 2
def baseEnd_6037129 : Nat := 3099948950197415438723255

theorem tailTrace_6037129 : CollatzResearch.WordTrace tailWord_6037129 prefixEnd_6037129 3099948950197415438723255 := by
  unfold tailWord_6037129
  simp only [CollatzResearch.WordTrace]
  refine ⟨220192184145520167391466441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146794789430346778260977627 220192184145520167391466441)
  ·
    refine ⟨165144138109140125543599831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 220192184145520167391466441 165144138109140125543599831)
    ·
      refine ⟨247716207163710188315399747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165144138109140125543599831 247716207163710188315399747)
      ·
        refine ⟨371574310745565282473099621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 247716207163710188315399747 371574310745565282473099621)
        ·
          refine ⟨69670183264793490463706179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 371574310745565282473099621 69670183264793490463706179)
          ·
            refine ⟨104505274897190235695559269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69670183264793490463706179 104505274897190235695559269)
            ·
              refine ⟨19594739043223169192917363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 104505274897190235695559269 19594739043223169192917363)
              ·
                refine ⟨29392108564834753789376045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19594739043223169192917363 29392108564834753789376045)
                ·
                  refine ⟨11022040711813032671016017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29392108564834753789376045 11022040711813032671016017)
                  ·
                    refine ⟨8266530533859774503262013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11022040711813032671016017 8266530533859774503262013)
                    ·
                      refine ⟨3099948950197415438723255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8266530533859774503262013 3099948950197415438723255)
                      ·
                        rfl

theorem cell23_6037129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 4, 1, 3, 2, 3].length) (baseStart_6037129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6037129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6037129 prefixEnd_6037129 := by exact prefixLift 6037129
  have htrace : WordTrace (prefixWord ++ tailWord_6037129) baseStart_6037129 baseEnd_6037129 := by
    simpa [prefixWord, tailWord_6037129, baseEnd_6037129] using wordTrace_append hprefix tailTrace_6037129
  have hstable : (prefixWord ++ tailWord_6037129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6037129).length < 2 ^ (prefixWord ++ tailWord_6037129).sum := by decide
  have hdescent : baseEnd_6037129 < baseStart_6037129 := by decide
  rcases family_descends (prefixWord ++ tailWord_6037129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6037140 : List Nat := [2, 4, 2, 2, 2, 2, 2, 1, 1, 5]
def baseStart_6037140 : Nat := 118140960795 + 6037140 * 2 ^ 59
def prefixEnd_6037140 : Nat := 4983230072969 + 3 ^ 40 * 6037140 * 2
def baseEnd_6037140 : Nat := 1033318199494871631895235

theorem tailTrace_6037140 : CollatzResearch.WordTrace tailWord_6037140 prefixEnd_6037140 1033318199494871631895235 := by
  unfold tailWord_6037140
  simp only [CollatzResearch.WordTrace]
  refine ⟨110096292674240158135058437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146795056898986877513411249 110096292674240158135058437)
  ·
    refine ⟨20643054876420029650323457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 110096292674240158135058437 20643054876420029650323457)
    ·
      refine ⟨15482291157315022237742593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20643054876420029650323457 15482291157315022237742593)
      ·
        refine ⟨11611718367986266678306945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15482291157315022237742593 11611718367986266678306945)
        ·
          refine ⟨8708788775989700008730209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11611718367986266678306945 8708788775989700008730209)
          ·
            refine ⟨6531591581992275006547657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8708788775989700008730209 6531591581992275006547657)
            ·
              refine ⟨4898693686494206254910743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6531591581992275006547657 4898693686494206254910743)
              ·
                refine ⟨7348040529741309382366115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4898693686494206254910743 7348040529741309382366115)
                ·
                  refine ⟨11022060794611964073549173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7348040529741309382366115 11022060794611964073549173)
                  ·
                    refine ⟨1033318199494871631895235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11022060794611964073549173 1033318199494871631895235)
                    ·
                      rfl

theorem cell23_6037140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 2, 2, 1, 1, 5].length) (baseStart_6037140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6037140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6037140 prefixEnd_6037140 := by exact prefixLift 6037140
  have htrace : WordTrace (prefixWord ++ tailWord_6037140) baseStart_6037140 baseEnd_6037140 := by
    simpa [prefixWord, tailWord_6037140, baseEnd_6037140] using wordTrace_append hprefix tailTrace_6037140
  have hstable : (prefixWord ++ tailWord_6037140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6037140).length < 2 ^ (prefixWord ++ tailWord_6037140).sum := by decide
  have hdescent : baseEnd_6037140 < baseStart_6037140 := by decide
  rcases family_descends (prefixWord ++ tailWord_6037140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6037143 : List Nat := [1, 1, 3, 3, 2, 4, 2, 1, 1, 1, 4]
def baseStart_6037143 : Nat := 118140960795 + 6037143 * 2 ^ 59
def prefixEnd_6037143 : Nat := 4983230072969 + 3 ^ 40 * 6037143 * 2
def baseEnd_6037143 : Nat := 3099956138926578383948191

theorem tailTrace_6037143 : CollatzResearch.WordTrace tailWord_6037143 prefixEnd_6037143 3099956138926578383948191 := by
  unfold tailWord_6037143
  simp only [CollatzResearch.WordTrace]
  refine ⟨220192694767469447782476083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146795129844979631854984055 220192694767469447782476083)
  ·
    refine ⟨330289042151204171673714125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220192694767469447782476083 330289042151204171673714125)
    ·
      refine ⟨123858390806701564377642797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 330289042151204171673714125 123858390806701564377642797)
      ·
        refine ⟨46446896552513086641616049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 123858390806701564377642797 46446896552513086641616049)
        ·
          refine ⟨34835172414384814981212037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46446896552513086641616049 34835172414384814981212037)
          ·
            refine ⟨6531594827697152808977257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34835172414384814981212037 6531594827697152808977257)
            ·
              refine ⟨4898696120772864606732943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6531594827697152808977257 4898696120772864606732943)
              ·
                refine ⟨7348044181159296910099415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4898696120772864606732943 7348044181159296910099415)
                ·
                  refine ⟨11022066271738945365149123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7348044181159296910099415 11022066271738945365149123)
                  ·
                    refine ⟨16533099407608418047723685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11022066271738945365149123 16533099407608418047723685)
                    ·
                      refine ⟨3099956138926578383948191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16533099407608418047723685 3099956138926578383948191)
                      ·
                        rfl

theorem cell23_6037143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 4, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 4, 2, 1, 1, 1, 4].length) (baseStart_6037143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6037143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6037143 prefixEnd_6037143 := by exact prefixLift 6037143
  have htrace : WordTrace (prefixWord ++ tailWord_6037143) baseStart_6037143 baseEnd_6037143 := by
    simpa [prefixWord, tailWord_6037143, baseEnd_6037143] using wordTrace_append hprefix tailTrace_6037143
  have hstable : (prefixWord ++ tailWord_6037143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6037143).length < 2 ^ (prefixWord ++ tailWord_6037143).sum := by decide
  have hdescent : baseEnd_6037143 < baseStart_6037143 := by decide
  rcases family_descends (prefixWord ++ tailWord_6037143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6037153 : List Nat := [1, 2, 3, 3, 2, 3, 1, 2, 2, 4]
def baseStart_6037153 : Nat := 118140960795 + 6037153 * 2 ^ 59
def prefixEnd_6037153 : Nat := 4983230072969 + 3 ^ 40 * 6037153 * 2
def baseEnd_6037153 : Nat := 1033320424577707781607715

theorem tailTrace_6037153 : CollatzResearch.WordTrace tailWord_6037153 prefixEnd_6037153 1033320424577707781607715 := by
  unfold tailWord_6037153
  simp only [CollatzResearch.WordTrace]
  refine ⟨220193059497433219490340113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146795372998288812993560075 220193059497433219490340113)
  ·
    refine ⟨165144794623074914617755085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 220193059497433219490340113 165144794623074914617755085)
    ·
      refine ⟨61929297983653092981658157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 165144794623074914617755085 61929297983653092981658157)
      ·
        refine ⟨23223486743869909868121809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61929297983653092981658157 23223486743869909868121809)
        ·
          refine ⟨17417615057902432401091357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23223486743869909868121809 17417615057902432401091357)
          ·
            refine ⟨6531605646713412150409259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17417615057902432401091357 6531605646713412150409259)
            ·
              refine ⟨9797408470070118225613889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6531605646713412150409259 9797408470070118225613889)
              ·
                refine ⟨7348056352552588669210417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9797408470070118225613889 7348056352552588669210417)
                ·
                  refine ⟨5511042264414441501907813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7348056352552588669210417 5511042264414441501907813)
                  ·
                    refine ⟨1033320424577707781607715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5511042264414441501907813 1033320424577707781607715)
                    ·
                      rfl

theorem cell23_6037153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 3, 1, 2, 2, 4].length) (baseStart_6037153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6037153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6037153 prefixEnd_6037153 := by exact prefixLift 6037153
  have htrace : WordTrace (prefixWord ++ tailWord_6037153) baseStart_6037153 baseEnd_6037153 := by
    simpa [prefixWord, tailWord_6037153, baseEnd_6037153] using wordTrace_append hprefix tailTrace_6037153
  have hstable : (prefixWord ++ tailWord_6037153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6037153).length < 2 ^ (prefixWord ++ tailWord_6037153).sum := by decide
  have hdescent : baseEnd_6037153 < baseStart_6037153 := by decide
  rcases family_descends (prefixWord ++ tailWord_6037153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6037173 : List Nat := [1, 3, 3, 3, 2, 2, 1, 1, 1, 2, 4]
def baseStart_6037173 : Nat := 118140960795 + 6037173 * 2 ^ 59
def prefixEnd_6037173 : Nat := 4983230072969 + 3 ^ 40 * 6037173 * 2
def baseEnd_6037173 : Nat := 3099971543346213266573053

theorem tailTrace_6037173 : CollatzResearch.WordTrace tailWord_6037173 prefixEnd_6037173 3099971543346213266573053 := by
  unfold tailWord_6037173
  simp only [CollatzResearch.WordTrace]
  refine ⟨220193788957360762906068173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146795859304907175270712115 220193788957360762906068173)
  ·
    refine ⟨82572670859010286089775565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 220193788957360762906068173 82572670859010286089775565)
    ·
      refine ⟨30964751572128857283665837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82572670859010286089775565 30964751572128857283665837)
      ·
        refine ⟨11611781839548321481374689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30964751572128857283665837 11611781839548321481374689)
        ·
          refine ⟨8708836379661241111031017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11611781839548321481374689 8708836379661241111031017)
          ·
            refine ⟨6531627284745930833273263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8708836379661241111031017 6531627284745930833273263)
            ·
              refine ⟨9797440927118896249909895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6531627284745930833273263 9797440927118896249909895)
              ·
                refine ⟨14696161390678344374864843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9797440927118896249909895 14696161390678344374864843)
                ·
                  refine ⟨22044242086017516562297265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14696161390678344374864843 22044242086017516562297265)
                  ·
                    refine ⟨16533181564513137421722949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22044242086017516562297265 16533181564513137421722949)
                    ·
                      refine ⟨3099971543346213266573053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16533181564513137421722949 3099971543346213266573053)
                      ·
                        rfl

theorem cell23_6037173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 2, 1, 1, 1, 2, 4].length) (baseStart_6037173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6037173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6037173 prefixEnd_6037173 := by exact prefixLift 6037173
  have htrace : WordTrace (prefixWord ++ tailWord_6037173) baseStart_6037173 baseEnd_6037173 := by
    simpa [prefixWord, tailWord_6037173, baseEnd_6037173] using wordTrace_append hprefix tailTrace_6037173
  have hstable : (prefixWord ++ tailWord_6037173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6037173).length < 2 ^ (prefixWord ++ tailWord_6037173).sum := by decide
  have hdescent : baseEnd_6037173 < baseStart_6037173 := by decide
  rcases family_descends (prefixWord ++ tailWord_6037173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6037176 : List Nat := [2, 1, 2, 1, 2, 1, 1, 7, 2, 1, 3]
def baseStart_6037176 : Nat := 118140960795 + 6037176 * 2 ^ 59
def prefixEnd_6037176 : Nat := 4983230072969 + 3 ^ 40 * 6037176 * 2
def baseEnd_6037176 : Nat := 3099973083788176754835539

theorem tailTrace_6037176 : CollatzResearch.WordTrace tailWord_6037176 prefixEnd_6037176 3099973083788176754835539 := by
  unfold tailWord_6037176
  simp only [CollatzResearch.WordTrace]
  refine ⟨110096949188174947209213691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146795932250899929612284921 110096949188174947209213691)
  ·
    refine ⟨165145423782262420813820537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110096949188174947209213691 165145423782262420813820537)
    ·
      refine ⟨123859067836696815610365403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 165145423782262420813820537 123859067836696815610365403)
      ·
        refine ⟨185788601755045223415548105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123859067836696815610365403 185788601755045223415548105)
        ·
          refine ⟨139341451316283917561661079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 185788601755045223415548105 139341451316283917561661079)
          ·
            refine ⟨209012176974425876342491619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139341451316283917561661079 209012176974425876342491619)
            ·
              refine ⟨313518265461638814513737429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 209012176974425876342491619 313518265461638814513737429)
              ·
                refine ⟨7348084346757159715165721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 313518265461638814513737429 7348084346757159715165721)
                ·
                  refine ⟨5511063260067869786374291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7348084346757159715165721 5511063260067869786374291)
                  ·
                    refine ⟨8266594890101804679561437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5511063260067869786374291 8266594890101804679561437)
                    ·
                      refine ⟨3099973083788176754835539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8266594890101804679561437 3099973083788176754835539)
                      ·
                        rfl

theorem cell23_6037176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 7, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 7, 2, 1, 3].length) (baseStart_6037176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6037176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6037176 prefixEnd_6037176 := by exact prefixLift 6037176
  have htrace : WordTrace (prefixWord ++ tailWord_6037176) baseStart_6037176 baseEnd_6037176 := by
    simpa [prefixWord, tailWord_6037176, baseEnd_6037176] using wordTrace_append hprefix tailTrace_6037176
  have hstable : (prefixWord ++ tailWord_6037176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6037176).length < 2 ^ (prefixWord ++ tailWord_6037176).sum := by decide
  have hdescent : baseEnd_6037176 < baseStart_6037176 := by decide
  rcases family_descends (prefixWord ++ tailWord_6037176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6037194 : List Nat := [3, 1, 2, 1, 6, 1, 1, 3, 1, 2, 2]
def baseStart_6037194 : Nat := 118140960795 + 6037194 * 2 ^ 59
def prefixEnd_6037194 : Nat := 4983230072969 + 3 ^ 40 * 6037194 * 2
def baseEnd_6037194 : Nat := 3099982326439957684410457

theorem tailTrace_6037194 : CollatzResearch.WordTrace tailWord_6037194 prefixEnd_6037194 3099982326439957684410457 := by
  unfold tailWord_6037194
  simp only [CollatzResearch.WordTrace]
  refine ⟨55048638722571170873145659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146796369926856455661721757 55048638722571170873145659)
  ·
    refine ⟨82572958083856756309718489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55048638722571170873145659 82572958083856756309718489)
    ·
      refine ⟨61929718562892567232288867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82572958083856756309718489 61929718562892567232288867)
      ·
        refine ⟨92894577844338850848433301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61929718562892567232288867 92894577844338850848433301)
        ·
          refine ⟨4354433336453383633520311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 92894577844338850848433301 4354433336453383633520311)
          ·
            refine ⟨6531650004680075450280467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4354433336453383633520311 6531650004680075450280467)
            ·
              refine ⟨9797475007020113175420701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6531650004680075450280467 9797475007020113175420701)
              ·
                refine ⟨3674053127632542440782763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9797475007020113175420701 3674053127632542440782763)
                ·
                  refine ⟨5511079691448813661174145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3674053127632542440782763 5511079691448813661174145)
                  ·
                    refine ⟨4133309768586610245880609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5511079691448813661174145 4133309768586610245880609)
                    ·
                      refine ⟨3099982326439957684410457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4133309768586610245880609 3099982326439957684410457)
                      ·
                        rfl

theorem cell23_6037194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 6, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 6, 1, 1, 3, 1, 2, 2].length) (baseStart_6037194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6037194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6037194 prefixEnd_6037194 := by exact prefixLift 6037194
  have htrace : WordTrace (prefixWord ++ tailWord_6037194) baseStart_6037194 baseEnd_6037194 := by
    simpa [prefixWord, tailWord_6037194, baseEnd_6037194] using wordTrace_append hprefix tailTrace_6037194
  have hstable : (prefixWord ++ tailWord_6037194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6037194).length < 2 ^ (prefixWord ++ tailWord_6037194).sum := by decide
  have hdescent : baseEnd_6037194 < baseStart_6037194 := by decide
  rcases family_descends (prefixWord ++ tailWord_6037194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6037256 : List Nat := [2, 1, 3, 2, 2, 1, 2, 5, 5]
def baseStart_6037256 : Nat := 118140960795 + 6037256 * 2 ^ 59
def prefixEnd_6037256 : Nat := 4983230072969 + 3 ^ 40 * 6037256 * 2
def baseEnd_6037256 : Nat := 344446018026726271315019

theorem tailTrace_6037256 : CollatzResearch.WordTrace tailWord_6037256 prefixEnd_6037256 344446018026726271315019 := by
  unfold tailWord_6037256
  simp only [CollatzResearch.WordTrace]
  refine ⟨110098408108030034040669811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146797877477373378720893081 110098408108030034040669811)
  ·
    refine ⟨165147612162045051061004717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110098408108030034040669811 165147612162045051061004717)
    ·
      refine ⟨61930354560766894147876769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 165147612162045051061004717 61930354560766894147876769)
      ·
        refine ⟨46447765920575170610907577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61930354560766894147876769 46447765920575170610907577)
        ·
          refine ⟨34835824440431377958180683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46447765920575170610907577 34835824440431377958180683)
          ·
            refine ⟨52253736660647066937271025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34835824440431377958180683 52253736660647066937271025)
            ·
              refine ⟨39190302495485300202953269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52253736660647066937271025 39190302495485300202953269)
              ·
                refine ⟨3674090858951746894026869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 39190302495485300202953269 3674090858951746894026869)
                ·
                  refine ⟨344446018026726271315019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3674090858951746894026869 344446018026726271315019)
                  ·
                    rfl

theorem cell23_6037256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 5, 5].length) (baseStart_6037256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6037256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6037256 prefixEnd_6037256 := by exact prefixLift 6037256
  have htrace : WordTrace (prefixWord ++ tailWord_6037256) baseStart_6037256 baseEnd_6037256 := by
    simpa [prefixWord, tailWord_6037256, baseEnd_6037256] using wordTrace_append hprefix tailTrace_6037256
  have hstable : (prefixWord ++ tailWord_6037256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6037256).length < 2 ^ (prefixWord ++ tailWord_6037256).sum := by decide
  have hdescent : baseEnd_6037256 < baseStart_6037256 := by decide
  rcases family_descends (prefixWord ++ tailWord_6037256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6037261 : List Nat := [1, 7, 2, 1, 1, 1, 2, 2, 2, 1, 3]
def baseStart_6037261 : Nat := 118140960795 + 6037261 * 2 ^ 59
def prefixEnd_6037261 : Nat := 4983230072969 + 3 ^ 40 * 6037261 * 2
def baseEnd_6037261 : Nat := 3100016729643808922272649

theorem tailTrace_6037261 : CollatzResearch.WordTrace tailWord_6037261 prefixEnd_6037261 3100016729643808922272649 := by
  unfold tailWord_6037261
  simp only [CollatzResearch.WordTrace]
  refine ⟨220196998581041953935271637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146797999054027969290181091 220196998581041953935271637)
  ·
    refine ⟨5160867154243170795357929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 220196998581041953935271637 5160867154243170795357929)
    ·
      refine ⟨3870650365682378096518447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5160867154243170795357929 3870650365682378096518447)
      ·
        refine ⟨5805975548523567144777671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3870650365682378096518447 5805975548523567144777671)
        ·
          refine ⟨8708963322785350717166507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5805975548523567144777671 8708963322785350717166507)
          ·
            refine ⟨13063444984178026075749761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8708963322785350717166507 13063444984178026075749761)
            ·
              refine ⟨9797583738133519556812321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13063444984178026075749761 9797583738133519556812321)
              ·
                refine ⟨7348187803600139667609241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9797583738133519556812321 7348187803600139667609241)
                ·
                  refine ⟨5511140852700104750706931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7348187803600139667609241 5511140852700104750706931)
                  ·
                    refine ⟨8266711279050157126060397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5511140852700104750706931 8266711279050157126060397)
                    ·
                      refine ⟨3100016729643808922272649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8266711279050157126060397 3100016729643808922272649)
                      ·
                        rfl

theorem cell23_6037261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 2, 2, 2, 1, 3].length) (baseStart_6037261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6037261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6037261 prefixEnd_6037261 := by exact prefixLift 6037261
  have htrace : WordTrace (prefixWord ++ tailWord_6037261) baseStart_6037261 baseEnd_6037261 := by
    simpa [prefixWord, tailWord_6037261, baseEnd_6037261] using wordTrace_append hprefix tailTrace_6037261
  have hstable : (prefixWord ++ tailWord_6037261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6037261).length < 2 ^ (prefixWord ++ tailWord_6037261).sum := by decide
  have hdescent : baseEnd_6037261 < baseStart_6037261 := by decide
  rcases family_descends (prefixWord ++ tailWord_6037261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6037276 : List Nat := [2, 2, 3, 1, 1, 2, 1, 1, 1, 7, 2]
def baseStart_6037276 : Nat := 118140960795 + 6037276 * 2 ^ 59
def prefixEnd_6037276 : Nat := 4983230072969 + 3 ^ 40 * 6037276 * 2
def baseEnd_6037276 : Nat := 3100024431853626363585079

theorem tailTrace_6037276 : CollatzResearch.WordTrace tailWord_6037276 prefixEnd_6037276 3100024431853626363585079 := by
  unfold tailWord_6037276
  simp only [CollatzResearch.WordTrace]
  refine ⟨110098772837993805748533841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146798363783991740998045121 110098772837993805748533841)
  ·
    refine ⟨82574079628495354311400381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110098772837993805748533841 82574079628495354311400381)
    ·
      refine ⟨30965279860685757866775143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82574079628495354311400381 30965279860685757866775143)
      ·
        refine ⟨46447919791028636800162715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30965279860685757866775143 46447919791028636800162715)
        ·
          refine ⟨69671879686542955200244073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46447919791028636800162715 69671879686542955200244073)
          ·
            refine ⟨52253909764907216400183055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69671879686542955200244073 52253909764907216400183055)
            ·
              refine ⟨78380864647360824600274583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52253909764907216400183055 78380864647360824600274583)
              ·
                refine ⟨117571296971041236900411875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78380864647360824600274583 117571296971041236900411875)
                ·
                  refine ⟨176356945456561855350617813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 117571296971041236900411875 176356945456561855350617813)
                  ·
                    refine ⟨4133365909138168484780105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 176356945456561855350617813 4133365909138168484780105)
                    ·
                      refine ⟨3100024431853626363585079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4133365909138168484780105 3100024431853626363585079)
                      ·
                        rfl

theorem cell23_6037276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 1, 1, 7, 2].length) (baseStart_6037276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6037276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6037276 prefixEnd_6037276 := by exact prefixLift 6037276
  have htrace : WordTrace (prefixWord ++ tailWord_6037276) baseStart_6037276 baseEnd_6037276 := by
    simpa [prefixWord, tailWord_6037276, baseEnd_6037276] using wordTrace_append hprefix tailTrace_6037276
  have hstable : (prefixWord ++ tailWord_6037276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6037276).length < 2 ^ (prefixWord ++ tailWord_6037276).sum := by decide
  have hdescent : baseEnd_6037276 < baseStart_6037276 := by decide
  rcases family_descends (prefixWord ++ tailWord_6037276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6037279 : List Nat := [1, 1, 2, 4, 2, 1, 1, 3, 1, 2, 5]
def baseStart_6037279 : Nat := 118140960795 + 6037279 * 2 ^ 59
def prefixEnd_6037279 : Nat := 4983230072969 + 3 ^ 40 * 6037279 * 2
def baseEnd_6037279 : Nat := 3100025972295589851847565

theorem tailTrace_6037279 : CollatzResearch.WordTrace tailWord_6037279 prefixEnd_6037279 3100025972295589851847565 := by
  unfold tailWord_6037279
  simp only [CollatzResearch.WordTrace]
  refine ⟨220197655094976743009426891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146798436729984495339617927 220197655094976743009426891)
  ·
    refine ⟨330296482642465114514140337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220197655094976743009426891 330296482642465114514140337)
    ·
      refine ⟨247722361981848835885605253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 330296482642465114514140337 247722361981848835885605253)
      ·
        refine ⟨46447942871596656728550985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 247722361981848835885605253 46447942871596656728550985)
        ·
          refine ⟨34835957153697492546413239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46447942871596656728550985 34835957153697492546413239)
          ·
            refine ⟨52253935730546238819619859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34835957153697492546413239 52253935730546238819619859)
            ·
              refine ⟨78380903595819358229429789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52253935730546238819619859 78380903595819358229429789)
              ·
                refine ⟨29392838848432259336036171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 78380903595819358229429789 29392838848432259336036171)
                ·
                  refine ⟨44089258272648389004054257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29392838848432259336036171 44089258272648389004054257)
                  ·
                    refine ⟨33066943704486291753040693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 44089258272648389004054257 33066943704486291753040693)
                    ·
                      refine ⟨3100025972295589851847565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33066943704486291753040693 3100025972295589851847565)
                      ·
                        rfl

theorem cell23_6037279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 3, 1, 2, 5].length) (baseStart_6037279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6037279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6037279 prefixEnd_6037279 := by exact prefixLift 6037279
  have htrace : WordTrace (prefixWord ++ tailWord_6037279) baseStart_6037279 baseEnd_6037279 := by
    simpa [prefixWord, tailWord_6037279, baseEnd_6037279] using wordTrace_append hprefix tailTrace_6037279
  have hstable : (prefixWord ++ tailWord_6037279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6037279).length < 2 ^ (prefixWord ++ tailWord_6037279).sum := by decide
  have hdescent : baseEnd_6037279 < baseStart_6037279 := by decide
  rcases family_descends (prefixWord ++ tailWord_6037279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6037306 : List Nat := [3, 1, 1, 1, 5, 2, 1, 1, 1, 3, 4]
def baseStart_6037306 : Nat := 118140960795 + 6037306 * 2 ^ 59
def prefixEnd_6037306 : Nat := 4983230072969 + 3 ^ 40 * 6037306 * 2
def baseEnd_6037306 : Nat := 3100039836273261246209941

theorem tailTrace_6037306 : CollatzResearch.WordTrace tailWord_6037306 prefixEnd_6037306 3100039836273261246209941 := by
  unfold tailWord_6037306
  simp only [CollatzResearch.WordTrace]
  refine ⟨55049659966469731655164943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146799093243919284413773181 55049659966469731655164943)
  ·
    refine ⟨82574489949704597482747415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55049659966469731655164943 82574489949704597482747415)
    ·
      refine ⟨123861734924556896224121123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82574489949704597482747415 123861734924556896224121123)
      ·
        refine ⟨185792602386835344336181685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123861734924556896224121123 185792602386835344336181685)
        ·
          refine ⟨17418056473765813531517033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 185792602386835344336181685 17418056473765813531517033)
          ·
            refine ⟨13063542355324360148637775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17418056473765813531517033 13063542355324360148637775)
            ·
              refine ⟨19595313532986540222956663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13063542355324360148637775 19595313532986540222956663)
              ·
                refine ⟨29392970299479810334434995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19595313532986540222956663 29392970299479810334434995)
                ·
                  refine ⟨44089455449219715501652493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29392970299479810334434995 44089455449219715501652493)
                  ·
                    refine ⟨16533545793457393313119685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 44089455449219715501652493 16533545793457393313119685)
                    ·
                      refine ⟨3100039836273261246209941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16533545793457393313119685 3100039836273261246209941)
                      ·
                        rfl

theorem cell23_6037306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 1, 1, 1, 3, 4].length) (baseStart_6037306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6037306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6037306 prefixEnd_6037306 := by exact prefixLift 6037306
  have htrace : WordTrace (prefixWord ++ tailWord_6037306) baseStart_6037306 baseEnd_6037306 := by
    simpa [prefixWord, tailWord_6037306, baseEnd_6037306] using wordTrace_append hprefix tailTrace_6037306
  have hstable : (prefixWord ++ tailWord_6037306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6037306).length < 2 ^ (prefixWord ++ tailWord_6037306).sum := by decide
  have hdescent : baseEnd_6037306 < baseStart_6037306 := by decide
  rcases family_descends (prefixWord ++ tailWord_6037306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6037319 : List Nat := [1, 1, 4, 1, 2, 1, 3, 1, 2, 1, 6]
def baseStart_6037319 : Nat := 118140960795 + 6037319 * 2 ^ 59
def prefixEnd_6037319 : Nat := 4983230072969 + 3 ^ 40 * 6037319 * 2
def baseEnd_6037319 : Nat := 3100046511521769695347381

theorem tailTrace_6037319 : CollatzResearch.WordTrace tailWord_6037319 prefixEnd_6037319 3100046511521769695347381 := by
  unfold tailWord_6037319
  simp only [CollatzResearch.WordTrace]
  refine ⟨220199114014831829840883011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146799409343221219893922007 220199114014831829840883011)
  ·
    refine ⟨330298671022247744761324517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220199114014831829840883011 330298671022247744761324517)
    ·
      refine ⟨61931000816671452142748347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 330298671022247744761324517 61931000816671452142748347)
      ·
        refine ⟨92896501225007178214122521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61931000816671452142748347 92896501225007178214122521)
        ·
          refine ⟨69672375918755383660591891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92896501225007178214122521 69672375918755383660591891)
          ·
            refine ⟨104508563878133075490887837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69672375918755383660591891 104508563878133075490887837)
            ·
              refine ⟨39190711454299903309082939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 104508563878133075490887837 39190711454299903309082939)
              ·
                refine ⟨58786067181449854963624409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39190711454299903309082939 58786067181449854963624409)
                ·
                  refine ⟨44089550386087391222718307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 58786067181449854963624409 44089550386087391222718307)
                  ·
                    refine ⟨66134325579131086834077461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 44089550386087391222718307 66134325579131086834077461)
                    ·
                      refine ⟨3100046511521769695347381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 66134325579131086834077461 3100046511521769695347381)
                      ·
                        rfl

theorem cell23_6037319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 1, 2, 1, 6].length) (baseStart_6037319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6037319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6037319 prefixEnd_6037319 := by exact prefixLift 6037319
  have htrace : WordTrace (prefixWord ++ tailWord_6037319) baseStart_6037319 baseEnd_6037319 := by
    simpa [prefixWord, tailWord_6037319, baseEnd_6037319] using wordTrace_append hprefix tailTrace_6037319
  have hstable : (prefixWord ++ tailWord_6037319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6037319).length < 2 ^ (prefixWord ++ tailWord_6037319).sum := by decide
  have hdescent : baseEnd_6037319 < baseStart_6037319 := by decide
  rcases family_descends (prefixWord ++ tailWord_6037319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6037333 : List Nat := [1, 3, 2, 2, 2, 3, 2, 1, 3, 4]
def baseStart_6037333 : Nat := 118140960795 + 6037333 * 2 ^ 59
def prefixEnd_6037333 : Nat := 4983230072969 + 3 ^ 40 * 6037333 * 2
def baseEnd_6037333 : Nat := 1033351233416977546857439

theorem tailTrace_6037333 : CollatzResearch.WordTrace tailWord_6037333 prefixEnd_6037333 1033351233416977546857439 := by
  unfold tailWord_6037333
  simp only [CollatzResearch.WordTrace]
  refine ⟨220199624636781110231892653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146799749757854073487928435 220199624636781110231892653)
  ·
    refine ⟨82574859238792916336959745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 220199624636781110231892653 82574859238792916336959745)
    ·
      refine ⟨61931144429094687252719809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82574859238792916336959745 61931144429094687252719809)
      ·
        refine ⟨46448358321821015439539857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61931144429094687252719809 46448358321821015439539857)
        ·
          refine ⟨34836268741365761579654893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46448358321821015439539857 34836268741365761579654893)
          ·
            refine ⟨13063600778012160592370585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34836268741365761579654893 13063600778012160592370585)
            ·
              refine ⟨9797700583509120444277939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13063600778012160592370585 9797700583509120444277939)
              ·
                refine ⟨14696550875263680666416909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9797700583509120444277939 14696550875263680666416909)
                ·
                  refine ⟨5511206578223880249906341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14696550875263680666416909 5511206578223880249906341)
                  ·
                    refine ⟨1033351233416977546857439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5511206578223880249906341 1033351233416977546857439)
                    ·
                      rfl

theorem cell23_6037333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 2, 1, 3, 4].length) (baseStart_6037333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6037333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6037333 prefixEnd_6037333 := by exact prefixLift 6037333
  have htrace : WordTrace (prefixWord ++ tailWord_6037333) baseStart_6037333 baseEnd_6037333 := by
    simpa [prefixWord, tailWord_6037333, baseEnd_6037333] using wordTrace_append hprefix tailTrace_6037333
  have hstable : (prefixWord ++ tailWord_6037333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6037333).length < 2 ^ (prefixWord ++ tailWord_6037333).sum := by decide
  have hdescent : baseEnd_6037333 < baseStart_6037333 := by decide
  rcases family_descends (prefixWord ++ tailWord_6037333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6037349 : List Nat := [1, 3, 1, 3, 1, 1, 1, 1, 3, 2, 6]
def baseStart_6037349 : Nat := 118140960795 + 6037349 * 2 ^ 59
def prefixEnd_6037349 : Nat := 4983230072969 + 3 ^ 40 * 6037349 * 2
def baseEnd_6037349 : Nat := 3100061915941404577972243

theorem tailTrace_6037349 : CollatzResearch.WordTrace tailWord_6037349 prefixEnd_6037349 3100061915941404577972243 := by
  unfold tailWord_6037349
  simp only [CollatzResearch.WordTrace]
  refine ⟨220200208204723144964475101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146800138803148763309650067 220200208204723144964475101)
  ·
    refine ⟨82575078076771179361678163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 220200208204723144964475101 82575078076771179361678163)
    ·
      refine ⟨123862617115156769042517245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82575078076771179361678163 123862617115156769042517245)
      ·
        refine ⟨46448481418183788390943967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 123862617115156769042517245 46448481418183788390943967)
        ·
          refine ⟨69672722127275682586415951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46448481418183788390943967 69672722127275682586415951)
          ·
            refine ⟨104509083190913523879623927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69672722127275682586415951 104509083190913523879623927)
            ·
              refine ⟨156763624786370285819435891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104509083190913523879623927 156763624786370285819435891)
              ·
                refine ⟨235145437179555428729153837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 156763624786370285819435891 235145437179555428729153837)
                ·
                  refine ⟨88179538942333285773432689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 235145437179555428729153837 88179538942333285773432689)
                  ·
                    refine ⟨66134654206749964330074517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 88179538942333285773432689 66134654206749964330074517)
                    ·
                      refine ⟨3100061915941404577972243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 66134654206749964330074517 3100061915941404577972243)
                      ·
                        rfl

theorem cell23_6037349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 1, 3, 2, 6].length) (baseStart_6037349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6037349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6037349 prefixEnd_6037349 := by exact prefixLift 6037349
  have htrace : WordTrace (prefixWord ++ tailWord_6037349) baseStart_6037349 baseEnd_6037349 := by
    simpa [prefixWord, tailWord_6037349, baseEnd_6037349] using wordTrace_append hprefix tailTrace_6037349
  have hstable : (prefixWord ++ tailWord_6037349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6037349).length < 2 ^ (prefixWord ++ tailWord_6037349).sum := by decide
  have hdescent : baseEnd_6037349 < baseStart_6037349 := by decide
  rcases family_descends (prefixWord ++ tailWord_6037349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6037376 : List Nat := [2, 1, 1, 2, 1, 2, 3, 5, 1, 5]
def baseStart_6037376 : Nat := 118140960795 + 6037376 * 2 ^ 59
def prefixEnd_6037376 : Nat := 4983230072969 + 3 ^ 40 * 6037376 * 2
def baseEnd_6037376 : Nat := 1033358593306358657444873

theorem tailTrace_6037376 : CollatzResearch.WordTrace tailWord_6037376 prefixEnd_6037376 1033358593306358657444873 := by
  unfold tailWord_6037376
  simp only [CollatzResearch.WordTrace]
  refine ⟨110100596487812664287853991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146800795317083552383805321 110100596487812664287853991)
  ·
    refine ⟨165150894731718996431780987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110100596487812664287853991 165150894731718996431780987)
    ·
      refine ⟨247726342097578494647671481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165150894731718996431780987 247726342097578494647671481)
      ·
        refine ⟨185794756573183870985753611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 247726342097578494647671481 185794756573183870985753611)
        ·
          refine ⟨278692134859775806478630417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 185794756573183870985753611 278692134859775806478630417)
          ·
            refine ⟨209019101144831854858972813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 278692134859775806478630417 209019101144831854858972813)
            ·
              refine ⟨78382162929311945572114805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 209019101144831854858972813 78382162929311945572114805)
              ·
                refine ⟨7348327774622994897385763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 78382162929311945572114805 7348327774622994897385763)
                ·
                  refine ⟨11022491661934492346078645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7348327774622994897385763 11022491661934492346078645)
                  ·
                    refine ⟨1033358593306358657444873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11022491661934492346078645 1033358593306358657444873)
                    ·
                      rfl

theorem cell23_6037376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 5, 1, 5].length) (baseStart_6037376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6037376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6037376 prefixEnd_6037376 := by exact prefixLift 6037376
  have htrace : WordTrace (prefixWord ++ tailWord_6037376) baseStart_6037376 baseEnd_6037376 := by
    simpa [prefixWord, tailWord_6037376, baseEnd_6037376] using wordTrace_append hprefix tailTrace_6037376
  have hstable : (prefixWord ++ tailWord_6037376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6037376).length < 2 ^ (prefixWord ++ tailWord_6037376).sum := by decide
  have hdescent : baseEnd_6037376 < baseStart_6037376 := by decide
  rcases family_descends (prefixWord ++ tailWord_6037376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6037436 : List Nat := [2, 2, 2, 5, 12]
def baseStart_6037436 : Nat := 118140960795 + 6037436 * 2 ^ 59
def prefixEnd_6037436 : Nat := 4983230072969 + 3 ^ 40 * 6037436 * 2
def baseEnd_6037436 : Nat := 4252546760985385099567

theorem tailTrace_6037436 : CollatzResearch.WordTrace tailWord_6037436 prefixEnd_6037436 4252546760985385099567 := by
  unfold tailWord_6037436
  simp only [CollatzResearch.WordTrace]
  refine ⟨110101690677703979411446081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146802254236938639215261441 110101690677703979411446081)
  ·
    refine ⟨82576268008277984558584561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110101690677703979411446081 82576268008277984558584561)
    ·
      refine ⟨61932201006208488418938421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82576268008277984558584561 61932201006208488418938421)
      ·
        refine ⟨5806143844332045789275477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 61932201006208488418938421 5806143844332045789275477)
        ·
          refine ⟨4252546760985385099567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 5806143844332045789275477 4252546760985385099567)
          ·
            rfl

theorem cell23_6037436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 12].length) (baseStart_6037436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6037436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6037436 prefixEnd_6037436 := by exact prefixLift 6037436
  have htrace : WordTrace (prefixWord ++ tailWord_6037436) baseStart_6037436 baseEnd_6037436 := by
    simpa [prefixWord, tailWord_6037436, baseEnd_6037436] using wordTrace_append hprefix tailTrace_6037436
  have hstable : (prefixWord ++ tailWord_6037436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6037436).length < 2 ^ (prefixWord ++ tailWord_6037436).sum := by decide
  have hdescent : baseEnd_6037436 < baseStart_6037436 := by decide
  rcases family_descends (prefixWord ++ tailWord_6037436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6037463 : List Nat := [1, 1, 3, 2, 1, 1, 6, 1, 1, 3, 3]
def baseStart_6037463 : Nat := 118140960795 + 6037463 * 2 ^ 59
def prefixEnd_6037463 : Nat := 4983230072969 + 3 ^ 40 * 6037463 * 2
def baseEnd_6037463 : Nat := 3100120452736017131946719

theorem tailTrace_6037463 : CollatzResearch.WordTrace tailWord_6037463 prefixEnd_6037463 3100120452736017131946719 := by
  unfold tailWord_6037463
  simp only [CollatzResearch.WordTrace]
  refine ⟨220204366126310142434125043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146802910750873428289416695 220204366126310142434125043)
  ·
    refine ⟨330306549189465213651187565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220204366126310142434125043 330306549189465213651187565)
    ·
      refine ⟨123864955946049455119195337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 330306549189465213651187565 123864955946049455119195337)
      ·
        refine ⟨92898716959537091339396503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123864955946049455119195337 92898716959537091339396503)
        ·
          refine ⟨139348075439305637009094755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92898716959537091339396503 139348075439305637009094755)
          ·
            refine ⟨209022113158958455513642133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139348075439305637009094755 209022113158958455513642133)
            ·
              refine ⟨9797911554326177602201975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 209022113158958455513642133 9797911554326177602201975)
              ·
                refine ⟨14696867331489266403302963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9797911554326177602201975 14696867331489266403302963)
                ·
                  refine ⟨22045300997233899604954445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14696867331489266403302963 22045300997233899604954445)
                  ·
                    refine ⟨8266987873962712351857917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22045300997233899604954445 8266987873962712351857917)
                    ·
                      refine ⟨3100120452736017131946719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8266987873962712351857917 3100120452736017131946719)
                      ·
                        rfl

theorem cell23_6037463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 6, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 6, 1, 1, 3, 3].length) (baseStart_6037463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6037463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6037463 prefixEnd_6037463 := by exact prefixLift 6037463
  have htrace : WordTrace (prefixWord ++ tailWord_6037463) baseStart_6037463 baseEnd_6037463 := by
    simpa [prefixWord, tailWord_6037463, baseEnd_6037463] using wordTrace_append hprefix tailTrace_6037463
  have hstable : (prefixWord ++ tailWord_6037463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6037463).length < 2 ^ (prefixWord ++ tailWord_6037463).sum := by decide
  have hdescent : baseEnd_6037463 < baseStart_6037463 := by decide
  rcases family_descends (prefixWord ++ tailWord_6037463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6037468 : List Nat := [2, 2, 6, 1, 2, 1, 1, 1, 2, 3, 2]
def baseStart_6037468 : Nat := 118140960795 + 6037468 * 2 ^ 59
def prefixEnd_6037468 : Nat := 4983230072969 + 3 ^ 40 * 6037468 * 2
def baseEnd_6037468 : Nat := 3100123020139289612384197

theorem tailTrace_6037468 : CollatzResearch.WordTrace tailWord_6037468 prefixEnd_6037468 3100123020139289612384197 := by
  unfold tailWord_6037468
  simp only [CollatzResearch.WordTrace]
  refine ⟨110102274245646014144028529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146803032327528018858704705 110102274245646014144028529)
  ·
    refine ⟨82576705684234510608021397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110102274245646014144028529 82576705684234510608021397)
    ·
      refine ⟨3870783078948492684751003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 82576705684234510608021397 3870783078948492684751003)
      ·
        refine ⟨5806174618422739027126505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3870783078948492684751003 5806174618422739027126505)
        ·
          refine ⟨4354630963817054270344879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5806174618422739027126505 4354630963817054270344879)
          ·
            refine ⟨6531946445725581405517319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4354630963817054270344879 6531946445725581405517319)
            ·
              refine ⟨9797919668588372108275979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6531946445725581405517319 9797919668588372108275979)
              ·
                refine ⟨14696879502882558162413969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9797919668588372108275979 14696879502882558162413969)
                ·
                  refine ⟨11022659627161918621810477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14696879502882558162413969 11022659627161918621810477)
                  ·
                    refine ⟨4133497360185719483178929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11022659627161918621810477 4133497360185719483178929)
                    ·
                      refine ⟨3100123020139289612384197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4133497360185719483178929 3100123020139289612384197)
                      ·
                        rfl

theorem cell23_6037468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 2, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 2, 1, 1, 1, 2, 3, 2].length) (baseStart_6037468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6037468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6037468 prefixEnd_6037468 := by exact prefixLift 6037468
  have htrace : WordTrace (prefixWord ++ tailWord_6037468) baseStart_6037468 baseEnd_6037468 := by
    simpa [prefixWord, tailWord_6037468, baseEnd_6037468] using wordTrace_append hprefix tailTrace_6037468
  have hstable : (prefixWord ++ tailWord_6037468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6037468).length < 2 ^ (prefixWord ++ tailWord_6037468).sum := by decide
  have hdescent : baseEnd_6037468 < baseStart_6037468 := by decide
  rcases family_descends (prefixWord ++ tailWord_6037468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6037476 : List Nat := [2, 3, 1, 1, 1, 1, 4, 1, 2, 2, 5]
def baseStart_6037476 : Nat := 118140960795 + 6037476 * 2 ^ 59
def prefixEnd_6037476 : Nat := 4983230072969 + 3 ^ 40 * 6037476 * 2
def baseEnd_6037476 : Nat := 3100127127984525581084159

theorem tailTrace_6037476 : CollatzResearch.WordTrace tailWord_6037476 prefixEnd_6037476 3100127127984525581084159 := by
  unfold tailWord_6037476
  simp only [CollatzResearch.WordTrace]
  refine ⟨110102420137631522827174141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146803226850175363769565521 110102420137631522827174141)
  ·
    refine ⟨41288407551611821060190303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110102420137631522827174141 41288407551611821060190303)
    ·
      refine ⟨61932611327417731590285455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41288407551611821060190303 61932611327417731590285455)
      ·
        refine ⟨92898916991126597385428183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61932611327417731590285455 92898916991126597385428183)
        ·
          refine ⟨139348375486689896078142275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92898916991126597385428183 139348375486689896078142275)
          ·
            refine ⟨209022563230034844117213413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139348375486689896078142275 209022563230034844117213413)
            ·
              refine ⟨39191730605631533271977515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 209022563230034844117213413 39191730605631533271977515)
              ·
                refine ⟨58787595908447299907966273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39191730605631533271977515 58787595908447299907966273)
                ·
                  refine ⟨44090696931335474930974705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 58787595908447299907966273 44090696931335474930974705)
                  ·
                    refine ⟨33068022698501606198231029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 44090696931335474930974705 33068022698501606198231029)
                    ·
                      refine ⟨3100127127984525581084159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33068022698501606198231029 3100127127984525581084159)
                      ·
                        rfl

theorem cell23_6037476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 1, 2, 2, 5].length) (baseStart_6037476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6037476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6037476 prefixEnd_6037476 := by exact prefixLift 6037476
  have htrace : WordTrace (prefixWord ++ tailWord_6037476) baseStart_6037476 baseEnd_6037476 := by
    simpa [prefixWord, tailWord_6037476, baseEnd_6037476] using wordTrace_append hprefix tailTrace_6037476
  have hstable : (prefixWord ++ tailWord_6037476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6037476).length < 2 ^ (prefixWord ++ tailWord_6037476).sum := by decide
  have hdescent : baseEnd_6037476 < baseStart_6037476 := by decide
  rcases family_descends (prefixWord ++ tailWord_6037476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6037496 : List Nat := [2, 1, 2, 1, 1, 3, 3, 2, 2, 6]
def baseStart_6037496 : Nat := 118140960795 + 6037496 * 2 ^ 59
def prefixEnd_6037496 : Nat := 4983230072969 + 3 ^ 40 * 6037496 * 2
def baseEnd_6037496 : Nat := 1033379132532538500944689

theorem tailTrace_6037496 : CollatzResearch.WordTrace tailWord_6037496 prefixEnd_6037496 1033379132532538500944689 := by
  unfold tailWord_6037496
  simp only [CollatzResearch.WordTrace]
  refine ⟨110102784867595294535038171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146803713156793726046717561 110102784867595294535038171)
  ·
    refine ⟨165154177301392941802557257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110102784867595294535038171 165154177301392941802557257)
    ·
      refine ⟨123865632976044706351917943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 165154177301392941802557257 123865632976044706351917943)
      ·
        refine ⟨185798449464067059527876915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123865632976044706351917943 185798449464067059527876915)
        ·
          refine ⟨278697674196100589291815373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 185798449464067059527876915 278697674196100589291815373)
          ·
            refine ⟨104511627823537720984430765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 278697674196100589291815373 104511627823537720984430765)
            ·
              refine ⟨39191860433826645369161537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 104511627823537720984430765 39191860433826645369161537)
              ·
                refine ⟨29393895325369984026871153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39191860433826645369161537 29393895325369984026871153)
                ·
                  refine ⟨22045421494027488020153365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29393895325369984026871153 22045421494027488020153365)
                  ·
                    refine ⟨1033379132532538500944689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22045421494027488020153365 1033379132532538500944689)
                    ·
                      rfl

theorem cell23_6037496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 2, 2, 6].length) (baseStart_6037496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6037496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6037496 prefixEnd_6037496 := by exact prefixLift 6037496
  have htrace : WordTrace (prefixWord ++ tailWord_6037496) baseStart_6037496 baseEnd_6037496 := by
    simpa [prefixWord, tailWord_6037496, baseEnd_6037496] using wordTrace_append hprefix tailTrace_6037496
  have hstable : (prefixWord ++ tailWord_6037496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6037496).length < 2 ^ (prefixWord ++ tailWord_6037496).sum := by decide
  have hdescent : baseEnd_6037496 < baseStart_6037496 := by decide
  rcases family_descends (prefixWord ++ tailWord_6037496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6037497 : List Nat := [1, 2, 1, 3, 1, 6, 1, 2, 2, 1, 3]
def baseStart_6037497 : Nat := 118140960795 + 6037497 * 2 ^ 59
def prefixEnd_6037497 : Nat := 4983230072969 + 3 ^ 40 * 6037497 * 2
def baseEnd_6037497 : Nat := 3100137911078269998921563

theorem tailTrace_6037497 : CollatzResearch.WordTrace tailWord_6037497 prefixEnd_6037497 3100137911078269998921563 := by
  unfold tailWord_6037497
  simp only [CollatzResearch.WordTrace]
  refine ⟨220205606208186966240862745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146803737472124644160575163 220205606208186966240862745)
  ·
    refine ⟨165154204656140224680647059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 220205606208186966240862745 165154204656140224680647059)
    ·
      refine ⟨247731306984210337020970589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165154204656140224680647059 247731306984210337020970589)
      ·
        refine ⟨92899240119078876382863971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 247731306984210337020970589 92899240119078876382863971)
        ·
          refine ⟨139348860178618314574295957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92899240119078876382863971 139348860178618314574295957)
          ·
            refine ⟨6531977820872733495670123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 139348860178618314574295957 6531977820872733495670123)
            ·
              refine ⟨9797966731309100243505185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6531977820872733495670123 9797966731309100243505185)
              ·
                refine ⟨7348475048481825182628889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9797966731309100243505185 7348475048481825182628889)
                ·
                  refine ⟨5511356286361368886971667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7348475048481825182628889 5511356286361368886971667)
                  ·
                    refine ⟨8267034429542053330457501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5511356286361368886971667 8267034429542053330457501)
                    ·
                      refine ⟨3100137911078269998921563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8267034429542053330457501 3100137911078269998921563)
                      ·
                        rfl

theorem cell23_6037497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 6, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 6, 1, 2, 2, 1, 3].length) (baseStart_6037497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6037497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6037497 prefixEnd_6037497 := by exact prefixLift 6037497
  have htrace : WordTrace (prefixWord ++ tailWord_6037497) baseStart_6037497 baseEnd_6037497 := by
    simpa [prefixWord, tailWord_6037497, baseEnd_6037497] using wordTrace_append hprefix tailTrace_6037497
  have hstable : (prefixWord ++ tailWord_6037497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6037497).length < 2 ^ (prefixWord ++ tailWord_6037497).sum := by decide
  have hdescent : baseEnd_6037497 < baseStart_6037497 := by decide
  rcases family_descends (prefixWord ++ tailWord_6037497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6037503 : List Nat := [1, 1, 2, 2, 1, 2, 1, 4, 3, 4, 2]
def baseStart_6037503 : Nat := 118140960795 + 6037503 * 2 ^ 59
def prefixEnd_6037503 : Nat := 4983230072969 + 3 ^ 40 * 6037503 * 2
def baseEnd_6037503 : Nat := 3100140991962196975446535

theorem tailTrace_6037503 : CollatzResearch.WordTrace tailWord_6037503 prefixEnd_6037503 3100140991962196975446535 := by
  unfold tailWord_6037503
  simp only [CollatzResearch.WordTrace]
  refine ⟨220205825046165229265581163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146803883364110152843720775 220205825046165229265581163)
  ·
    refine ⟨330308737569247843898371745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220205825046165229265581163 330308737569247843898371745)
    ·
      refine ⟨247731553176935882923778809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 330308737569247843898371745 247731553176935882923778809)
      ·
        refine ⟨185798664882701912192834107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 247731553176935882923778809 185798664882701912192834107)
        ·
          refine ⟨278697997324052868289251161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 185798664882701912192834107 278697997324052868289251161)
          ·
            refine ⟨209023497993039651216938371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 278697997324052868289251161 209023497993039651216938371)
            ·
              refine ⟨313535246989559476825407557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 209023497993039651216938371 313535246989559476825407557)
              ·
                refine ⟨58787858810542401904763917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 313535246989559476825407557 58787858810542401904763917)
                ·
                  refine ⟨22045447053953400714286469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 58787858810542401904763917 22045447053953400714286469)
                  ·
                    refine ⟨4133521322616262633928713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22045447053953400714286469 4133521322616262633928713)
                    ·
                      refine ⟨3100140991962196975446535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4133521322616262633928713 3100140991962196975446535)
                      ·
                        rfl

theorem cell23_6037503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 4, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 4, 3, 4, 2].length) (baseStart_6037503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6037503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6037503 prefixEnd_6037503 := by exact prefixLift 6037503
  have htrace : WordTrace (prefixWord ++ tailWord_6037503) baseStart_6037503 baseEnd_6037503 := by
    simpa [prefixWord, tailWord_6037503, baseEnd_6037503] using wordTrace_append hprefix tailTrace_6037503
  have hstable : (prefixWord ++ tailWord_6037503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6037503).length < 2 ^ (prefixWord ++ tailWord_6037503).sum := by decide
  have hdescent : baseEnd_6037503 < baseStart_6037503 := by decide
  rcases family_descends (prefixWord ++ tailWord_6037503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6037514 : List Nat := [3, 1, 2, 2, 4, 1, 3, 1, 2, 1, 3]
def baseStart_6037514 : Nat := 118140960795 + 6037514 * 2 ^ 59
def prefixEnd_6037514 : Nat := 4983230072969 + 3 ^ 40 * 6037514 * 2
def baseEnd_6037514 : Nat := 3100146640249396432408985

theorem tailTrace_6037514 : CollatzResearch.WordTrace tailWord_6037514 prefixEnd_6037514 3100146640249396432408985 := by
  unfold tailWord_6037514
  simp only [CollatzResearch.WordTrace]
  refine ⟨55051556562281344536057899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146804150832750252096154397 55051556562281344536057899)
  ·
    refine ⟨82577334843422016804086849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55051556562281344536057899 82577334843422016804086849)
    ·
      refine ⟨61933001132566512603065137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82577334843422016804086849 61933001132566512603065137)
      ·
        refine ⟨46449750849424884452298853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61933001132566512603065137 46449750849424884452298853)
        ·
          refine ⟨8709328284267165834806035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46449750849424884452298853 8709328284267165834806035)
          ·
            refine ⟨13063992426400748752209053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8709328284267165834806035 13063992426400748752209053)
            ·
              refine ⟨4898997159900280782078395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13063992426400748752209053 4898997159900280782078395)
              ·
                refine ⟨7348495739850421173117593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4898997159900280782078395 7348495739850421173117593)
                ·
                  refine ⟨5511371804887815879838195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7348495739850421173117593 5511371804887815879838195)
                  ·
                    refine ⟨8267057707331723819757293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5511371804887815879838195 8267057707331723819757293)
                    ·
                      refine ⟨3100146640249396432408985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8267057707331723819757293 3100146640249396432408985)
                      ·
                        rfl

theorem cell23_6037514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 3, 1, 2, 1, 3].length) (baseStart_6037514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6037514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6037514 prefixEnd_6037514 := by exact prefixLift 6037514
  have htrace : WordTrace (prefixWord ++ tailWord_6037514) baseStart_6037514 baseEnd_6037514 := by
    simpa [prefixWord, tailWord_6037514, baseEnd_6037514] using wordTrace_append hprefix tailTrace_6037514
  have hstable : (prefixWord ++ tailWord_6037514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6037514).length < 2 ^ (prefixWord ++ tailWord_6037514).sum := by decide
  have hdescent : baseEnd_6037514 < baseStart_6037514 := by decide
  rcases family_descends (prefixWord ++ tailWord_6037514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6037540 : List Nat := [2, 3, 1, 4, 2, 1, 1, 1, 2, 1, 5]
def baseStart_6037540 : Nat := 118140960795 + 6037540 * 2 ^ 59
def prefixEnd_6037540 : Nat := 4983230072969 + 3 ^ 40 * 6037540 * 2
def baseEnd_6037540 : Nat := 3100159990746413330683865

theorem tailTrace_6037540 : CollatzResearch.WordTrace tailWord_6037540 prefixEnd_6037540 3100159990746413330683865 := by
  unfold tailWord_6037540
  simp only [CollatzResearch.WordTrace]
  refine ⟨110103587273515592292339037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146804783031354123056452049 110103587273515592292339037)
  ·
    refine ⟨41288845227568347109627139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110103587273515592292339037 41288845227568347109627139)
    ·
      refine ⟨61933267841352520664440709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41288845227568347109627139 61933267841352520664440709)
      ·
        refine ⟨11612487720253597624582633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 61933267841352520664440709 11612487720253597624582633)
        ·
          refine ⟨8709365790190198218436975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11612487720253597624582633 8709365790190198218436975)
          ·
            refine ⟨13064048685285297327655463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8709365790190198218436975 13064048685285297327655463)
            ·
              refine ⟨19596073027927945991483195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13064048685285297327655463 19596073027927945991483195)
              ·
                refine ⟨29394109541891918987224793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19596073027927945991483195 29394109541891918987224793)
                ·
                  refine ⟨22045582156418939240418595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29394109541891918987224793 22045582156418939240418595)
                  ·
                    refine ⟨33068373234628408860627893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22045582156418939240418595 33068373234628408860627893)
                    ·
                      refine ⟨3100159990746413330683865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33068373234628408860627893 3100159990746413330683865)
                      ·
                        rfl

theorem cell23_6037540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 1, 1, 2, 1, 5].length) (baseStart_6037540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6037540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6037540 prefixEnd_6037540 := by exact prefixLift 6037540
  have htrace : WordTrace (prefixWord ++ tailWord_6037540) baseStart_6037540 baseEnd_6037540 := by
    simpa [prefixWord, tailWord_6037540, baseEnd_6037540] using wordTrace_append hprefix tailTrace_6037540
  have hstable : (prefixWord ++ tailWord_6037540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6037540).length < 2 ^ (prefixWord ++ tailWord_6037540).sum := by decide
  have hdescent : baseEnd_6037540 < baseStart_6037540 := by decide
  rcases family_descends (prefixWord ++ tailWord_6037540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6037560 : List Nat := [2, 1, 2, 1, 6, 2, 1, 1, 7]
def baseStart_6037560 : Nat := 118140960795 + 6037560 * 2 ^ 59
def prefixEnd_6037560 : Nat := 4983230072969 + 3 ^ 40 * 6037560 * 2
def baseEnd_6037560 : Nat := 344463362262167028048197

theorem tailTrace_6037560 : CollatzResearch.WordTrace tailWord_6037560 prefixEnd_6037560 344463362262167028048197 := by
  unfold tailWord_6037560
  simp only [CollatzResearch.WordTrace]
  refine ⟨110103952003479364000203067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146805269337972485333604089 110103952003479364000203067)
  ·
    refine ⟨165155928005219046000304601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110103952003479364000203067 165155928005219046000304601)
    ·
      refine ⟨123866946003914284500228451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 165155928005219046000304601 123866946003914284500228451)
      ·
        refine ⟨185800419005871426750342677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123866946003914284500228451 185800419005871426750342677)
        ·
          refine ⟨8709394640900223128922313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 185800419005871426750342677 8709394640900223128922313)
          ·
            refine ⟨6532045980675167346691735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8709394640900223128922313 6532045980675167346691735)
            ·
              refine ⟨9798068971012751020037603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6532045980675167346691735 9798068971012751020037603)
              ·
                refine ⟨14697103456519126530056405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9798068971012751020037603 14697103456519126530056405)
                ·
                  refine ⟨344463362262167028048197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14697103456519126530056405 344463362262167028048197)
                  ·
                    rfl

theorem cell23_6037560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 2, 1, 1, 7].length) (baseStart_6037560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6037560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6037560 prefixEnd_6037560 := by exact prefixLift 6037560
  have htrace : WordTrace (prefixWord ++ tailWord_6037560) baseStart_6037560 baseEnd_6037560 := by
    simpa [prefixWord, tailWord_6037560, baseEnd_6037560] using wordTrace_append hprefix tailTrace_6037560
  have hstable : (prefixWord ++ tailWord_6037560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6037560).length < 2 ^ (prefixWord ++ tailWord_6037560).sum := by decide
  have hdescent : baseEnd_6037560 < baseStart_6037560 := by decide
  rcases family_descends (prefixWord ++ tailWord_6037560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6037563 : List Nat := [1, 1, 1, 1, 1, 2, 1, 5, 1, 7, 2]
def baseStart_6037563 : Nat := 118140960795 + 6037563 * 2 ^ 59
def prefixEnd_6037563 : Nat := 4983230072969 + 3 ^ 40 * 6037563 * 2
def baseEnd_6037563 : Nat := 3100171800801466740696259

theorem tailTrace_6037563 : CollatzResearch.WordTrace tailWord_6037563 prefixEnd_6037563 3100171800801466740696259 := by
  unfold tailWord_6037563
  simp only [CollatzResearch.WordTrace]
  refine ⟨220208013425947859512765343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146805342283965239675176895 220208013425947859512765343)
  ·
    refine ⟨330312020138921789269148015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220208013425947859512765343 330312020138921789269148015)
    ·
      refine ⟨495468030208382683903722023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 330312020138921789269148015 495468030208382683903722023)
      ·
        refine ⟨743202045312574025855583035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 495468030208382683903722023 743202045312574025855583035)
        ·
          refine ⟨1114803067968861038783374553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 743202045312574025855583035 1114803067968861038783374553)
          ·
            refine ⟨836102300976645779087530915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1114803067968861038783374553 836102300976645779087530915)
            ·
              refine ⟨1254153451464968668631296373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 836102300976645779087530915 1254153451464968668631296373)
              ·
                refine ⟨117576886074840812684184035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1254153451464968668631296373 117576886074840812684184035)
                ·
                  refine ⟨176365329112261219026276053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 117576886074840812684184035 176365329112261219026276053)
                  ·
                    refine ⟨4133562401068622320928345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 176365329112261219026276053 4133562401068622320928345)
                    ·
                      refine ⟨3100171800801466740696259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4133562401068622320928345 3100171800801466740696259)
                      ·
                        rfl

theorem cell23_6037563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 5, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 5, 1, 7, 2].length) (baseStart_6037563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6037563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6037563 prefixEnd_6037563 := by exact prefixLift 6037563
  have htrace : WordTrace (prefixWord ++ tailWord_6037563) baseStart_6037563 baseEnd_6037563 := by
    simpa [prefixWord, tailWord_6037563, baseEnd_6037563] using wordTrace_append hprefix tailTrace_6037563
  have hstable : (prefixWord ++ tailWord_6037563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6037563).length < 2 ^ (prefixWord ++ tailWord_6037563).sum := by decide
  have hdescent : baseEnd_6037563 < baseStart_6037563 := by decide
  rcases family_descends (prefixWord ++ tailWord_6037563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6037613 : List Nat := [1, 5, 1, 1, 2, 1, 1, 1, 2, 3, 5]
def baseStart_6037613 : Nat := 118140960795 + 6037613 * 2 ^ 59
def prefixEnd_6037613 : Nat := 4983230072969 + 3 ^ 40 * 6037613 * 2
def baseEnd_6037613 : Nat := 3100197474834191545071029

theorem tailTrace_6037613 : CollatzResearch.WordTrace tailWord_6037613 prefixEnd_6037613 3100197474834191545071029 := by
  unfold tailWord_6037613
  simp only [CollatzResearch.WordTrace]
  refine ⟨220209837075766718052085493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146806558050511145368056995 220209837075766718052085493)
  ·
    refine ⟨20644672225853129817383015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 220209837075766718052085493 20644672225853129817383015)
    ·
      refine ⟨30967008338779694726074523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20644672225853129817383015 30967008338779694726074523)
      ·
        refine ⟨46450512508169542089111785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30967008338779694726074523 46450512508169542089111785)
        ·
          refine ⟨34837884381127156566833839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46450512508169542089111785 34837884381127156566833839)
          ·
            refine ⟨52256826571690734850250759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34837884381127156566833839 52256826571690734850250759)
            ·
              refine ⟨78385239857536102275376139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52256826571690734850250759 78385239857536102275376139)
              ·
                refine ⟨117577859786304153413064209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78385239857536102275376139 117577859786304153413064209)
                ·
                  refine ⟨88183394839728115059798157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 117577859786304153413064209 88183394839728115059798157)
                  ·
                    refine ⟨33068773064898043147424309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 88183394839728115059798157 33068773064898043147424309)
                    ·
                      refine ⟨3100197474834191545071029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33068773064898043147424309 3100197474834191545071029)
                      ·
                        rfl

theorem cell23_6037613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 1, 2, 3, 5].length) (baseStart_6037613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6037613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6037613 prefixEnd_6037613 := by exact prefixLift 6037613
  have htrace : WordTrace (prefixWord ++ tailWord_6037613) baseStart_6037613 baseEnd_6037613 := by
    simpa [prefixWord, tailWord_6037613, baseEnd_6037613] using wordTrace_append hprefix tailTrace_6037613
  have hstable : (prefixWord ++ tailWord_6037613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6037613).length < 2 ^ (prefixWord ++ tailWord_6037613).sum := by decide
  have hdescent : baseEnd_6037613 < baseStart_6037613 := by decide
  rcases family_descends (prefixWord ++ tailWord_6037613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6037720 : List Nat := [2, 1, 2, 2, 4, 1, 1, 3, 1, 1, 5]
def baseStart_6037720 : Nat := 118140960795 + 6037720 * 2 ^ 59
def prefixEnd_6037720 : Nat := 4983230072969 + 3 ^ 40 * 6037720 * 2
def baseEnd_6037720 : Nat := 3100252417264222626433037

theorem tailTrace_6037720 : CollatzResearch.WordTrace tailWord_6037720 prefixEnd_6037720 3100252417264222626433037 := by
  unfold tailWord_6037720
  simp only [CollatzResearch.WordTrace]
  refine ⟨110106869843189537663115307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146809159790919383550820409 110106869843189537663115307)
  ·
    refine ⟨165160304764784306494672961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110106869843189537663115307 165160304764784306494672961)
    ·
      refine ⟨123870228573588229871004721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 165160304764784306494672961 123870228573588229871004721)
      ·
        refine ⟨92902671430191172403253541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123870228573588229871004721 92902671430191172403253541)
        ·
          refine ⟨17419250893160844825610039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 92902671430191172403253541 17419250893160844825610039)
          ·
            refine ⟨26128876339741267238415059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17419250893160844825610039 26128876339741267238415059)
            ·
              refine ⟨39193314509611900857622589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26128876339741267238415059 39193314509611900857622589)
              ·
                refine ⟨14697492941104462821608471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39193314509611900857622589 14697492941104462821608471)
                ·
                  refine ⟨22046239411656694232412707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14697492941104462821608471 22046239411656694232412707)
                  ·
                    refine ⟨33069359117485041348619061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22046239411656694232412707 33069359117485041348619061)
                    ·
                      refine ⟨3100252417264222626433037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33069359117485041348619061 3100252417264222626433037)
                      ·
                        rfl

theorem cell23_6037720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 3, 1, 1, 5].length) (baseStart_6037720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6037720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6037720 prefixEnd_6037720 := by exact prefixLift 6037720
  have htrace : WordTrace (prefixWord ++ tailWord_6037720) baseStart_6037720 baseEnd_6037720 := by
    simpa [prefixWord, tailWord_6037720, baseEnd_6037720] using wordTrace_append hprefix tailTrace_6037720
  have hstable : (prefixWord ++ tailWord_6037720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6037720).length < 2 ^ (prefixWord ++ tailWord_6037720).sum := by decide
  have hdescent : baseEnd_6037720 < baseStart_6037720 := by decide
  rcases family_descends (prefixWord ++ tailWord_6037720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6037753 : List Nat := [1, 2, 1, 3, 1, 1, 2, 1, 4, 7]
def baseStart_6037753 : Nat := 118140960795 + 6037753 * 2 ^ 59
def prefixEnd_6037753 : Nat := 4983230072969 + 3 ^ 40 * 6037753 * 2
def baseEnd_6037753 : Nat := 1033423120708606999106795

theorem tailTrace_6037753 : CollatzResearch.WordTrace tailWord_6037753 prefixEnd_6037753 1033423120708606999106795 := by
  unfold tailWord_6037753
  simp only [CollatzResearch.WordTrace]
  refine ⟨220214943295259521962181913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146809962196839681308121275 220214943295259521962181913)
  ·
    refine ⟨165161207471444641471636435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 220214943295259521962181913 165161207471444641471636435)
    ·
      refine ⟨247741811207166962207454653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165161207471444641471636435 247741811207166962207454653)
      ·
        refine ⟨92903179202687610827795495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 247741811207166962207454653 92903179202687610827795495)
        ·
          refine ⟨139354768804031416241693243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92903179202687610827795495 139354768804031416241693243)
          ·
            refine ⟨209032153206047124362539865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139354768804031416241693243 209032153206047124362539865)
            ·
              refine ⟨156774114904535343271904899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 209032153206047124362539865 156774114904535343271904899)
              ·
                refine ⟨235161172356803014907857349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 156774114904535343271904899 235161172356803014907857349)
                ·
                  refine ⟨44092719816900565295223253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 235161172356803014907857349 44092719816900565295223253)
                  ·
                    refine ⟨1033423120708606999106795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 44092719816900565295223253 1033423120708606999106795)
                    ·
                      rfl

theorem cell23_6037753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 1, 4, 7].length) (baseStart_6037753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6037753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6037753 prefixEnd_6037753 := by exact prefixLift 6037753
  have htrace : WordTrace (prefixWord ++ tailWord_6037753) baseStart_6037753 baseEnd_6037753 := by
    simpa [prefixWord, tailWord_6037753, baseEnd_6037753] using wordTrace_append hprefix tailTrace_6037753
  have hstable : (prefixWord ++ tailWord_6037753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6037753).length < 2 ^ (prefixWord ++ tailWord_6037753).sum := by decide
  have hdescent : baseEnd_6037753 < baseStart_6037753 := by decide
  rcases family_descends (prefixWord ++ tailWord_6037753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6037754 : List Nat := [3, 1, 1, 1, 1, 7, 1, 2, 1, 2, 3]
def baseStart_6037754 : Nat := 118140960795 + 6037754 * 2 ^ 59
def prefixEnd_6037754 : Nat := 4983230072969 + 3 ^ 40 * 6037754 * 2
def baseEnd_6037754 : Nat := 3100269875606475493407881

theorem tailTrace_6037754 : CollatzResearch.WordTrace tailWord_6037754 prefixEnd_6037754 3100269875606475493407881 := by
  unfold tailWord_6037754
  simp only [CollatzResearch.WordTrace]
  refine ⟨55053744942063974783242079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146809986512170599421978877 55053744942063974783242079)
  ·
    refine ⟨82580617413095962174863119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55053744942063974783242079 82580617413095962174863119)
    ·
      refine ⟨123870926119643943262294679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82580617413095962174863119 123870926119643943262294679)
      ·
        refine ⟨185806389179465914893442019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123870926119643943262294679 185806389179465914893442019)
        ·
          refine ⟨278709583769198872340163029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 185806389179465914893442019 278709583769198872340163029)
          ·
            refine ⟨6532255869590598570472571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 278709583769198872340163029 6532255869590598570472571)
            ·
              refine ⟨9798383804385897855708857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6532255869590598570472571 9798383804385897855708857)
              ·
                refine ⟨7348787853289423391781643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9798383804385897855708857 7348787853289423391781643)
                ·
                  refine ⟨11023181779934135087672465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7348787853289423391781643 11023181779934135087672465)
                  ·
                    refine ⟨8267386334950601315754349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11023181779934135087672465 8267386334950601315754349)
                    ·
                      refine ⟨3100269875606475493407881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8267386334950601315754349 3100269875606475493407881)
                      ·
                        rfl

theorem cell23_6037754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 7, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 7, 1, 2, 1, 2, 3].length) (baseStart_6037754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6037754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6037754 prefixEnd_6037754 := by exact prefixLift 6037754
  have htrace : WordTrace (prefixWord ++ tailWord_6037754) baseStart_6037754 baseEnd_6037754 := by
    simpa [prefixWord, tailWord_6037754, baseEnd_6037754] using wordTrace_append hprefix tailTrace_6037754
  have hstable : (prefixWord ++ tailWord_6037754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6037754).length < 2 ^ (prefixWord ++ tailWord_6037754).sum := by decide
  have hdescent : baseEnd_6037754 < baseStart_6037754 := by decide
  rcases family_descends (prefixWord ++ tailWord_6037754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6037784 : List Nat := [2, 1, 2, 3, 1, 2, 4, 2, 2, 1, 3]
def baseStart_6037784 : Nat := 118140960795 + 6037784 * 2 ^ 59
def prefixEnd_6037784 : Nat := 4983230072969 + 3 ^ 40 * 6037784 * 2
def baseEnd_6037784 : Nat := 3100285280026110376032743

theorem tailTrace_6037784 : CollatzResearch.WordTrace tailWord_6037784 prefixEnd_6037784 3100285280026110376032743 := by
  unfold tailWord_6037784
  simp only [CollatzResearch.WordTrace]
  refine ⟨110108036979073607128280203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146810715972098142837706937 110108036979073607128280203)
  ·
    refine ⟨165162055468610410692420305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110108036979073607128280203 165162055468610410692420305)
    ·
      refine ⟨123871541601457808019315229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 165162055468610410692420305 123871541601457808019315229)
      ·
        refine ⟨46451828100546678007243211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 123871541601457808019315229 46451828100546678007243211)
        ·
          refine ⟨69677742150820017010864817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46451828100546678007243211 69677742150820017010864817)
          ·
            refine ⟨52258306613115012758148613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69677742150820017010864817 52258306613115012758148613)
            ·
              refine ⟨9798432489959064892152865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 52258306613115012758148613 9798432489959064892152865)
              ·
                refine ⟨7348824367469298669114649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9798432489959064892152865 7348824367469298669114649)
                ·
                  refine ⟨5511618275601974001835987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7348824367469298669114649 5511618275601974001835987)
                  ·
                    refine ⟨8267427413402961002753981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5511618275601974001835987 8267427413402961002753981)
                    ·
                      refine ⟨3100285280026110376032743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8267427413402961002753981 3100285280026110376032743)
                      ·
                        rfl

theorem cell23_6037784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 4, 2, 2, 1, 3].length) (baseStart_6037784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6037784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6037784 prefixEnd_6037784 := by exact prefixLift 6037784
  have htrace : WordTrace (prefixWord ++ tailWord_6037784) baseStart_6037784 baseEnd_6037784 := by
    simpa [prefixWord, tailWord_6037784, baseEnd_6037784] using wordTrace_append hprefix tailTrace_6037784
  have hstable : (prefixWord ++ tailWord_6037784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6037784).length < 2 ^ (prefixWord ++ tailWord_6037784).sum := by decide
  have hdescent : baseEnd_6037784 < baseStart_6037784 := by decide
  rcases family_descends (prefixWord ++ tailWord_6037784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6037794 : List Nat := [3, 3, 1, 1, 3, 1, 1, 2, 3, 3, 2]
def baseStart_6037794 : Nat := 118140960795 + 6037794 * 2 ^ 59
def prefixEnd_6037794 : Nat := 4983230072969 + 3 ^ 40 * 6037794 * 2
def baseEnd_6037794 : Nat := 3100290414832655336907697

theorem tailTrace_6037794 : CollatzResearch.WordTrace tailWord_6037794 prefixEnd_6037794 3100290414832655336907697 := by
  unfold tailWord_6037794
  simp only [CollatzResearch.WordTrace]
  refine ⟨55054109672027746491106109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146810959125407323976282957 55054109672027746491106109)
  ·
    refine ⟨20645291127010404934164791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55054109672027746491106109 20645291127010404934164791)
    ·
      refine ⟨30967936690515607401247187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20645291127010404934164791 30967936690515607401247187)
      ·
        refine ⟨46451905035773411101870781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30967936690515607401247187 46451905035773411101870781)
        ·
          refine ⟨17419464388415029163201543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46451905035773411101870781 17419464388415029163201543)
          ·
            refine ⟨26129196582622543744802315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17419464388415029163201543 26129196582622543744802315)
            ·
              refine ⟨39193794873933815617203473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26129196582622543744802315 39193794873933815617203473)
              ·
                refine ⟨29395346155450361712902605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39193794873933815617203473 29395346155450361712902605)
                ·
                  refine ⟨11023254808293885642338477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29395346155450361712902605 11023254808293885642338477)
                  ·
                    refine ⟨4133720553110207115876929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11023254808293885642338477 4133720553110207115876929)
                    ·
                      refine ⟨3100290414832655336907697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4133720553110207115876929 3100290414832655336907697)
                      ·
                        rfl

theorem cell23_6037794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 2, 3, 3, 2].length) (baseStart_6037794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6037794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6037794 prefixEnd_6037794 := by exact prefixLift 6037794
  have htrace : WordTrace (prefixWord ++ tailWord_6037794) baseStart_6037794 baseEnd_6037794 := by
    simpa [prefixWord, tailWord_6037794, baseEnd_6037794] using wordTrace_append hprefix tailTrace_6037794
  have hstable : (prefixWord ++ tailWord_6037794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6037794).length < 2 ^ (prefixWord ++ tailWord_6037794).sum := by decide
  have hdescent : baseEnd_6037794 < baseStart_6037794 := by decide
  rcases family_descends (prefixWord ++ tailWord_6037794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6037803 : List Nat := [1, 1, 1, 1, 2, 1, 2, 1, 1, 2, 10]
def baseStart_6037803 : Nat := 118140960795 + 6037803 * 2 ^ 59
def prefixEnd_6037803 : Nat := 4983230072969 + 3 ^ 40 * 6037803 * 2
def baseEnd_6037803 : Nat := 3100295036158545801695155

theorem tailTrace_6037803 : CollatzResearch.WordTrace tailWord_6037803 prefixEnd_6037803 3100295036158545801695155 := by
  unfold tailWord_6037803
  simp only [CollatzResearch.WordTrace]
  refine ⟨220216766945078380501502063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146811177963385587001001375 220216766945078380501502063)
  ·
    refine ⟨330325150417617570752253095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220216766945078380501502063 330325150417617570752253095)
    ·
      refine ⟨495487725626426356128379643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 330325150417617570752253095 495487725626426356128379643)
      ·
        refine ⟨743231588439639534192569465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 495487725626426356128379643 743231588439639534192569465)
        ·
          refine ⟨557423691329729650644427099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 743231588439639534192569465 557423691329729650644427099)
          ·
            refine ⟨836135536994594475966640649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 557423691329729650644427099 836135536994594475966640649)
            ·
              refine ⟨627101652745945856974980487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 836135536994594475966640649 627101652745945856974980487)
              ·
                refine ⟨940652479118918785462470731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 627101652745945856974980487 940652479118918785462470731)
                ·
                  refine ⟨1410978718678378178193706097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 940652479118918785462470731 1410978718678378178193706097)
                  ·
                    refine ⟨1058234039008783633645279573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1410978718678378178193706097 1058234039008783633645279573)
                    ·
                      refine ⟨3100295036158545801695155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 1058234039008783633645279573 3100295036158545801695155)
                      ·
                        rfl

theorem cell23_6037803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 2, 10].length) (baseStart_6037803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6037803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6037803 prefixEnd_6037803 := by exact prefixLift 6037803
  have htrace : WordTrace (prefixWord ++ tailWord_6037803) baseStart_6037803 baseEnd_6037803 := by
    simpa [prefixWord, tailWord_6037803, baseEnd_6037803] using wordTrace_append hprefix tailTrace_6037803
  have hstable : (prefixWord ++ tailWord_6037803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6037803).length < 2 ^ (prefixWord ++ tailWord_6037803).sum := by decide
  have hdescent : baseEnd_6037803 < baseStart_6037803 := by decide
  rcases family_descends (prefixWord ++ tailWord_6037803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6037807 : List Nat := [1, 1, 2, 1, 2, 1, 5, 3, 1, 4, 2]
def baseStart_6037807 : Nat := 118140960795 + 6037807 * 2 ^ 59
def prefixEnd_6037807 : Nat := 4983230072969 + 3 ^ 40 * 6037807 * 2
def baseEnd_6037807 : Nat := 3100297090081163786045137

theorem tailTrace_6037807 : CollatzResearch.WordTrace tailWord_6037807 prefixEnd_6037807 3100297090081163786045137 := by
  unfold tailWord_6037807
  simp only [CollatzResearch.WordTrace]
  refine ⟨220216912837063889184647675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146811275224709259456431783 220216912837063889184647675)
  ·
    refine ⟨330325369255595833776971513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220216912837063889184647675 330325369255595833776971513)
    ·
      refine ⟨247744026941696875332728635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 330325369255595833776971513 247744026941696875332728635)
      ·
        refine ⟨371616040412545312999092953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 247744026941696875332728635 371616040412545312999092953)
        ·
          refine ⟨278712030309408984749319715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 371616040412545312999092953 278712030309408984749319715)
          ·
            refine ⟨418068045464113477123979573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 278712030309408984749319715 418068045464113477123979573)
            ·
              refine ⟨39193879262260638480373085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 418068045464113477123979573 39193879262260638480373085)
              ·
                refine ⟨14697704723347739430139907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39193879262260638480373085 14697704723347739430139907)
                ·
                  refine ⟨22046557085021609145209861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14697704723347739430139907 22046557085021609145209861)
                  ·
                    refine ⟨4133729453441551714726849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22046557085021609145209861 4133729453441551714726849)
                    ·
                      refine ⟨3100297090081163786045137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4133729453441551714726849 3100297090081163786045137)
                      ·
                        rfl

theorem cell23_6037807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 3, 1, 4, 2].length) (baseStart_6037807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6037807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6037807 prefixEnd_6037807 := by exact prefixLift 6037807
  have htrace : WordTrace (prefixWord ++ tailWord_6037807) baseStart_6037807 baseEnd_6037807 := by
    simpa [prefixWord, tailWord_6037807, baseEnd_6037807] using wordTrace_append hprefix tailTrace_6037807
  have hstable : (prefixWord ++ tailWord_6037807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6037807).length < 2 ^ (prefixWord ++ tailWord_6037807).sum := by decide
  have hdescent : baseEnd_6037807 < baseStart_6037807 := by decide
  rcases family_descends (prefixWord ++ tailWord_6037807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6037820 : List Nat := [2, 2, 2, 2, 1, 2, 1, 2, 1, 4, 4]
def baseStart_6037820 : Nat := 118140960795 + 6037820 * 2 ^ 59
def prefixEnd_6037820 : Nat := 4983230072969 + 3 ^ 40 * 6037820 * 2
def baseEnd_6037820 : Nat := 3100303765329672235182577

theorem tailTrace_6037820 : CollatzResearch.WordTrace tailWord_6037820 prefixEnd_6037820 3100303765329672235182577 := by
  unfold tailWord_6037820
  simp only [CollatzResearch.WordTrace]
  refine ⟨110108693493008396202435457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146811591324011194936580609 110108693493008396202435457)
  ·
    refine ⟨82581520119756297151826593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110108693493008396202435457 82581520119756297151826593)
    ·
      refine ⟨61936140089817222863869945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82581520119756297151826593 61936140089817222863869945)
      ·
        refine ⟨46452105067362917147902459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61936140089817222863869945 46452105067362917147902459)
        ·
          refine ⟨69678157601044375721853689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46452105067362917147902459 69678157601044375721853689)
          ·
            refine ⟨52258618200783281791390267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69678157601044375721853689 52258618200783281791390267)
            ·
              refine ⟨78387927301174922687085401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52258618200783281791390267 78387927301174922687085401)
              ·
                refine ⟨58790945475881192015314051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 78387927301174922687085401 58790945475881192015314051)
                ·
                  refine ⟨88186418213821788022971077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58790945475881192015314051 88186418213821788022971077)
                  ·
                    refine ⟨16534953415091585254307077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 88186418213821788022971077 16534953415091585254307077)
                    ·
                      refine ⟨3100303765329672235182577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16534953415091585254307077 3100303765329672235182577)
                      ·
                        rfl

theorem cell23_6037820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 2, 1, 4, 4].length) (baseStart_6037820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6037820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6037820 prefixEnd_6037820 := by exact prefixLift 6037820
  have htrace : WordTrace (prefixWord ++ tailWord_6037820) baseStart_6037820 baseEnd_6037820 := by
    simpa [prefixWord, tailWord_6037820, baseEnd_6037820] using wordTrace_append hprefix tailTrace_6037820
  have hstable : (prefixWord ++ tailWord_6037820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6037820).length < 2 ^ (prefixWord ++ tailWord_6037820).sum := by decide
  have hdescent : baseEnd_6037820 < baseStart_6037820 := by decide
  rcases family_descends (prefixWord ++ tailWord_6037820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6037828 : List Nat := [2, 3, 4, 1, 2, 1, 1, 3, 1, 3, 2]
def baseStart_6037828 : Nat := 118140960795 + 6037828 * 2 ^ 59
def prefixEnd_6037828 : Nat := 4983230072969 + 3 ^ 40 * 6037828 * 2
def baseEnd_6037828 : Nat := 3100307873174908203882541

theorem tailTrace_6037828 : CollatzResearch.WordTrace tailWord_6037828 prefixEnd_6037828 3100307873174908203882541 := by
  unfold tailWord_6037828
  simp only [CollatzResearch.WordTrace]
  refine ⟨110108839384993904885581069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146811785846658539847441425 110108839384993904885581069)
  ·
    refine ⟨41290814769372714332092901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110108839384993904885581069 41290814769372714332092901)
    ·
      refine ⟨7742027769257383937267419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41290814769372714332092901 7742027769257383937267419)
      ·
        refine ⟨11613041653886075905901129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7742027769257383937267419 11613041653886075905901129)
        ·
          refine ⟨8709781240414556929425847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11613041653886075905901129 8709781240414556929425847)
          ·
            refine ⟨13064671860621835394138771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8709781240414556929425847 13064671860621835394138771)
            ·
              refine ⟨19597007790932753091208157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13064671860621835394138771 19597007790932753091208157)
              ·
                refine ⟨7348877921599782409203059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19597007790932753091208157 7348877921599782409203059)
                ·
                  refine ⟨11023316882399673613804589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7348877921599782409203059 11023316882399673613804589)
                  ·
                    refine ⟨4133743830899877605176721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11023316882399673613804589 4133743830899877605176721)
                    ·
                      refine ⟨3100307873174908203882541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4133743830899877605176721 3100307873174908203882541)
                      ·
                        rfl

theorem cell23_6037828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 1, 3, 1, 3, 2].length) (baseStart_6037828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6037828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6037828 prefixEnd_6037828 := by exact prefixLift 6037828
  have htrace : WordTrace (prefixWord ++ tailWord_6037828) baseStart_6037828 baseEnd_6037828 := by
    simpa [prefixWord, tailWord_6037828, baseEnd_6037828] using wordTrace_append hprefix tailTrace_6037828
  have hstable : (prefixWord ++ tailWord_6037828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6037828).length < 2 ^ (prefixWord ++ tailWord_6037828).sum := by decide
  have hdescent : baseEnd_6037828 < baseStart_6037828 := by decide
  rcases family_descends (prefixWord ++ tailWord_6037828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6037841 : List Nat := [1, 2, 2, 1, 4, 2, 3, 2, 2, 2, 2]
def baseStart_6037841 : Nat := 118140960795 + 6037841 * 2 ^ 59
def prefixEnd_6037841 : Nat := 4983230072969 + 3 ^ 40 * 6037841 * 2
def baseEnd_6037841 : Nat := 3100314548423416653019981

theorem tailTrace_6037841 : CollatzResearch.WordTrace tailWord_6037841 prefixEnd_6037841 3100314548423416653019981 := by
  unfold tailWord_6037841
  simp only [CollatzResearch.WordTrace]
  refine ⟨220218152918940712991385377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146812101945960475327590251 220218152918940712991385377)
  ·
    refine ⟨165163614689205534743539033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 220218152918940712991385377 165163614689205534743539033)
    ·
      refine ⟨123872711016904151057654275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 165163614689205534743539033 123872711016904151057654275)
      ·
        refine ⟨185809066525356226586481413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123872711016904151057654275 185809066525356226586481413)
        ·
          refine ⟨34839199973504292484965265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 185809066525356226586481413 34839199973504292484965265)
          ·
            refine ⟨26129399980128219363723949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34839199973504292484965265 26129399980128219363723949)
            ·
              refine ⟨9798524992548082261396481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26129399980128219363723949 9798524992548082261396481)
              ·
                refine ⟨7348893744411061696047361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9798524992548082261396481 7348893744411061696047361)
                ·
                  refine ⟨5511670308308296272035521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7348893744411061696047361 5511670308308296272035521)
                  ·
                    refine ⟨4133752731231222204026641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5511670308308296272035521 4133752731231222204026641)
                    ·
                      refine ⟨3100314548423416653019981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4133752731231222204026641 3100314548423416653019981)
                      ·
                        rfl

theorem cell23_6037841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 3, 2, 2, 2, 2].length) (baseStart_6037841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6037841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6037841 prefixEnd_6037841 := by exact prefixLift 6037841
  have htrace : WordTrace (prefixWord ++ tailWord_6037841) baseStart_6037841 baseEnd_6037841 := by
    simpa [prefixWord, tailWord_6037841, baseEnd_6037841] using wordTrace_append hprefix tailTrace_6037841
  have hstable : (prefixWord ++ tailWord_6037841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6037841).length < 2 ^ (prefixWord ++ tailWord_6037841).sum := by decide
  have hdescent : baseEnd_6037841 < baseStart_6037841 := by decide
  rcases family_descends (prefixWord ++ tailWord_6037841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6037847 : List Nat := [1, 1, 3, 2, 3, 1, 1, 6, 5]
def baseStart_6037847 : Nat := 118140960795 + 6037847 * 2 ^ 59
def prefixEnd_6037847 : Nat := 4983230072969 + 3 ^ 40 * 6037847 * 2
def baseEnd_6037847 : Nat := 344479736589704847727217

theorem tailTrace_6037847 : CollatzResearch.WordTrace tailWord_6037847 prefixEnd_6037847 344479736589704847727217 := by
  unfold tailWord_6037847
  simp only [CollatzResearch.WordTrace]
  refine ⟨220218371756918976016103795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146812247837945984010735863 220218371756918976016103795)
  ·
    refine ⟨330327557635378464024155693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220218371756918976016103795 330327557635378464024155693)
    ·
      refine ⟨123872834113266924009058385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 330327557635378464024155693 123872834113266924009058385)
      ·
        refine ⟨92904625584950193006793789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123872834113266924009058385 92904625584950193006793789)
        ·
          refine ⟨34839234594356322377547671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 92904625584950193006793789 34839234594356322377547671)
          ·
            refine ⟨52258851891534483566321507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34839234594356322377547671 52258851891534483566321507)
            ·
              refine ⟨78388277837301725349482261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52258851891534483566321507 78388277837301725349482261)
              ·
                refine ⟨3674450523623518375756981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 78388277837301725349482261 3674450523623518375756981)
                ·
                  refine ⟨344479736589704847727217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3674450523623518375756981 344479736589704847727217)
                  ·
                    rfl

theorem cell23_6037847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 6, 5].length) (baseStart_6037847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6037847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6037847 prefixEnd_6037847 := by exact prefixLift 6037847
  have htrace : WordTrace (prefixWord ++ tailWord_6037847) baseStart_6037847 baseEnd_6037847 := by
    simpa [prefixWord, tailWord_6037847, baseEnd_6037847] using wordTrace_append hprefix tailTrace_6037847
  have hstable : (prefixWord ++ tailWord_6037847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6037847).length < 2 ^ (prefixWord ++ tailWord_6037847).sum := by decide
  have hdescent : baseEnd_6037847 < baseStart_6037847 := by decide
  rcases family_descends (prefixWord ++ tailWord_6037847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6037860 : List Nat := [2, 3, 1, 1, 3, 1, 1, 1, 3, 7]
def baseStart_6037860 : Nat := 118140960795 + 6037860 * 2 ^ 59
def prefixEnd_6037860 : Nat := 4983230072969 + 3 ^ 40 * 6037860 * 2
def baseEnd_6037860 : Nat := 1033441434851950692894131

theorem tailTrace_6037860 : CollatzResearch.WordTrace tailWord_6037860 prefixEnd_6037860 1033441434851950692894131 := by
  unfold tailWord_6037860
  simp only [CollatzResearch.WordTrace]
  refine ⟨110109422952935939618163517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146812563937247919490884689 110109422952935939618163517)
  ·
    refine ⟨41291033607350977356811319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110109422952935939618163517 41291033607350977356811319)
    ·
      refine ⟨61936550411026466035216979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41291033607350977356811319 61936550411026466035216979)
      ·
        refine ⟨92904825616539699052825469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61936550411026466035216979 92904825616539699052825469)
        ·
          refine ⟨34839309606202387144809551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 92904825616539699052825469 34839309606202387144809551)
          ·
            refine ⟨52258964409303580717214327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34839309606202387144809551 52258964409303580717214327)
            ·
              refine ⟨78388446613955371075821491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52258964409303580717214327 78388446613955371075821491)
              ·
                refine ⟨117582669920933056613732237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78388446613955371075821491 117582669920933056613732237)
                ·
                  refine ⟨44093501220349896230149589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 117582669920933056613732237 44093501220349896230149589)
                  ·
                    refine ⟨1033441434851950692894131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 44093501220349896230149589 1033441434851950692894131)
                    ·
                      rfl

theorem cell23_6037860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 1, 3, 7].length) (baseStart_6037860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6037860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6037860 prefixEnd_6037860 := by exact prefixLift 6037860
  have htrace : WordTrace (prefixWord ++ tailWord_6037860) baseStart_6037860 baseEnd_6037860 := by
    simpa [prefixWord, tailWord_6037860, baseEnd_6037860] using wordTrace_append hprefix tailTrace_6037860
  have hstable : (prefixWord ++ tailWord_6037860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6037860).length < 2 ^ (prefixWord ++ tailWord_6037860).sum := by decide
  have hdescent : baseEnd_6037860 < baseStart_6037860 := by decide
  rcases family_descends (prefixWord ++ tailWord_6037860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6037877 : List Nat := [1, 3, 4, 1, 2, 1, 2, 1, 1, 7]
def baseStart_6037877 : Nat := 118140960795 + 6037877 * 2 ^ 59
def prefixEnd_6037877 : Nat := 4983230072969 + 3 ^ 40 * 6037877 * 2
def baseEnd_6037877 : Nat := 1033444344575659504056605

theorem tailTrace_6037877 : CollatzResearch.WordTrace tailWord_6037877 prefixEnd_6037877 1033444344575659504056605 := by
  unfold tailWord_6037877
  simp only [CollatzResearch.WordTrace]
  refine ⟨220219465946810291139695885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146812977297873527426463923 220219465946810291139695885)
  ·
    refine ⟨82582299730053859177385957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 220219465946810291139695885 82582299730053859177385957)
    ·
      refine ⟨15484181199385098595759867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 82582299730053859177385957 15484181199385098595759867)
      ·
        refine ⟨23226271799077647893639801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15484181199385098595759867 23226271799077647893639801)
        ·
          refine ⟨17419703849308235920229851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23226271799077647893639801 17419703849308235920229851)
          ·
            refine ⟨26129555773962353880344777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17419703849308235920229851 26129555773962353880344777)
            ·
              refine ⟨19597166830471765410258583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26129555773962353880344777 19597166830471765410258583)
              ·
                refine ⟨29395750245707648115387875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19597166830471765410258583 29395750245707648115387875)
                ·
                  refine ⟨44093625368561472173081813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29395750245707648115387875 44093625368561472173081813)
                  ·
                    refine ⟨1033444344575659504056605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 44093625368561472173081813 1033444344575659504056605)
                    ·
                      rfl

theorem cell23_6037877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 2, 1, 1, 7].length) (baseStart_6037877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6037877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6037877 prefixEnd_6037877 := by exact prefixLift 6037877
  have htrace : WordTrace (prefixWord ++ tailWord_6037877) baseStart_6037877 baseEnd_6037877 := by
    simpa [prefixWord, tailWord_6037877, baseEnd_6037877] using wordTrace_append hprefix tailTrace_6037877
  have hstable : (prefixWord ++ tailWord_6037877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6037877).length < 2 ^ (prefixWord ++ tailWord_6037877).sum := by decide
  have hdescent : baseEnd_6037877 < baseStart_6037877 := by decide
  rcases family_descends (prefixWord ++ tailWord_6037877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6037897 : List Nat := [1, 2, 1, 1, 6, 1, 1, 1, 4, 1, 4]
def baseStart_6037897 : Nat := 118140960795 + 6037897 * 2 ^ 59
def prefixEnd_6037897 : Nat := 4983230072969 + 3 ^ 40 * 6037897 * 2
def baseEnd_6037897 : Nat := 3100343303340068433919723

theorem tailTrace_6037897 : CollatzResearch.WordTrace tailWord_6037897 prefixEnd_6037897 3100343303340068433919723 := by
  unfold tailWord_6037897
  simp only [CollatzResearch.WordTrace]
  refine ⟨220220195406737834555423945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146813463604491889703615963 220220195406737834555423945)
  ·
    refine ⟨165165146555053375916567959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 220220195406737834555423945 165165146555053375916567959)
    ·
      refine ⟨247747719832580063874851939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165165146555053375916567959 247747719832580063874851939)
      ·
        refine ⟨371621579748870095812277909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 247747719832580063874851939 371621579748870095812277909)
        ·
          refine ⟨17419761550728285741200527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 371621579748870095812277909 17419761550728285741200527)
          ·
            refine ⟨26129642326092428611800791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17419761550728285741200527 26129642326092428611800791)
            ·
              refine ⟨39194463489138642917701187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26129642326092428611800791 39194463489138642917701187)
              ·
                refine ⟨58791695233707964376551781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39194463489138642917701187 58791695233707964376551781)
                ·
                  refine ⟨11023442856320243320603459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 58791695233707964376551781 11023442856320243320603459)
                  ·
                    refine ⟨16535164284480364980905189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11023442856320243320603459 16535164284480364980905189)
                    ·
                      refine ⟨3100343303340068433919723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16535164284480364980905189 3100343303340068433919723)
                      ·
                        rfl

theorem cell23_6037897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 1, 4, 1, 4].length) (baseStart_6037897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6037897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6037897 prefixEnd_6037897 := by exact prefixLift 6037897
  have htrace : WordTrace (prefixWord ++ tailWord_6037897) baseStart_6037897 baseEnd_6037897 := by
    simpa [prefixWord, tailWord_6037897, baseEnd_6037897] using wordTrace_append hprefix tailTrace_6037897
  have hstable : (prefixWord ++ tailWord_6037897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6037897).length < 2 ^ (prefixWord ++ tailWord_6037897).sum := by decide
  have hdescent : baseEnd_6037897 < baseStart_6037897 := by decide
  rcases family_descends (prefixWord ++ tailWord_6037897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6037898 : List Nat := [3, 1, 2, 5, 1, 1, 3, 2, 5]
def baseStart_6037898 : Nat := 118140960795 + 6037898 * 2 ^ 59
def prefixEnd_6037898 : Nat := 4983230072969 + 3 ^ 40 * 6037898 * 2
def baseEnd_6037898 : Nat := 344482646313413658889691

theorem tailTrace_6037898 : CollatzResearch.WordTrace tailWord_6037898 prefixEnd_6037898 344482646313413658889691 := by
  unfold tailWord_6037898
  simp only [CollatzResearch.WordTrace]
  refine ⟨55055057969933552931552587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146813487919822807817473565 55055057969933552931552587)
  ·
    refine ⟨82582586954900329397328881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55055057969933552931552587 82582586954900329397328881)
    ·
      refine ⟨61936940216175247047996661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82582586954900329397328881 61936940216175247047996661)
      ·
        refine ⟨5806588145266429410749687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 61936940216175247047996661 5806588145266429410749687)
        ·
          refine ⟨8709882217899644116124531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5806588145266429410749687 8709882217899644116124531)
          ·
            refine ⟨13064823326849466174186797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8709882217899644116124531 13064823326849466174186797)
            ·
              refine ⟨4899308747568549815320049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13064823326849466174186797 4899308747568549815320049)
              ·
                refine ⟨3674481560676412361490037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4899308747568549815320049 3674481560676412361490037)
                ·
                  refine ⟨344482646313413658889691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3674481560676412361490037 344482646313413658889691)
                  ·
                    rfl

theorem cell23_6037898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 3, 2, 5].length) (baseStart_6037898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6037898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6037898 prefixEnd_6037898 := by exact prefixLift 6037898
  have htrace : WordTrace (prefixWord ++ tailWord_6037898) baseStart_6037898 baseEnd_6037898 := by
    simpa [prefixWord, tailWord_6037898, baseEnd_6037898] using wordTrace_append hprefix tailTrace_6037898
  have hstable : (prefixWord ++ tailWord_6037898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6037898).length < 2 ^ (prefixWord ++ tailWord_6037898).sum := by decide
  have hdescent : baseEnd_6037898 < baseStart_6037898 := by decide
  rcases family_descends (prefixWord ++ tailWord_6037898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6037981 : List Nat := [1, 4, 3, 1, 1, 1, 3, 2, 3, 1, 3]
def baseStart_6037981 : Nat := 118140960795 + 6037981 * 2 ^ 59
def prefixEnd_6037981 : Nat := 4983230072969 + 3 ^ 40 * 6037981 * 2
def baseEnd_6037981 : Nat := 3100386435715046105269337

theorem tailTrace_6037981 : CollatzResearch.WordTrace tailWord_6037981 prefixEnd_6037981 3100386435715046105269337 := by
  unfold tailWord_6037981
  simp only [CollatzResearch.WordTrace]
  refine ⟨220223259138433516901481797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146815506092289011267654531 220223259138433516901481797)
  ·
    refine ⟨41291861088456284419027837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 220223259138433516901481797 41291861088456284419027837)
    ·
      refine ⟨15484447908171106657135439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41291861088456284419027837 15484447908171106657135439)
      ·
        refine ⟨23226671862256659985703159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15484447908171106657135439 23226671862256659985703159)
        ·
          refine ⟨34840007793384989978554739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23226671862256659985703159 34840007793384989978554739)
          ·
            refine ⟨52260011690077484967832109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34840007793384989978554739 52260011690077484967832109)
            ·
              refine ⟨19597504383779056862937041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52260011690077484967832109 19597504383779056862937041)
              ·
                refine ⟨14698128287834292647202781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19597504383779056862937041 14698128287834292647202781)
                ·
                  refine ⟨5511798107937859742701043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14698128287834292647202781 5511798107937859742701043)
                  ·
                    refine ⟨8267697161906789614051565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5511798107937859742701043 8267697161906789614051565)
                    ·
                      refine ⟨3100386435715046105269337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8267697161906789614051565 3100386435715046105269337)
                      ·
                        rfl

theorem cell23_6037981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 3, 2, 3, 1, 3].length) (baseStart_6037981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6037981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6037981 prefixEnd_6037981 := by exact prefixLift 6037981
  have htrace : WordTrace (prefixWord ++ tailWord_6037981) baseStart_6037981 baseEnd_6037981 := by
    simpa [prefixWord, tailWord_6037981, baseEnd_6037981] using wordTrace_append hprefix tailTrace_6037981
  have hstable : (prefixWord ++ tailWord_6037981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6037981).length < 2 ^ (prefixWord ++ tailWord_6037981).sum := by decide
  have hdescent : baseEnd_6037981 < baseStart_6037981 := by decide
  rcases family_descends (prefixWord ++ tailWord_6037981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6037998 : List Nat := [4, 1, 2, 1, 2, 2, 1, 5, 1, 1, 3]
def baseStart_6037998 : Nat := 118140960795 + 6037998 * 2 ^ 59
def prefixEnd_6037998 : Nat := 4983230072969 + 3 ^ 40 * 6037998 * 2
def baseEnd_6037998 : Nat := 3100395164886172538756759

theorem tailTrace_6037998 : CollatzResearch.WordTrace tailWord_6037998 prefixEnd_6037998 3100395164886172538756759 := by
  unfold tailWord_6037998
  simp only [CollatzResearch.WordTrace]
  refine ⟨27527984897421491100606331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 146815919452914619203233765 27527984897421491100606331)
  ·
    refine ⟨41291977346132236650909497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27527984897421491100606331 41291977346132236650909497)
    ·
      refine ⟨30968983009599177488182123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41291977346132236650909497 30968983009599177488182123)
      ·
        refine ⟨46453474514398766232273185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30968983009599177488182123 46453474514398766232273185)
        ·
          refine ⟨34840105885799074674204889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46453474514398766232273185 34840105885799074674204889)
          ·
            refine ⟨26130079414349306005653667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34840105885799074674204889 26130079414349306005653667)
            ·
              refine ⟨39195119121523959008480501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26130079414349306005653667 39195119121523959008480501)
              ·
                refine ⟨3674542417642871157045047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 39195119121523959008480501 3674542417642871157045047)
                ·
                  refine ⟨5511813626464306735567571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3674542417642871157045047 5511813626464306735567571)
                  ·
                    refine ⟨8267720439696460103351357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5511813626464306735567571 8267720439696460103351357)
                    ·
                      refine ⟨3100395164886172538756759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8267720439696460103351357 3100395164886172538756759)
                      ·
                        rfl

theorem cell23_6037998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 5, 1, 1, 3].length) (baseStart_6037998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6037998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6037998 prefixEnd_6037998 := by exact prefixLift 6037998
  have htrace : WordTrace (prefixWord ++ tailWord_6037998) baseStart_6037998 baseEnd_6037998 := by
    simpa [prefixWord, tailWord_6037998, baseEnd_6037998] using wordTrace_append hprefix tailTrace_6037998
  have hstable : (prefixWord ++ tailWord_6037998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6037998).length < 2 ^ (prefixWord ++ tailWord_6037998).sum := by decide
  have hdescent : baseEnd_6037998 < baseStart_6037998 := by decide
  rcases family_descends (prefixWord ++ tailWord_6037998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6038021 : List Nat := [1, 3, 1, 1, 2, 2, 3, 3, 3, 2, 2]
def baseStart_6038021 : Nat := 118140960795 + 6038021 * 2 ^ 59
def prefixEnd_6038021 : Nat := 4983230072969 + 3 ^ 40 * 6038021 * 2
def baseEnd_6038021 : Nat := 3100406974941225948769153

theorem tailTrace_6038021 : CollatzResearch.WordTrace tailWord_6038021 prefixEnd_6038021 3100406974941225948769153 := by
  unfold tailWord_6038021
  simp only [CollatzResearch.WordTrace]
  refine ⟨220224718058288603732937917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146816478705525735821958611 220224718058288603732937917)
  ·
    refine ⟨82584269271858226399851719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 220224718058288603732937917 82584269271858226399851719)
    ·
      refine ⟨123876403907787339599777579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82584269271858226399851719 123876403907787339599777579)
      ·
        refine ⟨185814605861681009399666369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123876403907787339599777579 185814605861681009399666369)
        ·
          refine ⟨139360954396260757049749777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 185814605861681009399666369 139360954396260757049749777)
          ·
            refine ⟨104520715797195567787312333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 139360954396260757049749777 104520715797195567787312333)
            ·
              refine ⟨39195268423948337920242125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 104520715797195567787312333 39195268423948337920242125)
              ·
                refine ⟨14698225658980626720090797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39195268423948337920242125 14698225658980626720090797)
                ·
                  refine ⟨5511834622117735020034049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14698225658980626720090797 5511834622117735020034049)
                  ·
                    refine ⟨4133875966588301265025537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5511834622117735020034049 4133875966588301265025537)
                    ·
                      refine ⟨3100406974941225948769153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4133875966588301265025537 3100406974941225948769153)
                      ·
                        rfl

theorem cell23_6038021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 3, 3, 2, 2].length) (baseStart_6038021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6038021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6038021 prefixEnd_6038021 := by exact prefixLift 6038021
  have htrace : WordTrace (prefixWord ++ tailWord_6038021) baseStart_6038021 baseEnd_6038021 := by
    simpa [prefixWord, tailWord_6038021, baseEnd_6038021] using wordTrace_append hprefix tailTrace_6038021
  have hstable : (prefixWord ++ tailWord_6038021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6038021).length < 2 ^ (prefixWord ++ tailWord_6038021).sum := by decide
  have hdescent : baseEnd_6038021 < baseStart_6038021 := by decide
  rcases family_descends (prefixWord ++ tailWord_6038021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6038044 : List Nat := [2, 2, 3, 1, 2, 2, 4, 7]
def baseStart_6038044 : Nat := 118140960795 + 6038044 * 2 ^ 59
def prefixEnd_6038044 : Nat := 4983230072969 + 3 ^ 40 * 6038044 * 2
def baseEnd_6038044 : Nat := 114830325370232568843761

theorem tailTrace_6038044 : CollatzResearch.WordTrace tailWord_6038044 prefixEnd_6038044 114830325370232568843761 := by
  unfold tailWord_6038044
  simp only [CollatzResearch.WordTrace]
  refine ⟨110112778468602639330512593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146817037958136852440683457 110112778468602639330512593)
  ·
    refine ⟨82584583851451979497884445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110112778468602639330512593 82584583851451979497884445)
    ·
      refine ⟨30969218944294492311706667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82584583851451979497884445 30969218944294492311706667)
      ·
        refine ⟨46453828416441738467560001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30969218944294492311706667 46453828416441738467560001)
        ·
          refine ⟨34840371312331303850670001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46453828416441738467560001 34840371312331303850670001)
          ·
            refine ⟨26130278484248477888002501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34840371312331303850670001 26130278484248477888002501)
            ·
              refine ⟨4899427215796589604000469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26130278484248477888002501 4899427215796589604000469)
              ·
                refine ⟨114830325370232568843761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4899427215796589604000469 114830325370232568843761)
                ·
                  rfl

theorem cell23_6038044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 4, 7].length) (baseStart_6038044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6038044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6038044 prefixEnd_6038044 := by exact prefixLift 6038044
  have htrace : WordTrace (prefixWord ++ tailWord_6038044) baseStart_6038044 baseEnd_6038044 := by
    simpa [prefixWord, tailWord_6038044, baseEnd_6038044] using wordTrace_append hprefix tailTrace_6038044
  have hstable : (prefixWord ++ tailWord_6038044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6038044).length < 2 ^ (prefixWord ++ tailWord_6038044).sum := by decide
  have hdescent : baseEnd_6038044 < baseStart_6038044 := by decide
  rcases family_descends (prefixWord ++ tailWord_6038044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6038067 : List Nat := [1, 1, 1, 2, 4, 2, 1, 2, 2, 2, 5]
def baseStart_6038067 : Nat := 118140960795 + 6038067 * 2 ^ 59
def prefixEnd_6038067 : Nat := 4983230072969 + 3 ^ 40 * 6038067 * 2
def baseEnd_6038067 : Nat := 3100430595051332768793941

theorem tailTrace_6038067 : CollatzResearch.WordTrace tailWord_6038067 prefixEnd_6038067 3100430595051332768793941 := by
  unfold tailWord_6038067
  simp only [CollatzResearch.WordTrace]
  refine ⟨220226395816121953589112455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146817597210747969059408303 220226395816121953589112455)
  ·
    refine ⟨330339593724182930383668683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220226395816121953589112455 330339593724182930383668683)
    ·
      refine ⟨495509390586274395575503025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 330339593724182930383668683 495509390586274395575503025)
      ·
        refine ⟨371632042939705796681627269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 495509390586274395575503025 371632042939705796681627269)
        ·
          refine ⟨69681008051194836877805113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 371632042939705796681627269 69681008051194836877805113)
          ·
            refine ⟨52260756038396127658353835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69681008051194836877805113 52260756038396127658353835)
            ·
              refine ⟨78391134057594191487530753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52260756038396127658353835 78391134057594191487530753)
              ·
                refine ⟨58793350543195643615648065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 78391134057594191487530753 58793350543195643615648065)
                ·
                  refine ⟨44095012907396732711736049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 58793350543195643615648065 44095012907396732711736049)
                  ·
                    refine ⟨33071259680547549533802037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 44095012907396732711736049 33071259680547549533802037)
                    ·
                      refine ⟨3100430595051332768793941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33071259680547549533802037 3100430595051332768793941)
                      ·
                        rfl

theorem cell23_6038067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 2, 2, 2, 5].length) (baseStart_6038067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6038067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6038067 prefixEnd_6038067 := by exact prefixLift 6038067
  have htrace : WordTrace (prefixWord ++ tailWord_6038067) baseStart_6038067 baseEnd_6038067 := by
    simpa [prefixWord, tailWord_6038067, baseEnd_6038067] using wordTrace_append hprefix tailTrace_6038067
  have hstable : (prefixWord ++ tailWord_6038067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6038067).length < 2 ^ (prefixWord ++ tailWord_6038067).sum := by decide
  have hdescent : baseEnd_6038067 < baseStart_6038067 := by decide
  rcases family_descends (prefixWord ++ tailWord_6038067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6038071 : List Nat := [1, 1, 3, 1, 2, 3, 2, 4, 2, 1, 3]
def baseStart_6038071 : Nat := 118140960795 + 6038071 * 2 ^ 59
def prefixEnd_6038071 : Nat := 4983230072969 + 3 ^ 40 * 6038071 * 2
def baseEnd_6038071 : Nat := 3100432648973950753143923

theorem tailTrace_6038071 : CollatzResearch.WordTrace tailWord_6038071 prefixEnd_6038071 3100432648973950753143923 := by
  unfold tailWord_6038071
  simp only [CollatzResearch.WordTrace]
  refine ⟨220226541708107462272258067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146817694472071641514838711 220226541708107462272258067)
  ·
    refine ⟨330339812562161193408387101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220226541708107462272258067 330339812562161193408387101)
    ·
      refine ⟨123877429710810447528145163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 330339812562161193408387101 123877429710810447528145163)
      ·
        refine ⟨185816144566215671292217745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123877429710810447528145163 185816144566215671292217745)
        ·
          refine ⟨139362108424661753469163309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 185816144566215671292217745 139362108424661753469163309)
          ·
            refine ⟨52260790659248157550936241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 139362108424661753469163309 52260790659248157550936241)
            ·
              refine ⟨39195592994436118163202181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52260790659248157550936241 39195592994436118163202181)
              ·
                refine ⟨7349173686456772155600409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39195592994436118163202181 7349173686456772155600409)
                ·
                  refine ⟨5511880264842579116700307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7349173686456772155600409 5511880264842579116700307)
                  ·
                    refine ⟨8267820397263868675050461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5511880264842579116700307 8267820397263868675050461)
                    ·
                      refine ⟨3100432648973950753143923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8267820397263868675050461 3100432648973950753143923)
                      ·
                        rfl

theorem cell23_6038071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 4, 2, 1, 3].length) (baseStart_6038071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6038071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6038071 prefixEnd_6038071 := by exact prefixLift 6038071
  have htrace : WordTrace (prefixWord ++ tailWord_6038071) baseStart_6038071 baseEnd_6038071 := by
    simpa [prefixWord, tailWord_6038071, baseEnd_6038071] using wordTrace_append hprefix tailTrace_6038071
  have hstable : (prefixWord ++ tailWord_6038071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6038071).length < 2 ^ (prefixWord ++ tailWord_6038071).sum := by decide
  have hdescent : baseEnd_6038071 < baseStart_6038071 := by decide
  rcases family_descends (prefixWord ++ tailWord_6038071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6038111 : List Nat := [1, 1, 2, 3, 1, 1, 1, 3, 6, 2, 2]
def baseStart_6038111 : Nat := 118140960795 + 6038111 * 2 ^ 59
def prefixEnd_6038111 : Nat := 4983230072969 + 3 ^ 40 * 6038111 * 2
def baseEnd_6038111 : Nat := 3100453188200130596643739

theorem tailTrace_6038111 : CollatzResearch.WordTrace tailWord_6038111 prefixEnd_6038111 3100453188200130596643739 := by
  unfold tailWord_6038111
  simp only [CollatzResearch.WordTrace]
  refine ⟨220228000627962549103714187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146818667085308366069142791 220228000627962549103714187)
  ·
    refine ⟨330342000941943823655571281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220228000627962549103714187 330342000941943823655571281)
    ·
      refine ⟨247756500706457867741678461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 330342000941943823655571281 247756500706457867741678461)
      ·
        refine ⟨92908687764921700403129423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 247756500706457867741678461 92908687764921700403129423)
        ·
          refine ⟨139363031647382550604694135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92908687764921700403129423 139363031647382550604694135)
          ·
            refine ⟨209044547471073825907041203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139363031647382550604694135 209044547471073825907041203)
            ·
              refine ⟨313566821206610738860561805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 209044547471073825907041203 313566821206610738860561805)
              ·
                refine ⟨117587557952479027072710677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 313566821206610738860561805 117587557952479027072710677)
                ·
                  refine ⟨5511916779022454394033313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 117587557952479027072710677 5511916779022454394033313)
                  ·
                    refine ⟨4133937584266840795524985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5511916779022454394033313 4133937584266840795524985)
                    ·
                      refine ⟨3100453188200130596643739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4133937584266840795524985 3100453188200130596643739)
                      ·
                        rfl

theorem cell23_6038111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 3, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 3, 6, 2, 2].length) (baseStart_6038111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6038111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6038111 prefixEnd_6038111 := by exact prefixLift 6038111
  have htrace : WordTrace (prefixWord ++ tailWord_6038111) baseStart_6038111 baseEnd_6038111 := by
    simpa [prefixWord, tailWord_6038111, baseEnd_6038111] using wordTrace_append hprefix tailTrace_6038111
  have hstable : (prefixWord ++ tailWord_6038111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6038111).length < 2 ^ (prefixWord ++ tailWord_6038111).sum := by decide
  have hdescent : baseEnd_6038111 < baseStart_6038111 := by decide
  rcases family_descends (prefixWord ++ tailWord_6038111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6038127 : List Nat := [1, 1, 2, 1, 3, 2, 2, 1, 1, 2, 7]
def baseStart_6038127 : Nat := 118140960795 + 6038127 * 2 ^ 59
def prefixEnd_6038127 : Nat := 4983230072969 + 3 ^ 40 * 6038127 * 2
def baseEnd_6038127 : Nat := 3100461403890602534043665

theorem tailTrace_6038127 : CollatzResearch.WordTrace tailWord_6038127 prefixEnd_6038127 3100461403890602534043665 := by
  unfold tailWord_6038127
  simp only [CollatzResearch.WordTrace]
  refine ⟨220228584195904583836296635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146819056130603055890864423 220228584195904583836296635)
  ·
    refine ⟨330342876293856875754444953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220228584195904583836296635 330342876293856875754444953)
    ·
      refine ⟨247757157220392656815833715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 330342876293856875754444953 247757157220392656815833715)
      ·
        refine ⟨371635735830588985223750573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 247757157220392656815833715 371635735830588985223750573)
        ·
          refine ⟨139363400936470869458906465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 371635735830588985223750573 139363400936470869458906465)
          ·
            refine ⟨104522550702353152094179849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 139363400936470869458906465 104522550702353152094179849)
            ·
              refine ⟨78391913026764864070634887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 104522550702353152094179849 78391913026764864070634887)
              ·
                refine ⟨117587869540147296105952331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78391913026764864070634887 117587869540147296105952331)
                ·
                  refine ⟨176381804310220944158928497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 117587869540147296105952331 176381804310220944158928497)
                  ·
                    refine ⟨132286353232665708119196373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 176381804310220944158928497 132286353232665708119196373)
                    ·
                      refine ⟨3100461403890602534043665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 132286353232665708119196373 3100461403890602534043665)
                      ·
                        rfl

theorem cell23_6038127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 1, 1, 2, 7].length) (baseStart_6038127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6038127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6038127 prefixEnd_6038127 := by exact prefixLift 6038127
  have htrace : WordTrace (prefixWord ++ tailWord_6038127) baseStart_6038127 baseEnd_6038127 := by
    simpa [prefixWord, tailWord_6038127, baseEnd_6038127] using wordTrace_append hprefix tailTrace_6038127
  have hstable : (prefixWord ++ tailWord_6038127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6038127).length < 2 ^ (prefixWord ++ tailWord_6038127).sum := by decide
  have hdescent : baseEnd_6038127 < baseStart_6038127 := by decide
  rcases family_descends (prefixWord ++ tailWord_6038127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6038141 : List Nat := [1, 4, 1, 1, 5, 1, 1, 1, 2, 2, 4]
def baseStart_6038141 : Nat := 118140960795 + 6038141 * 2 ^ 59
def prefixEnd_6038141 : Nat := 4983230072969 + 3 ^ 40 * 6038141 * 2
def baseEnd_6038141 : Nat := 3100468592619765479268601

theorem tailTrace_6038141 : CollatzResearch.WordTrace tailWord_6038141 prefixEnd_6038141 3100468592619765479268601 := by
  unfold tailWord_6038141
  simp only [CollatzResearch.WordTrace]
  refine ⟨220229094817853864227306277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146819396545235909484870851 220229094817853864227306277)
  ·
    refine ⟨41292955278347599542619927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 220229094817853864227306277 41292955278347599542619927)
    ·
      refine ⟨61939432917521399313929891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41292955278347599542619927 61939432917521399313929891)
      ·
        refine ⟨92909149376282098970894837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61939432917521399313929891 92909149376282098970894837)
        ·
          refine ⟨8710232754026446778521391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 92909149376282098970894837 8710232754026446778521391)
          ·
            refine ⟨13065349131039670167782087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8710232754026446778521391 13065349131039670167782087)
            ·
              refine ⟨19598023696559505251673131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13065349131039670167782087 19598023696559505251673131)
              ·
                refine ⟨29397035544839257877509697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19598023696559505251673131 29397035544839257877509697)
                ·
                  refine ⟨22047776658629443408132273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29397035544839257877509697 22047776658629443408132273)
                  ·
                    refine ⟨16535832493972082556099205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22047776658629443408132273 16535832493972082556099205)
                    ·
                      refine ⟨3100468592619765479268601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16535832493972082556099205 3100468592619765479268601)
                      ·
                        rfl

theorem cell23_6038141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 1, 1, 2, 2, 4].length) (baseStart_6038141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6038141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6038141 prefixEnd_6038141 := by exact prefixLift 6038141
  have htrace : WordTrace (prefixWord ++ tailWord_6038141) baseStart_6038141 baseEnd_6038141 := by
    simpa [prefixWord, tailWord_6038141, baseEnd_6038141] using wordTrace_append hprefix tailTrace_6038141
  have hstable : (prefixWord ++ tailWord_6038141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6038141).length < 2 ^ (prefixWord ++ tailWord_6038141).sum := by decide
  have hdescent : baseEnd_6038141 < baseStart_6038141 := by decide
  rcases family_descends (prefixWord ++ tailWord_6038141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6038144 : List Nat := [2, 1, 1, 2, 1, 5, 1, 1, 1, 5, 3]
def baseStart_6038144 : Nat := 118140960795 + 6038144 * 2 ^ 59
def prefixEnd_6038144 : Nat := 4983230072969 + 3 ^ 40 * 6038144 * 2
def baseEnd_6038144 : Nat := 3100470133061728967531087

theorem tailTrace_6038144 : CollatzResearch.WordTrace tailWord_6038144 prefixEnd_6038144 3100470133061728967531087 := by
  unfold tailWord_6038144
  simp only [CollatzResearch.WordTrace]
  refine ⟨110114602118421497869832743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146819469491228663826443657 110114602118421497869832743)
  ·
    refine ⟨165171903177632246804749115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110114602118421497869832743 165171903177632246804749115)
    ·
      refine ⟨247757854766448370207123673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165171903177632246804749115 247757854766448370207123673)
      ·
        refine ⟨185818391074836277655342755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 247757854766448370207123673 185818391074836277655342755)
        ·
          refine ⟨278727586612254416483014133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 185818391074836277655342755 278727586612254416483014133)
          ·
            refine ⟨26130711244898851545282575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 278727586612254416483014133 26130711244898851545282575)
            ·
              refine ⟨39196066867348277317923863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26130711244898851545282575 39196066867348277317923863)
              ·
                refine ⟨58794100301022415976885795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39196066867348277317923863 58794100301022415976885795)
                ·
                  refine ⟨88191150451533623965328693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58794100301022415976885795 88191150451533623965328693)
                  ·
                    refine ⟨8267920354831277246749565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 88191150451533623965328693 8267920354831277246749565)
                    ·
                      refine ⟨3100470133061728967531087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8267920354831277246749565 3100470133061728967531087)
                      ·
                        rfl

theorem cell23_6038144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 1, 1, 5, 3].length) (baseStart_6038144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6038144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6038144 prefixEnd_6038144 := by exact prefixLift 6038144
  have htrace : WordTrace (prefixWord ++ tailWord_6038144) baseStart_6038144 baseEnd_6038144 := by
    simpa [prefixWord, tailWord_6038144, baseEnd_6038144] using wordTrace_append hprefix tailTrace_6038144
  have hstable : (prefixWord ++ tailWord_6038144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6038144).length < 2 ^ (prefixWord ++ tailWord_6038144).sum := by decide
  have hdescent : baseEnd_6038144 < baseStart_6038144 := by decide
  rcases family_descends (prefixWord ++ tailWord_6038144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6038258 : List Nat := [3, 2, 1, 3, 1, 2, 4, 1, 6]
def baseStart_6038258 : Nat := 118140960795 + 6038258 * 2 ^ 59
def prefixEnd_6038258 : Nat := 4983230072969 + 3 ^ 40 * 6038258 * 2
def baseEnd_6038258 : Nat := 344503185539593502389507

theorem tailTrace_6038258 : CollatzResearch.WordTrace tailWord_6038258 prefixEnd_6038258 344503185539593502389507 := by
  unfold tailWord_6038258
  simp only [CollatzResearch.WordTrace]
  refine ⟨55058340539607498302328857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146822241438953328806210285 55058340539607498302328857)
  ·
    refine ⟨41293755404705623726746643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55058340539607498302328857 41293755404705623726746643)
    ·
      refine ⟨61940633107058435590119965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41293755404705623726746643 61940633107058435590119965)
      ·
        refine ⟨23227737415146913346294987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61940633107058435590119965 23227737415146913346294987)
        ·
          refine ⟨34841606122720370019442481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23227737415146913346294987 34841606122720370019442481)
          ·
            refine ⟨26131204592040277514581861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34841606122720370019442481 26131204592040277514581861)
            ·
              refine ⟨4899600861007552033984099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26131204592040277514581861 4899600861007552033984099)
              ·
                refine ⟨7349401291511328050976149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4899600861007552033984099 7349401291511328050976149)
                ·
                  refine ⟨344503185539593502389507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7349401291511328050976149 344503185539593502389507)
                  ·
                    rfl

theorem cell23_6038258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 4, 1, 6].length) (baseStart_6038258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6038258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6038258 prefixEnd_6038258 := by exact prefixLift 6038258
  have htrace : WordTrace (prefixWord ++ tailWord_6038258) baseStart_6038258 baseEnd_6038258 := by
    simpa [prefixWord, tailWord_6038258, baseEnd_6038258] using wordTrace_append hprefix tailTrace_6038258
  have hstable : (prefixWord ++ tailWord_6038258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6038258).length < 2 ^ (prefixWord ++ tailWord_6038258).sum := by decide
  have hdescent : baseEnd_6038258 < baseStart_6038258 := by decide
  rcases family_descends (prefixWord ++ tailWord_6038258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6038318 : List Nat := [4, 1, 3, 2, 1, 1, 1, 3, 1, 6]
def baseStart_6038318 : Nat := 118140960795 + 6038318 * 2 ^ 59
def prefixEnd_6038318 : Nat := 4983230072969 + 3 ^ 40 * 6038318 * 2
def baseEnd_6038318 : Nat := 1033519826231870428918429

theorem tailTrace_6038318 : CollatzResearch.WordTrace tailWord_6038318 prefixEnd_6038318 1033519826231870428918429 := by
  unfold tailWord_6038318
  simp only [CollatzResearch.WordTrace]
  refine ⟨27529443817276577932062451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 146823700358808415637666405 27529443817276577932062451)
  ·
    refine ⟨41294165725914866898093677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27529443817276577932062451 41294165725914866898093677)
    ·
      refine ⟨15485312147218075086785129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41294165725914866898093677 15485312147218075086785129)
      ·
        refine ⟨11613984110413556315088847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15485312147218075086785129 11613984110413556315088847)
        ·
          refine ⟨17420976165620334472633271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11613984110413556315088847 17420976165620334472633271)
          ·
            refine ⟨26131464248430501708949907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17420976165620334472633271 26131464248430501708949907)
            ·
              refine ⟨39197196372645752563424861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26131464248430501708949907 39197196372645752563424861)
              ·
                refine ⟨14698948639742157211284323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39197196372645752563424861 14698948639742157211284323)
                ·
                  refine ⟨22048422959613235816926485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14698948639742157211284323 22048422959613235816926485)
                  ·
                    refine ⟨1033519826231870428918429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22048422959613235816926485 1033519826231870428918429)
                    ·
                      rfl

theorem cell23_6038318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 3, 1, 6].length) (baseStart_6038318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6038318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6038318 prefixEnd_6038318 := by exact prefixLift 6038318
  have htrace : WordTrace (prefixWord ++ tailWord_6038318) baseStart_6038318 baseEnd_6038318 := by
    simpa [prefixWord, tailWord_6038318, baseEnd_6038318] using wordTrace_append hprefix tailTrace_6038318
  have hstable : (prefixWord ++ tailWord_6038318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6038318).length < 2 ^ (prefixWord ++ tailWord_6038318).sum := by decide
  have hdescent : baseEnd_6038318 < baseStart_6038318 := by decide
  rcases family_descends (prefixWord ++ tailWord_6038318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6038325 : List Nat := [1, 3, 3, 1, 3, 1, 1, 1, 5, 2, 2]
def baseStart_6038325 : Nat := 118140960795 + 6038325 * 2 ^ 59
def prefixEnd_6038325 : Nat := 4983230072969 + 3 ^ 40 * 6038325 * 2
def baseEnd_6038325 : Nat := 3100563073060192759367755

theorem tailTrace_6038325 : CollatzResearch.WordTrace tailWord_6038325 prefixEnd_6038325 3100563073060192759367755 := by
  unfold tailWord_6038325
  simp only [CollatzResearch.WordTrace]
  refine ⟨220235805849187263652004429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146823870566124842434669619 220235805849187263652004429)
  ·
    refine ⟨82588427193445223869501661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 220235805849187263652004429 82588427193445223869501661)
    ·
      refine ⟨30970660197541958951063123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82588427193445223869501661 30970660197541958951063123)
      ·
        refine ⟨46455990296312938426594685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30970660197541958951063123 46455990296312938426594685)
        ·
          refine ⟨17420996361117351909973007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46455990296312938426594685 17420996361117351909973007)
          ·
            refine ⟨26131494541676027864959511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17420996361117351909973007 26131494541676027864959511)
            ·
              refine ⟨39197241812514041797439267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26131494541676027864959511 39197241812514041797439267)
              ·
                refine ⟨58795862718771062696158901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39197241812514041797439267 58795862718771062696158901)
                ·
                  refine ⟨5512112129884787127764897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 58795862718771062696158901 5512112129884787127764897)
                  ·
                    refine ⟨4134084097413590345823673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5512112129884787127764897 4134084097413590345823673)
                    ·
                      refine ⟨3100563073060192759367755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4134084097413590345823673 3100563073060192759367755)
                      ·
                        rfl

theorem cell23_6038325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 1, 5, 2, 2].length) (baseStart_6038325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6038325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6038325 prefixEnd_6038325 := by exact prefixLift 6038325
  have htrace : WordTrace (prefixWord ++ tailWord_6038325) baseStart_6038325 baseEnd_6038325 := by
    simpa [prefixWord, tailWord_6038325, baseEnd_6038325] using wordTrace_append hprefix tailTrace_6038325
  have hstable : (prefixWord ++ tailWord_6038325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6038325).length < 2 ^ (prefixWord ++ tailWord_6038325).sum := by decide
  have hdescent : baseEnd_6038325 < baseStart_6038325 := by decide
  rcases family_descends (prefixWord ++ tailWord_6038325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6038328 : List Nat := [2, 1, 2, 1, 3, 2, 2, 4, 1, 2, 3]
def baseStart_6038328 : Nat := 118140960795 + 6038328 * 2 ^ 59
def prefixEnd_6038328 : Nat := 4983230072969 + 3 ^ 40 * 6038328 * 2
def baseEnd_6038328 : Nat := 3100564613502156247630241

theorem tailTrace_6038328 : CollatzResearch.WordTrace tailWord_6038328 prefixEnd_6038328 3100564613502156247630241 := by
  unfold tailWord_6038328
  simp only [CollatzResearch.WordTrace]
  refine ⟨110117957634088197582181819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146823943512117596776242425 110117957634088197582181819)
  ·
    refine ⟨165176936451132296373272729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110117957634088197582181819 165176936451132296373272729)
    ·
      refine ⟨123882702338349222279954547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 165176936451132296373272729 123882702338349222279954547)
      ·
        refine ⟨185824053507523833419931821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123882702338349222279954547 185824053507523833419931821)
        ·
          refine ⟨69684020065321437532474433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 185824053507523833419931821 69684020065321437532474433)
          ·
            refine ⟨52263015048991078149355825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69684020065321437532474433 52263015048991078149355825)
            ·
              refine ⟨39197261286743308612016869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52263015048991078149355825 39197261286743308612016869)
              ·
                refine ⟨7349486491264370364753163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39197261286743308612016869 7349486491264370364753163)
                ·
                  refine ⟨11024229736896555547129745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7349486491264370364753163 11024229736896555547129745)
                  ·
                    refine ⟨8268172302672416660347309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11024229736896555547129745 8268172302672416660347309)
                    ·
                      refine ⟨3100564613502156247630241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8268172302672416660347309 3100564613502156247630241)
                      ·
                        rfl

theorem cell23_6038328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 4, 1, 2, 3].length) (baseStart_6038328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6038328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6038328 prefixEnd_6038328 := by exact prefixLift 6038328
  have htrace : WordTrace (prefixWord ++ tailWord_6038328) baseStart_6038328 baseEnd_6038328 := by
    simpa [prefixWord, tailWord_6038328, baseEnd_6038328] using wordTrace_append hprefix tailTrace_6038328
  have hstable : (prefixWord ++ tailWord_6038328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6038328).length < 2 ^ (prefixWord ++ tailWord_6038328).sum := by decide
  have hdescent : baseEnd_6038328 < baseStart_6038328 := by decide
  rcases family_descends (prefixWord ++ tailWord_6038328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6038341 : List Nat := [1, 3, 1, 1, 1, 2, 2, 3, 3, 3, 3]
def baseStart_6038341 : Nat := 118140960795 + 6038341 * 2 ^ 59
def prefixEnd_6038341 : Nat := 4983230072969 + 3 ^ 40 * 6038341 * 2
def baseEnd_6038341 : Nat := 3100571288750664696767681

theorem tailTrace_6038341 : CollatzResearch.WordTrace tailWord_6038341 prefixEnd_6038341 3100571288750664696767681 := by
  unfold tailWord_6038341
  simp only [CollatzResearch.WordTrace]
  refine ⟨220236389417129298384586877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146824259611419532256391251 220236389417129298384586877)
  ·
    refine ⟨82588646031423486894220079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 220236389417129298384586877 82588646031423486894220079)
    ·
      refine ⟨123882969047135230341330119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82588646031423486894220079 123882969047135230341330119)
      ·
        refine ⟨185824453570702845511995179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123882969047135230341330119 185824453570702845511995179)
        ·
          refine ⟨278736680356054268267992769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 185824453570702845511995179 278736680356054268267992769)
          ·
            refine ⟨209052510267040701200994577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 278736680356054268267992769 209052510267040701200994577)
            ·
              refine ⟨156789382700280525900745933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 209052510267040701200994577 156789382700280525900745933)
              ·
                refine ⟨58796018512605197212779725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 156789382700280525900745933 58796018512605197212779725)
                ·
                  refine ⟨22048506942226948954792397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 58796018512605197212779725 22048506942226948954792397)
                  ·
                    refine ⟨8268190103335105858047149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22048506942226948954792397 8268190103335105858047149)
                    ·
                      refine ⟨3100571288750664696767681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8268190103335105858047149 3100571288750664696767681)
                      ·
                        rfl

theorem cell23_6038341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 3, 3, 3, 3].length) (baseStart_6038341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6038341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6038341 prefixEnd_6038341 := by exact prefixLift 6038341
  have htrace : WordTrace (prefixWord ++ tailWord_6038341) baseStart_6038341 baseEnd_6038341 := by
    simpa [prefixWord, tailWord_6038341, baseEnd_6038341] using wordTrace_append hprefix tailTrace_6038341
  have hstable : (prefixWord ++ tailWord_6038341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6038341).length < 2 ^ (prefixWord ++ tailWord_6038341).sum := by decide
  have hdescent : baseEnd_6038341 < baseStart_6038341 := by decide
  rcases family_descends (prefixWord ++ tailWord_6038341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6038345 : List Nat := [1, 2, 1, 1, 2, 5, 4, 1, 1, 2, 3]
def baseStart_6038345 : Nat := 118140960795 + 6038345 * 2 ^ 59
def prefixEnd_6038345 : Nat := 4983230072969 + 3 ^ 40 * 6038345 * 2
def baseEnd_6038345 : Nat := 3100573342673282681117663

theorem tailTrace_6038345 : CollatzResearch.WordTrace tailWord_6038345 prefixEnd_6038345 3100573342673282681117663 := by
  unfold tailWord_6038345
  simp only [CollatzResearch.WordTrace]
  refine ⟨220236535309114807067732489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146824356872743204711821659 220236535309114807067732489)
  ·
    refine ⟨165177401481836105300799367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 220236535309114807067732489 165177401481836105300799367)
    ·
      refine ⟨247766102222754157951199051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165177401481836105300799367 247766102222754157951199051)
      ·
        refine ⟨371649153334131236926798577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 247766102222754157951199051 371649153334131236926798577)
        ·
          refine ⟨278736865000598427695098933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 371649153334131236926798577 278736865000598427695098933)
          ·
            refine ⟨26131581093806102596415525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 278736865000598427695098933 26131581093806102596415525)
            ·
              refine ⟨4899671455088644236827911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26131581093806102596415525 4899671455088644236827911)
              ·
                refine ⟨7349507182632966355241867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4899671455088644236827911 7349507182632966355241867)
                ·
                  refine ⟨11024260773949449532862801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7349507182632966355241867 11024260773949449532862801)
                  ·
                    refine ⟨8268195580462087149647101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11024260773949449532862801 8268195580462087149647101)
                    ·
                      refine ⟨3100573342673282681117663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8268195580462087149647101 3100573342673282681117663)
                      ·
                        rfl

theorem cell23_6038345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 4, 1, 1, 2, 3].length) (baseStart_6038345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6038345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6038345 prefixEnd_6038345 := by exact prefixLift 6038345
  have htrace : WordTrace (prefixWord ++ tailWord_6038345) baseStart_6038345 baseEnd_6038345 := by
    simpa [prefixWord, tailWord_6038345, baseEnd_6038345] using wordTrace_append hprefix tailTrace_6038345
  have hstable : (prefixWord ++ tailWord_6038345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6038345).length < 2 ^ (prefixWord ++ tailWord_6038345).sum := by decide
  have hdescent : baseEnd_6038345 < baseStart_6038345 := by decide
  rcases family_descends (prefixWord ++ tailWord_6038345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6038375 : List Nat := [1, 1, 5, 1, 2, 4, 1, 1, 1, 3, 3]
def baseStart_6038375 : Nat := 118140960795 + 6038375 * 2 ^ 59
def prefixEnd_6038375 : Nat := 4983230072969 + 3 ^ 40 * 6038375 * 2
def baseEnd_6038375 : Nat := 3100588747092917563742525

theorem tailTrace_6038375 : CollatzResearch.WordTrace tailWord_6038375 prefixEnd_6038375 3100588747092917563742525 := by
  unfold tailWord_6038375
  simp only [CollatzResearch.WordTrace]
  refine ⟨220237629499006122191324579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146825086332670748127549719 220237629499006122191324579)
  ·
    refine ⟨330356444248509183286986869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220237629499006122191324579 330356444248509183286986869)
    ·
      refine ⟨30970916648297735933155019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 330356444248509183286986869 30970916648297735933155019)
      ·
        refine ⟨46456374972446603899732529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30970916648297735933155019 46456374972446603899732529)
        ·
          refine ⟨34842281229334952924799397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46456374972446603899732529 34842281229334952924799397)
          ·
            refine ⟨6532927730500303673399887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34842281229334952924799397 6532927730500303673399887)
            ·
              refine ⟨9799391595750455510099831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6532927730500303673399887 9799391595750455510099831)
              ·
                refine ⟨14699087393625683265149747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9799391595750455510099831 14699087393625683265149747)
                ·
                  refine ⟨22048631090438524897724621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14699087393625683265149747 22048631090438524897724621)
                  ·
                    refine ⟨8268236658914446836646733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22048631090438524897724621 8268236658914446836646733)
                    ·
                      refine ⟨3100588747092917563742525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8268236658914446836646733 3100588747092917563742525)
                      ·
                        rfl

theorem cell23_6038375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 4, 1, 1, 1, 3, 3].length) (baseStart_6038375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6038375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6038375 prefixEnd_6038375 := by exact prefixLift 6038375
  have htrace : WordTrace (prefixWord ++ tailWord_6038375) baseStart_6038375 baseEnd_6038375 := by
    simpa [prefixWord, tailWord_6038375, baseEnd_6038375] using wordTrace_append hprefix tailTrace_6038375
  have hstable : (prefixWord ++ tailWord_6038375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6038375).length < 2 ^ (prefixWord ++ tailWord_6038375).sum := by decide
  have hdescent : baseEnd_6038375 < baseStart_6038375 := by decide
  rcases family_descends (prefixWord ++ tailWord_6038375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6038382 : List Nat := [4, 1, 2, 3, 3, 1, 2, 7]
def baseStart_6038382 : Nat := 118140960795 + 6038382 * 2 ^ 59
def prefixEnd_6038382 : Nat := 4983230072969 + 3 ^ 40 * 6038382 * 2
def baseEnd_6038382 : Nat := 114836753387314779124259

theorem tailTrace_6038382 : CollatzResearch.WordTrace tailWord_6038382 prefixEnd_6038382 114836753387314779124259 := by
  unfold tailWord_6038382
  simp only [CollatzResearch.WordTrace]
  refine ⟨27529735601247595298353675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 146825256539987174924552933 27529735601247595298353675)
  ·
    refine ⟨41294603401871392947530513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27529735601247595298353675 41294603401871392947530513)
    ·
      refine ⟨30970952551403544710647885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41294603401871392947530513 30970952551403544710647885)
      ·
        refine ⟨11614107206776329266492957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30970952551403544710647885 11614107206776329266492957)
        ·
          refine ⟨4355290202541123474934859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11614107206776329266492957 4355290202541123474934859)
          ·
            refine ⟨6532935303811685212402289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4355290202541123474934859 6532935303811685212402289)
            ·
              refine ⟨4899701477858763909301717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6532935303811685212402289 4899701477858763909301717)
              ·
                refine ⟨114836753387314779124259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4899701477858763909301717 114836753387314779124259)
                ·
                  rfl

theorem cell23_6038382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 3, 1, 2, 7].length) (baseStart_6038382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6038382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6038382 prefixEnd_6038382 := by exact prefixLift 6038382
  have htrace : WordTrace (prefixWord ++ tailWord_6038382) baseStart_6038382 baseEnd_6038382 := by
    simpa [prefixWord, tailWord_6038382, baseEnd_6038382] using wordTrace_append hprefix tailTrace_6038382
  have hstable : (prefixWord ++ tailWord_6038382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6038382).length < 2 ^ (prefixWord ++ tailWord_6038382).sum := by decide
  have hdescent : baseEnd_6038382 < baseStart_6038382 := by decide
  rcases family_descends (prefixWord ++ tailWord_6038382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6038385 : List Nat := [1, 2, 2, 2, 1, 4, 1, 4, 1, 3, 2]
def baseStart_6038385 : Nat := 118140960795 + 6038385 * 2 ^ 59
def prefixEnd_6038385 : Nat := 4983230072969 + 3 ^ 40 * 6038385 * 2
def baseEnd_6038385 : Nat := 3100593881899462524617479

theorem tailTrace_6038385 : CollatzResearch.WordTrace tailWord_6038385 prefixEnd_6038385 3100593881899462524617479 := by
  unfold tailWord_6038385
  simp only [CollatzResearch.WordTrace]
  refine ⟨220237994228969893899188609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146825329485979929266125739 220237994228969893899188609)
  ·
    refine ⟨165178495671727420424391457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 220237994228969893899188609 165178495671727420424391457)
    ·
      refine ⟨123883871753795565318293593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 165178495671727420424391457 123883871753795565318293593)
      ·
        refine ⟨92912903815346673988720195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123883871753795565318293593 92912903815346673988720195)
        ·
          refine ⟨139369355723020010983080293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92912903815346673988720195 139369355723020010983080293)
          ·
            refine ⟨26131754198066252059327555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 139369355723020010983080293 26131754198066252059327555)
            ·
              refine ⟨39197631297099378088991333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26131754198066252059327555 39197631297099378088991333)
              ·
                refine ⟨7349555868206133391685875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39197631297099378088991333 7349555868206133391685875)
                ·
                  refine ⟨11024333802309200087528813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7349555868206133391685875 11024333802309200087528813)
                  ·
                    refine ⟨4134125175865950032823305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11024333802309200087528813 4134125175865950032823305)
                    ·
                      refine ⟨3100593881899462524617479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4134125175865950032823305 3100593881899462524617479)
                      ·
                        rfl

theorem cell23_6038385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 4, 1, 3, 2].length) (baseStart_6038385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6038385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6038385 prefixEnd_6038385 := by exact prefixLift 6038385
  have htrace : WordTrace (prefixWord ++ tailWord_6038385) baseStart_6038385 baseEnd_6038385 := by
    simpa [prefixWord, tailWord_6038385, baseEnd_6038385] using wordTrace_append hprefix tailTrace_6038385
  have hstable : (prefixWord ++ tailWord_6038385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6038385).length < 2 ^ (prefixWord ++ tailWord_6038385).sum := by decide
  have hdescent : baseEnd_6038385 < baseStart_6038385 := by decide
  rcases family_descends (prefixWord ++ tailWord_6038385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6038411 : List Nat := [1, 1, 1, 1, 4, 2, 2, 1, 4, 2, 4]
def baseStart_6038411 : Nat := 118140960795 + 6038411 * 2 ^ 59
def prefixEnd_6038411 : Nat := 4983230072969 + 3 ^ 40 * 6038411 * 2
def baseEnd_6038411 : Nat := 3100607232396479422892359

theorem tailTrace_6038411 : CollatzResearch.WordTrace tailWord_6038411 prefixEnd_6038411 3100607232396479422892359 := by
  unfold tailWord_6038411
  simp only [CollatzResearch.WordTrace]
  refine ⟨220238942526875700339635087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146825961684583800226423391 220238942526875700339635087)
  ·
    refine ⟨330358413790313550509452631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220238942526875700339635087 330358413790313550509452631)
    ·
      refine ⟨495537620685470325764178947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 330358413790313550509452631 495537620685470325764178947)
      ·
        refine ⟨743306431028205488646268421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 495537620685470325764178947 743306431028205488646268421)
        ·
          refine ⟨139369955817788529121175329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 743306431028205488646268421 139369955817788529121175329)
          ·
            refine ⟨104527466863341396840881497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 139369955817788529121175329 104527466863341396840881497)
            ·
              refine ⟨78395600147506047630661123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 104527466863341396840881497 78395600147506047630661123)
              ·
                refine ⟨117593400221259071445991685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78395600147506047630661123 117593400221259071445991685)
                ·
                  refine ⟨22048762541486075896123441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 117593400221259071445991685 22048762541486075896123441)
                  ·
                    refine ⟨16536571906114556922092581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22048762541486075896123441 16536571906114556922092581)
                    ·
                      refine ⟨3100607232396479422892359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16536571906114556922092581 3100607232396479422892359)
                      ·
                        rfl

theorem cell23_6038411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 1, 4, 2, 4].length) (baseStart_6038411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6038411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6038411 prefixEnd_6038411 := by exact prefixLift 6038411
  have htrace : WordTrace (prefixWord ++ tailWord_6038411) baseStart_6038411 baseEnd_6038411 := by
    simpa [prefixWord, tailWord_6038411, baseEnd_6038411] using wordTrace_append hprefix tailTrace_6038411
  have hstable : (prefixWord ++ tailWord_6038411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6038411).length < 2 ^ (prefixWord ++ tailWord_6038411).sum := by decide
  have hdescent : baseEnd_6038411 < baseStart_6038411 := by decide
  rcases family_descends (prefixWord ++ tailWord_6038411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6038426 : List Nat := [3, 1, 1, 4, 4, 1, 2, 1, 2, 1, 3]
def baseStart_6038426 : Nat := 118140960795 + 6038426 * 2 ^ 59
def prefixEnd_6038426 : Nat := 4983230072969 + 3 ^ 40 * 6038426 * 2
def baseEnd_6038426 : Nat := 3100614934606296864204791

theorem tailTrace_6038426 : CollatzResearch.WordTrace tailWord_6038426 prefixEnd_6038426 3100614934606296864204791 := by
  unfold tailWord_6038426
  simp only [CollatzResearch.WordTrace]
  refine ⟨55059872405455339475357783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146826326414547571934287421 55059872405455339475357783)
  ·
    refine ⟨82589808608183009213036675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55059872405455339475357783 82589808608183009213036675)
    ·
      refine ⟨123884712912274513819555013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82589808608183009213036675 123884712912274513819555013)
      ·
        refine ⟨23228383671051471341166565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 123884712912274513819555013 23228383671051471341166565)
        ·
          refine ⟨4355321938322150876468731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23228383671051471341166565 4355321938322150876468731)
          ·
            refine ⟨6532982907483226314703097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4355321938322150876468731 6532982907483226314703097)
            ·
              refine ⟨4899737180612419736027323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6532982907483226314703097 4899737180612419736027323)
              ·
                refine ⟨7349605770918629604040985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4899737180612419736027323 7349605770918629604040985)
                ·
                  refine ⟨5512204328188972203030739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7349605770918629604040985 5512204328188972203030739)
                  ·
                    refine ⟨8268306492283458304546109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5512204328188972203030739 8268306492283458304546109)
                    ·
                      refine ⟨3100614934606296864204791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8268306492283458304546109 3100614934606296864204791)
                      ·
                        rfl

theorem cell23_6038426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 4, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 4, 1, 2, 1, 2, 1, 3].length) (baseStart_6038426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6038426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6038426 prefixEnd_6038426 := by exact prefixLift 6038426
  have htrace : WordTrace (prefixWord ++ tailWord_6038426) baseStart_6038426 baseEnd_6038426 := by
    simpa [prefixWord, tailWord_6038426, baseEnd_6038426] using wordTrace_append hprefix tailTrace_6038426
  have hstable : (prefixWord ++ tailWord_6038426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6038426).length < 2 ^ (prefixWord ++ tailWord_6038426).sum := by decide
  have hdescent : baseEnd_6038426 < baseStart_6038426 := by decide
  rcases family_descends (prefixWord ++ tailWord_6038426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6038478 : List Nat := [4, 1, 1, 1, 2, 3, 2, 1, 1, 2, 5]
def baseStart_6038478 : Nat := 118140960795 + 6038478 * 2 ^ 59
def prefixEnd_6038478 : Nat := 4983230072969 + 3 ^ 40 * 6038478 * 2
def baseEnd_6038478 : Nat := 3100641635600330660754551

theorem tailTrace_6038478 : CollatzResearch.WordTrace tailWord_6038478 prefixEnd_6038478 3100641635600330660754551 := by
  unfold tailWord_6038478
  simp only [CollatzResearch.WordTrace]
  refine ⟨27530173277204121347790511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 146827590811755313854882725 27530173277204121347790511)
  ·
    refine ⟨41295259915806182021685767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27530173277204121347790511 41295259915806182021685767)
    ·
      refine ⟨61942889873709273032528651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41295259915806182021685767 61942889873709273032528651)
      ·
        refine ⟨92914334810563909548792977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61942889873709273032528651 92914334810563909548792977)
        ·
          refine ⟨69685751107922932161594733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92914334810563909548792977 69685751107922932161594733)
          ·
            refine ⟨26132156665471099560598025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69685751107922932161594733 26132156665471099560598025)
            ·
              refine ⟨19599117499103324670448519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26132156665471099560598025 19599117499103324670448519)
              ·
                refine ⟨29398676248654987005672779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19599117499103324670448519 29398676248654987005672779)
                ·
                  refine ⟨44098014372982480508509169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29398676248654987005672779 44098014372982480508509169)
                  ·
                    refine ⟨33073510779736860381381877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 44098014372982480508509169 33073510779736860381381877)
                    ·
                      refine ⟨3100641635600330660754551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33073510779736860381381877 3100641635600330660754551)
                      ·
                        rfl

theorem cell23_6038478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 2, 1, 1, 2, 5].length) (baseStart_6038478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6038478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6038478 prefixEnd_6038478 := by exact prefixLift 6038478
  have htrace : WordTrace (prefixWord ++ tailWord_6038478) baseStart_6038478 baseEnd_6038478 := by
    simpa [prefixWord, tailWord_6038478, baseEnd_6038478] using wordTrace_append hprefix tailTrace_6038478
  have hstable : (prefixWord ++ tailWord_6038478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6038478).length < 2 ^ (prefixWord ++ tailWord_6038478).sum := by decide
  have hdescent : baseEnd_6038478 < baseStart_6038478 := by decide
  rcases family_descends (prefixWord ++ tailWord_6038478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6038565 : List Nat := [1, 3, 1, 2, 2, 2, 1, 3, 1, 5, 2]
def baseStart_6038565 : Nat := 118140960795 + 6038565 * 2 ^ 59
def prefixEnd_6038565 : Nat := 4983230072969 + 3 ^ 40 * 6038565 * 2
def baseEnd_6038565 : Nat := 3100686308417271820366651

theorem tailTrace_6038565 : CollatzResearch.WordTrace tailWord_6038565 prefixEnd_6038565 3100686308417271820366651 := by
  unfold tailWord_6038565
  simp only [CollatzResearch.WordTrace]
  refine ⟨220244559368317784640741149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146829706245545189760494099 220244559368317784640741149)
  ·
    refine ⟨82591709763119169240277931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 220244559368317784640741149 82591709763119169240277931)
    ·
      refine ⟨123887564644678753860416897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82591709763119169240277931 123887564644678753860416897)
      ·
        refine ⟨92915673483509065395312673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123887564644678753860416897 92915673483509065395312673)
        ·
          refine ⟨69686755112631799046484505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92915673483509065395312673 69686755112631799046484505)
          ·
            refine ⟨52265066334473849284863379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69686755112631799046484505 52265066334473849284863379)
            ·
              refine ⟨78397599501710773927295069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52265066334473849284863379 78397599501710773927295069)
              ·
                refine ⟨29399099813141540222735651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 78397599501710773927295069 29399099813141540222735651)
                ·
                  refine ⟨44098649719712310334103477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29399099813141540222735651 44098649719712310334103477)
                  ·
                    refine ⟨4134248411223029093822201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 44098649719712310334103477 4134248411223029093822201)
                    ·
                      refine ⟨3100686308417271820366651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4134248411223029093822201 3100686308417271820366651)
                      ·
                        rfl

theorem cell23_6038565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 3, 1, 5, 2].length) (baseStart_6038565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6038565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6038565 prefixEnd_6038565 := by exact prefixLift 6038565
  have htrace : WordTrace (prefixWord ++ tailWord_6038565) baseStart_6038565 baseEnd_6038565 := by
    simpa [prefixWord, tailWord_6038565, baseEnd_6038565] using wordTrace_append hprefix tailTrace_6038565
  have hstable : (prefixWord ++ tailWord_6038565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6038565).length < 2 ^ (prefixWord ++ tailWord_6038565).sum := by decide
  have hdescent : baseEnd_6038565 < baseStart_6038565 := by decide
  rcases family_descends (prefixWord ++ tailWord_6038565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6038589 : List Nat := [1, 4, 1, 3, 1, 4, 1, 1, 3, 1, 3]
def baseStart_6038589 : Nat := 118140960795 + 6038589 * 2 ^ 59
def prefixEnd_6038589 : Nat := 4983230072969 + 3 ^ 40 * 6038589 * 2
def baseEnd_6038589 : Nat := 3100698631952979726466541

theorem tailTrace_6038589 : CollatzResearch.WordTrace tailWord_6038589 prefixEnd_6038589 3100698631952979726466541 := by
  unfold tailWord_6038589
  simp only [CollatzResearch.WordTrace]
  refine ⟨220245434720230836739614821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146830289813487224493076547 220245434720230836739614821)
  ·
    refine ⟨41296019010043281888677779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 220245434720230836739614821 41296019010043281888677779)
    ·
      refine ⟨61944028515064922833016669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41296019010043281888677779 61944028515064922833016669)
      ·
        refine ⟨23229010693149346062381251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61944028515064922833016669 23229010693149346062381251)
        ·
          refine ⟨34843516039724019093571877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23229010693149346062381251 34843516039724019093571877)
          ·
            refine ⟨6533159257448253580044727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34843516039724019093571877 6533159257448253580044727)
            ·
              refine ⟨9799738886172380370067091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6533159257448253580044727 9799738886172380370067091)
              ·
                refine ⟨14699608329258570555100637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9799738886172380370067091 14699608329258570555100637)
                ·
                  refine ⟨5512353123471963958162739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14699608329258570555100637 5512353123471963958162739)
                  ·
                    refine ⟨8268529685207945937244109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5512353123471963958162739 8268529685207945937244109)
                    ·
                      refine ⟨3100698631952979726466541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8268529685207945937244109 3100698631952979726466541)
                      ·
                        rfl

theorem cell23_6038589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 4, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 4, 1, 1, 3, 1, 3].length) (baseStart_6038589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6038589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6038589 prefixEnd_6038589 := by exact prefixLift 6038589
  have htrace : WordTrace (prefixWord ++ tailWord_6038589) baseStart_6038589 baseEnd_6038589 := by
    simpa [prefixWord, tailWord_6038589, baseEnd_6038589] using wordTrace_append hprefix tailTrace_6038589
  have hstable : (prefixWord ++ tailWord_6038589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6038589).length < 2 ^ (prefixWord ++ tailWord_6038589).sum := by decide
  have hdescent : baseEnd_6038589 < baseStart_6038589 := by decide
  rcases family_descends (prefixWord ++ tailWord_6038589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6038608 : List Nat := [2, 1, 1, 1, 1, 3, 1, 2, 5, 2, 4]
def baseStart_6038608 : Nat := 118140960795 + 6038608 * 2 ^ 59
def prefixEnd_6038608 : Nat := 4983230072969 + 3 ^ 40 * 6038608 * 2
def baseEnd_6038608 : Nat := 3100708388085415152128953

theorem tailTrace_6038608 : CollatzResearch.WordTrace tailWord_6038608 prefixEnd_6038608 3100708388085415152128953 := by
  unfold tailWord_6038608
  simp only [CollatzResearch.WordTrace]
  refine ⟨110123063853581001492278239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146830751804774668656370985 110123063853581001492278239)
  ·
    refine ⟨165184595780371502238417359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110123063853581001492278239 165184595780371502238417359)
    ·
      refine ⟨247776893670557253357626039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165184595780371502238417359 247776893670557253357626039)
      ·
        refine ⟨371665340505835880036439059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 247776893670557253357626039 371665340505835880036439059)
        ·
          refine ⟨557498010758753820054658589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 371665340505835880036439059 557498010758753820054658589)
          ·
            refine ⟨209061754034532682520496971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 557498010758753820054658589 209061754034532682520496971)
            ·
              refine ⟨313592631051799023780745457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 209061754034532682520496971 313592631051799023780745457)
              ·
                refine ⟨235194473288849267835559093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 313592631051799023780745457 235194473288849267835559093)
                ·
                  refine ⟨22049481870829618859583665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 235194473288849267835559093 22049481870829618859583665)
                  ·
                    refine ⟨16537111403122214144687749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22049481870829618859583665 16537111403122214144687749)
                    ·
                      refine ⟨3100708388085415152128953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16537111403122214144687749 3100708388085415152128953)
                      ·
                        rfl

theorem cell23_6038608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 2, 5, 2, 4].length) (baseStart_6038608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6038608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6038608 prefixEnd_6038608 := by exact prefixLift 6038608
  have htrace : WordTrace (prefixWord ++ tailWord_6038608) baseStart_6038608 baseEnd_6038608 := by
    simpa [prefixWord, tailWord_6038608, baseEnd_6038608] using wordTrace_append hprefix tailTrace_6038608
  have hstable : (prefixWord ++ tailWord_6038608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6038608).length < 2 ^ (prefixWord ++ tailWord_6038608).sum := by decide
  have hdescent : baseEnd_6038608 < baseStart_6038608 := by decide
  rcases family_descends (prefixWord ++ tailWord_6038608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6038612 : List Nat := [2, 4, 1, 1, 1, 1, 5, 2, 1, 1, 4]
def baseStart_6038612 : Nat := 118140960795 + 6038612 * 2 ^ 59
def prefixEnd_6038612 : Nat := 4983230072969 + 3 ^ 40 * 6038612 * 2
def baseEnd_6038612 : Nat := 3100710442008033136478935

theorem tailTrace_6038612 : CollatzResearch.WordTrace tailWord_6038612 prefixEnd_6038612 3100710442008033136478935 := by
  unfold tailWord_6038612
  simp only [CollatzResearch.WordTrace]
  refine ⟨110123136799573755833851045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146830849066098341111801393 110123136799573755833851045)
  ·
    refine ⟨20648088149920079218847071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 110123136799573755833851045 20648088149920079218847071)
    ·
      refine ⟨30972132224880118828270607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20648088149920079218847071 30972132224880118828270607)
      ·
        refine ⟨46458198337320178242405911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30972132224880118828270607 46458198337320178242405911)
        ·
          refine ⟨69687297505980267363608867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46458198337320178242405911 69687297505980267363608867)
          ·
            refine ⟨104530946258970401045413301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69687297505980267363608867 104530946258970401045413301)
            ·
              refine ⟨9799776211778475098007497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 104530946258970401045413301 9799776211778475098007497)
              ·
                refine ⟨7349832158833856323505623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9799776211778475098007497 7349832158833856323505623)
                ·
                  refine ⟨11024748238250784485258435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7349832158833856323505623 11024748238250784485258435)
                  ·
                    refine ⟨16537122357376176727887653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11024748238250784485258435 16537122357376176727887653)
                    ·
                      refine ⟨3100710442008033136478935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16537122357376176727887653 3100710442008033136478935)
                      ·
                        rfl

theorem cell23_6038612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 5, 2, 1, 1, 4].length) (baseStart_6038612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6038612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6038612 prefixEnd_6038612 := by exact prefixLift 6038612
  have htrace : WordTrace (prefixWord ++ tailWord_6038612) baseStart_6038612 baseEnd_6038612 := by
    simpa [prefixWord, tailWord_6038612, baseEnd_6038612] using wordTrace_append hprefix tailTrace_6038612
  have hstable : (prefixWord ++ tailWord_6038612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6038612).length < 2 ^ (prefixWord ++ tailWord_6038612).sum := by decide
  have hdescent : baseEnd_6038612 < baseStart_6038612 := by decide
  rcases family_descends (prefixWord ++ tailWord_6038612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6038648 : List Nat := [2, 1, 2, 1, 1, 1, 5, 1, 2, 7]
def baseStart_6038648 : Nat := 118140960795 + 6038648 * 2 ^ 59
def prefixEnd_6038648 : Nat := 4983230072969 + 3 ^ 40 * 6038648 * 2
def baseEnd_6038648 : Nat := 1033576309103864998542923

theorem tailTrace_6038648 : CollatzResearch.WordTrace tailWord_6038648 prefixEnd_6038648 1033576309103864998542923 := by
  unfold tailWord_6038648
  simp only [CollatzResearch.WordTrace]
  refine ⟨110123793313508544908006299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146831724418011393210675065 110123793313508544908006299)
  ·
    refine ⟨165185689970262817362009449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110123793313508544908006299 165185689970262817362009449)
    ·
      refine ⟨123889267477697113021507087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 165185689970262817362009449 123889267477697113021507087)
      ·
        refine ⟨185833901216545669532260631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123889267477697113021507087 185833901216545669532260631)
        ·
          refine ⟨278750851824818504298390947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 185833901216545669532260631 278750851824818504298390947)
          ·
            refine ⟨418126277737227756447586421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 278750851824818504298390947 418126277737227756447586421)
            ·
              refine ⟨39199338537865102166961227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 418126277737227756447586421 39199338537865102166961227)
              ·
                refine ⟨58799007806797653250441841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39199338537865102166961227 58799007806797653250441841)
                ·
                  refine ⟨44099255855098239937831381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 58799007806797653250441841 44099255855098239937831381)
                  ·
                    refine ⟨1033576309103864998542923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 44099255855098239937831381 1033576309103864998542923)
                    ·
                      rfl

theorem cell23_6038648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 1, 2, 7].length) (baseStart_6038648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6038648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6038648 prefixEnd_6038648 := by exact prefixLift 6038648
  have htrace : WordTrace (prefixWord ++ tailWord_6038648) baseStart_6038648 baseEnd_6038648 := by
    simpa [prefixWord, tailWord_6038648, baseEnd_6038648] using wordTrace_append hprefix tailTrace_6038648
  have hstable : (prefixWord ++ tailWord_6038648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6038648).length < 2 ^ (prefixWord ++ tailWord_6038648).sum := by decide
  have hdescent : baseEnd_6038648 < baseStart_6038648 := by decide
  rcases family_descends (prefixWord ++ tailWord_6038648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6038689 : List Nat := [1, 2, 3, 3, 1, 1, 3, 3, 1, 3, 2]
def baseStart_6038689 : Nat := 118140960795 + 6038689 * 2 ^ 59
def prefixEnd_6038689 : Nat := 4983230072969 + 3 ^ 40 * 6038689 * 2
def baseEnd_6038689 : Nat := 3100749980018429335216081

theorem tailTrace_6038689 : CollatzResearch.WordTrace tailWord_6038689 prefixEnd_6038689 3100749980018429335216081 := by
  unfold tailWord_6038689
  simp only [CollatzResearch.WordTrace]
  refine ⟨220249082019868553818255121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146832721346579035878836747 220249082019868553818255121)
  ·
    refine ⟨165186811514901415363691341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 220249082019868553818255121 165186811514901415363691341)
    ·
      refine ⟨61945054318088030761384253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 165186811514901415363691341 61945054318088030761384253)
      ·
        refine ⟨23229395369283011535519095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61945054318088030761384253 23229395369283011535519095)
        ·
          refine ⟨34844093053924517303278643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23229395369283011535519095 34844093053924517303278643)
          ·
            refine ⟨52266139580886775954917965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34844093053924517303278643 52266139580886775954917965)
            ·
              refine ⟨19599802342832540983094237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52266139580886775954917965 19599802342832540983094237)
              ·
                refine ⟨7349925878562202868660339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19599802342832540983094237 7349925878562202868660339)
                ·
                  refine ⟨11024888817843304302990509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7349925878562202868660339 11024888817843304302990509)
                  ·
                    refine ⟨4134333306691239113621441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11024888817843304302990509 4134333306691239113621441)
                    ·
                      refine ⟨3100749980018429335216081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4134333306691239113621441 3100749980018429335216081)
                      ·
                        rfl

theorem cell23_6038689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 3, 3, 1, 3, 2].length) (baseStart_6038689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6038689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6038689 prefixEnd_6038689 := by exact prefixLift 6038689
  have htrace : WordTrace (prefixWord ++ tailWord_6038689) baseStart_6038689 baseEnd_6038689 := by
    simpa [prefixWord, tailWord_6038689, baseEnd_6038689] using wordTrace_append hprefix tailTrace_6038689
  have hstable : (prefixWord ++ tailWord_6038689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6038689).length < 2 ^ (prefixWord ++ tailWord_6038689).sum := by decide
  have hdescent : baseEnd_6038689 < baseStart_6038689 := by decide
  rcases family_descends (prefixWord ++ tailWord_6038689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6038719 : List Nat := [1, 1, 2, 2, 2, 2, 2, 5, 2, 2, 2]
def baseStart_6038719 : Nat := 118140960795 + 6038719 * 2 ^ 59
def prefixEnd_6038719 : Nat := 4983230072969 + 3 ^ 40 * 6038719 * 2
def baseEnd_6038719 : Nat := 3100765384438064217840943

theorem tailTrace_6038719 : CollatzResearch.WordTrace tailWord_6038719 prefixEnd_6038719 3100765384438064217840943 := by
  unfold tailWord_6038719
  simp only [CollatzResearch.WordTrace]
  refine ⟨220250176209759868941847211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146833450806506579294564807 220250176209759868941847211)
  ·
    refine ⟨330375264314639803412770817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220250176209759868941847211 330375264314639803412770817)
    ·
      refine ⟨247781448235979852559578113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 330375264314639803412770817 247781448235979852559578113)
      ·
        refine ⟨185836086176984889419683585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 247781448235979852559578113 185836086176984889419683585)
        ·
          refine ⟨139377064632738667064762689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 185836086176984889419683585 139377064632738667064762689)
          ·
            refine ⟨104532798474554000298572017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 139377064632738667064762689 104532798474554000298572017)
            ·
              refine ⟨78399598855915500223929013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 104532798474554000298572017 78399598855915500223929013)
              ·
                refine ⟨7349962392742078145993345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 78399598855915500223929013 7349962392742078145993345)
                ·
                  refine ⟨5512471794556558609495009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7349962392742078145993345 5512471794556558609495009)
                  ·
                    refine ⟨4134353845917418957121257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5512471794556558609495009 4134353845917418957121257)
                    ·
                      refine ⟨3100765384438064217840943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4134353845917418957121257 3100765384438064217840943)
                      ·
                        rfl

theorem cell23_6038719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 5, 2, 2, 2].length) (baseStart_6038719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6038719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6038719 prefixEnd_6038719 := by exact prefixLift 6038719
  have htrace : WordTrace (prefixWord ++ tailWord_6038719) baseStart_6038719 baseEnd_6038719 := by
    simpa [prefixWord, tailWord_6038719, baseEnd_6038719] using wordTrace_append hprefix tailTrace_6038719
  have hstable : (prefixWord ++ tailWord_6038719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6038719).length < 2 ^ (prefixWord ++ tailWord_6038719).sum := by decide
  have hdescent : baseEnd_6038719 < baseStart_6038719 := by decide
  rcases family_descends (prefixWord ++ tailWord_6038719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6038735 : List Nat := [1, 1, 2, 1, 1, 3, 2, 2, 4, 3, 3]
def baseStart_6038735 : Nat := 118140960795 + 6038735 * 2 ^ 59
def prefixEnd_6038735 : Nat := 4983230072969 + 3 ^ 40 * 6038735 * 2
def baseEnd_6038735 : Nat := 3100773600128536155240869

theorem tailTrace_6038735 : CollatzResearch.WordTrace tailWord_6038735 prefixEnd_6038735 3100773600128536155240869 := by
  unfold tailWord_6038735
  simp only [CollatzResearch.WordTrace]
  refine ⟨220250759777701903674429659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146833839851801269116286439 220250759777701903674429659)
  ·
    refine ⟨330376139666552855511644489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220250759777701903674429659 330376139666552855511644489)
    ·
      refine ⟨247782104749914641633733367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 330376139666552855511644489 247782104749914641633733367)
      ·
        refine ⟨371673157124871962450600051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 247782104749914641633733367 371673157124871962450600051)
        ·
          refine ⟨557509735687307943675900077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 371673157124871962450600051 557509735687307943675900077)
          ·
            refine ⟨209066150882740478878462529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 557509735687307943675900077 209066150882740478878462529)
            ·
              refine ⟨156799613162055359158846897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 209066150882740478878462529 156799613162055359158846897)
              ·
                refine ⟨117599709871541519369135173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 156799613162055359158846897 117599709871541519369135173)
                ·
                  refine ⟨22049945600914034881712845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 117599709871541519369135173 22049945600914034881712845)
                  ·
                    refine ⟨8268729600342763080642317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22049945600914034881712845 8268729600342763080642317)
                    ·
                      refine ⟨3100773600128536155240869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8268729600342763080642317 3100773600128536155240869)
                      ·
                        rfl

theorem cell23_6038735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 2, 4, 3, 3].length) (baseStart_6038735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6038735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6038735 prefixEnd_6038735 := by exact prefixLift 6038735
  have htrace : WordTrace (prefixWord ++ tailWord_6038735) baseStart_6038735 baseEnd_6038735 := by
    simpa [prefixWord, tailWord_6038735, baseEnd_6038735] using wordTrace_append hprefix tailTrace_6038735
  have hstable : (prefixWord ++ tailWord_6038735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6038735).length < 2 ^ (prefixWord ++ tailWord_6038735).sum := by decide
  have hdescent : baseEnd_6038735 < baseStart_6038735 := by decide
  rcases family_descends (prefixWord ++ tailWord_6038735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6038759 : List Nat := [1, 1, 5, 3, 2, 2, 1, 1, 7]
def baseStart_6038759 : Nat := 118140960795 + 6038759 * 2 ^ 59
def prefixEnd_6038759 : Nat := 4983230072969 + 3 ^ 40 * 6038759 * 2
def baseEnd_6038759 : Nat := 344531769296027117926751

theorem tailTrace_6038759 : CollatzResearch.WordTrace tailWord_6038759 prefixEnd_6038759 344531769296027117926751 := by
  unfold tailWord_6038759
  simp only [CollatzResearch.WordTrace]
  refine ⟨220251635129614955773303331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146834423419743303848868887 220251635129614955773303331)
  ·
    refine ⟨330377452694422433659954997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220251635129614955773303331 330377452694422433659954997)
    ·
      refine ⟨30972886190102103155620781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 330377452694422433659954997 30972886190102103155620781)
      ·
        refine ⟨11614832321288288683357793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30972886190102103155620781 11614832321288288683357793)
        ·
          refine ⟨8711124240966216512518345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11614832321288288683357793 8711124240966216512518345)
          ·
            refine ⟨6533343180724662384388759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8711124240966216512518345 6533343180724662384388759)
            ·
              refine ⟨9800014771086993576583139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6533343180724662384388759 9800014771086993576583139)
              ·
                refine ⟨14700022156630490364874709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9800014771086993576583139 14700022156630490364874709)
                ·
                  refine ⟨344531769296027117926751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14700022156630490364874709 344531769296027117926751)
                  ·
                    rfl

theorem cell23_6038759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 2, 1, 1, 7].length) (baseStart_6038759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6038759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6038759 prefixEnd_6038759 := by exact prefixLift 6038759
  have htrace : WordTrace (prefixWord ++ tailWord_6038759) baseStart_6038759 baseEnd_6038759 := by
    simpa [prefixWord, tailWord_6038759, baseEnd_6038759] using wordTrace_append hprefix tailTrace_6038759
  have hstable : (prefixWord ++ tailWord_6038759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6038759).length < 2 ^ (prefixWord ++ tailWord_6038759).sum := by decide
  have hdescent : baseEnd_6038759 < baseStart_6038759 := by decide
  rcases family_descends (prefixWord ++ tailWord_6038759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6038770 : List Nat := [3, 2, 1, 3, 3, 2, 2, 1, 2, 2, 2]
def baseStart_6038770 : Nat := 118140960795 + 6038770 * 2 ^ 59
def prefixEnd_6038770 : Nat := 4983230072969 + 3 ^ 40 * 6038770 * 2
def baseEnd_6038770 : Nat := 3100791571951443518303209

theorem tailTrace_6038770 : CollatzResearch.WordTrace tailWord_6038770 prefixEnd_6038770 3100791571951443518303209 := by
  unfold tailWord_6038770
  simp only [CollatzResearch.WordTrace]
  refine ⟨55063009083143776162988441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146834690888383403101302509 55063009083143776162988441)
  ·
    refine ⟨41297256812357832122241331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55063009083143776162988441 41297256812357832122241331)
    ·
      refine ⟨61945885218536748183361997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41297256812357832122241331 61945885218536748183361997)
      ·
        refine ⟨23229706956951280568760749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61945885218536748183361997 23229706956951280568760749)
        ·
          refine ⟨8711140108856730213285281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23229706956951280568760749 8711140108856730213285281)
          ·
            refine ⟨6533355081642547659963961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8711140108856730213285281 6533355081642547659963961)
            ·
              refine ⟨4900016311231910744972971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6533355081642547659963961 4900016311231910744972971)
              ·
                refine ⟨7350024466847866117459457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4900016311231910744972971 7350024466847866117459457)
                ·
                  refine ⟨5512518350135899588094593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7350024466847866117459457 5512518350135899588094593)
                  ·
                    refine ⟨4134388762601924691070945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5512518350135899588094593 4134388762601924691070945)
                    ·
                      refine ⟨3100791571951443518303209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4134388762601924691070945 3100791571951443518303209)
                      ·
                        rfl

theorem cell23_6038770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 2, 2, 1, 2, 2, 2].length) (baseStart_6038770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6038770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6038770 prefixEnd_6038770 := by exact prefixLift 6038770
  have htrace : WordTrace (prefixWord ++ tailWord_6038770) baseStart_6038770 baseEnd_6038770 := by
    simpa [prefixWord, tailWord_6038770, baseEnd_6038770] using wordTrace_append hprefix tailTrace_6038770
  have hstable : (prefixWord ++ tailWord_6038770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6038770).length < 2 ^ (prefixWord ++ tailWord_6038770).sum := by decide
  have hdescent : baseEnd_6038770 < baseStart_6038770 := by decide
  rcases family_descends (prefixWord ++ tailWord_6038770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6038805 : List Nat := [1, 3, 2, 1, 2, 1, 1, 3, 2, 1, 6]
def baseStart_6038805 : Nat := 118140960795 + 6038805 * 2 ^ 59
def prefixEnd_6038805 : Nat := 4983230072969 + 3 ^ 40 * 6038805 * 2
def baseEnd_6038805 : Nat := 3100809543774350881365547

theorem tailTrace_6038805 : CollatzResearch.WordTrace tailWord_6038805 prefixEnd_6038805 3100809543774350881365547 := by
  unfold tailWord_6038805
  simp only [CollatzResearch.WordTrace]
  refine ⟨220253312887448305629477869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146835541924965537086318579 220253312887448305629477869)
  ·
    refine ⟨82594992332793114611054201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 220253312887448305629477869 82594992332793114611054201)
    ·
      refine ⟨61946244249594835958290651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82594992332793114611054201 61946244249594835958290651)
      ·
        refine ⟨92919366374392253937435977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61946244249594835958290651 92919366374392253937435977)
        ·
          refine ⟨69689524780794190453076983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92919366374392253937435977 69689524780794190453076983)
          ·
            refine ⟨104534287171191285679615475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69689524780794190453076983 104534287171191285679615475)
            ·
              refine ⟨156801430756786928519423213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104534287171191285679615475 156801430756786928519423213)
              ·
                refine ⟨58800536533795098194783705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 156801430756786928519423213 58800536533795098194783705)
                ·
                  refine ⟨44100402400346323646087779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 58800536533795098194783705 44100402400346323646087779)
                  ·
                    refine ⟨66150603600519485469131669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 44100402400346323646087779 66150603600519485469131669)
                    ·
                      refine ⟨3100809543774350881365547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 66150603600519485469131669 3100809543774350881365547)
                      ·
                        rfl

theorem cell23_6038805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 3, 2, 1, 6].length) (baseStart_6038805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6038805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6038805 prefixEnd_6038805 := by exact prefixLift 6038805
  have htrace : WordTrace (prefixWord ++ tailWord_6038805) baseStart_6038805 baseEnd_6038805 := by
    simpa [prefixWord, tailWord_6038805, baseEnd_6038805] using wordTrace_append hprefix tailTrace_6038805
  have hstable : (prefixWord ++ tailWord_6038805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6038805).length < 2 ^ (prefixWord ++ tailWord_6038805).sum := by decide
  have hdescent : baseEnd_6038805 < baseStart_6038805 := by decide
  rcases family_descends (prefixWord ++ tailWord_6038805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6038826 : List Nat := [3, 1, 4, 2, 1, 2, 1, 1, 2, 4, 2]
def baseStart_6038826 : Nat := 118140960795 + 6038826 * 2 ^ 59
def prefixEnd_6038826 : Nat := 4983230072969 + 3 ^ 40 * 6038826 * 2
def baseEnd_6038826 : Nat := 3100820326868095299202951

theorem tailTrace_6038826 : CollatzResearch.WordTrace tailWord_6038826 prefixEnd_6038826 3100820326868095299202951 := by
  unfold tailWord_6038826
  simp only [CollatzResearch.WordTrace]
  refine ⟨55063519705093056553998083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146836052546914817477328221 55063519705093056553998083)
  ·
    refine ⟨82595279557639584830997125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55063519705093056553998083 82595279557639584830997125)
    ·
      refine ⟨15486614917057422155811961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 82595279557639584830997125 15486614917057422155811961)
      ·
        refine ⟨11614961187793066616858971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15486614917057422155811961 11614961187793066616858971)
        ·
          refine ⟨17422441781689599925288457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11614961187793066616858971 17422441781689599925288457)
          ·
            refine ⟨13066831336267199943966343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17422441781689599925288457 13066831336267199943966343)
            ·
              refine ⟨19600247004400799915949515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13066831336267199943966343 19600247004400799915949515)
              ·
                refine ⟨29400370506601199873924273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19600247004400799915949515 29400370506601199873924273)
                ·
                  refine ⟨22050277879950899905443205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29400370506601199873924273 22050277879950899905443205)
                  ·
                    refine ⟨4134427102490793732270601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22050277879950899905443205 4134427102490793732270601)
                    ·
                      refine ⟨3100820326868095299202951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4134427102490793732270601 3100820326868095299202951)
                      ·
                        rfl

theorem cell23_6038826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 1, 1, 2, 4, 2].length) (baseStart_6038826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6038826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6038826 prefixEnd_6038826 := by exact prefixLift 6038826
  have htrace : WordTrace (prefixWord ++ tailWord_6038826) baseStart_6038826 baseEnd_6038826 := by
    simpa [prefixWord, tailWord_6038826, baseEnd_6038826] using wordTrace_append hprefix tailTrace_6038826
  have hstable : (prefixWord ++ tailWord_6038826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6038826).length < 2 ^ (prefixWord ++ tailWord_6038826).sum := by decide
  have hdescent : baseEnd_6038826 < baseStart_6038826 := by decide
  rcases family_descends (prefixWord ++ tailWord_6038826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6038912 : List Nat := [2, 1, 1, 2, 1, 2, 1, 6, 1, 2, 4]
def baseStart_6038912 : Nat := 118140960795 + 6038912 * 2 ^ 59
def prefixEnd_6038912 : Nat := 4983230072969 + 3 ^ 40 * 6038912 * 2
def baseEnd_6038912 : Nat := 3100864486204381962727555

theorem tailTrace_6038912 : CollatzResearch.WordTrace tailWord_6038912 prefixEnd_6038912 3100864486204381962727555 := by
  unfold tailWord_6038912
  simp only [CollatzResearch.WordTrace]
  refine ⟨110128607749030331451811495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146838143665373775269081993 110128607749030331451811495)
  ·
    refine ⟨165192911623545497177717243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110128607749030331451811495 165192911623545497177717243)
    ·
      refine ⟨247789367435318245766575865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165192911623545497177717243 247789367435318245766575865)
      ·
        refine ⟨185842025576488684324931899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 247789367435318245766575865 185842025576488684324931899)
        ·
          refine ⟨278763038364733026487397849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 185842025576488684324931899 278763038364733026487397849)
          ·
            refine ⟨209072278773549769865548387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 278763038364733026487397849 209072278773549769865548387)
            ·
              refine ⟨313608418160324654798322581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 209072278773549769865548387 313608418160324654798322581)
              ·
                refine ⟨14700394601265218193671371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 313608418160324654798322581 14700394601265218193671371)
                ·
                  refine ⟨22050591901897827290507057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14700394601265218193671371 22050591901897827290507057)
                  ·
                    refine ⟨16537943926423370467880293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22050591901897827290507057 16537943926423370467880293)
                    ·
                      refine ⟨3100864486204381962727555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16537943926423370467880293 3100864486204381962727555)
                      ·
                        rfl

theorem cell23_6038912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 6, 1, 2, 4].length) (baseStart_6038912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6038912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6038912 prefixEnd_6038912 := by exact prefixLift 6038912
  have htrace : WordTrace (prefixWord ++ tailWord_6038912) baseStart_6038912 baseEnd_6038912 := by
    simpa [prefixWord, tailWord_6038912, baseEnd_6038912] using wordTrace_append hprefix tailTrace_6038912
  have hstable : (prefixWord ++ tailWord_6038912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6038912).length < 2 ^ (prefixWord ++ tailWord_6038912).sum := by decide
  have hdescent : baseEnd_6038912 < baseStart_6038912 := by decide
  rcases family_descends (prefixWord ++ tailWord_6038912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6038919 : List Nat := [1, 1, 4, 2, 2, 3, 2, 1, 1, 1, 5]
def baseStart_6038919 : Nat := 118140960795 + 6038919 * 2 ^ 59
def prefixEnd_6038919 : Nat := 4983230072969 + 3 ^ 40 * 6038919 * 2
def baseEnd_6038919 : Nat := 3100868080568963435340023

theorem tailTrace_6038919 : CollatzResearch.WordTrace tailWord_6038919 prefixEnd_6038919 3100868080568963435340023 := by
  unfold tailWord_6038919
  simp only [CollatzResearch.WordTrace]
  refine ⟨220257470809035303099127811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146838313872690202066085207 220257470809035303099127811)
  ·
    refine ⟨330386206213552954648691717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220257470809035303099127811 330386206213552954648691717)
    ·
      refine ⟨61947413665041178996629697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 330386206213552954648691717 61947413665041178996629697)
      ·
        refine ⟨46460560248780884247472273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61947413665041178996629697 46460560248780884247472273)
        ·
          refine ⟨34845420186585663185604205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46460560248780884247472273 34845420186585663185604205)
          ·
            refine ⟨13067032569969623694601577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34845420186585663185604205 13067032569969623694601577)
            ·
              refine ⟨9800274427477217770951183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13067032569969623694601577 9800274427477217770951183)
              ·
                refine ⟨14700411641215826656426775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9800274427477217770951183 14700411641215826656426775)
                ·
                  refine ⟨22050617461823739984640163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14700411641215826656426775 22050617461823739984640163)
                  ·
                    refine ⟨33075926192735609976960245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22050617461823739984640163 33075926192735609976960245)
                    ·
                      refine ⟨3100868080568963435340023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33075926192735609976960245 3100868080568963435340023)
                      ·
                        rfl

theorem cell23_6038919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 2, 1, 1, 1, 5].length) (baseStart_6038919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6038919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6038919 prefixEnd_6038919 := by exact prefixLift 6038919
  have htrace : WordTrace (prefixWord ++ tailWord_6038919) baseStart_6038919 baseEnd_6038919 := by
    simpa [prefixWord, tailWord_6038919, baseEnd_6038919] using wordTrace_append hprefix tailTrace_6038919
  have hstable : (prefixWord ++ tailWord_6038919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6038919).length < 2 ^ (prefixWord ++ tailWord_6038919).sum := by decide
  have hdescent : baseEnd_6038919 < baseStart_6038919 := by decide
  rcases family_descends (prefixWord ++ tailWord_6038919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
