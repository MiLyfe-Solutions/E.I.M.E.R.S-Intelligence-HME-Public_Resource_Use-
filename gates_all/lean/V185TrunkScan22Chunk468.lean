import V185TrunkScan22Chunk467

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_4171345 : List Nat := [1, 2, 2, 1, 3, 2, 2, 4, 2, 3]
def baseStart_4171345 : Nat := 118140960795 + 4171345 * 2 ^ 59
def prefixEnd_4171345 : Nat := 4983230072969 + 3 ^ 40 * 4171345 * 2
def baseEnd_4171345 : Nat := 1427936640486058218135893

theorem tailTrace_4171345 : CollatzResearch.WordTrace tailWord_4171345 prefixEnd_4171345 1427936640486058218135893 := by
  unfold tailWord_4171345
  simp only [CollatzResearch.WordTrace]
  refine ⟨152141451072936948853331489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101427634048624632568887659 152141451072936948853331489)
  ·
    refine ⟨114106088304702711639998617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152141451072936948853331489 114106088304702711639998617)
    ·
      refine ⟨85579566228527033729998963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114106088304702711639998617 85579566228527033729998963)
      ·
        refine ⟨128369349342790550594998445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85579566228527033729998963 128369349342790550594998445)
        ·
          refine ⟨48138506003546456473124417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 128369349342790550594998445 48138506003546456473124417)
          ·
            refine ⟨36103879502659842354843313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48138506003546456473124417 36103879502659842354843313)
            ·
              refine ⟨27077909626994881766132485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36103879502659842354843313 27077909626994881766132485)
              ·
                refine ⟨5077108055061540331149841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27077909626994881766132485 5077108055061540331149841)
                ·
                  refine ⟨3807831041296155248362381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5077108055061540331149841 3807831041296155248362381)
                  ·
                    refine ⟨1427936640486058218135893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3807831041296155248362381 1427936640486058218135893)
                    ·
                      rfl

theorem cell22_4171345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 4, 2, 3].length) (baseStart_4171345 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4171345 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4171345 prefixEnd_4171345 := by exact prefixLift 4171345
  have htrace : WordTrace (prefixWord ++ tailWord_4171345) baseStart_4171345 baseEnd_4171345 := by
    simpa [prefixWord, tailWord_4171345, baseEnd_4171345] using wordTrace_append hprefix tailTrace_4171345
  have hstable : (prefixWord ++ tailWord_4171345).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4171345).length < 2 ^ (prefixWord ++ tailWord_4171345).sum := by decide
  have hdescent : baseEnd_4171345 < baseStart_4171345 := by decide
  rcases family_descends (prefixWord ++ tailWord_4171345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4171433 : List Nat := [1, 2, 1, 1, 1, 1, 2, 2, 7, 4]
def baseStart_4171433 : Nat := 118140960795 + 4171433 * 2 ^ 59
def prefixEnd_4171433 : Nat := 4983230072969 + 3 ^ 40 * 4171433 * 2
def baseEnd_4171433 : Nat := 1427966764684455321935623

theorem tailTrace_4171433 : CollatzResearch.WordTrace tailWord_4171433 prefixEnd_4171433 1427966764684455321935623 := by
  unfold tailWord_4171433
  simp only [CollatzResearch.WordTrace]
  refine ⟨152144660696618139882534953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101429773797745426588356635 152144660696618139882534953)
  ·
    refine ⟨114108495522463604911901215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152144660696618139882534953 114108495522463604911901215)
    ·
      refine ⟨171162743283695407367851823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114108495522463604911901215 171162743283695407367851823)
      ·
        refine ⟨256744114925543111051777735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171162743283695407367851823 256744114925543111051777735)
        ·
          refine ⟨385116172388314666577666603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 256744114925543111051777735 385116172388314666577666603)
          ·
            refine ⟨577674258582471999866499905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 385116172388314666577666603 577674258582471999866499905)
            ·
              refine ⟨433255693936853999899874929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 577674258582471999866499905 433255693936853999899874929)
              ·
                refine ⟨324941770452640499924906197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 433255693936853999899874929 324941770452640499924906197)
                ·
                  refine ⟨7615822744983761716989989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 324941770452640499924906197 7615822744983761716989989)
                  ·
                    refine ⟨1427966764684455321935623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7615822744983761716989989 1427966764684455321935623)
                    ·
                      rfl

theorem cell22_4171433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 2, 7, 4].length) (baseStart_4171433 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4171433 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4171433 prefixEnd_4171433 := by exact prefixLift 4171433
  have htrace : WordTrace (prefixWord ++ tailWord_4171433) baseStart_4171433 baseEnd_4171433 := by
    simpa [prefixWord, tailWord_4171433, baseEnd_4171433] using wordTrace_append hprefix tailTrace_4171433
  have hstable : (prefixWord ++ tailWord_4171433).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4171433).length < 2 ^ (prefixWord ++ tailWord_4171433).sum := by decide
  have hdescent : baseEnd_4171433 < baseStart_4171433 := by decide
  rcases family_descends (prefixWord ++ tailWord_4171433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4171458 : List Nat := [3, 5, 1, 2, 1, 1, 2, 1, 3, 3]
def baseStart_4171458 : Nat := 118140960795 + 4171458 * 2 ^ 59
def prefixEnd_4171458 : Nat := 4983230072969 + 3 ^ 40 * 4171458 * 2
def baseEnd_4171458 : Nat := 1427975322695363590060547

theorem tailTrace_4171458 : CollatzResearch.WordTrace tailWord_4171458 prefixEnd_4171458 1427975322695363590060547 := by
  unfold tailWord_4171458
  simp only [CollatzResearch.WordTrace]
  refine ⟨38036393130381892288048757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101430381681018379434796685 38036393130381892288048757)
  ·
    refine ⟨3565911855973302402004571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 38036393130381892288048757 3565911855973302402004571)
    ·
      refine ⟨5348867783959953603006857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3565911855973302402004571 5348867783959953603006857)
      ·
        refine ⟨4011650837969965202255143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5348867783959953603006857 4011650837969965202255143)
        ·
          refine ⟨6017476256954947803382715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4011650837969965202255143 6017476256954947803382715)
          ·
            refine ⟨9026214385432421705074073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6017476256954947803382715 9026214385432421705074073)
            ·
              refine ⟨6769660789074316278805555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9026214385432421705074073 6769660789074316278805555)
              ·
                refine ⟨10154491183611474418208333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6769660789074316278805555 10154491183611474418208333)
                ·
                  refine ⟨3807934193854302906828125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10154491183611474418208333 3807934193854302906828125)
                  ·
                    refine ⟨1427975322695363590060547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3807934193854302906828125 1427975322695363590060547)
                    ·
                      rfl

theorem cell22_4171458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 2, 1, 3, 3].length) (baseStart_4171458 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4171458 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4171458 prefixEnd_4171458 := by exact prefixLift 4171458
  have htrace : WordTrace (prefixWord ++ tailWord_4171458) baseStart_4171458 baseEnd_4171458 := by
    simpa [prefixWord, tailWord_4171458, baseEnd_4171458] using wordTrace_append hprefix tailTrace_4171458
  have hstable : (prefixWord ++ tailWord_4171458).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4171458).length < 2 ^ (prefixWord ++ tailWord_4171458).sum := by decide
  have hdescent : baseEnd_4171458 < baseStart_4171458 := by decide
  rcases family_descends (prefixWord ++ tailWord_4171458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4171510 : List Nat := [5, 1, 1, 1, 1, 3, 10]
def baseStart_4171510 : Nat := 118140960795 + 4171510 * 2 ^ 59
def prefixEnd_4171510 : Nat := 4983230072969 + 3 ^ 40 * 4171510 * 2
def baseEnd_4171510 : Nat := 52888634198446399546681

theorem tailTrace_4171510 : CollatzResearch.WordTrace tailWord_4171510 prefixEnd_4171510 52888634198446399546681 := by
  unfold tailWord_4171510
  simp only [CollatzResearch.WordTrace]
  refine ⟨9509216819833698877067999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 101431646078226121355391989 9509216819833698877067999)
  ·
    refine ⟨14263825229750548315601999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9509216819833698877067999 14263825229750548315601999)
    ·
      refine ⟨21395737844625822473402999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14263825229750548315601999 21395737844625822473402999)
      ·
        refine ⟨32093606766938733710104499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21395737844625822473402999 32093606766938733710104499)
        ·
          refine ⟨48140410150408100565156749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32093606766938733710104499 48140410150408100565156749)
          ·
            refine ⟨18052653806403037711933781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48140410150408100565156749 18052653806403037711933781)
            ·
              refine ⟨52888634198446399546681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 18052653806403037711933781 52888634198446399546681)
              ·
                rfl

theorem cell22_4171510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 10].length) (baseStart_4171510 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4171510 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4171510 prefixEnd_4171510 := by exact prefixLift 4171510
  have htrace : WordTrace (prefixWord ++ tailWord_4171510) baseStart_4171510 baseEnd_4171510 := by
    simpa [prefixWord, tailWord_4171510, baseEnd_4171510] using wordTrace_append hprefix tailTrace_4171510
  have hstable : (prefixWord ++ tailWord_4171510).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4171510).length < 2 ^ (prefixWord ++ tailWord_4171510).sum := by decide
  have hdescent : baseEnd_4171510 < baseStart_4171510 := by decide
  rcases family_descends (prefixWord ++ tailWord_4171510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4171527 : List Nat := [1, 1, 4, 4, 2, 1, 2, 7]
def baseStart_4171527 : Nat := 118140960795 + 4171527 * 2 ^ 59
def prefixEnd_4171527 : Nat := 4983230072969 + 3 ^ 40 * 4171527 * 2
def baseEnd_4171527 : Nat := 158666549200607823342815

theorem tailTrace_4171527 : CollatzResearch.WordTrace tailWord_4171527 prefixEnd_4171527 158666549200607823342815 := by
  unfold tailWord_4171527
  simp only [CollatzResearch.WordTrace]
  refine ⟨152148089158277593936456835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101432059438851729290971223 152148089158277593936456835)
  ·
    refine ⟨228222133737416390904685253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152148089158277593936456835 228222133737416390904685253)
    ·
      refine ⟨42791650075765573294628485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 228222133737416390904685253 42791650075765573294628485)
      ·
        refine ⟨8023434389206044992742841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42791650075765573294628485 8023434389206044992742841)
        ·
          refine ⟨6017575791904533744557131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8023434389206044992742841 6017575791904533744557131)
          ·
            refine ⟨9026363687856800616835697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6017575791904533744557131 9026363687856800616835697)
            ·
              refine ⟨6769772765892600462626773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9026363687856800616835697 6769772765892600462626773)
              ·
                refine ⟨158666549200607823342815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6769772765892600462626773 158666549200607823342815)
                ·
                  rfl

theorem cell22_4171527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 2, 7].length) (baseStart_4171527 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4171527 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4171527 prefixEnd_4171527 := by exact prefixLift 4171527
  have htrace : WordTrace (prefixWord ++ tailWord_4171527) baseStart_4171527 baseEnd_4171527 := by
    simpa [prefixWord, tailWord_4171527, baseEnd_4171527] using wordTrace_append hprefix tailTrace_4171527
  have hstable : (prefixWord ++ tailWord_4171527).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4171527).length < 2 ^ (prefixWord ++ tailWord_4171527).sum := by decide
  have hdescent : baseEnd_4171527 < baseStart_4171527 := by decide
  rcases family_descends (prefixWord ++ tailWord_4171527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4171576 : List Nat := [2, 1, 2, 1, 3, 3, 4, 2, 1, 3]
def baseStart_4171576 : Nat := 118140960795 + 4171576 * 2 ^ 59
def prefixEnd_4171576 : Nat := 4983230072969 + 3 ^ 40 * 4171576 * 2
def baseEnd_4171576 : Nat := 1428015716506850615610185

theorem tailTrace_4171576 : CollatzResearch.WordTrace tailWord_4171576 prefixEnd_4171576 1428015716506850615610185 := by
  unfold tailWord_4171576
  simp only [CollatzResearch.WordTrace]
  refine ⟨76074938167550037652495291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101433250890066716869993721 76074938167550037652495291)
  ·
    refine ⟨114112407251325056478742937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76074938167550037652495291 114112407251325056478742937)
    ·
      refine ⟨85584305438493792359057203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114112407251325056478742937 85584305438493792359057203)
      ·
        refine ⟨128376458157740688538585805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85584305438493792359057203 128376458157740688538585805)
        ·
          refine ⟨48141171809152758201969677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 128376458157740688538585805 48141171809152758201969677)
          ·
            refine ⟨18052939428432284325738629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48141171809152758201969677 18052939428432284325738629)
            ·
              refine ⟨3384926142831053311075993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18052939428432284325738629 3384926142831053311075993)
              ·
                refine ⟨2538694607123289983306995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3384926142831053311075993 2538694607123289983306995)
                ·
                  refine ⟨3808041910684934974960493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2538694607123289983306995 3808041910684934974960493)
                  ·
                    refine ⟨1428015716506850615610185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3808041910684934974960493 1428015716506850615610185)
                    ·
                      rfl

theorem cell22_4171576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 4, 2, 1, 3].length) (baseStart_4171576 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4171576 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4171576 prefixEnd_4171576 := by exact prefixLift 4171576
  have htrace : WordTrace (prefixWord ++ tailWord_4171576) baseStart_4171576 baseEnd_4171576 := by
    simpa [prefixWord, tailWord_4171576, baseEnd_4171576] using wordTrace_append hprefix tailTrace_4171576
  have hstable : (prefixWord ++ tailWord_4171576).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4171576).length < 2 ^ (prefixWord ++ tailWord_4171576).sum := by decide
  have hdescent : baseEnd_4171576 < baseStart_4171576 := by decide
  rcases family_descends (prefixWord ++ tailWord_4171576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4171602 : List Nat := [3, 2, 2, 1, 1, 3, 2, 1, 3, 4]
def baseStart_4171602 : Nat := 118140960795 + 4171602 * 2 ^ 59
def prefixEnd_4171602 : Nat := 4983230072969 + 3 ^ 40 * 4171602 * 2
def baseEnd_4171602 : Nat := 1428024616838195214460105

theorem tailTrace_4171602 : CollatzResearch.WordTrace tailWord_4171602 prefixEnd_4171602 1428024616838195214460105 := by
  unfold tailWord_4171602
  simp only [CollatzResearch.WordTrace]
  refine ⟨38037706158251470436359265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101433883088670587830291373 38037706158251470436359265)
  ·
    refine ⟨28528279618688602827269449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38037706158251470436359265 28528279618688602827269449)
    ·
      refine ⟨21396209714016452120452087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28528279618688602827269449 21396209714016452120452087)
      ·
        refine ⟨32094314571024678180678131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21396209714016452120452087 32094314571024678180678131)
        ·
          refine ⟨48141471856537017271017197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32094314571024678180678131 48141471856537017271017197)
          ·
            refine ⟨18053051946201381476631449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48141471856537017271017197 18053051946201381476631449)
            ·
              refine ⟨13539788959651036107473587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18053051946201381476631449 13539788959651036107473587)
              ·
                refine ⟨20309683439476554161210381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13539788959651036107473587 20309683439476554161210381)
                ·
                  refine ⟨7616131289803707810453893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20309683439476554161210381 7616131289803707810453893)
                  ·
                    refine ⟨1428024616838195214460105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7616131289803707810453893 1428024616838195214460105)
                    ·
                      rfl

theorem cell22_4171602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 2, 1, 3, 4].length) (baseStart_4171602 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4171602 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4171602 prefixEnd_4171602 := by exact prefixLift 4171602
  have htrace : WordTrace (prefixWord ++ tailWord_4171602) baseStart_4171602 baseEnd_4171602 := by
    simpa [prefixWord, tailWord_4171602, baseEnd_4171602] using wordTrace_append hprefix tailTrace_4171602
  have hstable : (prefixWord ++ tailWord_4171602).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4171602).length < 2 ^ (prefixWord ++ tailWord_4171602).sum := by decide
  have hdescent : baseEnd_4171602 < baseStart_4171602 := by decide
  rcases family_descends (prefixWord ++ tailWord_4171602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4171619 : List Nat := [1, 1, 1, 5, 4, 1, 1, 3, 1, 4]
def baseStart_4171619 : Nat := 118140960795 + 4171619 * 2 ^ 59
def prefixEnd_4171619 : Nat := 4983230072969 + 3 ^ 40 * 4171619 * 2
def baseEnd_4171619 : Nat := 1428030436285612836785053

theorem tailTrace_4171619 : CollatzResearch.WordTrace tailWord_4171619 prefixEnd_4171619 1428030436285612836785053 := by
  unfold tailWord_4171619
  simp only [CollatzResearch.WordTrace]
  refine ⟨152151444673944293648805911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101434296449296195765870607 152151444673944293648805911)
  ·
    refine ⟨228227167010916440473208867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152151444673944293648805911 228227167010916440473208867)
    ·
      refine ⟨342340750516374660709813301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228227167010916440473208867 342340750516374660709813301)
      ·
        refine ⟨32094445360910124441544997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 342340750516374660709813301 32094445360910124441544997)
        ·
          refine ⟨6017708505170648332789687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32094445360910124441544997 6017708505170648332789687)
          ·
            refine ⟨9026562757755972499184531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6017708505170648332789687 9026562757755972499184531)
            ·
              refine ⟨13539844136633958748776797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9026562757755972499184531 13539844136633958748776797)
              ·
                refine ⟨5077441551237734530791299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13539844136633958748776797 5077441551237734530791299)
                ·
                  refine ⟨7616162326856601796186949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5077441551237734530791299 7616162326856601796186949)
                  ·
                    refine ⟨1428030436285612836785053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7616162326856601796186949 1428030436285612836785053)
                    ·
                      rfl

theorem cell22_4171619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 1, 3, 1, 4].length) (baseStart_4171619 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4171619 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4171619 prefixEnd_4171619 := by exact prefixLift 4171619
  have htrace : WordTrace (prefixWord ++ tailWord_4171619) baseStart_4171619 baseEnd_4171619 := by
    simpa [prefixWord, tailWord_4171619, baseEnd_4171619] using wordTrace_append hprefix tailTrace_4171619
  have hstable : (prefixWord ++ tailWord_4171619).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4171619).length < 2 ^ (prefixWord ++ tailWord_4171619).sum := by decide
  have hdescent : baseEnd_4171619 < baseStart_4171619 := by decide
  rcases family_descends (prefixWord ++ tailWord_4171619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4171645 : List Nat := [1, 4, 1, 1, 2, 1, 1, 11]
def baseStart_4171645 : Nat := 118140960795 + 4171645 * 2 ^ 59
def prefixEnd_4171645 : Nat := 4983230072969 + 3 ^ 40 * 4171645 * 2
def baseEnd_4171645 : Nat := 158671037401884159514997

theorem tailTrace_4171645 : CollatzResearch.WordTrace tailWord_4171645 prefixEnd_4171645 158671037401884159514997 := by
  unfold tailWord_4171645
  simp only [CollatzResearch.WordTrace]
  refine ⟨152152392971850100089252389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101434928647900066726168259 152152392971850100089252389)
  ·
    refine ⟨28528573682221893766734823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 152152392971850100089252389 28528573682221893766734823)
    ·
      refine ⟨42792860523332840650102235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28528573682221893766734823 42792860523332840650102235)
      ·
        refine ⟨64189290784999260975153353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42792860523332840650102235 64189290784999260975153353)
        ·
          refine ⟨48141968088749445731365015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64189290784999260975153353 48141968088749445731365015)
          ·
            refine ⟨72212952133124168597047523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48141968088749445731365015 72212952133124168597047523)
            ·
              refine ⟨108319428199686252895571285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72212952133124168597047523 108319428199686252895571285)
              ·
                refine ⟨158671037401884159514997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 108319428199686252895571285 158671037401884159514997)
                ·
                  rfl

theorem cell22_4171645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 11].length) (baseStart_4171645 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4171645 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4171645 prefixEnd_4171645 := by exact prefixLift 4171645
  have htrace : WordTrace (prefixWord ++ tailWord_4171645) baseStart_4171645 baseEnd_4171645 := by
    simpa [prefixWord, tailWord_4171645, baseEnd_4171645] using wordTrace_append hprefix tailTrace_4171645
  have hstable : (prefixWord ++ tailWord_4171645).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4171645).length < 2 ^ (prefixWord ++ tailWord_4171645).sum := by decide
  have hdescent : baseEnd_4171645 < baseStart_4171645 := by decide
  rcases family_descends (prefixWord ++ tailWord_4171645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4171660 : List Nat := [2, 2, 1, 2, 1, 2, 1, 1, 1, 9]
def baseStart_4171660 : Nat := 118140960795 + 4171660 * 2 ^ 59
def prefixEnd_4171660 : Nat := 4983230072969 + 3 ^ 40 * 4171660 * 2
def baseEnd_4171660 : Nat := 1428044471423502396509927

theorem tailTrace_4171660 : CollatzResearch.WordTrace tailWord_4171660 prefixEnd_4171660 1428044471423502396509927 := by
  unfold tailWord_4171660
  simp only [CollatzResearch.WordTrace]
  refine ⟨76076470033397878825524217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101435293377863838434032289 76076470033397878825524217)
  ·
    refine ⟨57057352525048409119143163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76076470033397878825524217 57057352525048409119143163)
    ·
      refine ⟨85586028787572613678714745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57057352525048409119143163 85586028787572613678714745)
      ·
        refine ⟨64189521590679460259036059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85586028787572613678714745 64189521590679460259036059)
        ·
          refine ⟨96284282386019190388554089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64189521590679460259036059 96284282386019190388554089)
          ·
            refine ⟨72213211789514392791415567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96284282386019190388554089 72213211789514392791415567)
            ·
              refine ⟨108319817684271589187123351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72213211789514392791415567 108319817684271589187123351)
              ·
                refine ⟨162479726526407383780685027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108319817684271589187123351 162479726526407383780685027)
                ·
                  refine ⟨243719589789611075671027541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 162479726526407383780685027 243719589789611075671027541)
                  ·
                    refine ⟨1428044471423502396509927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 243719589789611075671027541 1428044471423502396509927)
                    ·
                      rfl

theorem cell22_4171660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 1, 1, 9].length) (baseStart_4171660 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4171660 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4171660 prefixEnd_4171660 := by exact prefixLift 4171660
  have htrace : WordTrace (prefixWord ++ tailWord_4171660) baseStart_4171660 baseEnd_4171660 := by
    simpa [prefixWord, tailWord_4171660, baseEnd_4171660] using wordTrace_append hprefix tailTrace_4171660
  have hstable : (prefixWord ++ tailWord_4171660).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4171660).length < 2 ^ (prefixWord ++ tailWord_4171660).sum := by decide
  have hdescent : baseEnd_4171660 < baseStart_4171660 := by decide
  rcases family_descends (prefixWord ++ tailWord_4171660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4171679 : List Nat := [1, 1, 2, 5, 4, 1, 8]
def baseStart_4171679 : Nat := 118140960795 + 4171679 * 2 ^ 59
def prefixEnd_4171679 : Nat := 4983230072969 + 3 ^ 40 * 4171679 * 2
def baseEnd_4171679 : Nat := 52890776870807136306847

theorem tailTrace_4171679 : CollatzResearch.WordTrace tailWord_4171679 prefixEnd_4171679 52890776870807136306847 := by
  unfold tailWord_4171679
  simp only [CollatzResearch.WordTrace]
  refine ⟨152153633053726923895990091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101435755369151282597326727 152153633053726923895990091)
  ·
    refine ⟨228230449580590385843985137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152153633053726923895990091 228230449580590385843985137)
    ·
      refine ⟨171172837185442789382988853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 228230449580590385843985137 171172837185442789382988853)
      ·
        refine ⟨16047453486135261504655205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 171172837185442789382988853 16047453486135261504655205)
        ·
          refine ⟨3008897528650361532122851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16047453486135261504655205 3008897528650361532122851)
          ·
            refine ⟨4513346292975542298184277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3008897528650361532122851 4513346292975542298184277)
            ·
              refine ⟨52890776870807136306847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4513346292975542298184277 52890776870807136306847)
              ·
                rfl

theorem cell22_4171679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 4, 1, 8].length) (baseStart_4171679 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4171679 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4171679 prefixEnd_4171679 := by exact prefixLift 4171679
  have htrace : WordTrace (prefixWord ++ tailWord_4171679) baseStart_4171679 baseEnd_4171679 := by
    simpa [prefixWord, tailWord_4171679, baseEnd_4171679] using wordTrace_append hprefix tailTrace_4171679
  have hstable : (prefixWord ++ tailWord_4171679).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4171679).length < 2 ^ (prefixWord ++ tailWord_4171679).sum := by decide
  have hdescent : baseEnd_4171679 < baseStart_4171679 := by decide
  rcases family_descends (prefixWord ++ tailWord_4171679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4171741 : List Nat := [1, 4, 3, 1, 3, 1, 2, 2, 5]
def baseStart_4171741 : Nat := 118140960795 + 4171741 * 2 ^ 59
def prefixEnd_4171741 : Nat := 4983230072969 + 3 ^ 40 * 4171741 * 2
def baseEnd_4171741 : Nat := 476024066459615061744893

theorem tailTrace_4171741 : CollatzResearch.WordTrace tailWord_4171741 prefixEnd_4171741 476024066459615061744893 := by
  unfold tailWord_4171741
  simp only [CollatzResearch.WordTrace]
  refine ⟨152155894379502308484747077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101437262919668205656498051 152155894379502308484747077)
  ·
    refine ⟨28529230196156682840890077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 152155894379502308484747077 28529230196156682840890077)
    ·
      refine ⟨10698461323558756065333779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28529230196156682840890077 10698461323558756065333779)
      ·
        refine ⟨16047691985338134098000669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10698461323558756065333779 16047691985338134098000669)
        ·
          refine ⟨6017884494501800286750251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16047691985338134098000669 6017884494501800286750251)
          ·
            refine ⟨9026826741752700430125377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6017884494501800286750251 9026826741752700430125377)
            ·
              refine ⟨6770120056314525322594033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9026826741752700430125377 6770120056314525322594033)
              ·
                refine ⟨5077590042235893991945525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6770120056314525322594033 5077590042235893991945525)
                ·
                  refine ⟨476024066459615061744893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5077590042235893991945525 476024066459615061744893)
                  ·
                    rfl

theorem cell22_4171741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 2, 2, 5].length) (baseStart_4171741 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4171741 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4171741 prefixEnd_4171741 := by exact prefixLift 4171741
  have htrace : WordTrace (prefixWord ++ tailWord_4171741) baseStart_4171741 baseEnd_4171741 := by
    simpa [prefixWord, tailWord_4171741, baseEnd_4171741] using wordTrace_append hprefix tailTrace_4171741
  have hstable : (prefixWord ++ tailWord_4171741).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4171741).length < 2 ^ (prefixWord ++ tailWord_4171741).sum := by decide
  have hdescent : baseEnd_4171741 < baseStart_4171741 := by decide
  rcases family_descends (prefixWord ++ tailWord_4171741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4171752 : List Nat := [2, 1, 4, 1, 1, 1, 1, 5, 6]
def baseStart_4171752 : Nat := 118140960795 + 4171752 * 2 ^ 59
def prefixEnd_4171752 : Nat := 4983230072969 + 3 ^ 40 * 4171752 * 2
def baseEnd_4171752 : Nat := 476025321634548274403215

theorem tailTrace_4171752 : CollatzResearch.WordTrace tailWord_4171752 prefixEnd_4171752 476025321634548274403215 := by
  unfold tailWord_4171752
  simp only [CollatzResearch.WordTrace]
  refine ⟨76078147791231228681698755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101437530388308304908931673 76078147791231228681698755)
  ·
    refine ⟨114117221686846843022548133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76078147791231228681698755 114117221686846843022548133)
    ·
      refine ⟨21396979066283783066727775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 114117221686846843022548133 21396979066283783066727775)
      ·
        refine ⟨32095468599425674600091663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21396979066283783066727775 32095468599425674600091663)
        ·
          refine ⟨48143202899138511900137495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32095468599425674600091663 48143202899138511900137495)
          ·
            refine ⟨72214804348707767850206243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48143202899138511900137495 72214804348707767850206243)
            ·
              refine ⟨108322206523061651775309365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72214804348707767850206243 108322206523061651775309365)
              ·
                refine ⟨10155206861537029853935253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 108322206523061651775309365 10155206861537029853935253)
                ·
                  refine ⟨476025321634548274403215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10155206861537029853935253 476025321634548274403215)
                  ·
                    rfl

theorem cell22_4171752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 5, 6].length) (baseStart_4171752 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4171752 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4171752 prefixEnd_4171752 := by exact prefixLift 4171752
  have htrace : WordTrace (prefixWord ++ tailWord_4171752) baseStart_4171752 baseEnd_4171752 := by
    simpa [prefixWord, tailWord_4171752, baseEnd_4171752] using wordTrace_append hprefix tailTrace_4171752
  have hstable : (prefixWord ++ tailWord_4171752).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4171752).length < 2 ^ (prefixWord ++ tailWord_4171752).sum := by decide
  have hdescent : baseEnd_4171752 < baseStart_4171752 := by decide
  rcases family_descends (prefixWord ++ tailWord_4171752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4171784 : List Nat := [2, 1, 3, 2, 1, 2, 2, 2, 4, 3]
def baseStart_4171784 : Nat := 118140960795 + 4171784 * 2 ^ 59
def prefixEnd_4171784 : Nat := 4983230072969 + 3 ^ 40 * 4171784 * 2
def baseEnd_4171784 : Nat := 1428086919157607406409547

theorem tailTrace_4171784 : CollatzResearch.WordTrace tailWord_4171784 prefixEnd_4171784 1428086919157607406409547 := by
  unfold tailWord_4171784
  simp only [CollatzResearch.WordTrace]
  refine ⟨76078731359173263414281203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101438308478897684552374937 76078731359173263414281203)
  ·
    refine ⟨114118097038759895121421805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76078731359173263414281203 114118097038759895121421805)
    ·
      refine ⟨42794286389534960670533177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114118097038759895121421805 42794286389534960670533177)
      ·
        refine ⟨32095714792151220502899883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42794286389534960670533177 32095714792151220502899883)
        ·
          refine ⟨48143572188226830754349825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32095714792151220502899883 48143572188226830754349825)
          ·
            refine ⟨36107679141170123065762369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48143572188226830754349825 36107679141170123065762369)
            ·
              refine ⟨27080759355877592299321777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36107679141170123065762369 27080759355877592299321777)
              ·
                refine ⟨20310569516908194224491333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27080759355877592299321777 20310569516908194224491333)
                ·
                  refine ⟨3808231784420286417092125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20310569516908194224491333 3808231784420286417092125)
                  ·
                    refine ⟨1428086919157607406409547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3808231784420286417092125 1428086919157607406409547)
                    ·
                      rfl

theorem cell22_4171784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 2, 4, 3].length) (baseStart_4171784 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4171784 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4171784 prefixEnd_4171784 := by exact prefixLift 4171784
  have htrace : WordTrace (prefixWord ++ tailWord_4171784) baseStart_4171784 baseEnd_4171784 := by
    simpa [prefixWord, tailWord_4171784, baseEnd_4171784] using wordTrace_append hprefix tailTrace_4171784
  have hstable : (prefixWord ++ tailWord_4171784).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4171784).length < 2 ^ (prefixWord ++ tailWord_4171784).sum := by decide
  have hdescent : baseEnd_4171784 < baseStart_4171784 := by decide
  rcases family_descends (prefixWord ++ tailWord_4171784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4171827 : List Nat := [1, 1, 1, 2, 4, 1, 2, 2, 2, 6]
def baseStart_4171827 : Nat := 118140960795 + 4171827 * 2 ^ 59
def prefixEnd_4171827 : Nat := 4983230072969 + 3 ^ 40 * 4171827 * 2
def baseEnd_4171827 : Nat := 1428101638936369627584415

theorem tailTrace_4171827 : CollatzResearch.WordTrace tailWord_4171827 prefixEnd_4171827 1428101638936369627584415 := by
  unfold tailWord_4171827
  simp only [CollatzResearch.WordTrace]
  refine ⟨152159031057190745172377735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101439354038127163448251823 152159031057190745172377735)
  ·
    refine ⟨228238546585786117758566603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152159031057190745172377735 228238546585786117758566603)
    ·
      refine ⟨342357819878679176637849905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228238546585786117758566603 342357819878679176637849905)
      ·
        refine ⟨256768364909009382478387429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 342357819878679176637849905 256768364909009382478387429)
        ·
          refine ⟨48144068420439259214697643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 256768364909009382478387429 48144068420439259214697643)
          ·
            refine ⟨72216102630658888822046465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48144068420439259214697643 72216102630658888822046465)
            ·
              refine ⟨54162076972994166616534849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72216102630658888822046465 54162076972994166616534849)
              ·
                refine ⟨40621557729745624962401137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54162076972994166616534849 40621557729745624962401137)
                ·
                  refine ⟨30466168297309218721800853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40621557729745624962401137 30466168297309218721800853)
                  ·
                    refine ⟨1428101638936369627584415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30466168297309218721800853 1428101638936369627584415)
                    ·
                      rfl

theorem cell22_4171827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 2, 2, 6].length) (baseStart_4171827 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4171827 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4171827 prefixEnd_4171827 := by exact prefixLift 4171827
  have htrace : WordTrace (prefixWord ++ tailWord_4171827) baseStart_4171827 baseEnd_4171827 := by
    simpa [prefixWord, tailWord_4171827, baseEnd_4171827] using wordTrace_append hprefix tailTrace_4171827
  have hstable : (prefixWord ++ tailWord_4171827).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4171827).length < 2 ^ (prefixWord ++ tailWord_4171827).sum := by decide
  have hdescent : baseEnd_4171827 < baseStart_4171827 := by decide
  rcases family_descends (prefixWord ++ tailWord_4171827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4171876 : List Nat := [2, 3, 1, 1, 2, 1, 6, 1, 5]
def baseStart_4171876 : Nat := 118140960795 + 4171876 * 2 ^ 59
def prefixEnd_4171876 : Nat := 4983230072969 + 3 ^ 40 * 4171876 * 2
def baseEnd_4171876 : Nat := 476039470879249944369755

theorem tailTrace_4171876 : CollatzResearch.WordTrace tailWord_4171876 prefixEnd_4171876 476039470879249944369755 := by
  unfold tailWord_4171876
  simp only [CollatzResearch.WordTrace]
  refine ⟨76080409117006613270455741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101440545489342151027274321 76080409117006613270455741)
  ·
    refine ⟨28530153418877479976420903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76080409117006613270455741 28530153418877479976420903)
    ·
      refine ⟨42795230128316219964631355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28530153418877479976420903 42795230128316219964631355)
      ·
        refine ⟨64192845192474329946947033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42795230128316219964631355 64192845192474329946947033)
        ·
          refine ⟨48144633894355747460210275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64192845192474329946947033 48144633894355747460210275)
          ·
            refine ⟨72216950841533621190315413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48144633894355747460210275 72216950841533621190315413)
            ·
              refine ⟨3385169570696888493296035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 72216950841533621190315413 3385169570696888493296035)
              ·
                refine ⟨5077754356045332739944053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3385169570696888493296035 5077754356045332739944053)
                ·
                  refine ⟨476039470879249944369755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5077754356045332739944053 476039470879249944369755)
                  ·
                    rfl

theorem cell22_4171876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 6, 1, 5].length) (baseStart_4171876 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4171876 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4171876 prefixEnd_4171876 := by exact prefixLift 4171876
  have htrace : WordTrace (prefixWord ++ tailWord_4171876) baseStart_4171876 baseEnd_4171876 := by
    simpa [prefixWord, tailWord_4171876, baseEnd_4171876] using wordTrace_append hprefix tailTrace_4171876
  have hstable : (prefixWord ++ tailWord_4171876).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4171876).length < 2 ^ (prefixWord ++ tailWord_4171876).sum := by decide
  have hdescent : baseEnd_4171876 < baseStart_4171876 := by decide
  rcases family_descends (prefixWord ++ tailWord_4171876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4171889 : List Nat := [1, 2, 2, 2, 1, 1, 5, 1, 3, 4]
def baseStart_4171889 : Nat := 118140960795 + 4171889 * 2 ^ 59
def prefixEnd_4171889 : Nat := 4983230072969 + 3 ^ 40 * 4171889 * 2
def baseEnd_4171889 : Nat := 1428122862803422132534225

theorem tailTrace_4171889 : CollatzResearch.WordTrace tailWord_4171889 prefixEnd_4171889 1428122862803422132534225 := by
  unfold tailWord_4171889
  simp only [CollatzResearch.WordTrace]
  refine ⟨152161292382966129761134721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101440861588644086507423147 152161292382966129761134721)
  ·
    refine ⟨114120969287224597320851041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152161292382966129761134721 114120969287224597320851041)
    ·
      refine ⟨85590726965418447990638281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114120969287224597320851041 85590726965418447990638281)
      ·
        refine ⟨64193045224063835992978711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85590726965418447990638281 64193045224063835992978711)
        ·
          refine ⟨96289567836095753989468067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64193045224063835992978711 96289567836095753989468067)
          ·
            refine ⟨144434351754143630984202101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96289567836095753989468067 144434351754143630984202101)
            ·
              refine ⟨13540720476950965404768947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 144434351754143630984202101 13540720476950965404768947)
              ·
                refine ⟨20311080715426448107153421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13540720476950965404768947 20311080715426448107153421)
                ·
                  refine ⟨7616655268284918040182533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20311080715426448107153421 7616655268284918040182533)
                  ·
                    refine ⟨1428122862803422132534225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7616655268284918040182533 1428122862803422132534225)
                    ·
                      rfl

theorem cell22_4171889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 5, 1, 3, 4].length) (baseStart_4171889 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4171889 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4171889 prefixEnd_4171889 := by exact prefixLift 4171889
  have htrace : WordTrace (prefixWord ++ tailWord_4171889) baseStart_4171889 baseEnd_4171889 := by
    simpa [prefixWord, tailWord_4171889, baseEnd_4171889] using wordTrace_append hprefix tailTrace_4171889
  have hstable : (prefixWord ++ tailWord_4171889).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4171889).length < 2 ^ (prefixWord ++ tailWord_4171889).sum := by decide
  have hdescent : baseEnd_4171889 < baseStart_4171889 := by decide
  rcases family_descends (prefixWord ++ tailWord_4171889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4171936 : List Nat := [2, 1, 1, 4, 2, 3, 2, 1, 1, 5]
def baseStart_4171936 : Nat := 118140960795 + 4171936 * 2 ^ 59
def prefixEnd_4171936 : Nat := 4983230072969 + 3 ^ 40 * 4171936 * 2
def baseEnd_4171936 : Nat := 1428138951863929676609081

theorem tailTrace_4171936 : CollatzResearch.WordTrace tailWord_4171936 prefixEnd_4171936 1428138951863929676609081 := by
  unfold tailWord_4171936
  simp only [CollatzResearch.WordTrace]
  refine ⟨76081503306897928394047831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101442004409197237858730441 76081503306897928394047831)
  ·
    refine ⟨114122254960346892591071747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76081503306897928394047831 114122254960346892591071747)
    ·
      refine ⟨171183382440520338886607621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114122254960346892591071747 171183382440520338886607621)
      ·
        refine ⟨32096884207597563541238929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 171183382440520338886607621 32096884207597563541238929)
        ·
          refine ⟨24072663155698172655929197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32096884207597563541238929 24072663155698172655929197)
          ·
            refine ⟨9027248683386814745973449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24072663155698172655929197 9027248683386814745973449)
            ·
              refine ⟨6770436512540111059480087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9027248683386814745973449 6770436512540111059480087)
              ·
                refine ⟨10155654768810166589220131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6770436512540111059480087 10155654768810166589220131)
                ·
                  refine ⟨15233482153215249883830197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10155654768810166589220131 15233482153215249883830197)
                  ·
                    refine ⟨1428138951863929676609081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15233482153215249883830197 1428138951863929676609081)
                    ·
                      rfl

theorem cell22_4171936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 2, 1, 1, 5].length) (baseStart_4171936 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4171936 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4171936 prefixEnd_4171936 := by exact prefixLift 4171936
  have htrace : WordTrace (prefixWord ++ tailWord_4171936) baseStart_4171936 baseEnd_4171936 := by
    simpa [prefixWord, tailWord_4171936, baseEnd_4171936] using wordTrace_append hprefix tailTrace_4171936
  have hstable : (prefixWord ++ tailWord_4171936).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4171936).length < 2 ^ (prefixWord ++ tailWord_4171936).sum := by decide
  have hdescent : baseEnd_4171936 < baseStart_4171936 := by decide
  rcases family_descends (prefixWord ++ tailWord_4171936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4171957 : List Nat := [1, 3, 3, 4, 1, 2, 2, 1, 1, 4]
def baseStart_4171957 : Nat := 118140960795 + 4171957 * 2 ^ 59
def prefixEnd_4171957 : Nat := 4983230072969 + 3 ^ 40 * 4171957 * 2
def baseEnd_4171957 : Nat := 1428146140593092621834017

theorem tailTrace_4171957 : CollatzResearch.WordTrace tailWord_4171957 prefixEnd_4171957 1428146140593092621834017 := by
  unfold tailWord_4171957
  simp only [CollatzResearch.WordTrace]
  refine ⟨152163772546719777374610125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101442515031146518249740083 152163772546719777374610125)
  ·
    refine ⟨57061414705019916515478797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152163772546719777374610125 57061414705019916515478797)
    ·
      refine ⟨21398030514382468693304549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57061414705019916515478797 21398030514382468693304549)
      ·
        refine ⟨4012130721446712879994603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21398030514382468693304549 4012130721446712879994603)
        ·
          refine ⟨6018196082170069319991905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4012130721446712879994603 6018196082170069319991905)
          ·
            refine ⟨4513647061627551989993929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6018196082170069319991905 4513647061627551989993929)
            ·
              refine ⟨3385235296220663992495447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4513647061627551989993929 3385235296220663992495447)
              ·
                refine ⟨5077852944330995988743171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3385235296220663992495447 5077852944330995988743171)
                ·
                  refine ⟨7616779416496493983114757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5077852944330995988743171 7616779416496493983114757)
                  ·
                    refine ⟨1428146140593092621834017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7616779416496493983114757 1428146140593092621834017)
                    ·
                      rfl

theorem cell22_4171957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 2, 2, 1, 1, 4].length) (baseStart_4171957 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4171957 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4171957 prefixEnd_4171957 := by exact prefixLift 4171957
  have htrace : WordTrace (prefixWord ++ tailWord_4171957) baseStart_4171957 baseEnd_4171957 := by
    simpa [prefixWord, tailWord_4171957, baseEnd_4171957] using wordTrace_append hprefix tailTrace_4171957
  have hstable : (prefixWord ++ tailWord_4171957).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4171957).length < 2 ^ (prefixWord ++ tailWord_4171957).sum := by decide
  have hdescent : baseEnd_4171957 < baseStart_4171957 := by decide
  rcases family_descends (prefixWord ++ tailWord_4171957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4171966 : List Nat := [4, 2, 1, 1, 4, 1, 9]
def baseStart_4171966 : Nat := 118140960795 + 4171966 * 2 ^ 59
def prefixEnd_4171966 : Nat := 4983230072969 + 3 ^ 40 * 4171966 * 2
def baseEnd_4171966 : Nat := 52894415610259985124407

theorem tailTrace_4171966 : CollatzResearch.WordTrace tailWord_4171966 prefixEnd_4171966 52894415610259985124407 := by
  unfold tailWord_4171966
  simp only [CollatzResearch.WordTrace]
  refine ⟨19020512600460896488960969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 101442733869124781274458501 19020512600460896488960969)
  ·
    refine ⟨14265384450345672366720727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19020512600460896488960969 14265384450345672366720727)
    ·
      refine ⟨21398076675518508550081091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14265384450345672366720727 21398076675518508550081091)
      ·
        refine ⟨32097115013277762825121637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21398076675518508550081091 32097115013277762825121637)
        ·
          refine ⟨6018209064989580529710307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32097115013277762825121637 6018209064989580529710307)
          ·
            refine ⟨9027313597484370794565461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6018209064989580529710307 9027313597484370794565461)
            ·
              refine ⟨52894415610259985124407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 9027313597484370794565461 52894415610259985124407)
              ·
                rfl

theorem cell22_4171966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 9].length) (baseStart_4171966 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4171966 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4171966 prefixEnd_4171966 := by exact prefixLift 4171966
  have htrace : WordTrace (prefixWord ++ tailWord_4171966) baseStart_4171966 baseEnd_4171966 := by
    simpa [prefixWord, tailWord_4171966, baseEnd_4171966] using wordTrace_append hprefix tailTrace_4171966
  have hstable : (prefixWord ++ tailWord_4171966).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4171966).length < 2 ^ (prefixWord ++ tailWord_4171966).sum := by decide
  have hdescent : baseEnd_4171966 < baseStart_4171966 := by decide
  rcases family_descends (prefixWord ++ tailWord_4171966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4172015 : List Nat := [1, 1, 2, 1, 6, 1, 3, 3, 1, 3]
def baseStart_4172015 : Nat := 118140960795 + 4172015 * 2 ^ 59
def prefixEnd_4172015 : Nat := 4983230072969 + 3 ^ 40 * 4172015 * 2
def baseEnd_4172015 : Nat := 1428165995178399803883839

theorem tailTrace_4172015 : CollatzResearch.WordTrace tailWord_4172015 prefixEnd_4172015 1428165995178399803883839 := by
  unfold tailWord_4172015
  simp only [CollatzResearch.WordTrace]
  refine ⟨152165887980509653280221499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101443925320339768853480999 152165887980509653280221499)
  ·
    refine ⟨228248831970764479920332249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152165887980509653280221499 228248831970764479920332249)
    ·
      refine ⟨171186623978073359940249187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 228248831970764479920332249 171186623978073359940249187)
      ·
        refine ⟨256779935967110039910373781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171186623978073359940249187 256779935967110039910373781)
        ·
          refine ⟨12036559498458283120798771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 256779935967110039910373781 12036559498458283120798771)
          ·
            refine ⟨18054839247687424681198157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12036559498458283120798771 18054839247687424681198157)
            ·
              refine ⟨6770564717882784255449309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18054839247687424681198157 6770564717882784255449309)
              ·
                refine ⟨2538961769206044095793491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6770564717882784255449309 2538961769206044095793491)
                ·
                  refine ⟨3808442653809066143690237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2538961769206044095793491 3808442653809066143690237)
                  ·
                    refine ⟨1428165995178399803883839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3808442653809066143690237 1428165995178399803883839)
                    ·
                      rfl

theorem cell22_4172015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 3, 3, 1, 3].length) (baseStart_4172015 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4172015 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4172015 prefixEnd_4172015 := by exact prefixLift 4172015
  have htrace : WordTrace (prefixWord ++ tailWord_4172015) baseStart_4172015 baseEnd_4172015 := by
    simpa [prefixWord, tailWord_4172015, baseEnd_4172015] using wordTrace_append hprefix tailTrace_4172015
  have hstable : (prefixWord ++ tailWord_4172015).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4172015).length < 2 ^ (prefixWord ++ tailWord_4172015).sum := by decide
  have hdescent : baseEnd_4172015 < baseStart_4172015 := by decide
  rcases family_descends (prefixWord ++ tailWord_4172015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4172058 : List Nat := [3, 1, 1, 3, 4, 1, 1, 1, 3, 4]
def baseStart_4172058 : Nat := 118140960795 + 4172058 * 2 ^ 59
def prefixEnd_4172058 : Nat := 4983230072969 + 3 ^ 40 * 4172058 * 2
def baseEnd_4172058 : Nat := 1428180714957162025058707

theorem tailTrace_4172058 : CollatzResearch.WordTrace tailWord_4172058 prefixEnd_4172058 1428180714957162025058707 := by
  unfold tailWord_4172058
  simp only [CollatzResearch.WordTrace]
  refine ⟨38041864079838467906009207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101444970879569247749357885 38041864079838467906009207)
  ·
    refine ⟨57062796119757701859013811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38041864079838467906009207 57062796119757701859013811)
    ·
      refine ⟨85594194179636552788520717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57062796119757701859013811 85594194179636552788520717)
      ·
        refine ⟨32097822817363707295695269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85594194179636552788520717 32097822817363707295695269)
        ·
          refine ⟨6018341778255695117942863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32097822817363707295695269 6018341778255695117942863)
          ·
            refine ⟨9027512667383542676914295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6018341778255695117942863 9027512667383542676914295)
            ·
              refine ⟨13541269001075314015371443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9027512667383542676914295 13541269001075314015371443)
              ·
                refine ⟨20311903501612971023057165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13541269001075314015371443 20311903501612971023057165)
                ·
                  refine ⟨7616963813104864133646437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20311903501612971023057165 7616963813104864133646437)
                  ·
                    refine ⟨1428180714957162025058707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7616963813104864133646437 1428180714957162025058707)
                    ·
                      rfl

theorem cell22_4172058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 1, 1, 3, 4].length) (baseStart_4172058 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4172058 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4172058 prefixEnd_4172058 := by exact prefixLift 4172058
  have htrace : WordTrace (prefixWord ++ tailWord_4172058) baseStart_4172058 baseEnd_4172058 := by
    simpa [prefixWord, tailWord_4172058, baseEnd_4172058] using wordTrace_append hprefix tailTrace_4172058
  have hstable : (prefixWord ++ tailWord_4172058).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4172058).length < 2 ^ (prefixWord ++ tailWord_4172058).sum := by decide
  have hdescent : baseEnd_4172058 < baseStart_4172058 := by decide
  rcases family_descends (prefixWord ++ tailWord_4172058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4172088 : List Nat := [2, 1, 2, 1, 3, 1, 3, 4, 2, 3]
def baseStart_4172088 : Nat := 118140960795 + 4172088 * 2 ^ 59
def prefixEnd_4172088 : Nat := 4983230072969 + 3 ^ 40 * 4172088 * 2
def baseEnd_4172088 : Nat := 1428190984570251946808615

theorem tailTrace_4172088 : CollatzResearch.WordTrace tailWord_4172088 prefixEnd_4172088 1428190984570251946808615 := by
  unfold tailWord_4172088
  simp only [CollatzResearch.WordTrace]
  refine ⟨76084275254622593373814459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101445700339496791165085945 76084275254622593373814459)
  ·
    refine ⟨114126412881933890060721689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76084275254622593373814459 114126412881933890060721689)
    ·
      refine ⟨85594809661450417545541267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114126412881933890060721689 85594809661450417545541267)
      ·
        refine ⟨128392214492175626318311901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85594809661450417545541267 128392214492175626318311901)
        ·
          refine ⟨48147080434565859869366963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 128392214492175626318311901 48147080434565859869366963)
          ·
            refine ⟨72220620651848789804050445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48147080434565859869366963 72220620651848789804050445)
            ·
              refine ⟨27082732744443296176518917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72220620651848789804050445 27082732744443296176518917)
              ·
                refine ⟨5078012389583118033097297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27082732744443296176518917 5078012389583118033097297)
                ·
                  refine ⟨3808509292187338524822973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5078012389583118033097297 3808509292187338524822973)
                  ·
                    refine ⟨1428190984570251946808615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3808509292187338524822973 1428190984570251946808615)
                    ·
                      rfl

theorem cell22_4172088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 4, 2, 3].length) (baseStart_4172088 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4172088 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4172088 prefixEnd_4172088 := by exact prefixLift 4172088
  have htrace : WordTrace (prefixWord ++ tailWord_4172088) baseStart_4172088 baseEnd_4172088 := by
    simpa [prefixWord, tailWord_4172088, baseEnd_4172088] using wordTrace_append hprefix tailTrace_4172088
  have hstable : (prefixWord ++ tailWord_4172088).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4172088).length < 2 ^ (prefixWord ++ tailWord_4172088).sum := by decide
  have hdescent : baseEnd_4172088 < baseStart_4172088 := by decide
  rcases family_descends (prefixWord ++ tailWord_4172088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4172090 : List Nat := [3, 1, 1, 1, 4, 2, 4, 2, 4]
def baseStart_4172090 : Nat := 118140960795 + 4172090 * 2 ^ 59
def prefixEnd_4172090 : Nat := 4983230072969 + 3 ^ 40 * 4172090 * 2
def baseEnd_4172090 : Nat := 476063889737041536086203

theorem tailTrace_4172090 : CollatzResearch.WordTrace tailWord_4172090 prefixEnd_4172090 476063889737041536086203 := by
  unfold tailWord_4172090
  simp only [CollatzResearch.WordTrace]
  refine ⟨38042155863809485272300431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101445748970158627392801149 38042155863809485272300431)
  ·
    refine ⟨57063233795714227908450647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38042155863809485272300431 57063233795714227908450647)
    ·
      refine ⟨85594850693571341862675971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57063233795714227908450647 85594850693571341862675971)
      ·
        refine ⟨128392276040357012794013957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85594850693571341862675971 128392276040357012794013957)
        ·
          refine ⟨24073551757566939898877617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 128392276040357012794013957 24073551757566939898877617)
          ·
            refine ⟨18055163818175204924158213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24073551757566939898877617 18055163818175204924158213)
            ·
              refine ⟨3385343215907850923279665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18055163818175204924158213 3385343215907850923279665)
              ·
                refine ⟨2539007411930888192459749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3385343215907850923279665 2539007411930888192459749)
                ·
                  refine ⟨476063889737041536086203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2539007411930888192459749 476063889737041536086203)
                  ·
                    rfl

theorem cell22_4172090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 4, 2, 4].length) (baseStart_4172090 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4172090 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4172090 prefixEnd_4172090 := by exact prefixLift 4172090
  have htrace : WordTrace (prefixWord ++ tailWord_4172090) baseStart_4172090 baseEnd_4172090 := by
    simpa [prefixWord, tailWord_4172090, baseEnd_4172090] using wordTrace_append hprefix tailTrace_4172090
  have hstable : (prefixWord ++ tailWord_4172090).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4172090).length < 2 ^ (prefixWord ++ tailWord_4172090).sum := by decide
  have hdescent : baseEnd_4172090 < baseStart_4172090 := by decide
  rcases family_descends (prefixWord ++ tailWord_4172090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4172126 : List Nat := [4, 4, 2, 1, 1, 1, 1, 3, 1, 4]
def baseStart_4172126 : Nat := 118140960795 + 4172126 * 2 ^ 59
def prefixEnd_4172126 : Nat := 4983230072969 + 3 ^ 40 * 4172126 * 2
def baseEnd_4172126 : Nat := 1428203992746832514358499

theorem tailTrace_4172126 : CollatzResearch.WordTrace tailWord_4172126 prefixEnd_4172126 1428203992746832514358499 := by
  unfold tailWord_4172126
  simp only [CollatzResearch.WordTrace]
  refine ⟨19021242060388439904689029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 101446624322071679491674821 19021242060388439904689029)
  ·
    refine ⟨3566482886322832482129193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19021242060388439904689029 3566482886322832482129193)
    ·
      refine ⟨2674862164742124361596895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3566482886322832482129193 2674862164742124361596895)
      ·
        refine ⟨4012293247113186542395343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2674862164742124361596895 4012293247113186542395343)
        ·
          refine ⟨6018439870669779813593015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4012293247113186542395343 6018439870669779813593015)
          ·
            refine ⟨9027659806004669720389523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6018439870669779813593015 9027659806004669720389523)
            ·
              refine ⟨13541489709007004580584285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9027659806004669720389523 13541489709007004580584285)
              ·
                refine ⟨5078058640877626717719107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13541489709007004580584285 5078058640877626717719107)
                ·
                  refine ⟨7617087961316440076578661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5078058640877626717719107 7617087961316440076578661)
                  ·
                    refine ⟨1428203992746832514358499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7617087961316440076578661 1428203992746832514358499)
                    ·
                      rfl

theorem cell22_4172126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 1, 3, 1, 4].length) (baseStart_4172126 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4172126 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4172126 prefixEnd_4172126 := by exact prefixLift 4172126
  have htrace : WordTrace (prefixWord ++ tailWord_4172126) baseStart_4172126 baseEnd_4172126 := by
    simpa [prefixWord, tailWord_4172126, baseEnd_4172126] using wordTrace_append hprefix tailTrace_4172126
  have hstable : (prefixWord ++ tailWord_4172126).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4172126).length < 2 ^ (prefixWord ++ tailWord_4172126).sum := by decide
  have hdescent : baseEnd_4172126 < baseStart_4172126 := by decide
  rcases family_descends (prefixWord ++ tailWord_4172126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4172184 : List Nat := [2, 1, 2, 5, 1, 3, 1, 3, 1, 3]
def baseStart_4172184 : Nat := 118140960795 + 4172184 * 2 ^ 59
def prefixEnd_4172184 : Nat := 4983230072969 + 3 ^ 40 * 4172184 * 2
def baseEnd_4172184 : Nat := 1428223847332139696408321

theorem tailTrace_4172184 : CollatzResearch.WordTrace tailWord_4172184 prefixEnd_4172184 1428223847332139696408321 := by
  unfold tailWord_4172184
  simp only [CollatzResearch.WordTrace]
  refine ⟨76086025958448697571561803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101448034611264930095415737 76086025958448697571561803)
  ·
    refine ⟨114129038937673046357342705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76086025958448697571561803 114129038937673046357342705)
    ·
      refine ⟨85596779203254784768007029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114129038937673046357342705 85596779203254784768007029)
      ·
        refine ⟨8024698050305136072000659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 85596779203254784768007029 8024698050305136072000659)
        ·
          refine ⟨12037047075457704108000989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8024698050305136072000659 12037047075457704108000989)
          ·
            refine ⟨4513892653296639040500371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12037047075457704108000989 4513892653296639040500371)
            ·
              refine ⟨6770838979944958560750557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4513892653296639040500371 6770838979944958560750557)
              ·
                refine ⟨2539064617479359460281459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6770838979944958560750557 2539064617479359460281459)
                ·
                  refine ⟨3808596926219039190422189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2539064617479359460281459 3808596926219039190422189)
                  ·
                    refine ⟨1428223847332139696408321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3808596926219039190422189 1428223847332139696408321)
                    ·
                      rfl

theorem cell22_4172184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 3, 1, 3, 1, 3].length) (baseStart_4172184 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4172184 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4172184 prefixEnd_4172184 := by exact prefixLift 4172184
  have htrace : WordTrace (prefixWord ++ tailWord_4172184) baseStart_4172184 baseEnd_4172184 := by
    simpa [prefixWord, tailWord_4172184, baseEnd_4172184] using wordTrace_append hprefix tailTrace_4172184
  have hstable : (prefixWord ++ tailWord_4172184).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4172184).length < 2 ^ (prefixWord ++ tailWord_4172184).sum := by decide
  have hdescent : baseEnd_4172184 < baseStart_4172184 := by decide
  rcases family_descends (prefixWord ++ tailWord_4172184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4172259 : List Nat := [1, 1, 1, 6, 3, 2, 2, 2, 4]
def baseStart_4172259 : Nat := 118140960795 + 4172259 * 2 ^ 59
def prefixEnd_4172259 : Nat := 4983230072969 + 3 ^ 40 * 4172259 * 2
def baseEnd_4172259 : Nat := 476083173788288166927697

theorem tailTrace_4172259 : CollatzResearch.WordTrace tailWord_4172259 prefixEnd_4172259 476083173788288166927697 := by
  unfold tailWord_4172259
  simp only [CollatzResearch.WordTrace]
  refine ⟨152174787391625682952103831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101449858261083788634735887 152174787391625682952103831)
  ·
    refine ⟨228262181087438524428155747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152174787391625682952103831 228262181087438524428155747)
    ·
      refine ⟨342393271631157786642233621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228262181087438524428155747 342393271631157786642233621)
      ·
        refine ⟨16049684607710521248854701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 342393271631157786642233621 16049684607710521248854701)
        ·
          refine ⟨6018631727891445468320513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16049684607710521248854701 6018631727891445468320513)
          ·
            refine ⟨4513973795918584101240385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6018631727891445468320513 4513973795918584101240385)
            ·
              refine ⟨3385480346938938075930289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4513973795918584101240385 3385480346938938075930289)
              ·
                refine ⟨2539110260204203556947717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3385480346938938075930289 2539110260204203556947717)
                ·
                  refine ⟨476083173788288166927697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2539110260204203556947717 476083173788288166927697)
                  ·
                    rfl

theorem cell22_4172259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 2, 2, 2, 4].length) (baseStart_4172259 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4172259 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4172259 prefixEnd_4172259 := by exact prefixLift 4172259
  have htrace : WordTrace (prefixWord ++ tailWord_4172259) baseStart_4172259 baseEnd_4172259 := by
    simpa [prefixWord, tailWord_4172259, baseEnd_4172259] using wordTrace_append hprefix tailTrace_4172259
  have hstable : (prefixWord ++ tailWord_4172259).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4172259).length < 2 ^ (prefixWord ++ tailWord_4172259).sum := by decide
  have hdescent : baseEnd_4172259 < baseStart_4172259 := by decide
  rcases family_descends (prefixWord ++ tailWord_4172259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4172270 : List Nat := [4, 1, 2, 1, 2, 4, 1, 7]
def baseStart_4172270 : Nat := 118140960795 + 4172270 * 2 ^ 59
def prefixEnd_4172270 : Nat := 4983230072969 + 3 ^ 40 * 4172270 * 2
def baseEnd_4172270 : Nat := 158694809654407126528673

theorem tailTrace_4172270 : CollatzResearch.WordTrace tailWord_4172270 prefixEnd_4172270 158694809654407126528673 := by
  unfold tailWord_4172270
  simp only [CollatzResearch.WordTrace]
  refine ⟨19021898574323228978844283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 101450125729723887887169509 19021898574323228978844283)
  ·
    refine ⟨28532847861484843468266425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19021898574323228978844283 28532847861484843468266425)
    ·
      refine ⟨21399635896113632601199819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28532847861484843468266425 21399635896113632601199819)
      ·
        refine ⟨32099453844170448901799729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21399635896113632601199819 32099453844170448901799729)
        ·
          refine ⟨24074590383127836676349797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32099453844170448901799729 24074590383127836676349797)
          ·
            refine ⟨4513985696836469376815587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24074590383127836676349797 4513985696836469376815587)
            ·
              refine ⟨6770978545254704065223381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4513985696836469376815587 6770978545254704065223381)
              ·
                refine ⟨158694809654407126528673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6770978545254704065223381 158694809654407126528673)
                ·
                  rfl

theorem cell22_4172270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 4, 1, 7].length) (baseStart_4172270 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4172270 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4172270 prefixEnd_4172270 := by exact prefixLift 4172270
  have htrace : WordTrace (prefixWord ++ tailWord_4172270) baseStart_4172270 baseEnd_4172270 := by
    simpa [prefixWord, tailWord_4172270, baseEnd_4172270] using wordTrace_append hprefix tailTrace_4172270
  have hstable : (prefixWord ++ tailWord_4172270).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4172270).length < 2 ^ (prefixWord ++ tailWord_4172270).sum := by decide
  have hdescent : baseEnd_4172270 < baseStart_4172270 := by decide
  rcases family_descends (prefixWord ++ tailWord_4172270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4172285 : List Nat := [1, 4, 1, 1, 1, 3, 3, 2, 3, 3]
def baseStart_4172285 : Nat := 118140960795 + 4172285 * 2 ^ 59
def prefixEnd_4172285 : Nat := 4983230072969 + 3 ^ 40 * 4172285 * 2
def baseEnd_4172285 : Nat := 1428258421696209099633011

theorem tailTrace_4172285 : CollatzResearch.WordTrace tailWord_4172285 prefixEnd_4172285 1428258421696209099633011 := by
  unfold tailWord_4172285
  simp only [CollatzResearch.WordTrace]
  refine ⟨152175735689531489392550309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101450490459687659595033539 152175735689531489392550309)
  ·
    refine ⟨28532950441787154261103183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 152175735689531489392550309 28532950441787154261103183)
    ·
      refine ⟨42799425662680731391654775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28532950441787154261103183 42799425662680731391654775)
      ·
        refine ⟨64199138494021097087482163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42799425662680731391654775 64199138494021097087482163)
        ·
          refine ⟨96298707741031645631223245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64199138494021097087482163 96298707741031645631223245)
          ·
            refine ⟨36112015402886867111708717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96298707741031645631223245 36112015402886867111708717)
            ·
              refine ⟨13542005776082575166890769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36112015402886867111708717 13542005776082575166890769)
              ·
                refine ⟨10156504332061931375168077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13542005776082575166890769 10156504332061931375168077)
                ·
                  refine ⟨3808689124523224265688029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10156504332061931375168077 3808689124523224265688029)
                  ·
                    refine ⟨1428258421696209099633011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3808689124523224265688029 1428258421696209099633011)
                    ·
                      rfl

theorem cell22_4172285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 3, 2, 3, 3].length) (baseStart_4172285 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4172285 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4172285 prefixEnd_4172285 := by exact prefixLift 4172285
  have htrace : WordTrace (prefixWord ++ tailWord_4172285) baseStart_4172285 baseEnd_4172285 := by
    simpa [prefixWord, tailWord_4172285, baseEnd_4172285] using wordTrace_append hprefix tailTrace_4172285
  have hstable : (prefixWord ++ tailWord_4172285).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4172285).length < 2 ^ (prefixWord ++ tailWord_4172285).sum := by decide
  have hdescent : baseEnd_4172285 < baseStart_4172285 := by decide
  rcases family_descends (prefixWord ++ tailWord_4172285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4172298 : List Nat := [3, 1, 2, 2, 2, 1, 2, 2, 7]
def baseStart_4172298 : Nat := 118140960795 + 4172298 * 2 ^ 59
def prefixEnd_4172298 : Nat := 4983230072969 + 3 ^ 40 * 4172298 * 2
def baseEnd_4172298 : Nat := 476087623953960466352657

theorem tailTrace_4172298 : CollatzResearch.WordTrace tailWord_4172298 prefixEnd_4172298 476087623953960466352657 := by
  unfold tailWord_4172298
  simp only [CollatzResearch.WordTrace]
  refine ⟨38044052459621098153193387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101450806558989595075182365 38044052459621098153193387)
  ·
    refine ⟨57066078689431647229790081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38044052459621098153193387 57066078689431647229790081)
    ·
      refine ⟨42799559017073735422342561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57066078689431647229790081 42799559017073735422342561)
      ·
        refine ⟨32099669262805301566756921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42799559017073735422342561 32099669262805301566756921)
        ·
          refine ⟨24074751947103976175067691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32099669262805301566756921 24074751947103976175067691)
          ·
            refine ⟨36112127920655964262601537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24074751947103976175067691 36112127920655964262601537)
            ·
              refine ⟨27084095940491973196951153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36112127920655964262601537 27084095940491973196951153)
              ·
                refine ⟨20313071955368979897713365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27084095940491973196951153 20313071955368979897713365)
                ·
                  refine ⟨476087623953960466352657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20313071955368979897713365 476087623953960466352657)
                  ·
                    rfl

theorem cell22_4172298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 2, 7].length) (baseStart_4172298 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4172298 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4172298 prefixEnd_4172298 := by exact prefixLift 4172298
  have htrace : WordTrace (prefixWord ++ tailWord_4172298) baseStart_4172298 baseEnd_4172298 := by
    simpa [prefixWord, tailWord_4172298, baseEnd_4172298] using wordTrace_append hprefix tailTrace_4172298
  have hstable : (prefixWord ++ tailWord_4172298).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4172298).length < 2 ^ (prefixWord ++ tailWord_4172298).sum := by decide
  have hdescent : baseEnd_4172298 < baseStart_4172298 := by decide
  rcases family_descends (prefixWord ++ tailWord_4172298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4172330 : List Nat := [3, 1, 4, 1, 1, 2, 2, 1, 2, 5]
def baseStart_4172330 : Nat := 118140960795 + 4172330 * 2 ^ 59
def prefixEnd_4172330 : Nat := 4983230072969 + 3 ^ 40 * 4172330 * 2
def baseEnd_4172330 : Nat := 1428273826115843982257873

theorem tailTrace_4172330 : CollatzResearch.WordTrace tailWord_4172330 prefixEnd_4172330 1428273826115843982257873 := by
  unfold tailWord_4172330
  simp only [CollatzResearch.WordTrace]
  refine ⟨38044344243592115519484611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101451584649578974718625629 38044344243592115519484611)
  ·
    refine ⟨57066516365388173279226917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38044344243592115519484611 57066516365388173279226917)
    ·
      refine ⟨10699971818510282489855047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 57066516365388173279226917 10699971818510282489855047)
      ·
        refine ⟨16049957727765423734782571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10699971818510282489855047 16049957727765423734782571)
        ·
          refine ⟨24074936591648135602173857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16049957727765423734782571 24074936591648135602173857)
          ·
            refine ⟨18056202443736101701630393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24074936591648135602173857 18056202443736101701630393)
            ·
              refine ⟨13542151832802076276222795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18056202443736101701630393 13542151832802076276222795)
              ·
                refine ⟨20313227749203114414334193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13542151832802076276222795 20313227749203114414334193)
                ·
                  refine ⟨15234920811902335810750645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20313227749203114414334193 15234920811902335810750645)
                  ·
                    refine ⟨1428273826115843982257873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15234920811902335810750645 1428273826115843982257873)
                    ·
                      rfl

theorem cell22_4172330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 2, 1, 2, 5].length) (baseStart_4172330 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4172330 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4172330 prefixEnd_4172330 := by exact prefixLift 4172330
  have htrace : WordTrace (prefixWord ++ tailWord_4172330) baseStart_4172330 baseEnd_4172330 := by
    simpa [prefixWord, tailWord_4172330, baseEnd_4172330] using wordTrace_append hprefix tailTrace_4172330
  have hstable : (prefixWord ++ tailWord_4172330).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4172330).length < 2 ^ (prefixWord ++ tailWord_4172330).sum := by decide
  have hdescent : baseEnd_4172330 < baseStart_4172330 := by decide
  rcases family_descends (prefixWord ++ tailWord_4172330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4172343 : List Nat := [1, 1, 3, 1, 2, 3, 1, 4, 6]
def baseStart_4172343 : Nat := 118140960795 + 4172343 * 2 ^ 59
def prefixEnd_4172343 : Nat := 4983230072969 + 3 ^ 40 * 4172343 * 2
def baseEnd_4172343 : Nat := 476092758760505427227611

theorem tailTrace_4172343 : CollatzResearch.WordTrace tailWord_4172343 prefixEnd_4172343 476092758760505427227611 := by
  unfold tailWord_4172343
  simp only [CollatzResearch.WordTrace]
  refine ⟨152177851123321365298161683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101451900748880910198774455 152177851123321365298161683)
  ·
    refine ⟨228266776684982047947242525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152177851123321365298161683 228266776684982047947242525)
    ·
      refine ⟨85600041256868267980215947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 228266776684982047947242525 85600041256868267980215947)
      ·
        refine ⟨128400061885302401970323921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85600041256868267980215947 128400061885302401970323921)
        ·
          refine ⟨96300046413976801477742941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128400061885302401970323921 96300046413976801477742941)
          ·
            refine ⟨36112517405241300554153603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96300046413976801477742941 36112517405241300554153603)
            ·
              refine ⟨54168776107861950831230405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36112517405241300554153603 54168776107861950831230405)
              ·
                refine ⟨10156645520224115780855701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 54168776107861950831230405 10156645520224115780855701)
                ·
                  refine ⟨476092758760505427227611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10156645520224115780855701 476092758760505427227611)
                  ·
                    rfl

theorem cell22_4172343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 4, 6].length) (baseStart_4172343 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4172343 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4172343 prefixEnd_4172343 := by exact prefixLift 4172343
  have htrace : WordTrace (prefixWord ++ tailWord_4172343) baseStart_4172343 baseEnd_4172343 := by
    simpa [prefixWord, tailWord_4172343, baseEnd_4172343] using wordTrace_append hprefix tailTrace_4172343
  have hstable : (prefixWord ++ tailWord_4172343).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4172343).length < 2 ^ (prefixWord ++ tailWord_4172343).sum := by decide
  have hdescent : baseEnd_4172343 < baseStart_4172343 := by decide
  rcases family_descends (prefixWord ++ tailWord_4172343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4172375 : List Nat := [1, 1, 3, 2, 2, 2, 1, 3, 4, 3]
def baseStart_4172375 : Nat := 118140960795 + 4172375 * 2 ^ 59
def prefixEnd_4172375 : Nat := 4983230072969 + 3 ^ 40 * 4172375 * 2
def baseEnd_4172375 : Nat := 1428289230535478864882735

theorem tailTrace_4172375 : CollatzResearch.WordTrace tailWord_4172375 prefixEnd_4172375 1428289230535478864882735 := by
  unfold tailWord_4172375
  simp only [CollatzResearch.WordTrace]
  refine ⟨152179018259205434763326579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101452678839470289842217719 152179018259205434763326579)
  ·
    refine ⟨228268527388808152144989869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152179018259205434763326579 228268527388808152144989869)
    ·
      refine ⟨85600697770803057054371201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 228268527388808152144989869 85600697770803057054371201)
      ·
        refine ⟨64200523328102292790778401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85600697770803057054371201 64200523328102292790778401)
        ·
          refine ⟨48150392496076719593083801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64200523328102292790778401 48150392496076719593083801)
          ·
            refine ⟨36112794372057539694812851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48150392496076719593083801 36112794372057539694812851)
            ·
              refine ⟨54169191558086309542219277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36112794372057539694812851 54169191558086309542219277)
              ·
                refine ⟨20313446834282366078332229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54169191558086309542219277 20313446834282366078332229)
                ·
                  refine ⟨3808771281427943639687293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20313446834282366078332229 3808771281427943639687293)
                  ·
                    refine ⟨1428289230535478864882735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3808771281427943639687293 1428289230535478864882735)
                    ·
                      rfl

theorem cell22_4172375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 3, 4, 3].length) (baseStart_4172375 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4172375 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4172375 prefixEnd_4172375 := by exact prefixLift 4172375
  have htrace : WordTrace (prefixWord ++ tailWord_4172375) baseStart_4172375 baseEnd_4172375 := by
    simpa [prefixWord, tailWord_4172375, baseEnd_4172375] using wordTrace_append hprefix tailTrace_4172375
  have hstable : (prefixWord ++ tailWord_4172375).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4172375).length < 2 ^ (prefixWord ++ tailWord_4172375).sum := by decide
  have hdescent : baseEnd_4172375 < baseStart_4172375 := by decide
  rcases family_descends (prefixWord ++ tailWord_4172375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4172433 : List Nat := [1, 2, 2, 1, 1, 1, 1, 2, 11]
def baseStart_4172433 : Nat := 118140960795 + 4172433 * 2 ^ 59
def prefixEnd_4172433 : Nat := 4983230072969 + 3 ^ 40 * 4172433 * 2
def baseEnd_4172433 : Nat := 476103028373595348977519

theorem tailTrace_4172433 : CollatzResearch.WordTrace tailWord_4172433 prefixEnd_4172433 476103028373595348977519 := by
  unfold tailWord_4172433
  simp only [CollatzResearch.WordTrace]
  refine ⟨152181133692995310668937953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101454089128663540445958635 152181133692995310668937953)
  ·
    refine ⟨114135850269746483001703465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152181133692995310668937953 114135850269746483001703465)
    ·
      refine ⟨85601887702309862251277599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114135850269746483001703465 85601887702309862251277599)
      ·
        refine ⟨128402831553464793376916399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85601887702309862251277599 128402831553464793376916399)
        ·
          refine ⟨192604247330197190065374599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128402831553464793376916399 192604247330197190065374599)
          ·
            refine ⟨288906370995295785098061899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192604247330197190065374599 288906370995295785098061899)
            ·
              refine ⟨433359556492943677647092849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 288906370995295785098061899 433359556492943677647092849)
              ·
                refine ⟨325019667369707758235319637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 433359556492943677647092849 325019667369707758235319637)
                ·
                  refine ⟨476103028373595348977519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 325019667369707758235319637 476103028373595348977519)
                  ·
                    rfl

theorem cell22_4172433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 2, 11].length) (baseStart_4172433 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4172433 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4172433 prefixEnd_4172433 := by exact prefixLift 4172433
  have htrace : WordTrace (prefixWord ++ tailWord_4172433) baseStart_4172433 baseEnd_4172433 := by
    simpa [prefixWord, tailWord_4172433, baseEnd_4172433] using wordTrace_append hprefix tailTrace_4172433
  have hstable : (prefixWord ++ tailWord_4172433).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4172433).length < 2 ^ (prefixWord ++ tailWord_4172433).sum := by decide
  have hdescent : baseEnd_4172433 < baseStart_4172433 := by decide
  rcases family_descends (prefixWord ++ tailWord_4172433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4172458 : List Nat := [3, 1, 5, 2, 2, 1, 1, 1, 2, 4]
def baseStart_4172458 : Nat := 118140960795 + 4172458 * 2 ^ 59
def prefixEnd_4172458 : Nat := 4983230072969 + 3 ^ 40 * 4172458 * 2
def baseEnd_4172458 : Nat := 1428317643131694315057481

theorem tailTrace_4172458 : CollatzResearch.WordTrace tailWord_4172458 prefixEnd_4172458 1428317643131694315057481 := by
  unfold tailWord_4172458
  simp only [CollatzResearch.WordTrace]
  refine ⟨38045511379476184984649507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101454697011936493292398685 38045511379476184984649507)
  ·
    refine ⟨57068267069214277476974261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38045511379476184984649507 57068267069214277476974261)
    ·
      refine ⟨5350150037738838513466337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 57068267069214277476974261 5350150037738838513466337)
      ·
        refine ⟨4012612528304128885099753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5350150037738838513466337 4012612528304128885099753)
        ·
          refine ⟨3009459396228096663824815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4012612528304128885099753 3009459396228096663824815)
          ·
            refine ⟨4514189094342144995737223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3009459396228096663824815 4514189094342144995737223)
            ·
              refine ⟨6771283641513217493605835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4514189094342144995737223 6771283641513217493605835)
              ·
                refine ⟨10156925462269826240408753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6771283641513217493605835 10156925462269826240408753)
                ·
                  refine ⟨7617694096702369680306565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10156925462269826240408753 7617694096702369680306565)
                  ·
                    refine ⟨1428317643131694315057481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7617694096702369680306565 1428317643131694315057481)
                    ·
                      rfl

theorem cell22_4172458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 2, 1, 1, 1, 2, 4].length) (baseStart_4172458 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4172458 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4172458 prefixEnd_4172458 := by exact prefixLift 4172458
  have htrace : WordTrace (prefixWord ++ tailWord_4172458) baseStart_4172458 baseEnd_4172458 := by
    simpa [prefixWord, tailWord_4172458, baseEnd_4172458] using wordTrace_append hprefix tailTrace_4172458
  have hstable : (prefixWord ++ tailWord_4172458).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4172458).length < 2 ^ (prefixWord ++ tailWord_4172458).sum := by decide
  have hdescent : baseEnd_4172458 < baseStart_4172458 := by decide
  rcases family_descends (prefixWord ++ tailWord_4172458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4172471 : List Nat := [1, 1, 3, 1, 6, 1, 2, 3, 1, 3]
def baseStart_4172471 : Nat := 118140960795 + 4172471 * 2 ^ 59
def prefixEnd_4172471 : Nat := 4983230072969 + 3 ^ 40 * 4172471 * 2
def baseEnd_4172471 : Nat := 1428322093297366614482441

theorem tailTrace_4172471 : CollatzResearch.WordTrace tailWord_4172471 prefixEnd_4172471 1428322093297366614482441 := by
  unfold tailWord_4172471
  simp only [CollatzResearch.WordTrace]
  refine ⟨152182519666857643158821267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101455013111238428772547511 152182519666857643158821267)
  ·
    refine ⟨228273779500286464738231901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152182519666857643158821267 228273779500286464738231901)
    ·
      refine ⟨85602667312607424276836963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 228273779500286464738231901 85602667312607424276836963)
      ·
        refine ⟨128404000968911136415255445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85602667312607424276836963 128404000968911136415255445)
        ·
          refine ⟨6018937545417709519465099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 128404000968911136415255445 6018937545417709519465099)
          ·
            refine ⟨9028406318126564279197649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6018937545417709519465099 9028406318126564279197649)
            ·
              refine ⟨6771304738594923209398237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9028406318126564279197649 6771304738594923209398237)
              ·
                refine ⟨2539239276973096203524339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6771304738594923209398237 2539239276973096203524339)
                ·
                  refine ⟨3808858915459644305286509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2539239276973096203524339 3808858915459644305286509)
                  ·
                    refine ⟨1428322093297366614482441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3808858915459644305286509 1428322093297366614482441)
                    ·
                      rfl

theorem cell22_4172471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 2, 3, 1, 3].length) (baseStart_4172471 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4172471 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4172471 prefixEnd_4172471 := by exact prefixLift 4172471
  have htrace : WordTrace (prefixWord ++ tailWord_4172471) baseStart_4172471 baseEnd_4172471 := by
    simpa [prefixWord, tailWord_4172471, baseEnd_4172471] using wordTrace_append hprefix tailTrace_4172471
  have hstable : (prefixWord ++ tailWord_4172471).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4172471).length < 2 ^ (prefixWord ++ tailWord_4172471).sum := by decide
  have hdescent : baseEnd_4172471 < baseStart_4172471 := by decide
  rcases family_descends (prefixWord ++ tailWord_4172471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4172484 : List Nat := [2, 3, 3, 1, 1, 4, 1, 2, 5]
def baseStart_4172484 : Nat := 118140960795 + 4172484 * 2 ^ 59
def prefixEnd_4172484 : Nat := 4983230072969 + 3 ^ 40 * 4172484 * 2
def baseEnd_4172484 : Nat := 476108847821012971302467

theorem tailTrace_4172484 : CollatzResearch.WordTrace tailWord_4172484 prefixEnd_4172484 476108847821012971302467 := by
  unfold tailWord_4172484
  simp only [CollatzResearch.WordTrace]
  refine ⟨76091496907905273189522253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101455329210540364252696337 76091496907905273189522253)
  ·
    refine ⟨28534311340464477446070845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76091496907905273189522253 28534311340464477446070845)
    ·
      refine ⟨10700366752674179042276567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28534311340464477446070845 10700366752674179042276567)
      ·
        refine ⟨16050550129011268563414851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10700366752674179042276567 16050550129011268563414851)
        ·
          refine ⟨24075825193516902845122277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16050550129011268563414851 24075825193516902845122277)
          ·
            refine ⟨4514217223784419283460427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24075825193516902845122277 4514217223784419283460427)
            ·
              refine ⟨6771325835676628925190641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4514217223784419283460427 6771325835676628925190641)
              ·
                refine ⟨5078494376757471693892981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6771325835676628925190641 5078494376757471693892981)
                ·
                  refine ⟨476108847821012971302467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5078494376757471693892981 476108847821012971302467)
                  ·
                    rfl

theorem cell22_4172484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 4, 1, 2, 5].length) (baseStart_4172484 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4172484 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4172484 prefixEnd_4172484 := by exact prefixLift 4172484
  have htrace : WordTrace (prefixWord ++ tailWord_4172484) baseStart_4172484 baseEnd_4172484 := by
    simpa [prefixWord, tailWord_4172484, baseEnd_4172484] using wordTrace_append hprefix tailTrace_4172484
  have hstable : (prefixWord ++ tailWord_4172484).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4172484).length < 2 ^ (prefixWord ++ tailWord_4172484).sum := by decide
  have hdescent : baseEnd_4172484 < baseStart_4172484 := by decide
  rcases family_descends (prefixWord ++ tailWord_4172484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4172501 : List Nat := [1, 3, 2, 5, 1, 1, 3, 1, 5]
def baseStart_4172501 : Nat := 118140960795 + 4172501 * 2 ^ 59
def prefixEnd_4172501 : Nat := 4983230072969 + 3 ^ 40 * 4172501 * 2
def baseEnd_4172501 : Nat := 476110787636818845410783

theorem tailTrace_4172501 : CollatzResearch.WordTrace tailWord_4172501 prefixEnd_4172501 476110787636818845410783 := by
  unfold tailWord_4172501
  simp only [CollatzResearch.WordTrace]
  refine ⟨152183613856748958282413357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101455742571165972188275571 152183613856748958282413357)
  ·
    refine ⟨57068855196280859355905009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152183613856748958282413357 57068855196280859355905009)
    ·
      refine ⟨42801641397210644516928757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57068855196280859355905009 42801641397210644516928757)
      ·
        refine ⟨4012653880988497923462071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 42801641397210644516928757 4012653880988497923462071)
        ·
          refine ⟨6018980821482746885193107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4012653880988497923462071 6018980821482746885193107)
          ·
            refine ⟨9028471232224120327789661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6018980821482746885193107 9028471232224120327789661)
            ·
              refine ⟨3385676712084045122921123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9028471232224120327789661 3385676712084045122921123)
              ·
                refine ⟨5078515068126067684381685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3385676712084045122921123 5078515068126067684381685)
                ·
                  refine ⟨476110787636818845410783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5078515068126067684381685 476110787636818845410783)
                  ·
                    rfl

theorem cell22_4172501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 3, 1, 5].length) (baseStart_4172501 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4172501 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4172501 prefixEnd_4172501 := by exact prefixLift 4172501
  have htrace : WordTrace (prefixWord ++ tailWord_4172501) baseStart_4172501 baseEnd_4172501 := by
    simpa [prefixWord, tailWord_4172501, baseEnd_4172501] using wordTrace_append hprefix tailTrace_4172501
  have hstable : (prefixWord ++ tailWord_4172501).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4172501).length < 2 ^ (prefixWord ++ tailWord_4172501).sum := by decide
  have hdescent : baseEnd_4172501 < baseStart_4172501 := by decide
  rcases family_descends (prefixWord ++ tailWord_4172501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4172527 : List Nat := [1, 1, 2, 1, 5, 2, 1, 2, 4, 3]
def baseStart_4172527 : Nat := 118140960795 + 4172527 * 2 ^ 59
def prefixEnd_4172527 : Nat := 4983230072969 + 3 ^ 40 * 4172527 * 2
def baseEnd_4172527 : Nat := 1428341263241801135082269

theorem tailTrace_4172527 : CollatzResearch.WordTrace tailWord_4172527 prefixEnd_4172527 1428341263241801135082269 := by
  unfold tailWord_4172527
  simp only [CollatzResearch.WordTrace]
  refine ⟨152184562154654764722859835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101456374769769843148573223 152184562154654764722859835)
  ·
    refine ⟨228276843231982147084289753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152184562154654764722859835 228276843231982147084289753)
    ·
      refine ⟨171207632423986610313217315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 228276843231982147084289753 171207632423986610313217315)
      ·
        refine ⟨256811448635979915469825973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171207632423986610313217315 256811448635979915469825973)
        ·
          refine ⟨24076073309623117075296185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 256811448635979915469825973 24076073309623117075296185)
          ·
            refine ⟨18057054982217337806472139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24076073309623117075296185 18057054982217337806472139)
            ·
              refine ⟨27085582473326006709708209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18057054982217337806472139 27085582473326006709708209)
              ·
                refine ⟨20314186854994505032281157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27085582473326006709708209 20314186854994505032281157)
                ·
                  refine ⟨3808910035311469693552717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20314186854994505032281157 3808910035311469693552717)
                  ·
                    refine ⟨1428341263241801135082269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3808910035311469693552717 1428341263241801135082269)
                    ·
                      rfl

theorem cell22_4172527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 2, 4, 3].length) (baseStart_4172527 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4172527 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4172527 prefixEnd_4172527 := by exact prefixLift 4172527
  have htrace : WordTrace (prefixWord ++ tailWord_4172527) baseStart_4172527 baseEnd_4172527 := by
    simpa [prefixWord, tailWord_4172527, baseEnd_4172527] using wordTrace_append hprefix tailTrace_4172527
  have hstable : (prefixWord ++ tailWord_4172527).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4172527).length < 2 ^ (prefixWord ++ tailWord_4172527).sum := by decide
  have hdescent : baseEnd_4172527 < baseStart_4172527 := by decide
  rcases family_descends (prefixWord ++ tailWord_4172527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4172540 : List Nat := [2, 2, 2, 1, 3, 2, 10]
def baseStart_4172540 : Nat := 118140960795 + 4172540 * 2 ^ 59
def prefixEnd_4172540 : Nat := 4983230072969 + 3 ^ 40 * 4172540 * 2
def baseEnd_4172540 : Nat := 52901693089165682759527

theorem tailTrace_4172540 : CollatzResearch.WordTrace tailWord_4172540 prefixEnd_4172540 52901693089165682759527 := by
  unfold tailWord_4172540
  simp only [CollatzResearch.WordTrace]
  refine ⟨76092518151803833971541537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101456690869071778628722049 76092518151803833971541537)
  ·
    refine ⟨57069388613852875478656153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76092518151803833971541537 57069388613852875478656153)
    ·
      refine ⟨42802041460389656608992115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57069388613852875478656153 42802041460389656608992115)
      ·
        refine ⟨64203062190584484913488173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42802041460389656608992115 64203062190584484913488173)
        ·
          refine ⟨24076148321469181842558065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64203062190584484913488173 24076148321469181842558065)
          ·
            refine ⟨18057111241101886381918549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24076148321469181842558065 18057111241101886381918549)
            ·
              refine ⟨52901693089165682759527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 18057111241101886381918549 52901693089165682759527)
              ·
                rfl

theorem cell22_4172540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 10].length) (baseStart_4172540 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4172540 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4172540 prefixEnd_4172540 := by exact prefixLift 4172540
  have htrace : WordTrace (prefixWord ++ tailWord_4172540) baseStart_4172540 baseEnd_4172540 := by
    simpa [prefixWord, tailWord_4172540, baseEnd_4172540] using wordTrace_append hprefix tailTrace_4172540
  have hstable : (prefixWord ++ tailWord_4172540).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4172540).length < 2 ^ (prefixWord ++ tailWord_4172540).sum := by decide
  have hdescent : baseEnd_4172540 < baseStart_4172540 := by decide
  rcases family_descends (prefixWord ++ tailWord_4172540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4172617 : List Nat := [1, 2, 1, 1, 2, 6, 1, 1, 2, 5]
def baseStart_4172617 : Nat := 118140960795 + 4172617 * 2 ^ 59
def prefixEnd_4172617 : Nat := 4983230072969 + 3 ^ 40 * 4172617 * 2
def baseEnd_4172617 : Nat := 1428372072081070900331993

theorem tailTrace_4172617 : CollatzResearch.WordTrace tailWord_4172617 prefixEnd_4172617 1428372072081070900331993 := by
  unfold tailWord_4172617
  simp only [CollatzResearch.WordTrace]
  refine ⟨152187844724328710093636105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101458563149552473395757403 152187844724328710093636105)
  ·
    refine ⟨114140883543246532570227079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152187844724328710093636105 114140883543246532570227079)
    ·
      refine ⟨171211325314869798855340619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114140883543246532570227079 171211325314869798855340619)
      ·
        refine ⟨256816987972304698283010929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171211325314869798855340619 256816987972304698283010929)
        ·
          refine ⟨192612740979228523712258197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 256816987972304698283010929 192612740979228523712258197)
          ·
            refine ⟨9028722233401337049012103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 192612740979228523712258197 9028722233401337049012103)
            ·
              refine ⟨13543083350102005573518155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9028722233401337049012103 13543083350102005573518155)
              ·
                refine ⟨20314625025153008360277233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13543083350102005573518155 20314625025153008360277233)
                ·
                  refine ⟨15235968768864756270207925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20314625025153008360277233 15235968768864756270207925)
                  ·
                    refine ⟨1428372072081070900331993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15235968768864756270207925 1428372072081070900331993)
                    ·
                      rfl

theorem cell22_4172617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 1, 1, 2, 5].length) (baseStart_4172617 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4172617 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4172617 prefixEnd_4172617 := by exact prefixLift 4172617
  have htrace : WordTrace (prefixWord ++ tailWord_4172617) baseStart_4172617 baseEnd_4172617 := by
    simpa [prefixWord, tailWord_4172617, baseEnd_4172617] using wordTrace_append hprefix tailTrace_4172617
  have hstable : (prefixWord ++ tailWord_4172617).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4172617).length < 2 ^ (prefixWord ++ tailWord_4172617).sum := by decide
  have hdescent : baseEnd_4172617 < baseStart_4172617 := by decide
  rcases family_descends (prefixWord ++ tailWord_4172617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4172677 : List Nat := [1, 3, 1, 1, 3, 3, 1, 2, 1, 6]
def baseStart_4172677 : Nat := 118140960795 + 4172677 * 2 ^ 59
def prefixEnd_4172677 : Nat := 4983230072969 + 3 ^ 40 * 4172677 * 2
def baseEnd_4172677 : Nat := 1428392611307250743831809

theorem tailTrace_4172677 : CollatzResearch.WordTrace tailWord_4172677 prefixEnd_4172677 1428392611307250743831809 := by
  unfold tailWord_4172677
  simp only [CollatzResearch.WordTrace]
  refine ⟨152190033104111340340820285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101460022069407560227213523 152190033104111340340820285)
  ·
    refine ⟨57071262414041752627807607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152190033104111340340820285 57071262414041752627807607)
    ·
      refine ⟨85606893621062628941711411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57071262414041752627807607 85606893621062628941711411)
      ·
        refine ⟨128410340431593943412567117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85606893621062628941711411 128410340431593943412567117)
        ·
          refine ⟨48153877661847728779712669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 128410340431593943412567117 48153877661847728779712669)
          ·
            refine ⟨18057704123192898292392251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48153877661847728779712669 18057704123192898292392251)
            ·
              refine ⟨27086556184789347438588377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18057704123192898292392251 27086556184789347438588377)
              ·
                refine ⟨20314917138592010578941283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27086556184789347438588377 20314917138592010578941283)
                ·
                  refine ⟨30472375707888015868411925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20314917138592010578941283 30472375707888015868411925)
                  ·
                    refine ⟨1428392611307250743831809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30472375707888015868411925 1428392611307250743831809)
                    ·
                      rfl

theorem cell22_4172677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 2, 1, 6].length) (baseStart_4172677 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4172677 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4172677 prefixEnd_4172677 := by exact prefixLift 4172677
  have htrace : WordTrace (prefixWord ++ tailWord_4172677) baseStart_4172677 baseEnd_4172677 := by
    simpa [prefixWord, tailWord_4172677, baseEnd_4172677] using wordTrace_append hprefix tailTrace_4172677
  have hstable : (prefixWord ++ tailWord_4172677).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4172677).length < 2 ^ (prefixWord ++ tailWord_4172677).sum := by decide
  have hdescent : baseEnd_4172677 < baseStart_4172677 := by decide
  rcases family_descends (prefixWord ++ tailWord_4172677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4172679 : List Nat := [1, 1, 4, 2, 3, 1, 3, 1, 1, 5]
def baseStart_4172679 : Nat := 118140960795 + 4172679 * 2 ^ 59
def prefixEnd_4172679 : Nat := 4983230072969 + 3 ^ 40 * 4172679 * 2
def baseEnd_4172679 : Nat := 1428393295948123405281803

theorem tailTrace_4172679 : CollatzResearch.WordTrace tailWord_4172679 prefixEnd_4172679 1428393295948123405281803 := by
  unfold tailWord_4172679
  simp only [CollatzResearch.WordTrace]
  refine ⟨152190106050104094682393091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101460070700069396454928727 152190106050104094682393091)
  ·
    refine ⟨228285159075156142023589637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152190106050104094682393091 228285159075156142023589637)
    ·
      refine ⟨42803467326591776629423057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 228285159075156142023589637 42803467326591776629423057)
      ·
        refine ⟨32102600494943832472067293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42803467326591776629423057 32102600494943832472067293)
        ·
          refine ⟨12038475185603937177025235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32102600494943832472067293 12038475185603937177025235)
          ·
            refine ⟨18057712778405905765537853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12038475185603937177025235 18057712778405905765537853)
            ·
              refine ⟨6771642291902214662076695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18057712778405905765537853 6771642291902214662076695)
              ·
                refine ⟨10157463437853321993115043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6771642291902214662076695 10157463437853321993115043)
                ·
                  refine ⟨15236195156779982989672565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10157463437853321993115043 15236195156779982989672565)
                  ·
                    refine ⟨1428393295948123405281803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15236195156779982989672565 1428393295948123405281803)
                    ·
                      rfl

theorem cell22_4172679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 3, 1, 1, 5].length) (baseStart_4172679 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4172679 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4172679 prefixEnd_4172679 := by exact prefixLift 4172679
  have htrace : WordTrace (prefixWord ++ tailWord_4172679) baseStart_4172679 baseEnd_4172679 := by
    simpa [prefixWord, tailWord_4172679, baseEnd_4172679] using wordTrace_append hprefix tailTrace_4172679
  have hstable : (prefixWord ++ tailWord_4172679).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4172679).length < 2 ^ (prefixWord ++ tailWord_4172679).sum := by decide
  have hdescent : baseEnd_4172679 < baseStart_4172679 := by decide
  rcases family_descends (prefixWord ++ tailWord_4172679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4172698 : List Nat := [3, 1, 1, 4, 3, 2, 1, 3, 4]
def baseStart_4172698 : Nat := 118140960795 + 4172698 * 2 ^ 59
def prefixEnd_4172698 : Nat := 4983230072969 + 3 ^ 40 * 4172698 * 2
def baseEnd_4172698 : Nat := 476133266678804563018915

theorem tailTrace_4172698 : CollatzResearch.WordTrace tailWord_4172698 prefixEnd_4172698 476133266678804563018915 := by
  unfold tailWord_4172698
  simp only [CollatzResearch.WordTrace]
  refine ⟨38047699759258815231833687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101460532691356840618223165 38047699759258815231833687)
  ·
    refine ⟨57071549638888222847750531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38047699759258815231833687 57071549638888222847750531)
    ·
      refine ⟨85607324458332334271625797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57071549638888222847750531 85607324458332334271625797)
      ·
        refine ⟨16051373335937312675929837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 85607324458332334271625797 16051373335937312675929837)
        ·
          refine ⟨6019265000976492253473689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16051373335937312675929837 6019265000976492253473689)
          ·
            refine ⟨4514448750732369190105267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6019265000976492253473689 4514448750732369190105267)
            ·
              refine ⟨6771673126098553785157901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4514448750732369190105267 6771673126098553785157901)
              ·
                refine ⟨2539377422286957669434213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6771673126098553785157901 2539377422286957669434213)
                ·
                  refine ⟨476133266678804563018915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2539377422286957669434213 476133266678804563018915)
                  ·
                    rfl

theorem cell22_4172698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 2, 1, 3, 4].length) (baseStart_4172698 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4172698 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4172698 prefixEnd_4172698 := by exact prefixLift 4172698
  have htrace : WordTrace (prefixWord ++ tailWord_4172698) baseStart_4172698 baseEnd_4172698 := by
    simpa [prefixWord, tailWord_4172698, baseEnd_4172698] using wordTrace_append hprefix tailTrace_4172698
  have hstable : (prefixWord ++ tailWord_4172698).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4172698).length < 2 ^ (prefixWord ++ tailWord_4172698).sum := by decide
  have hdescent : baseEnd_4172698 < baseStart_4172698 := by decide
  rcases family_descends (prefixWord ++ tailWord_4172698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4172711 : List Nat := [1, 1, 6, 1, 3, 1, 1, 2, 2, 4]
def baseStart_4172711 : Nat := 118140960795 + 4172711 * 2 ^ 59
def prefixEnd_4172711 : Nat := 4983230072969 + 3 ^ 40 * 4172711 * 2
def baseEnd_4172711 : Nat := 1428404250202085988481705

theorem tailTrace_4172711 : CollatzResearch.WordTrace tailWord_4172711 prefixEnd_4172711 1428404250202085988481705 := by
  unfold tailWord_4172711
  simp only [CollatzResearch.WordTrace]
  refine ⟨152191273185988164147557987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101460848790658776098371991 152191273185988164147557987)
  ·
    refine ⟨228286909778982246221336981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152191273185988164147557987 228286909778982246221336981)
    ·
      refine ⟨10700948895889792791625171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 228286909778982246221336981 10700948895889792791625171)
      ·
        refine ⟨16051423343834689187437757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10700948895889792791625171 16051423343834689187437757)
        ·
          refine ⟨6019283753938008445289159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16051423343834689187437757 6019283753938008445289159)
          ·
            refine ⟨9028925630907012667933739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6019283753938008445289159 9028925630907012667933739)
            ·
              refine ⟨13543388446360519001900609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9028925630907012667933739 13543388446360519001900609)
              ·
                refine ⟨10157541334770389251425457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13543388446360519001900609 10157541334770389251425457)
                ·
                  refine ⟨7618156001077791938569093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10157541334770389251425457 7618156001077791938569093)
                  ·
                    refine ⟨1428404250202085988481705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7618156001077791938569093 1428404250202085988481705)
                    ·
                      rfl

theorem cell22_4172711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 1, 2, 2, 4].length) (baseStart_4172711 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4172711 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4172711 prefixEnd_4172711 := by exact prefixLift 4172711
  have htrace : WordTrace (prefixWord ++ tailWord_4172711) baseStart_4172711 baseEnd_4172711 := by
    simpa [prefixWord, tailWord_4172711, baseEnd_4172711] using wordTrace_append hprefix tailTrace_4172711
  have hstable : (prefixWord ++ tailWord_4172711).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4172711).length < 2 ^ (prefixWord ++ tailWord_4172711).sum := by decide
  have hdescent : baseEnd_4172711 < baseStart_4172711 := by decide
  rcases family_descends (prefixWord ++ tailWord_4172711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4172752 : List Nat := [2, 1, 1, 1, 1, 2, 3, 2, 4, 5]
def baseStart_4172752 : Nat := 118140960795 + 4172752 * 2 ^ 59
def prefixEnd_4172752 : Nat := 4983230072969 + 3 ^ 40 * 4172752 * 2
def baseEnd_4172752 : Nat := 1428418285339975548206579

theorem tailTrace_4172752 : CollatzResearch.WordTrace tailWord_4172752 prefixEnd_4172752 1428418285339975548206579 := by
  unfold tailWord_4172752
  simp only [CollatzResearch.WordTrace]
  refine ⟨76096384289419814074900255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101461845719226418766533673 76096384289419814074900255)
  ·
    refine ⟨114144576434129721112350383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76096384289419814074900255 114144576434129721112350383)
    ·
      refine ⟨171216864651194581668525575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114144576434129721112350383 171216864651194581668525575)
      ·
        refine ⟨256825296976791872502788363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171216864651194581668525575 256825296976791872502788363)
        ·
          refine ⟨385237945465187808754182545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 256825296976791872502788363 385237945465187808754182545)
          ·
            refine ⟨288928459098890856565636909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 385237945465187808754182545 288928459098890856565636909)
            ·
              refine ⟨108348172162084071212113841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 288928459098890856565636909 108348172162084071212113841)
              ·
                refine ⟨81261129121563053409085381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 108348172162084071212113841 81261129121563053409085381)
                ·
                  refine ⟨15236461710293072514203509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 81261129121563053409085381 15236461710293072514203509)
                  ·
                    refine ⟨1428418285339975548206579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15236461710293072514203509 1428418285339975548206579)
                    ·
                      rfl

theorem cell22_4172752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 2, 4, 5].length) (baseStart_4172752 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4172752 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4172752 prefixEnd_4172752 := by exact prefixLift 4172752
  have htrace : WordTrace (prefixWord ++ tailWord_4172752) baseStart_4172752 baseEnd_4172752 := by
    simpa [prefixWord, tailWord_4172752, baseEnd_4172752] using wordTrace_append hprefix tailTrace_4172752
  have hstable : (prefixWord ++ tailWord_4172752).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4172752).length < 2 ^ (prefixWord ++ tailWord_4172752).sum := by decide
  have hdescent : baseEnd_4172752 < baseStart_4172752 := by decide
  rcases family_descends (prefixWord ++ tailWord_4172752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4172775 : List Nat := [1, 1, 5, 2, 2, 1, 4, 2, 1, 3]
def baseStart_4172775 : Nat := 118140960795 + 4172775 * 2 ^ 59
def prefixEnd_4172775 : Nat := 4983230072969 + 3 ^ 40 * 4172775 * 2
def baseEnd_4172775 : Nat := 1428426158710011154881509

theorem tailTrace_4172775 : CollatzResearch.WordTrace tailWord_4172775 prefixEnd_4172775 1428426158710011154881509 := by
  unfold tailWord_4172775
  simp only [CollatzResearch.WordTrace]
  refine ⟨152193607457756303077887779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101462404971837535385258519 152193607457756303077887779)
  ·
    refine ⟨228290411186634454616831669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152193607457756303077887779 228290411186634454616831669)
    ·
      refine ⟨21402226048746980120327969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 228290411186634454616831669 21402226048746980120327969)
      ·
        refine ⟨16051669536560235090245977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21402226048746980120327969 16051669536560235090245977)
        ·
          refine ⟨12038752152420176317684483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16051669536560235090245977 12038752152420176317684483)
          ·
            refine ⟨18058128228630264476526725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12038752152420176317684483 18058128228630264476526725)
            ·
              refine ⟨3385899042868174589348761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18058128228630264476526725 3385899042868174589348761)
              ·
                refine ⟨2539424282151130942011571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3385899042868174589348761 2539424282151130942011571)
                ·
                  refine ⟨3809136423226696413017357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2539424282151130942011571 3809136423226696413017357)
                  ·
                    refine ⟨1428426158710011154881509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3809136423226696413017357 1428426158710011154881509)
                    ·
                      rfl

theorem cell22_4172775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 4, 2, 1, 3].length) (baseStart_4172775 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4172775 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4172775 prefixEnd_4172775 := by exact prefixLift 4172775
  have htrace : WordTrace (prefixWord ++ tailWord_4172775) baseStart_4172775 baseEnd_4172775 := by
    simpa [prefixWord, tailWord_4172775, baseEnd_4172775] using wordTrace_append hprefix tailTrace_4172775
  have hstable : (prefixWord ++ tailWord_4172775).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4172775).length < 2 ^ (prefixWord ++ tailWord_4172775).sum := by decide
  have hdescent : baseEnd_4172775 < baseStart_4172775 := by decide
  rcases family_descends (prefixWord ++ tailWord_4172775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4172831 : List Nat := [1, 1, 2, 4, 1, 4, 1, 1, 4, 3]
def baseStart_4172831 : Nat := 118140960795 + 4172831 * 2 ^ 59
def prefixEnd_4172831 : Nat := 4983230072969 + 3 ^ 40 * 4172831 * 2
def baseEnd_4172831 : Nat := 1428445328654445675481337

theorem tailTrace_4172831 : CollatzResearch.WordTrace tailWord_4172831 prefixEnd_4172831 1428445328654445675481337 := by
  unfold tailWord_4172831
  simp only [CollatzResearch.WordTrace]
  refine ⟨152195649945553424641926347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101463766630368949761284231 152195649945553424641926347)
  ·
    refine ⟨228293474918330136962889521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152195649945553424641926347 228293474918330136962889521)
    ·
      refine ⟨171220106188747602722167141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 228293474918330136962889521 171220106188747602722167141)
      ·
        refine ⟨32103769910390175510406339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 171220106188747602722167141 32103769910390175510406339)
        ·
          refine ⟨48155654865585263265609509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32103769910390175510406339 48155654865585263265609509)
          ·
            refine ⟨9029185287297236862301783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48155654865585263265609509 9029185287297236862301783)
            ·
              refine ⟨13543777930945855293452675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9029185287297236862301783 13543777930945855293452675)
              ·
                refine ⟨20315666896418782940179013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13543777930945855293452675 20315666896418782940179013)
                ·
                  refine ⟨3809187543078521801283565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20315666896418782940179013 3809187543078521801283565)
                  ·
                    refine ⟨1428445328654445675481337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3809187543078521801283565 1428445328654445675481337)
                    ·
                      rfl

theorem cell22_4172831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 1, 1, 4, 3].length) (baseStart_4172831 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4172831 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4172831 prefixEnd_4172831 := by exact prefixLift 4172831
  have htrace : WordTrace (prefixWord ++ tailWord_4172831) baseStart_4172831 baseEnd_4172831 := by
    simpa [prefixWord, tailWord_4172831, baseEnd_4172831] using wordTrace_append hprefix tailTrace_4172831
  have hstable : (prefixWord ++ tailWord_4172831).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4172831).length < 2 ^ (prefixWord ++ tailWord_4172831).sum := by decide
  have hdescent : baseEnd_4172831 < baseStart_4172831 := by decide
  rcases family_descends (prefixWord ++ tailWord_4172831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4172848 : List Nat := [2, 1, 1, 1, 2, 4, 5, 1, 2, 3]
def baseStart_4172848 : Nat := 118140960795 + 4172848 * 2 ^ 59
def prefixEnd_4172848 : Nat := 4983230072969 + 3 ^ 40 * 4172848 * 2
def baseEnd_4172848 : Nat := 1428451148101863297806285

theorem tailTrace_4172848 : CollatzResearch.WordTrace tailWord_4172848 prefixEnd_4172848 1428451148101863297806285 := by
  unfold tailWord_4172848
  simp only [CollatzResearch.WordTrace]
  refine ⟨76098134993245918272647599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101464179990994557696863465 76098134993245918272647599)
  ·
    refine ⟨114147202489868877408971399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76098134993245918272647599 114147202489868877408971399)
    ·
      refine ⟨171220803734803316113457099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114147202489868877408971399 171220803734803316113457099)
      ·
        refine ⟨256831205602204974170185649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171220803734803316113457099 256831205602204974170185649)
        ·
          refine ⟨192623404201653730627639237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 256831205602204974170185649 192623404201653730627639237)
          ·
            refine ⟨36116888287810074492682357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 192623404201653730627639237 36116888287810074492682357)
            ·
              refine ⟨3385958276982194483688971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 36116888287810074492682357 3385958276982194483688971)
              ·
                refine ⟨5078937415473291725533457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3385958276982194483688971 5078937415473291725533457)
                ·
                  refine ⟨3809203061604968794150093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5078937415473291725533457 3809203061604968794150093)
                  ·
                    refine ⟨1428451148101863297806285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3809203061604968794150093 1428451148101863297806285)
                    ·
                      rfl

theorem cell22_4172848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 5, 1, 2, 3].length) (baseStart_4172848 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4172848 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4172848 prefixEnd_4172848 := by exact prefixLift 4172848
  have htrace : WordTrace (prefixWord ++ tailWord_4172848) baseStart_4172848 baseEnd_4172848 := by
    simpa [prefixWord, tailWord_4172848, baseEnd_4172848] using wordTrace_append hprefix tailTrace_4172848
  have hstable : (prefixWord ++ tailWord_4172848).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4172848).length < 2 ^ (prefixWord ++ tailWord_4172848).sum := by decide
  have hdescent : baseEnd_4172848 < baseStart_4172848 := by decide
  rcases family_descends (prefixWord ++ tailWord_4172848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4172861 : List Nat := [1, 4, 1, 3, 1, 2, 4, 6]
def baseStart_4172861 : Nat := 118140960795 + 4172861 * 2 ^ 59
def prefixEnd_4172861 : Nat := 4983230072969 + 3 ^ 40 * 4172861 * 2
def baseEnd_4172861 : Nat := 158717288696392844136805

theorem tailTrace_4172861 : CollatzResearch.WordTrace tailWord_4172861 prefixEnd_4172861 158717288696392844136805 := by
  unfold tailWord_4172861
  simp only [CollatzResearch.WordTrace]
  refine ⟨152196744135444739765518437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101464496090296493177012291 152196744135444739765518437)
  ·
    refine ⟨28536889525395888706034707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 152196744135444739765518437 28536889525395888706034707)
    ·
      refine ⟨42805334288093833059052061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28536889525395888706034707 42805334288093833059052061)
      ·
        refine ⟨16052000358035187397144523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42805334288093833059052061 16052000358035187397144523)
        ·
          refine ⟨24078000537052781095716785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16052000358035187397144523 24078000537052781095716785)
          ·
            refine ⟨18058500402789585821787589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24078000537052781095716785 18058500402789585821787589)
            ·
              refine ⟨3385968825523047341585173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18058500402789585821787589 3385968825523047341585173)
              ·
                refine ⟨158717288696392844136805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3385968825523047341585173 158717288696392844136805)
                ·
                  rfl

theorem cell22_4172861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 4, 6].length) (baseStart_4172861 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4172861 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4172861 prefixEnd_4172861 := by exact prefixLift 4172861
  have htrace : WordTrace (prefixWord ++ tailWord_4172861) baseStart_4172861 baseEnd_4172861 := by
    simpa [prefixWord, tailWord_4172861, baseEnd_4172861] using wordTrace_append hprefix tailTrace_4172861
  have hstable : (prefixWord ++ tailWord_4172861).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4172861).length < 2 ^ (prefixWord ++ tailWord_4172861).sum := by decide
  have hdescent : baseEnd_4172861 < baseStart_4172861 := by decide
  rcases family_descends (prefixWord ++ tailWord_4172861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4172979 : List Nat := [1, 1, 1, 2, 3, 2, 2, 10]
def baseStart_4172979 : Nat := 118140960795 + 4172979 * 2 ^ 59
def prefixEnd_4172979 : Nat := 4983230072969 + 3 ^ 40 * 4172979 * 2
def baseEnd_4172979 : Nat := 158721776897669180308987

theorem tailTrace_4172979 : CollatzResearch.WordTrace tailWord_4172979 prefixEnd_4172979 158721776897669180308987 := by
  unfold tailWord_4172979
  simp only [CollatzResearch.WordTrace]
  refine ⟨152201047949017245918313991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101467365299344830612209327 152201047949017245918313991)
  ·
    refine ⟨228301571923525868877470987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152201047949017245918313991 228301571923525868877470987)
    ·
      refine ⟨342452357885288803316206481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228301571923525868877470987 342452357885288803316206481)
      ·
        refine ⟨256839268413966602487154861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 342452357885288803316206481 256839268413966602487154861)
        ·
          refine ⟨96314725655237475932683073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 256839268413966602487154861 96314725655237475932683073)
          ·
            refine ⟨72236044241428106949512305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96314725655237475932683073 72236044241428106949512305)
            ·
              refine ⟨54177033181071080212134229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72236044241428106949512305 54177033181071080212134229)
              ·
                refine ⟨158721776897669180308987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 54177033181071080212134229 158721776897669180308987)
                ·
                  rfl

theorem cell22_4172979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 10].length) (baseStart_4172979 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4172979 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4172979 prefixEnd_4172979 := by exact prefixLift 4172979
  have htrace : WordTrace (prefixWord ++ tailWord_4172979) baseStart_4172979 baseEnd_4172979 := by
    simpa [prefixWord, tailWord_4172979, baseEnd_4172979] using wordTrace_append hprefix tailTrace_4172979
  have hstable : (prefixWord ++ tailWord_4172979).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4172979).length < 2 ^ (prefixWord ++ tailWord_4172979).sum := by decide
  have hdescent : baseEnd_4172979 < baseStart_4172979 := by decide
  rcases family_descends (prefixWord ++ tailWord_4172979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4173011 : List Nat := [1, 1, 1, 2, 1, 1, 1, 4, 7, 3]
def baseStart_4173011 : Nat := 118140960795 + 4173011 * 2 ^ 59
def prefixEnd_4173011 : Nat := 4983230072969 + 3 ^ 40 * 4173011 * 2
def baseEnd_4173011 : Nat := 1428506946332985205980785

theorem tailTrace_4173011 : CollatzResearch.WordTrace tailWord_4173011 prefixEnd_4173011 1428506946332985205980785 := by
  unfold tailWord_4173011
  simp only [CollatzResearch.WordTrace]
  refine ⟨152202215084901315383478887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101468143389934210255652591 152202215084901315383478887)
  ·
    refine ⟨228303322627351973075218331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152202215084901315383478887 228303322627351973075218331)
    ·
      refine ⟨342454983941027959612827497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228303322627351973075218331 342454983941027959612827497)
      ·
        refine ⟨256841237955770969709620623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 342454983941027959612827497 256841237955770969709620623)
        ·
          refine ⟨385261856933656454564430935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 256841237955770969709620623 385261856933656454564430935)
          ·
            refine ⟨577892785400484681846646403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 385261856933656454564430935 577892785400484681846646403)
            ·
              refine ⟨866839178100727022769969605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 577892785400484681846646403 866839178100727022769969605)
              ·
                refine ⟨162532345893886316769369301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 866839178100727022769969605 162532345893886316769369301)
                ·
                  refine ⟨3809351856887960549282093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 162532345893886316769369301 3809351856887960549282093)
                  ·
                    refine ⟨1428506946332985205980785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3809351856887960549282093 1428506946332985205980785)
                    ·
                      rfl

theorem cell22_4173011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 4, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 4, 7, 3].length) (baseStart_4173011 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4173011 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4173011 prefixEnd_4173011 := by exact prefixLift 4173011
  have htrace : WordTrace (prefixWord ++ tailWord_4173011) baseStart_4173011 baseEnd_4173011 := by
    simpa [prefixWord, tailWord_4173011, baseEnd_4173011] using wordTrace_append hprefix tailTrace_4173011
  have hstable : (prefixWord ++ tailWord_4173011).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4173011).length < 2 ^ (prefixWord ++ tailWord_4173011).sum := by decide
  have hdescent : baseEnd_4173011 < baseStart_4173011 := by decide
  rcases family_descends (prefixWord ++ tailWord_4173011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4173028 : List Nat := [2, 3, 1, 1, 1, 2, 4, 2, 3, 3]
def baseStart_4173028 : Nat := 118140960795 + 4173028 * 2 ^ 59
def prefixEnd_4173028 : Nat := 4983230072969 + 3 ^ 40 * 4173028 * 2
def baseEnd_4173028 : Nat := 1428512765780402828305733

theorem tailTrace_4173028 : CollatzResearch.WordTrace tailWord_4173028 prefixEnd_4173028 1428512765780402828305733 := by
  unfold tailWord_4173028
  simp only [CollatzResearch.WordTrace]
  refine ⟨76101417562919863643423869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101468556750559818191231825 76101417562919863643423869)
  ·
    refine ⟨28538031586094948866283951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76101417562919863643423869 28538031586094948866283951)
    ·
      refine ⟨42807047379142423299425927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28538031586094948866283951 42807047379142423299425927)
      ·
        refine ⟨64210571068713634949138891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42807047379142423299425927 64210571068713634949138891)
        ·
          refine ⟨96315856603070452423708337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64210571068713634949138891 96315856603070452423708337)
          ·
            refine ⟨72236892452302839317781253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96315856603070452423708337 72236892452302839317781253)
            ·
              refine ⟨13544417334806782372083985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 72236892452302839317781253 13544417334806782372083985)
              ·
                refine ⟨10158313001105086779062989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13544417334806782372083985 10158313001105086779062989)
                ·
                  refine ⟨3809367375414407542148621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10158313001105086779062989 3809367375414407542148621)
                  ·
                    refine ⟨1428512765780402828305733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3809367375414407542148621 1428512765780402828305733)
                    ·
                      rfl

theorem cell22_4173028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 4, 2, 3, 3].length) (baseStart_4173028 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4173028 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4173028 prefixEnd_4173028 := by exact prefixLift 4173028
  have htrace : WordTrace (prefixWord ++ tailWord_4173028) baseStart_4173028 baseEnd_4173028 := by
    simpa [prefixWord, tailWord_4173028, baseEnd_4173028] using wordTrace_append hprefix tailTrace_4173028
  have hstable : (prefixWord ++ tailWord_4173028).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4173028).length < 2 ^ (prefixWord ++ tailWord_4173028).sum := by decide
  have hdescent : baseEnd_4173028 < baseStart_4173028 := by decide
  rcases family_descends (prefixWord ++ tailWord_4173028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4173103 : List Nat := [1, 1, 2, 1, 2, 1, 3, 7, 4]
def baseStart_4173103 : Nat := 118140960795 + 4173103 * 2 ^ 59
def prefixEnd_4173103 : Nat := 4983230072969 + 3 ^ 40 * 4173103 * 2
def baseEnd_4173103 : Nat := 476179479937709210893501

theorem tailTrace_4173103 : CollatzResearch.WordTrace tailWord_4173103 prefixEnd_4173103 476179479937709210893501 := by
  unfold tailWord_4173103
  simp only [CollatzResearch.WordTrace]
  refine ⟨152205570600568015095827963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101470380400378676730551975 152205570600568015095827963)
  ·
    refine ⟨228308355900852022643741945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152205570600568015095827963 228308355900852022643741945)
    ·
      refine ⟨171231266925639016982806459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 228308355900852022643741945 171231266925639016982806459)
      ·
        refine ⟨256846900388458525474209689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171231266925639016982806459 256846900388458525474209689)
        ·
          refine ⟨192635175291343894105657267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 256846900388458525474209689 192635175291343894105657267)
          ·
            refine ⟨288952762937015841158485901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192635175291343894105657267 288952762937015841158485901)
            ·
              refine ⟨108357286101380940434432213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 288952762937015841158485901 108357286101380940434432213)
              ·
                refine ⟨2539623893001115791432005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 108357286101380940434432213 2539623893001115791432005)
                ·
                  refine ⟨476179479937709210893501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2539623893001115791432005 476179479937709210893501)
                  ·
                    rfl

theorem cell22_4173103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 7, 4].length) (baseStart_4173103 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4173103 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4173103 prefixEnd_4173103 := by exact prefixLift 4173103
  have htrace : WordTrace (prefixWord ++ tailWord_4173103) baseStart_4173103 baseEnd_4173103 := by
    simpa [prefixWord, tailWord_4173103, baseEnd_4173103] using wordTrace_append hprefix tailTrace_4173103
  have hstable : (prefixWord ++ tailWord_4173103).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4173103).length < 2 ^ (prefixWord ++ tailWord_4173103).sum := by decide
  have hdescent : baseEnd_4173103 < baseStart_4173103 := by decide
  rcases family_descends (prefixWord ++ tailWord_4173103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4173118 : List Nat := [4, 2, 1, 2, 1, 1, 1, 2, 3, 5]
def baseStart_4173118 : Nat := 118140960795 + 4173118 * 2 ^ 59
def prefixEnd_4173118 : Nat := 4983230072969 + 3 ^ 40 * 4173118 * 2
def baseEnd_4173118 : Nat := 1428543574619672593555457

theorem tailTrace_4173118 : CollatzResearch.WordTrace tailWord_4173118 prefixEnd_4173118 1428543574619672593555457 := by
  unfold tailWord_4173118
  simp only [CollatzResearch.WordTrace]
  refine ⟨19025764711939209082203001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 101470745130342448438416005 19025764711939209082203001)
  ·
    refine ⟨14269323533954406811652251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19025764711939209082203001 14269323533954406811652251)
    ·
      refine ⟨21403985300931610217478377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14269323533954406811652251 21403985300931610217478377)
      ·
        refine ⟨16052988975698707663108783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21403985300931610217478377 16052988975698707663108783)
        ·
          refine ⟨24079483463548061494663175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16052988975698707663108783 24079483463548061494663175)
          ·
            refine ⟨36119225195322092241994763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24079483463548061494663175 36119225195322092241994763)
            ·
              refine ⟨54178837792983138362992145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36119225195322092241994763 54178837792983138362992145)
              ·
                refine ⟨40634128344737353772244109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54178837792983138362992145 40634128344737353772244109)
                ·
                  refine ⟨15237798129276507664591541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40634128344737353772244109 15237798129276507664591541)
                  ·
                    refine ⟨1428543574619672593555457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15237798129276507664591541 1428543574619672593555457)
                    ·
                      rfl

theorem cell22_4173118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 2, 3, 5].length) (baseStart_4173118 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4173118 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4173118 prefixEnd_4173118 := by exact prefixLift 4173118
  have htrace : WordTrace (prefixWord ++ tailWord_4173118) baseStart_4173118 baseEnd_4173118 := by
    simpa [prefixWord, tailWord_4173118, baseEnd_4173118] using wordTrace_append hprefix tailTrace_4173118
  have hstable : (prefixWord ++ tailWord_4173118).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4173118).length < 2 ^ (prefixWord ++ tailWord_4173118).sum := by decide
  have hdescent : baseEnd_4173118 < baseStart_4173118 := by decide
  rcases family_descends (prefixWord ++ tailWord_4173118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4173161 : List Nat := [1, 2, 1, 1, 1, 3, 2, 2, 1, 8]
def baseStart_4173161 : Nat := 118140960795 + 4173161 * 2 ^ 59
def prefixEnd_4173161 : Nat := 4983230072969 + 3 ^ 40 * 4173161 * 2
def baseEnd_4173161 : Nat := 1428558294398434814730325

theorem tailTrace_4173161 : CollatzResearch.WordTrace tailWord_4173161 prefixEnd_4173161 1428558294398434814730325 := by
  unfold tailWord_4173161
  simp only [CollatzResearch.WordTrace]
  refine ⟨152207686034357891001439337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101471790689571927334292891 152207686034357891001439337)
  ·
    refine ⟨114155764525768418251079503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152207686034357891001439337 114155764525768418251079503)
    ·
      refine ⟨171233646788652627376619255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114155764525768418251079503 171233646788652627376619255)
      ·
        refine ⟨256850470182978941064928883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171233646788652627376619255 256850470182978941064928883)
        ·
          refine ⟨385275705274468411597393325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 256850470182978941064928883 385275705274468411597393325)
          ·
            refine ⟨144478389477925654349022497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 385275705274468411597393325 144478389477925654349022497)
            ·
              refine ⟨108358792108444240761766873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 144478389477925654349022497 108358792108444240761766873)
              ·
                refine ⟨81269094081333180571325155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 108358792108444240761766873 81269094081333180571325155)
                ·
                  refine ⟨121903641121999770856987733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 81269094081333180571325155 121903641121999770856987733)
                  ·
                    refine ⟨1428558294398434814730325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 121903641121999770856987733 1428558294398434814730325)
                    ·
                      rfl

theorem cell22_4173161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 2, 1, 8].length) (baseStart_4173161 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4173161 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4173161 prefixEnd_4173161 := by exact prefixLift 4173161
  have htrace : WordTrace (prefixWord ++ tailWord_4173161) baseStart_4173161 baseEnd_4173161 := by
    simpa [prefixWord, tailWord_4173161, baseEnd_4173161] using wordTrace_append hprefix tailTrace_4173161
  have hstable : (prefixWord ++ tailWord_4173161).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4173161).length < 2 ^ (prefixWord ++ tailWord_4173161).sum := by decide
  have hdescent : baseEnd_4173161 < baseStart_4173161 := by decide
  rcases family_descends (prefixWord ++ tailWord_4173161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4173180 : List Nat := [2, 2, 2, 1, 1, 1, 6, 1, 3, 3]
def baseStart_4173180 : Nat := 118140960795 + 4173180 * 2 ^ 59
def prefixEnd_4173180 : Nat := 4983230072969 + 3 ^ 40 * 4173180 * 2
def baseEnd_4173180 : Nat := 1428564798486725098505267

theorem tailTrace_4173180 : CollatzResearch.WordTrace tailWord_4173180 prefixEnd_4173180 1428564798486725098505267 := by
  unfold tailWord_4173180
  simp only [CollatzResearch.WordTrace]
  refine ⟨76104189510644528623190497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101472252680859371497587329 76104189510644528623190497)
  ·
    refine ⟨57078142132983396467392873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76104189510644528623190497 57078142132983396467392873)
    ·
      refine ⟨42808606599737547350544655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57078142132983396467392873 42808606599737547350544655)
      ·
        refine ⟨64212909899606321025816983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42808606599737547350544655 64212909899606321025816983)
        ·
          refine ⟨96319364849409481538725475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64212909899606321025816983 96319364849409481538725475)
          ·
            refine ⟨144479047274114222308088213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96319364849409481538725475 144479047274114222308088213)
            ·
              refine ⟨6772455340974104170691635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 144479047274114222308088213 6772455340974104170691635)
              ·
                refine ⟨10158683011461156256037453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6772455340974104170691635 10158683011461156256037453)
                ·
                  refine ⟨3809506129297933596014045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10158683011461156256037453 3809506129297933596014045)
                  ·
                    refine ⟨1428564798486725098505267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3809506129297933596014045 1428564798486725098505267)
                    ·
                      rfl

theorem cell22_4173180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 6, 1, 3, 3].length) (baseStart_4173180 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4173180 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4173180 prefixEnd_4173180 := by exact prefixLift 4173180
  have htrace : WordTrace (prefixWord ++ tailWord_4173180) baseStart_4173180 baseEnd_4173180 := by
    simpa [prefixWord, tailWord_4173180, baseEnd_4173180] using wordTrace_append hprefix tailTrace_4173180
  have hstable : (prefixWord ++ tailWord_4173180).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4173180).length < 2 ^ (prefixWord ++ tailWord_4173180).sum := by decide
  have hdescent : baseEnd_4173180 < baseStart_4173180 := by decide
  rcases family_descends (prefixWord ++ tailWord_4173180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4173186 : List Nat := [3, 4, 2, 1, 1, 2, 3, 1, 2, 3]
def baseStart_4173186 : Nat := 118140960795 + 4173186 * 2 ^ 59
def prefixEnd_4173186 : Nat := 4983230072969 + 3 ^ 40 * 4173186 * 2
def baseEnd_4173186 : Nat := 1428566852409343082855249

theorem tailTrace_4173186 : CollatzResearch.WordTrace tailWord_4173186 prefixEnd_4173186 1428566852409343082855249 := by
  unfold tailWord_4173186
  simp only [CollatzResearch.WordTrace]
  refine ⟨38052149464816830067774853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101472398572844880180732941 38052149464816830067774853)
  ·
    refine ⟨7134778024653155637707785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38052149464816830067774853 7134778024653155637707785)
    ·
      refine ⟨5351083518489866728280839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7134778024653155637707785 5351083518489866728280839)
      ·
        refine ⟨8026625277734800092421259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5351083518489866728280839 8026625277734800092421259)
        ·
          refine ⟨12039937916602200138631889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8026625277734800092421259 12039937916602200138631889)
          ·
            refine ⟨9029953437451650103973917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12039937916602200138631889 9029953437451650103973917)
            ·
              refine ⟨3386232539044368788990219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9029953437451650103973917 3386232539044368788990219)
              ·
                refine ⟨5079348808566553183485329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3386232539044368788990219 5079348808566553183485329)
                ·
                  refine ⟨3809511606424914887613997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5079348808566553183485329 3809511606424914887613997)
                  ·
                    refine ⟨1428566852409343082855249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3809511606424914887613997 1428566852409343082855249)
                    ·
                      rfl

theorem cell22_4173186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 3, 1, 2, 3].length) (baseStart_4173186 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4173186 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4173186 prefixEnd_4173186 := by exact prefixLift 4173186
  have htrace : WordTrace (prefixWord ++ tailWord_4173186) baseStart_4173186 baseEnd_4173186 := by
    simpa [prefixWord, tailWord_4173186, baseEnd_4173186] using wordTrace_append hprefix tailTrace_4173186
  have hstable : (prefixWord ++ tailWord_4173186).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4173186).length < 2 ^ (prefixWord ++ tailWord_4173186).sum := by decide
  have hdescent : baseEnd_4173186 < baseStart_4173186 := by decide
  rcases family_descends (prefixWord ++ tailWord_4173186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4173244 : List Nat := [2, 2, 2, 4, 2, 2, 2, 1, 5]
def baseStart_4173244 : Nat := 118140960795 + 4173244 * 2 ^ 59
def prefixEnd_4173244 : Nat := 4983230072969 + 3 ^ 40 * 4173244 * 2
def baseEnd_4173244 : Nat := 476195568998216754968357

theorem tailTrace_4173244 : CollatzResearch.WordTrace tailWord_4173244 prefixEnd_4173244 476195568998216754968357 := by
  unfold tailWord_4173244
  simp only [CollatzResearch.WordTrace]
  refine ⟨76105356646528598088355393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101473808862038130784473857 76105356646528598088355393)
  ·
    refine ⟨57079017484896448566266545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76105356646528598088355393 57079017484896448566266545)
    ·
      refine ⟨42809263113672336424699909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57079017484896448566266545 42809263113672336424699909)
      ·
        refine ⟨8026736833813563079631233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42809263113672336424699909 8026736833813563079631233)
        ·
          refine ⟨6020052625360172309723425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8026736833813563079631233 6020052625360172309723425)
          ·
            refine ⟨4515039469020129232292569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6020052625360172309723425 4515039469020129232292569)
            ·
              refine ⟨3386279601765096924219427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4515039469020129232292569 3386279601765096924219427)
              ·
                refine ⟨5079419402647645386329141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3386279601765096924219427 5079419402647645386329141)
                ·
                  refine ⟨476195568998216754968357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5079419402647645386329141 476195568998216754968357)
                  ·
                    rfl

theorem cell22_4173244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 2, 2, 1, 5].length) (baseStart_4173244 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4173244 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4173244 prefixEnd_4173244 := by exact prefixLift 4173244
  have htrace : WordTrace (prefixWord ++ tailWord_4173244) baseStart_4173244 baseEnd_4173244 := by
    simpa [prefixWord, tailWord_4173244, baseEnd_4173244] using wordTrace_append hprefix tailTrace_4173244
  have hstable : (prefixWord ++ tailWord_4173244).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4173244).length < 2 ^ (prefixWord ++ tailWord_4173244).sum := by decide
  have hdescent : baseEnd_4173244 < baseStart_4173244 := by decide
  rcases family_descends (prefixWord ++ tailWord_4173244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4173283 : List Nat := [1, 1, 1, 6, 2, 11]
def baseStart_4173283 : Nat := 118140960795 + 4173283 * 2 ^ 59
def prefixEnd_4173283 : Nat := 4983230072969 + 3 ^ 40 * 4173283 * 2
def baseEnd_4173283 : Nat := 17637037746810705718271

theorem tailTrace_4173283 : CollatzResearch.WordTrace tailWord_4173283 prefixEnd_4173283 17637037746810705718271 := by
  unfold tailWord_4173283
  simp only [CollatzResearch.WordTrace]
  refine ⟨152212135739915905837380503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101474757159943937224920335 152212135739915905837380503)
  ·
    refine ⟨228318203609873858756070755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152212135739915905837380503 228318203609873858756070755)
    ·
      refine ⟨342477305414810788134106133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228318203609873858756070755 342477305414810788134106133)
      ·
        refine ⟨16053623691319255693786225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 342477305414810788134106133 16053623691319255693786225)
        ·
          refine ⟨12040217768489441770339669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16053623691319255693786225 12040217768489441770339669)
          ·
            refine ⟨17637037746810705718271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 12040217768489441770339669 17637037746810705718271)
            ·
              rfl

theorem cell22_4173283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 11].length) (baseStart_4173283 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4173283 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4173283 prefixEnd_4173283 := by exact prefixLift 4173283
  have htrace : WordTrace (prefixWord ++ tailWord_4173283) baseStart_4173283 baseEnd_4173283 := by
    simpa [prefixWord, tailWord_4173283, baseEnd_4173283] using wordTrace_append hprefix tailTrace_4173283
  have hstable : (prefixWord ++ tailWord_4173283).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4173283).length < 2 ^ (prefixWord ++ tailWord_4173283).sum := by decide
  have hdescent : baseEnd_4173283 < baseStart_4173283 := by decide
  rcases family_descends (prefixWord ++ tailWord_4173283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4173287 : List Nat := [1, 1, 5, 2, 1, 2, 1, 4, 2, 3]
def baseStart_4173287 : Nat := 118140960795 + 4173287 * 2 ^ 59
def prefixEnd_4173287 : Nat := 4983230072969 + 3 ^ 40 * 4173287 * 2
def baseEnd_4173287 : Nat := 1428601426773412486079939

theorem tailTrace_4173287 : CollatzResearch.WordTrace tailWord_4173287 prefixEnd_4173287 1428601426773412486079939 := by
  unfold tailWord_4173287
  simp only [CollatzResearch.WordTrace]
  refine ⟨152212281631901414520526115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101474854421267609680350743 152212281631901414520526115)
  ·
    refine ⟨228318422447852121780789173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152212281631901414520526115 228318422447852121780789173)
    ·
      refine ⟨21404852104486136416948985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 228318422447852121780789173 21404852104486136416948985)
      ·
        refine ⟨16053639078364602312711739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21404852104486136416948985 16053639078364602312711739)
        ·
          refine ⟨24080458617546903469067609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16053639078364602312711739 24080458617546903469067609)
          ·
            refine ⟨18060343963160177601800707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24080458617546903469067609 18060343963160177601800707)
            ·
              refine ⟨27090515944740266402701061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18060343963160177601800707 27090515944740266402701061)
              ·
                refine ⟨5079471739638799950506449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27090515944740266402701061 5079471739638799950506449)
                ·
                  refine ⟨3809603804729099962879837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5079471739638799950506449 3809603804729099962879837)
                  ·
                    refine ⟨1428601426773412486079939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3809603804729099962879837 1428601426773412486079939)
                    ·
                      rfl

theorem cell22_4173287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 4, 2, 3].length) (baseStart_4173287 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4173287 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4173287 prefixEnd_4173287 := by exact prefixLift 4173287
  have htrace : WordTrace (prefixWord ++ tailWord_4173287) baseStart_4173287 baseEnd_4173287 := by
    simpa [prefixWord, tailWord_4173287, baseEnd_4173287] using wordTrace_append hprefix tailTrace_4173287
  have hstable : (prefixWord ++ tailWord_4173287).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4173287).length < 2 ^ (prefixWord ++ tailWord_4173287).sum := by decide
  have hdescent : baseEnd_4173287 < baseStart_4173287 := by decide
  rcases family_descends (prefixWord ++ tailWord_4173287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4173325 : List Nat := [1, 7, 1, 1, 3, 1, 2, 1, 1, 4]
def baseStart_4173325 : Nat := 118140960795 + 4173325 * 2 ^ 59
def prefixEnd_4173325 : Nat := 4983230072969 + 3 ^ 40 * 4173325 * 2
def baseEnd_4173325 : Nat := 1428614434949993053629823

theorem tailTrace_4173325 : CollatzResearch.WordTrace tailWord_4173325 prefixEnd_4173325 1428614434949993053629823 := by
  unfold tailWord_4173325
  simp only [CollatzResearch.WordTrace]
  refine ⟨152213667605763747010409429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101475778403842498006939619 152213667605763747010409429)
  ·
    refine ⟨3567507834510087820556471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 152213667605763747010409429 3567507834510087820556471)
    ·
      refine ⟨5351261751765131730834707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3567507834510087820556471 5351261751765131730834707)
      ·
        refine ⟨8026892627647697596252061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5351261751765131730834707 8026892627647697596252061)
        ·
          refine ⟨3010084735367886598594523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8026892627647697596252061 3010084735367886598594523)
          ·
            refine ⟨4515127103051829897891785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3010084735367886598594523 4515127103051829897891785)
            ·
              refine ⟨3386345327288872423418839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4515127103051829897891785 3386345327288872423418839)
              ·
                refine ⟨5079517990933308635128259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3386345327288872423418839 5079517990933308635128259)
                ·
                  refine ⟨7619276986399962952692389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5079517990933308635128259 7619276986399962952692389)
                  ·
                    refine ⟨1428614434949993053629823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7619276986399962952692389 1428614434949993053629823)
                    ·
                      rfl

theorem cell22_4173325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 3, 1, 2, 1, 1, 4].length) (baseStart_4173325 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4173325 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4173325 prefixEnd_4173325 := by exact prefixLift 4173325
  have htrace : WordTrace (prefixWord ++ tailWord_4173325) baseStart_4173325 baseEnd_4173325 := by
    simpa [prefixWord, tailWord_4173325, baseEnd_4173325] using wordTrace_append hprefix tailTrace_4173325
  have hstable : (prefixWord ++ tailWord_4173325).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4173325).length < 2 ^ (prefixWord ++ tailWord_4173325).sum := by decide
  have hdescent : baseEnd_4173325 < baseStart_4173325 := by decide
  rcases family_descends (prefixWord ++ tailWord_4173325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4173345 : List Nat := [1, 2, 3, 2, 2, 3, 1, 1, 7]
def baseStart_4173345 : Nat := 118140960795 + 4173345 * 2 ^ 59
def prefixEnd_4173345 : Nat := 4983230072969 + 3 ^ 40 * 4173345 * 2
def baseEnd_4173345 : Nat := 476207093786239889376587

theorem tailTrace_4173345 : CollatzResearch.WordTrace tailWord_4173345 prefixEnd_4173345 476207093786239889376587 := by
  unfold tailWord_4173345
  simp only [CollatzResearch.WordTrace]
  refine ⟨152214397065691290426137489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101476264710460860284091659 152214397065691290426137489)
  ·
    refine ⟨114160797799268467819603117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152214397065691290426137489 114160797799268467819603117)
    ·
      refine ⟨42810299174725675432351169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114160797799268467819603117 42810299174725675432351169)
      ·
        refine ⟨32107724381044256574263377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42810299174725675432351169 32107724381044256574263377)
        ·
          refine ⟨24080793285783192430697533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32107724381044256574263377 24080793285783192430697533)
          ·
            refine ⟨9030297482168697161511575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24080793285783192430697533 9030297482168697161511575)
            ·
              refine ⟨13545446223253045742267363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9030297482168697161511575 13545446223253045742267363)
              ·
                refine ⟨20318169334879568613401045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13545446223253045742267363 20318169334879568613401045)
                ·
                  refine ⟨476207093786239889376587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20318169334879568613401045 476207093786239889376587)
                  ·
                    rfl

theorem cell22_4173345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 1, 1, 7].length) (baseStart_4173345 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4173345 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4173345 prefixEnd_4173345 := by exact prefixLift 4173345
  have htrace : WordTrace (prefixWord ++ tailWord_4173345) baseStart_4173345 baseEnd_4173345 := by
    simpa [prefixWord, tailWord_4173345, baseEnd_4173345] using wordTrace_append hprefix tailTrace_4173345
  have hstable : (prefixWord ++ tailWord_4173345).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4173345).length < 2 ^ (prefixWord ++ tailWord_4173345).sum := by decide
  have hdescent : baseEnd_4173345 < baseStart_4173345 := by decide
  rcases family_descends (prefixWord ++ tailWord_4173345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4173383 : List Nat := [1, 1, 4, 1, 6, 1, 1, 3, 1, 3]
def baseStart_4173383 : Nat := 118140960795 + 4173383 * 2 ^ 59
def prefixEnd_4173383 : Nat := 4983230072969 + 3 ^ 40 * 4173383 * 2
def baseEnd_4173383 : Nat := 1428634289535300235679645

theorem tailTrace_4173383 : CollatzResearch.WordTrace tailWord_4173383 prefixEnd_4173383 1428634289535300235679645 := by
  unfold tailWord_4173383
  simp only [CollatzResearch.WordTrace]
  refine ⟨152215783039553622916020803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101477188693035748610680535 152215783039553622916020803)
  ·
    refine ⟨228323674559330434374031205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152215783039553622916020803 228323674559330434374031205)
    ·
      refine ⟨42810688979874456445130851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 228323674559330434374031205 42810688979874456445130851)
      ·
        refine ⟨64216033469811684667696277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42810688979874456445130851 64216033469811684667696277)
        ·
          refine ⟨3010126568897422718798263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 64216033469811684667696277 3010126568897422718798263)
          ·
            refine ⟨4515189853346134078197395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3010126568897422718798263 4515189853346134078197395)
            ·
              refine ⟨6772784780019201117296093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4515189853346134078197395 6772784780019201117296093)
              ·
                refine ⟨2539794292507200418986035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6772784780019201117296093 2539794292507200418986035)
                ·
                  refine ⟨3809691438760800628479053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2539794292507200418986035 3809691438760800628479053)
                  ·
                    refine ⟨1428634289535300235679645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3809691438760800628479053 1428634289535300235679645)
                    ·
                      rfl

theorem cell22_4173383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 6, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 6, 1, 1, 3, 1, 3].length) (baseStart_4173383 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4173383 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4173383 prefixEnd_4173383 := by exact prefixLift 4173383
  have htrace : WordTrace (prefixWord ++ tailWord_4173383) baseStart_4173383 baseEnd_4173383 := by
    simpa [prefixWord, tailWord_4173383, baseEnd_4173383] using wordTrace_append hprefix tailTrace_4173383
  have hstable : (prefixWord ++ tailWord_4173383).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4173383).length < 2 ^ (prefixWord ++ tailWord_4173383).sum := by decide
  have hdescent : baseEnd_4173383 < baseStart_4173383 := by decide
  rcases family_descends (prefixWord ++ tailWord_4173383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4173420 : List Nat := [2, 2, 1, 1, 3, 1, 1, 1, 6, 4]
def baseStart_4173420 : Nat := 118140960795 + 4173420 * 2 ^ 59
def prefixEnd_4173420 : Nat := 4983230072969 + 3 ^ 40 * 4173420 * 2
def baseEnd_4173420 : Nat := 1428646955391444472504531

theorem tailTrace_4173420 : CollatzResearch.WordTrace tailWord_4173420 prefixEnd_4173420 1428646955391444472504531 := by
  unfold tailWord_4173420
  simp only [CollatzResearch.WordTrace]
  refine ⟨76108566270209789117558857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101478088360279718823411809 76108566270209789117558857)
  ·
    refine ⟨57081424702657341838169143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76108566270209789117558857 57081424702657341838169143)
    ·
      refine ⟨85622137053986012757253715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57081424702657341838169143 85622137053986012757253715)
      ·
        refine ⟨128433205580979019135880573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85622137053986012757253715 128433205580979019135880573)
        ·
          refine ⟨48162452092867132175955215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 128433205580979019135880573 48162452092867132175955215)
          ·
            refine ⟨72243678139300698263932823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48162452092867132175955215 72243678139300698263932823)
            ·
              refine ⟨108365517208951047395899235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72243678139300698263932823 108365517208951047395899235)
              ·
                refine ⟨162548275813426571093848853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108365517208951047395899235 162548275813426571093848853)
                ·
                  refine ⟨7619450428754370520024165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 162548275813426571093848853 7619450428754370520024165)
                  ·
                    refine ⟨1428646955391444472504531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7619450428754370520024165 1428646955391444472504531)
                    ·
                      rfl

theorem cell22_4173420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 4].length) (baseStart_4173420 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4173420 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4173420 prefixEnd_4173420 := by exact prefixLift 4173420
  have htrace : WordTrace (prefixWord ++ tailWord_4173420) baseStart_4173420 baseEnd_4173420 := by
    simpa [prefixWord, tailWord_4173420, baseEnd_4173420] using wordTrace_append hprefix tailTrace_4173420
  have hstable : (prefixWord ++ tailWord_4173420).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4173420).length < 2 ^ (prefixWord ++ tailWord_4173420).sum := by decide
  have hdescent : baseEnd_4173420 < baseStart_4173420 := by decide
  rcases family_descends (prefixWord ++ tailWord_4173420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4173437 : List Nat := [1, 4, 1, 1, 4, 1, 1, 3, 2, 4]
def baseStart_4173437 : Nat := 118140960795 + 4173437 * 2 ^ 59
def prefixEnd_4173437 : Nat := 4983230072969 + 3 ^ 40 * 4173437 * 2
def baseEnd_4173437 : Nat := 1428652774838862094829479

theorem tailTrace_4173437 : CollatzResearch.WordTrace tailWord_4173437 prefixEnd_4173437 1428652774838862094829479 := by
  unfold tailWord_4173437
  simp only [CollatzResearch.WordTrace]
  refine ⟨152217752581357990138486565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101478501720905326758991043 152217752581357990138486565)
  ·
    refine ⟨28540828609004623150966231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 152217752581357990138486565 28540828609004623150966231)
    ·
      refine ⟨42811242913506934726449347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28540828609004623150966231 42811242913506934726449347)
      ·
        refine ⟨64216864370260402089674021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42811242913506934726449347 64216864370260402089674021)
        ·
          refine ⟨12040662069423825391813879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 64216864370260402089674021 12040662069423825391813879)
          ·
            refine ⟨18060993104135738087720819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12040662069423825391813879 18060993104135738087720819)
            ·
              refine ⟨27091489656203607131581229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18060993104135738087720819 27091489656203607131581229)
              ·
                refine ⟨10159308621076352674342961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27091489656203607131581229 10159308621076352674342961)
                ·
                  refine ⟨7619481465807264505757221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10159308621076352674342961 7619481465807264505757221)
                  ·
                    refine ⟨1428652774838862094829479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7619481465807264505757221 1428652774838862094829479)
                    ·
                      rfl

theorem cell22_4173437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 3, 2, 4].length) (baseStart_4173437 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4173437 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4173437 prefixEnd_4173437 := by exact prefixLift 4173437
  have htrace : WordTrace (prefixWord ++ tailWord_4173437) baseStart_4173437 baseEnd_4173437 := by
    simpa [prefixWord, tailWord_4173437, baseEnd_4173437] using wordTrace_append hprefix tailTrace_4173437
  have hstable : (prefixWord ++ tailWord_4173437).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4173437).length < 2 ^ (prefixWord ++ tailWord_4173437).sum := by decide
  have hdescent : baseEnd_4173437 < baseStart_4173437 := by decide
  rcases family_descends (prefixWord ++ tailWord_4173437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4173458 : List Nat := [3, 2, 3, 1, 3, 2, 2, 2, 4]
def baseStart_4173458 : Nat := 118140960795 + 4173458 * 2 ^ 59
def prefixEnd_4173458 : Nat := 4983230072969 + 3 ^ 40 * 4173458 * 2
def baseEnd_4173458 : Nat := 476219987856008346684805

theorem tailTrace_4173458 : CollatzResearch.WordTrace tailWord_4173458 prefixEnd_4173458 476219987856008346684805 := by
  unfold tailWord_4173458
  simp only [CollatzResearch.WordTrace]
  refine ⟨38054629628570477681250257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101479012342854607150000685 38054629628570477681250257)
  ·
    refine ⟨28540972221427858260937693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38054629628570477681250257 28540972221427858260937693)
    ·
      refine ⟨10702864583035446847851635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28540972221427858260937693 10702864583035446847851635)
      ·
        refine ⟨16054296874553170271777453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10702864583035446847851635 16054296874553170271777453)
        ·
          refine ⟨6020361327957438851916545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16054296874553170271777453 6020361327957438851916545)
          ·
            refine ⟨4515270995968079138937409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6020361327957438851916545 4515270995968079138937409)
            ·
              refine ⟨3386453246976059354203057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4515270995968079138937409 3386453246976059354203057)
              ·
                refine ⟨2539839935232044515652293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3386453246976059354203057 2539839935232044515652293)
                ·
                  refine ⟨476219987856008346684805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2539839935232044515652293 476219987856008346684805)
                  ·
                    rfl

theorem cell22_4173458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 2, 2, 2, 4].length) (baseStart_4173458 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4173458 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4173458 prefixEnd_4173458 := by exact prefixLift 4173458
  have htrace : WordTrace (prefixWord ++ tailWord_4173458) baseStart_4173458 baseEnd_4173458 := by
    simpa [prefixWord, tailWord_4173458, baseEnd_4173458] using wordTrace_append hprefix tailTrace_4173458
  have hstable : (prefixWord ++ tailWord_4173458).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4173458).length < 2 ^ (prefixWord ++ tailWord_4173458).sum := by decide
  have hdescent : baseEnd_4173458 < baseStart_4173458 := by decide
  rcases family_descends (prefixWord ++ tailWord_4173458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4173486 : List Nat := [4, 1, 4, 1, 2, 1, 3, 6]
def baseStart_4173486 : Nat := 118140960795 + 4173486 * 2 ^ 59
def prefixEnd_4173486 : Nat := 4983230072969 + 3 ^ 40 * 4173486 * 2
def baseEnd_4173486 : Nat := 158741060948915811150481

theorem tailTrace_4173486 : CollatzResearch.WordTrace tailWord_4173486 prefixEnd_4173486 158741060948915811150481 := by
  unfold tailWord_4173486
  simp only [CollatzResearch.WordTrace]
  refine ⟨19027442469772558938377539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 101479693172120314338013541 19027442469772558938377539)
  ·
    refine ⟨28541163704658838407566309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19027442469772558938377539 28541163704658838407566309)
    ·
      refine ⟨5351468194623532201418683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28541163704658838407566309 5351468194623532201418683)
      ·
        refine ⟨8027202291935298302128025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5351468194623532201418683 8027202291935298302128025)
        ·
          refine ⟨6020401718951473726596019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8027202291935298302128025 6020401718951473726596019)
          ·
            refine ⟨9030602578427210589894029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6020401718951473726596019 9030602578427210589894029)
            ·
              refine ⟨3386475966910203971210261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9030602578427210589894029 3386475966910203971210261)
              ·
                refine ⟨158741060948915811150481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3386475966910203971210261 158741060948915811150481)
                ·
                  rfl

theorem cell22_4173486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 3, 6].length) (baseStart_4173486 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4173486 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4173486 prefixEnd_4173486 := by exact prefixLift 4173486
  have htrace : WordTrace (prefixWord ++ tailWord_4173486) baseStart_4173486 baseEnd_4173486 := by
    simpa [prefixWord, tailWord_4173486, baseEnd_4173486] using wordTrace_append hprefix tailTrace_4173486
  have hstable : (prefixWord ++ tailWord_4173486).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4173486).length < 2 ^ (prefixWord ++ tailWord_4173486).sum := by decide
  have hdescent : baseEnd_4173486 < baseStart_4173486 := by decide
  rcases family_descends (prefixWord ++ tailWord_4173486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4173501 : List Nat := [1, 4, 1, 2, 1, 2, 4, 3, 1, 3]
def baseStart_4173501 : Nat := 118140960795 + 4173501 * 2 ^ 59
def prefixEnd_4173501 : Nat := 4983230072969 + 3 ^ 40 * 4173501 * 2
def baseEnd_4173501 : Nat := 1428674683346787261229283

theorem tailTrace_4173501 : CollatzResearch.WordTrace tailWord_4173501 prefixEnd_4173501 1428674683346787261229283 := by
  unfold tailWord_4173501
  simp only [CollatzResearch.WordTrace]
  refine ⟨152220086853126129068816357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101480057902084086045877571 152220086853126129068816357)
  ·
    refine ⟨28541266284961149200403067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 152220086853126129068816357 28541266284961149200403067)
    ·
      refine ⟨42811899427441723800604601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28541266284961149200403067 42811899427441723800604601)
      ·
        refine ⟨32108924570581292850453451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42811899427441723800604601 32108924570581292850453451)
        ·
          refine ⟨48163386855871939275680177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32108924570581292850453451 48163386855871939275680177)
          ·
            refine ⟨36122540141903954456760133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48163386855871939275680177 36122540141903954456760133)
            ·
              refine ⟨6772976276606991460642525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36122540141903954456760133 6772976276606991460642525)
              ·
                refine ⟨2539866103727621797740947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6772976276606991460642525 2539866103727621797740947)
                ·
                  refine ⟨3809799155591432696611421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2539866103727621797740947 3809799155591432696611421)
                  ·
                    refine ⟨1428674683346787261229283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3809799155591432696611421 1428674683346787261229283)
                    ·
                      rfl

theorem cell22_4173501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 4, 3, 1, 3].length) (baseStart_4173501 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4173501 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4173501 prefixEnd_4173501 := by exact prefixLift 4173501
  have htrace : WordTrace (prefixWord ++ tailWord_4173501) baseStart_4173501 baseEnd_4173501 := by
    simpa [prefixWord, tailWord_4173501, baseEnd_4173501] using wordTrace_append hprefix tailTrace_4173501
  have hstable : (prefixWord ++ tailWord_4173501).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4173501).length < 2 ^ (prefixWord ++ tailWord_4173501).sum := by decide
  have hdescent : baseEnd_4173501 < baseStart_4173501 := by decide
  rcases family_descends (prefixWord ++ tailWord_4173501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4173544 : List Nat := [2, 1, 4, 1, 3, 1, 1, 4, 1, 4]
def baseStart_4173544 : Nat := 118140960795 + 4173544 * 2 ^ 59
def prefixEnd_4173544 : Nat := 4983230072969 + 3 ^ 40 * 4173544 * 2
def baseEnd_4173544 : Nat := 1428689403125549482404151

theorem tailTrace_4173544 : CollatzResearch.WordTrace tailWord_4173544 prefixEnd_4173544 1428689403125549482404151 := by
  unfold tailWord_4173544
  simp only [CollatzResearch.WordTrace]
  refine ⟨76110827595985173706315843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101481103461313564941754457 76110827595985173706315843)
  ·
    refine ⟨114166241393977760559473765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76110827595985173706315843 114166241393977760559473765)
    ·
      refine ⟨21406170261370830104901331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 114166241393977760559473765 21406170261370830104901331)
      ·
        refine ⟨32109255392056245157351997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21406170261370830104901331 32109255392056245157351997)
        ·
          refine ⟨12040970772021091934006999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32109255392056245157351997 12040970772021091934006999)
          ·
            refine ⟨18061456158031637901010499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12040970772021091934006999 18061456158031637901010499)
            ·
              refine ⟨27092184237047456851515749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18061456158031637901010499 27092184237047456851515749)
              ·
                refine ⟨5079784544446398159659203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27092184237047456851515749 5079784544446398159659203)
                ·
                  refine ⟨7619676816669597239488805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5079784544446398159659203 7619676816669597239488805)
                  ·
                    refine ⟨1428689403125549482404151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7619676816669597239488805 1428689403125549482404151)
                    ·
                      rfl

theorem cell22_4173544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 4, 1, 4].length) (baseStart_4173544 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4173544 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4173544 prefixEnd_4173544 := by exact prefixLift 4173544
  have htrace : WordTrace (prefixWord ++ tailWord_4173544) baseStart_4173544 baseEnd_4173544 := by
    simpa [prefixWord, tailWord_4173544, baseEnd_4173544] using wordTrace_append hprefix tailTrace_4173544
  have hstable : (prefixWord ++ tailWord_4173544).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4173544).length < 2 ^ (prefixWord ++ tailWord_4173544).sum := by decide
  have hdescent : baseEnd_4173544 < baseStart_4173544 := by decide
  rcases family_descends (prefixWord ++ tailWord_4173544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4173559 : List Nat := [1, 1, 3, 1, 1, 1, 7, 3, 4]
def baseStart_4173559 : Nat := 118140960795 + 4173559 * 2 ^ 59
def prefixEnd_4173559 : Nat := 4983230072969 + 3 ^ 40 * 4173559 * 2
def baseEnd_4173559 : Nat := 476231512644031481093035

theorem tailTrace_4173559 : CollatzResearch.WordTrace tailWord_4173559 prefixEnd_4173559 476231512644031481093035 := by
  unfold tailWord_4173559
  simp only [CollatzResearch.WordTrace]
  refine ⟨152222202286916004974427731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101481468191277336649618487 152222202286916004974427731)
  ·
    refine ⟨228333303430374007461641597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152222202286916004974427731 228333303430374007461641597)
    ·
      refine ⟨85624988786390252798115599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 228333303430374007461641597 85624988786390252798115599)
      ·
        refine ⟨128437483179585379197173399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85624988786390252798115599 128437483179585379197173399)
        ·
          refine ⟨192656224769378068795760099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128437483179585379197173399 192656224769378068795760099)
          ·
            refine ⟨288984337154067103193640149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192656224769378068795760099 288984337154067103193640149)
            ·
              refine ⟨6773070402048447731100941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 288984337154067103193640149 6773070402048447731100941)
              ·
                refine ⟨2539901400768167899162853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6773070402048447731100941 2539901400768167899162853)
                ·
                  refine ⟨476231512644031481093035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2539901400768167899162853 476231512644031481093035)
                  ·
                    rfl

theorem cell22_4173559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 7, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 7, 3, 4].length) (baseStart_4173559 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4173559 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4173559 prefixEnd_4173559 := by exact prefixLift 4173559
  have htrace : WordTrace (prefixWord ++ tailWord_4173559) baseStart_4173559 baseEnd_4173559 := by
    simpa [prefixWord, tailWord_4173559, baseEnd_4173559] using wordTrace_append hprefix tailTrace_4173559
  have hstable : (prefixWord ++ tailWord_4173559).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4173559).length < 2 ^ (prefixWord ++ tailWord_4173559).sum := by decide
  have hdescent : baseEnd_4173559 < baseStart_4173559 := by decide
  rcases family_descends (prefixWord ++ tailWord_4173559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4173576 : List Nat := [2, 1, 3, 2, 2, 1, 5, 2, 4]
def baseStart_4173576 : Nat := 118140960795 + 4173576 * 2 ^ 59
def prefixEnd_4173576 : Nat := 4983230072969 + 3 ^ 40 * 4173576 * 2
def baseEnd_4173576 : Nat := 476233452459837355201351

theorem tailTrace_4173576 : CollatzResearch.WordTrace tailWord_4173576 prefixEnd_4173576 476233452459837355201351 := by
  unfold tailWord_4173576
  simp only [CollatzResearch.WordTrace]
  refine ⟨76111411163927208438898291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101481881551902944585197721 76111411163927208438898291)
  ·
    refine ⟨114167116745890812658347437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76111411163927208438898291 114167116745890812658347437)
    ·
      refine ⟨42812668779709054746880289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114167116745890812658347437 42812668779709054746880289)
      ·
        refine ⟨32109501584781791060160217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42812668779709054746880289 32109501584781791060160217)
        ·
          refine ⟨24082126188586343295120163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32109501584781791060160217 24082126188586343295120163)
          ·
            refine ⟨36123189282879514942680245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24082126188586343295120163 36123189282879514942680245)
            ·
              refine ⟨3386548995269954525876273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 36123189282879514942680245 3386548995269954525876273)
              ·
                refine ⟨2539911746452465894407205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3386548995269954525876273 2539911746452465894407205)
                ·
                  refine ⟨476233452459837355201351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2539911746452465894407205 476233452459837355201351)
                  ·
                    rfl

theorem cell22_4173576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 5, 2, 4].length) (baseStart_4173576 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4173576 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4173576 prefixEnd_4173576 := by exact prefixLift 4173576
  have htrace : WordTrace (prefixWord ++ tailWord_4173576) baseStart_4173576 baseEnd_4173576 := by
    simpa [prefixWord, tailWord_4173576, baseEnd_4173576] using wordTrace_append hprefix tailTrace_4173576
  have hstable : (prefixWord ++ tailWord_4173576).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4173576).length < 2 ^ (prefixWord ++ tailWord_4173576).sum := by decide
  have hdescent : baseEnd_4173576 < baseStart_4173576 := by decide
  rcases family_descends (prefixWord ++ tailWord_4173576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4173591 : List Nat := [1, 1, 3, 4, 2, 2, 1, 3, 2, 3]
def baseStart_4173591 : Nat := 118140960795 + 4173591 * 2 ^ 59
def prefixEnd_4173591 : Nat := 4983230072969 + 3 ^ 40 * 4173591 * 2
def baseEnd_4173591 : Nat := 1428705492186057026479007

theorem tailTrace_4173591 : CollatzResearch.WordTrace tailWord_4173591 prefixEnd_4173591 1428705492186057026479007 := by
  unfold tailWord_4173591
  simp only [CollatzResearch.WordTrace]
  refine ⟨152223369422800074439592627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101482246281866716293061751 152223369422800074439592627)
  ·
    refine ⟨228335054134200111659388941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152223369422800074439592627 228335054134200111659388941)
    ·
      refine ⟨85625645300325041872270853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 228335054134200111659388941 85625645300325041872270853)
      ·
        refine ⟨16054808493810945351050785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 85625645300325041872270853 16054808493810945351050785)
        ·
          refine ⟨12041106370358209013288089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16054808493810945351050785 12041106370358209013288089)
          ·
            refine ⟨9030829777768656759966067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12041106370358209013288089 9030829777768656759966067)
            ·
              refine ⟨13546244666652985139949101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9030829777768656759966067 13546244666652985139949101)
              ·
                refine ⟨5079841749994869427480913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13546244666652985139949101 5079841749994869427480913)
                ·
                  refine ⟨3809881312496152070610685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5079841749994869427480913 3809881312496152070610685)
                  ·
                    refine ⟨1428705492186057026479007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3809881312496152070610685 1428705492186057026479007)
                    ·
                      rfl

theorem cell22_4173591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 1, 3, 2, 3].length) (baseStart_4173591 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4173591 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4173591 prefixEnd_4173591 := by exact prefixLift 4173591
  have htrace : WordTrace (prefixWord ++ tailWord_4173591) baseStart_4173591 baseEnd_4173591 := by
    simpa [prefixWord, tailWord_4173591, baseEnd_4173591] using wordTrace_append hprefix tailTrace_4173591
  have hstable : (prefixWord ++ tailWord_4173591).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4173591).length < 2 ^ (prefixWord ++ tailWord_4173591).sum := by decide
  have hdescent : baseEnd_4173591 < baseStart_4173591 := by decide
  rcases family_descends (prefixWord ++ tailWord_4173591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4173638 : List Nat := [6, 1, 1, 2, 1, 3, 1, 7]
def baseStart_4173638 : Nat := 118140960795 + 4173638 * 2 ^ 59
def prefixEnd_4173638 : Nat := 4983230072969 + 3 ^ 40 * 4173638 * 2
def baseEnd_4173638 : Nat := 158746842360729396728207

theorem tailTrace_4173638 : CollatzResearch.WordTrace tailWord_4173638 prefixEnd_4173638 158746842360729396728207 := by
  unfold tailWord_4173638
  simp only [CollatzResearch.WordTrace]
  refine ⟨4757033864175931295829799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 101483389102419867644369045 4757033864175931295829799)
  ·
    refine ⟨7135550796263896943744699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4757033864175931295829799 7135550796263896943744699)
    ·
      refine ⟨10703326194395845415617049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7135550796263896943744699 10703326194395845415617049)
      ·
        refine ⟨8027494645796884061712787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10703326194395845415617049 8027494645796884061712787)
        ·
          refine ⟨12041241968695326092569181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8027494645796884061712787 12041241968695326092569181)
          ·
            refine ⟨4515465738260747284713443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12041241968695326092569181 4515465738260747284713443)
            ·
              refine ⟨6773198607391120927070165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4515465738260747284713443 6773198607391120927070165)
              ·
                refine ⟨158746842360729396728207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6773198607391120927070165 158746842360729396728207)
                ·
                  rfl

theorem cell22_4173638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 3, 1, 7].length) (baseStart_4173638 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4173638 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4173638 prefixEnd_4173638 := by exact prefixLift 4173638
  have htrace : WordTrace (prefixWord ++ tailWord_4173638) baseStart_4173638 baseEnd_4173638 := by
    simpa [prefixWord, tailWord_4173638, baseEnd_4173638] using wordTrace_append hprefix tailTrace_4173638
  have hstable : (prefixWord ++ tailWord_4173638).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4173638).length < 2 ^ (prefixWord ++ tailWord_4173638).sum := by decide
  have hdescent : baseEnd_4173638 < baseStart_4173638 := by decide
  rcases family_descends (prefixWord ++ tailWord_4173638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4173649 : List Nat := [1, 2, 2, 1, 5, 1, 2, 3, 5]
def baseStart_4173649 : Nat := 118140960795 + 4173649 * 2 ^ 59
def prefixEnd_4173649 : Nat := 4983230072969 + 3 ^ 40 * 4173649 * 2
def baseEnd_4173649 : Nat := 476241782257121402842943

theorem tailTrace_4173649 : CollatzResearch.WordTrace tailWord_4173649 prefixEnd_4173649 476241782257121402842943 := by
  unfold tailWord_4173649
  simp only [CollatzResearch.WordTrace]
  refine ⟨152225484856589950345204001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101483656571059966896802667 152225484856589950345204001)
  ·
    refine ⟨114169113642442462758903001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152225484856589950345204001 114169113642442462758903001)
    ·
      refine ⟨85626835231831847069177251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114169113642442462758903001 85626835231831847069177251)
      ·
        refine ⟨128440252847747770603765877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85626835231831847069177251 128440252847747770603765877)
        ·
          refine ⟨12041273704476353494103051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 128440252847747770603765877 12041273704476353494103051)
          ·
            refine ⟨18061910556714530241154577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12041273704476353494103051 18061910556714530241154577)
            ·
              refine ⟨13546432917535897680865933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18061910556714530241154577 13546432917535897680865933)
              ·
                refine ⟨5079912344075961630324725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13546432917535897680865933 5079912344075961630324725)
                ·
                  refine ⟨476241782257121402842943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5079912344075961630324725 476241782257121402842943)
                  ·
                    rfl

theorem cell22_4173649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 2, 3, 5].length) (baseStart_4173649 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4173649 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4173649 prefixEnd_4173649 := by exact prefixLift 4173649
  have htrace : WordTrace (prefixWord ++ tailWord_4173649) baseStart_4173649 baseEnd_4173649 := by
    simpa [prefixWord, tailWord_4173649, baseEnd_4173649] using wordTrace_append hprefix tailTrace_4173649
  have hstable : (prefixWord ++ tailWord_4173649).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4173649).length < 2 ^ (prefixWord ++ tailWord_4173649).sum := by decide
  have hdescent : baseEnd_4173649 < baseStart_4173649 := by decide
  rcases family_descends (prefixWord ++ tailWord_4173649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4173692 : List Nat := [2, 2, 2, 1, 1, 1, 1, 1, 2, 9]
def baseStart_4173692 : Nat := 118140960795 + 4173692 * 2 ^ 59
def prefixEnd_4173692 : Nat := 4983230072969 + 3 ^ 40 * 4173692 * 2
def baseEnd_4173692 : Nat := 1428740066550126429703697

theorem tailTrace_4173692 : CollatzResearch.WordTrace tailWord_4173692 prefixEnd_4173692 1428740066550126429703697 := by
  unfold tailWord_4173692
  simp only [CollatzResearch.WordTrace]
  refine ⟨76113526597717084344509665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101484702130289445792679553 76113526597717084344509665)
  ·
    refine ⟨57085144948287813258382249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76113526597717084344509665 57085144948287813258382249)
    ·
      refine ⟨42813858711215859943786687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57085144948287813258382249 42813858711215859943786687)
      ·
        refine ⟨64220788066823789915680031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42813858711215859943786687 64220788066823789915680031)
        ·
          refine ⟨96331182100235684873520047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64220788066823789915680031 96331182100235684873520047)
          ·
            refine ⟨144496773150353527310280071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96331182100235684873520047 144496773150353527310280071)
            ·
              refine ⟨216745159725530290965420107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144496773150353527310280071 216745159725530290965420107)
              ·
                refine ⟨325117739588295436448130161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 216745159725530290965420107 325117739588295436448130161)
                ·
                  refine ⟨243838304691221577336097621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 325117739588295436448130161 243838304691221577336097621)
                  ·
                    refine ⟨1428740066550126429703697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 243838304691221577336097621 1428740066550126429703697)
                    ·
                      rfl

theorem cell22_4173692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 1, 2, 9].length) (baseStart_4173692 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4173692 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4173692 prefixEnd_4173692 := by exact prefixLift 4173692
  have htrace : WordTrace (prefixWord ++ tailWord_4173692) baseStart_4173692 baseEnd_4173692 := by
    simpa [prefixWord, tailWord_4173692, baseEnd_4173692] using wordTrace_append hprefix tailTrace_4173692
  have hstable : (prefixWord ++ tailWord_4173692).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4173692).length < 2 ^ (prefixWord ++ tailWord_4173692).sum := by decide
  have hdescent : baseEnd_4173692 < baseStart_4173692 := by decide
  rcases family_descends (prefixWord ++ tailWord_4173692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4173829 : List Nat := [1, 3, 1, 1, 2, 4, 1, 1, 8]
def baseStart_4173829 : Nat := 118140960795 + 4173829 * 2 ^ 59
def prefixEnd_4173829 : Nat := 4983230072969 + 3 ^ 40 * 4173829 * 2
def baseEnd_4173829 : Nat := 476262321483301246342759

theorem tailTrace_4173829 : CollatzResearch.WordTrace tailWord_4173829 prefixEnd_4173829 476262321483301246342759 := by
  unfold tailWord_4173829
  simp only [CollatzResearch.WordTrace]
  refine ⟨152232049995937841086756541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101488033330625227391171027 152232049995937841086756541)
  ·
    refine ⟨57087018748476690407533703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152232049995937841086756541 57087018748476690407533703)
    ·
      refine ⟨85630528122715035611300555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57087018748476690407533703 85630528122715035611300555)
      ·
        refine ⟨128445792184072553416950833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85630528122715035611300555 128445792184072553416950833)
        ·
          refine ⟨96334344138054415062713125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128445792184072553416950833 96334344138054415062713125)
          ·
            refine ⟨18062689525885202824258711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 96334344138054415062713125 18062689525885202824258711)
            ·
              refine ⟨27094034288827804236388067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18062689525885202824258711 27094034288827804236388067)
              ·
                refine ⟨40641051433241706354582101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27094034288827804236388067 40641051433241706354582101)
                ·
                  refine ⟨476262321483301246342759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 40641051433241706354582101 476262321483301246342759)
                  ·
                    rfl

theorem cell22_4173829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 1, 8].length) (baseStart_4173829 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4173829 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4173829 prefixEnd_4173829 := by exact prefixLift 4173829
  have htrace : WordTrace (prefixWord ++ tailWord_4173829) baseStart_4173829 baseEnd_4173829 := by
    simpa [prefixWord, tailWord_4173829, baseEnd_4173829] using wordTrace_append hprefix tailTrace_4173829
  have hstable : (prefixWord ++ tailWord_4173829).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4173829).length < 2 ^ (prefixWord ++ tailWord_4173829).sum := by decide
  have hdescent : baseEnd_4173829 < baseStart_4173829 := by decide
  rcases family_descends (prefixWord ++ tailWord_4173829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4173831 : List Nat := [1, 1, 4, 3, 1, 2, 2, 1, 3, 4]
def baseStart_4173831 : Nat := 118140960795 + 4173831 * 2 ^ 59
def prefixEnd_4173831 : Nat := 4983230072969 + 3 ^ 40 * 4173831 * 2
def baseEnd_4173831 : Nat := 1428787649090776400478271

theorem tailTrace_4173831 : CollatzResearch.WordTrace tailWord_4173831 prefixEnd_4173831 1428787649090776400478271 := by
  unfold tailWord_4173831
  simp only [CollatzResearch.WordTrace]
  refine ⟨152232122941930595428329347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101488081961287063618886231 152232122941930595428329347)
  ·
    refine ⟨228348184412895893142494021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152232122941930595428329347 228348184412895893142494021)
    ·
      refine ⟨42815284577417979964217629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 228348184412895893142494021 42815284577417979964217629)
      ·
        refine ⟨16055731716531742486581611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42815284577417979964217629 16055731716531742486581611)
        ·
          refine ⟨24083597574797613729872417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16055731716531742486581611 24083597574797613729872417)
          ·
            refine ⟨18062698181098210297404313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24083597574797613729872417 18062698181098210297404313)
            ·
              refine ⟨13547023635823657723053235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18062698181098210297404313 13547023635823657723053235)
              ·
                refine ⟨20320535453735486584579853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13547023635823657723053235 20320535453735486584579853)
                ·
                  refine ⟨7620200795150807469217445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20320535453735486584579853 7620200795150807469217445)
                  ·
                    refine ⟨1428787649090776400478271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7620200795150807469217445 1428787649090776400478271)
                    ·
                      rfl

theorem cell22_4173831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 2, 1, 3, 4].length) (baseStart_4173831 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4173831 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4173831 prefixEnd_4173831 := by exact prefixLift 4173831
  have htrace : WordTrace (prefixWord ++ tailWord_4173831) baseStart_4173831 baseEnd_4173831 := by
    simpa [prefixWord, tailWord_4173831, baseEnd_4173831] using wordTrace_append hprefix tailTrace_4173831
  have hstable : (prefixWord ++ tailWord_4173831).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4173831).length < 2 ^ (prefixWord ++ tailWord_4173831).sum := by decide
  have hdescent : baseEnd_4173831 < baseStart_4173831 := by decide
  rcases family_descends (prefixWord ++ tailWord_4173831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4173904 : List Nat := [2, 1, 1, 1, 1, 3, 1, 1, 3, 8]
def baseStart_4173904 : Nat := 118140960795 + 4173904 * 2 ^ 59
def prefixEnd_4173904 : Nat := 4983230072969 + 3 ^ 40 * 4173904 * 2
def baseEnd_4173904 : Nat := 1428812638482628543403047

theorem tailTrace_4173904 : CollatzResearch.WordTrace tailWord_4173904 prefixEnd_4173904 1428812638482628543403047 := by
  unfold tailWord_4173904
  simp only [CollatzResearch.WordTrace]
  refine ⟨76117392735333064447868383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101489856980444085930491177 76117392735333064447868383)
  ·
    refine ⟨114176089102999596671802575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76117392735333064447868383 114176089102999596671802575)
    ·
      refine ⟨171264133654499395007703863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114176089102999596671802575 171264133654499395007703863)
      ·
        refine ⟨256896200481749092511555795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171264133654499395007703863 256896200481749092511555795)
        ·
          refine ⟨385344300722623638767333693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 256896200481749092511555795 385344300722623638767333693)
          ·
            refine ⟨144504112770983864537750135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 385344300722623638767333693 144504112770983864537750135)
            ·
              refine ⟨216756169156475796806625203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144504112770983864537750135 216756169156475796806625203)
              ·
                refine ⟨325134253734713695209937805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 216756169156475796806625203 325134253734713695209937805)
                ·
                  refine ⟨121925345150517635703726677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 325134253734713695209937805 121925345150517635703726677)
                  ·
                    refine ⟨1428812638482628543403047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 121925345150517635703726677 1428812638482628543403047)
                    ·
                      rfl

theorem cell22_4173904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 3, 8].length) (baseStart_4173904 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4173904 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4173904 prefixEnd_4173904 := by exact prefixLift 4173904
  have htrace : WordTrace (prefixWord ++ tailWord_4173904) baseStart_4173904 baseEnd_4173904 := by
    simpa [prefixWord, tailWord_4173904, baseEnd_4173904] using wordTrace_append hprefix tailTrace_4173904
  have hstable : (prefixWord ++ tailWord_4173904).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4173904).length < 2 ^ (prefixWord ++ tailWord_4173904).sum := by decide
  have hdescent : baseEnd_4173904 < baseStart_4173904 := by decide
  rcases family_descends (prefixWord ++ tailWord_4173904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4173910 : List Nat := [5, 2, 2, 1, 1, 1, 1, 1, 4, 4]
def baseStart_4173910 : Nat := 118140960795 + 4173910 * 2 ^ 59
def prefixEnd_4173910 : Nat := 4983230072969 + 3 ^ 40 * 4173910 * 2
def baseEnd_4173910 : Nat := 1428814692405246527753029

theorem tailTrace_4173910 : CollatzResearch.WordTrace tailWord_4173910 prefixEnd_4173910 1428814692405246527753029 := by
  unfold tailWord_4173910
  simp only [CollatzResearch.WordTrace]
  refine ⟨9514687769290274495028449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 101490002872429594613636789 9514687769290274495028449)
  ·
    refine ⟨7136015826967705871271337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9514687769290274495028449 7136015826967705871271337)
    ·
      refine ⟨5352011870225779403453503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7136015826967705871271337 5352011870225779403453503)
      ·
        refine ⟨8028017805338669105180255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5352011870225779403453503 8028017805338669105180255)
        ·
          refine ⟨12042026708008003657770383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8028017805338669105180255 12042026708008003657770383)
          ·
            refine ⟨18063040062012005486655575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12042026708008003657770383 18063040062012005486655575)
            ·
              refine ⟨27094560093018008229983363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18063040062012005486655575 27094560093018008229983363)
              ·
                refine ⟨40641840139527012344975045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27094560093018008229983363 40641840139527012344975045)
                ·
                  refine ⟨7620345026161314814682821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40641840139527012344975045 7620345026161314814682821)
                  ·
                    refine ⟨1428814692405246527753029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7620345026161314814682821 1428814692405246527753029)
                    ·
                      rfl

theorem cell22_4173910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 1, 4, 4].length) (baseStart_4173910 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4173910 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4173910 prefixEnd_4173910 := by exact prefixLift 4173910
  have htrace : WordTrace (prefixWord ++ tailWord_4173910) baseStart_4173910 baseEnd_4173910 := by
    simpa [prefixWord, tailWord_4173910, baseEnd_4173910] using wordTrace_append hprefix tailTrace_4173910
  have hstable : (prefixWord ++ tailWord_4173910).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4173910).length < 2 ^ (prefixWord ++ tailWord_4173910).sum := by decide
  have hdescent : baseEnd_4173910 < baseStart_4173910 := by decide
  rcases family_descends (prefixWord ++ tailWord_4173910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4173923 : List Nat := [1, 1, 1, 5, 1, 1, 5, 1, 3, 3]
def baseStart_4173923 : Nat := 118140960795 + 4173923 * 2 ^ 59
def prefixEnd_4173923 : Nat := 4983230072969 + 3 ^ 40 * 4173923 * 2
def baseEnd_4173923 : Nat := 1428819142570918827177989

theorem tailTrace_4173923 : CollatzResearch.WordTrace tailWord_4173923 prefixEnd_4173923 1428819142570918827177989 := by
  unfold tailWord_4173923
  simp only [CollatzResearch.WordTrace]
  refine ⟨152235478457597295140678423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101490318971731530093785615 152235478457597295140678423)
  ·
    refine ⟨228353217686395942711017635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152235478457597295140678423 228353217686395942711017635)
    ·
      refine ⟨342529826529593914066526453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228353217686395942711017635 342529826529593914066526453)
      ·
        refine ⟨32112171237149429443736855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 342529826529593914066526453 32112171237149429443736855)
        ·
          refine ⟨48168256855724144165605283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32112171237149429443736855 48168256855724144165605283)
          ·
            refine ⟨72252385283586216248407925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48168256855724144165605283 72252385283586216248407925)
            ·
              refine ⟨6773661120336207773288243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 72252385283586216248407925 6773661120336207773288243)
              ·
                refine ⟨10160491680504311659932365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6773661120336207773288243 10160491680504311659932365)
                ·
                  refine ⟨3810184380189116872474637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10160491680504311659932365 3810184380189116872474637)
                  ·
                    refine ⟨1428819142570918827177989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3810184380189116872474637 1428819142570918827177989)
                    ·
                      rfl

theorem cell22_4173923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 5, 1, 3, 3].length) (baseStart_4173923 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4173923 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4173923 prefixEnd_4173923 := by exact prefixLift 4173923
  have htrace : WordTrace (prefixWord ++ tailWord_4173923) baseStart_4173923 baseEnd_4173923 := by
    simpa [prefixWord, tailWord_4173923, baseEnd_4173923] using wordTrace_append hprefix tailTrace_4173923
  have hstable : (prefixWord ++ tailWord_4173923).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4173923).length < 2 ^ (prefixWord ++ tailWord_4173923).sum := by decide
  have hdescent : baseEnd_4173923 < baseStart_4173923 := by decide
  rcases family_descends (prefixWord ++ tailWord_4173923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4173983 : List Nat := [1, 1, 2, 6, 1, 1, 1, 2, 3, 4]
def baseStart_4173983 : Nat := 118140960795 + 4173983 * 2 ^ 59
def prefixEnd_4173983 : Nat := 4983230072969 + 3 ^ 40 * 4173983 * 2
def baseEnd_4173983 : Nat := 1428839681797098670677805

theorem tailTrace_4173983 : CollatzResearch.WordTrace tailWord_4173983 prefixEnd_4173983 1428839681797098670677805 := by
  unfold tailWord_4173983
  simp only [CollatzResearch.WordTrace]
  refine ⟨152237666837379925387862603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101491777891586616925241735 152237666837379925387862603)
  ·
    refine ⟨228356500256069888081793905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152237666837379925387862603 228356500256069888081793905)
    ·
      refine ⟨171267375192052416061345429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 228356500256069888081793905 171267375192052416061345429)
      ·
        refine ⟨8028158212127457002875567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 171267375192052416061345429 8028158212127457002875567)
        ·
          refine ⟨12042237318191185504313351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8028158212127457002875567 12042237318191185504313351)
          ·
            refine ⟨18063355977286778256470027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12042237318191185504313351 18063355977286778256470027)
            ·
              refine ⟨27095033965930167384705041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18063355977286778256470027 27095033965930167384705041)
              ·
                refine ⟨20321275474447625538528781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27095033965930167384705041 20321275474447625538528781)
                ·
                  refine ⟨7620478302917859576948293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20321275474447625538528781 7620478302917859576948293)
                  ·
                    refine ⟨1428839681797098670677805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7620478302917859576948293 1428839681797098670677805)
                    ·
                      rfl

theorem cell22_4173983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 2, 3, 4].length) (baseStart_4173983 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4173983 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4173983 prefixEnd_4173983 := by exact prefixLift 4173983
  have htrace : WordTrace (prefixWord ++ tailWord_4173983) baseStart_4173983 baseEnd_4173983 := by
    simpa [prefixWord, tailWord_4173983, baseEnd_4173983] using wordTrace_append hprefix tailTrace_4173983
  have hstable : (prefixWord ++ tailWord_4173983).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4173983).length < 2 ^ (prefixWord ++ tailWord_4173983).sum := by decide
  have hdescent : baseEnd_4173983 < baseStart_4173983 := by decide
  rcases family_descends (prefixWord ++ tailWord_4173983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4174011 : List Nat := [1, 1, 1, 1, 1, 2, 7, 1, 1, 6]
def baseStart_4174011 : Nat := 118140960795 + 4174011 * 2 ^ 59
def prefixEnd_4174011 : Nat := 4983230072969 + 3 ^ 40 * 4174011 * 2
def baseEnd_4174011 : Nat := 1428849266769315930977719

theorem tailTrace_4174011 : CollatzResearch.WordTrace tailWord_4174011 prefixEnd_4174011 1428849266769315930977719 := by
  unfold tailWord_4174011
  simp only [CollatzResearch.WordTrace]
  refine ⟨152238688081278486169881887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101492458720852324113254591 152238688081278486169881887)
  ·
    refine ⟨228358032121917729254822831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152238688081278486169881887 228358032121917729254822831)
    ·
      refine ⟨342537048182876593882234247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228358032121917729254822831 342537048182876593882234247)
      ·
        refine ⟨513805572274314890823351371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 342537048182876593882234247 513805572274314890823351371)
        ·
          refine ⟨770708358411472336235027057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 513805572274314890823351371 770708358411472336235027057)
          ·
            refine ⟨578031268808604252176270293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 770708358411472336235027057 578031268808604252176270293)
            ·
              refine ⟨13547607862701662160381335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 578031268808604252176270293 13547607862701662160381335)
              ·
                refine ⟨20321411794052493240572003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13547607862701662160381335 20321411794052493240572003)
                ·
                  refine ⟨30482117691078739860858005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20321411794052493240572003 30482117691078739860858005)
                  ·
                    refine ⟨1428849266769315930977719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30482117691078739860858005 1428849266769315930977719)
                    ·
                      rfl

theorem cell22_4174011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 7, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 7, 1, 1, 6].length) (baseStart_4174011 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4174011 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4174011 prefixEnd_4174011 := by exact prefixLift 4174011
  have htrace : WordTrace (prefixWord ++ tailWord_4174011) baseStart_4174011 baseEnd_4174011 := by
    simpa [prefixWord, tailWord_4174011, baseEnd_4174011] using wordTrace_append hprefix tailTrace_4174011
  have hstable : (prefixWord ++ tailWord_4174011).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4174011).length < 2 ^ (prefixWord ++ tailWord_4174011).sum := by decide
  have hdescent : baseEnd_4174011 < baseStart_4174011 := by decide
  rcases family_descends (prefixWord ++ tailWord_4174011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4174013 : List Nat := [1, 4, 1, 2, 1, 1, 1, 4, 4, 3]
def baseStart_4174013 : Nat := 118140960795 + 4174013 * 2 ^ 59
def prefixEnd_4174013 : Nat := 4983230072969 + 3 ^ 40 * 4174013 * 2
def baseEnd_4174013 : Nat := 1428849951410188592427713

theorem tailTrace_4174013 : CollatzResearch.WordTrace tailWord_4174013 prefixEnd_4174013 1428849951410188592427713 := by
  unfold tailWord_4174013
  simp only [CollatzResearch.WordTrace]
  refine ⟨152238761027271240511454693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101492507351514160340969795 152238761027271240511454693)
  ·
    refine ⟨28544767692613357595897755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 152238761027271240511454693 28544767692613357595897755)
    ·
      refine ⟨42817151538920036393846633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28544767692613357595897755 42817151538920036393846633)
      ·
        refine ⟨32112863654190027295384975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42817151538920036393846633 32112863654190027295384975)
        ·
          refine ⟨48169295481285040943077463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32112863654190027295384975 48169295481285040943077463)
          ·
            refine ⟨72253943221927561414616195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48169295481285040943077463 72253943221927561414616195)
            ·
              refine ⟨108380914832891342121924293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72253943221927561414616195 108380914832891342121924293)
              ·
                refine ⟨20321421531167126647860805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 108380914832891342121924293 20321421531167126647860805)
                ·
                  refine ⟨3810266537093836246473901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20321421531167126647860805 3810266537093836246473901)
                  ·
                    refine ⟨1428849951410188592427713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3810266537093836246473901 1428849951410188592427713)
                    ·
                      rfl

theorem cell22_4174013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 4, 4, 3].length) (baseStart_4174013 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4174013 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4174013 prefixEnd_4174013 := by exact prefixLift 4174013
  have htrace : WordTrace (prefixWord ++ tailWord_4174013) baseStart_4174013 baseEnd_4174013 := by
    simpa [prefixWord, tailWord_4174013, baseEnd_4174013] using wordTrace_append hprefix tailTrace_4174013
  have hstable : (prefixWord ++ tailWord_4174013).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4174013).length < 2 ^ (prefixWord ++ tailWord_4174013).sum := by decide
  have hdescent : baseEnd_4174013 < baseStart_4174013 := by decide
  rcases family_descends (prefixWord ++ tailWord_4174013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4174017 : List Nat := [1, 2, 6, 1, 2, 1, 1, 3, 1, 4]
def baseStart_4174017 : Nat := 118140960795 + 4174017 * 2 ^ 59
def prefixEnd_4174017 : Nat := 4983230072969 + 3 ^ 40 * 4174017 * 2
def baseEnd_4174017 : Nat := 1428851320691933915327701

theorem tailTrace_4174017 : CollatzResearch.WordTrace tailWord_4174017 prefixEnd_4174017 1428851320691933915327701 := by
  unfold tailWord_4174017
  simp only [CollatzResearch.WordTrace]
  refine ⟨152238906919256749194600305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101492604612837832796400203 152238906919256749194600305)
  ·
    refine ⟨114179180189442561895950229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152238906919256749194600305 114179180189442561895950229)
    ·
      refine ⟨5352149071380120088872667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 114179180189442561895950229 5352149071380120088872667)
      ·
        refine ⟨8028223607070180133309001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5352149071380120088872667 8028223607070180133309001)
        ·
          refine ⟨6021167705302635099981751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8028223607070180133309001 6021167705302635099981751)
          ·
            refine ⟨9031751557953952649972627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6021167705302635099981751 9031751557953952649972627)
            ·
              refine ⟨13547627336930928974958941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9031751557953952649972627 13547627336930928974958941)
              ·
                refine ⟨5080360251349098365609603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13547627336930928974958941 5080360251349098365609603)
                ·
                  refine ⟨7620540377023647548414405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5080360251349098365609603 7620540377023647548414405)
                  ·
                    refine ⟨1428851320691933915327701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7620540377023647548414405 1428851320691933915327701)
                    ·
                      rfl

theorem cell22_4174017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 1, 3, 1, 4].length) (baseStart_4174017 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4174017 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4174017 prefixEnd_4174017 := by exact prefixLift 4174017
  have htrace : WordTrace (prefixWord ++ tailWord_4174017) baseStart_4174017 baseEnd_4174017 := by
    simpa [prefixWord, tailWord_4174017, baseEnd_4174017] using wordTrace_append hprefix tailTrace_4174017
  have hstable : (prefixWord ++ tailWord_4174017).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4174017).length < 2 ^ (prefixWord ++ tailWord_4174017).sum := by decide
  have hdescent : baseEnd_4174017 < baseStart_4174017 := by decide
  rcases family_descends (prefixWord ++ tailWord_4174017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4174026 : List Nat := [3, 1, 2, 1, 3, 1, 11]
def baseStart_4174026 : Nat := 118140960795 + 4174026 * 2 ^ 59
def prefixEnd_4174026 : Nat := 4983230072969 + 3 ^ 40 * 4174026 * 2
def baseEnd_4174026 : Nat := 52920533391698551550099

theorem tailTrace_4174026 : CollatzResearch.WordTrace tailWord_4174026 prefixEnd_4174026 52920533391698551550099 := by
  unfold tailWord_4174026
  simp only [CollatzResearch.WordTrace]
  refine ⟨38059808794056035932919483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101492823450816095821118621 38059808794056035932919483)
  ·
    refine ⟨57089713191084053899379225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38059808794056035932919483 57089713191084053899379225)
    ·
      refine ⟨42817284893313040424534419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57089713191084053899379225 42817284893313040424534419)
      ·
        refine ⟨64225927339969560636801629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42817284893313040424534419 64225927339969560636801629)
        ·
          refine ⟨24084722752488585238800611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64225927339969560636801629 24084722752488585238800611)
          ·
            refine ⟨36127084128732877858200917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24084722752488585238800611 36127084128732877858200917)
            ·
              refine ⟨52920533391698551550099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 36127084128732877858200917 52920533391698551550099)
              ·
                rfl

theorem cell22_4174026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 11].length) (baseStart_4174026 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4174026 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4174026 prefixEnd_4174026 := by exact prefixLift 4174026
  have htrace : WordTrace (prefixWord ++ tailWord_4174026) baseStart_4174026 baseEnd_4174026 := by
    simpa [prefixWord, tailWord_4174026, baseEnd_4174026] using wordTrace_append hprefix tailTrace_4174026
  have hstable : (prefixWord ++ tailWord_4174026).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4174026).length < 2 ^ (prefixWord ++ tailWord_4174026).sum := by decide
  have hdescent : baseEnd_4174026 < baseStart_4174026 := by decide
  rcases family_descends (prefixWord ++ tailWord_4174026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4174030 : List Nat := [4, 1, 1, 1, 4, 2, 1, 1, 4, 3]
def baseStart_4174030 : Nat := 118140960795 + 4174030 * 2 ^ 59
def prefixEnd_4174030 : Nat := 4983230072969 + 3 ^ 40 * 4174030 * 2
def baseEnd_4174030 : Nat := 1428855770857606214752661

theorem tailTrace_4174030 : CollatzResearch.WordTrace tailWord_4174030 prefixEnd_4174030 1428855770857606214752661 := by
  unfold tailWord_4174030
  simp only [CollatzResearch.WordTrace]
  refine ⟨19029922633526206551852943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 101492920712139768276549029 19029922633526206551852943)
  ·
    refine ⟨28544883950289309827779415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19029922633526206551852943 28544883950289309827779415)
    ·
      refine ⟨42817325925433964741669123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28544883950289309827779415 42817325925433964741669123)
      ·
        refine ⟨64225988888150947112503685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42817325925433964741669123 64225988888150947112503685)
        ·
          refine ⟨12042372916528302583594441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 64225988888150947112503685 12042372916528302583594441)
          ·
            refine ⟨9031779687396226937695831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12042372916528302583594441 9031779687396226937695831)
            ·
              refine ⟨13547669531094340406543747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9031779687396226937695831 13547669531094340406543747)
              ·
                refine ⟨20321504296641510609815621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13547669531094340406543747 20321504296641510609815621)
                ·
                  refine ⟨3810282055620283239340429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20321504296641510609815621 3810282055620283239340429)
                  ·
                    refine ⟨1428855770857606214752661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3810282055620283239340429 1428855770857606214752661)
                    ·
                      rfl

theorem cell22_4174030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 1, 1, 4, 3].length) (baseStart_4174030 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4174030 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4174030 prefixEnd_4174030 := by exact prefixLift 4174030
  have htrace : WordTrace (prefixWord ++ tailWord_4174030) baseStart_4174030 baseEnd_4174030 := by
    simpa [prefixWord, tailWord_4174030, baseEnd_4174030] using wordTrace_append hprefix tailTrace_4174030
  have hstable : (prefixWord ++ tailWord_4174030).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4174030).length < 2 ^ (prefixWord ++ tailWord_4174030).sum := by decide
  have hdescent : baseEnd_4174030 < baseStart_4174030 := by decide
  rcases family_descends (prefixWord ++ tailWord_4174030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4174088 : List Nat := [2, 1, 3, 2, 3, 1, 2, 1, 7]
def baseStart_4174088 : Nat := 118140960795 + 4174088 * 2 ^ 59
def prefixEnd_4174088 : Nat := 4983230072969 + 3 ^ 40 * 4174088 * 2
def baseEnd_4174088 : Nat := 476291875147637798934161

theorem tailTrace_4174088 : CollatzResearch.WordTrace tailWord_4174088 prefixEnd_4174088 476291875147637798934161 := by
  unfold tailWord_4174088
  simp only [CollatzResearch.WordTrace]
  refine ⟨76120748250999764160217459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101494331001333018880289945 76120748250999764160217459)
  ·
    refine ⟨114181122376499646240326189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76120748250999764160217459 114181122376499646240326189)
    ·
      refine ⟨42817920891187367340122321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114181122376499646240326189 42817920891187367340122321)
      ·
        refine ⟨32113440668390525505091741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42817920891187367340122321 32113440668390525505091741)
        ·
          refine ⟨12042540250646447064409403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32113440668390525505091741 12042540250646447064409403)
          ·
            refine ⟨18063810375969670596614105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12042540250646447064409403 18063810375969670596614105)
            ·
              refine ⟨13547857781977252947460579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18063810375969670596614105 13547857781977252947460579)
              ·
                refine ⟨20321786672965879421190869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13547857781977252947460579 20321786672965879421190869)
                ·
                  refine ⟨476291875147637798934161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20321786672965879421190869 476291875147637798934161)
                  ·
                    rfl

theorem cell22_4174088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 2, 1, 7].length) (baseStart_4174088 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4174088 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4174088 prefixEnd_4174088 := by exact prefixLift 4174088
  have htrace : WordTrace (prefixWord ++ tailWord_4174088) baseStart_4174088 baseEnd_4174088 := by
    simpa [prefixWord, tailWord_4174088, baseEnd_4174088] using wordTrace_append hprefix tailTrace_4174088
  have hstable : (prefixWord ++ tailWord_4174088).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4174088).length < 2 ^ (prefixWord ++ tailWord_4174088).sum := by decide
  have hdescent : baseEnd_4174088 < baseStart_4174088 := by decide
  rcases family_descends (prefixWord ++ tailWord_4174088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4174244 : List Nat := [2, 3, 1, 2, 1, 1, 5, 3, 1, 3]
def baseStart_4174244 : Nat := 118140960795 + 4174244 * 2 ^ 59
def prefixEnd_4174244 : Nat := 4983230072969 + 3 ^ 40 * 4174244 * 2
def baseEnd_4174244 : Nat := 1428929027430980989902005

theorem tailTrace_4174244 : CollatzResearch.WordTrace tailWord_4174244 prefixEnd_4174244 1428929027430980989902005 := by
  unfold tailWord_4174244
  simp only [CollatzResearch.WordTrace]
  refine ⟨76123593144717183481556893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101498124192956244642075857 76123593144717183481556893)
  ·
    refine ⟨28546347429268943805583835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76123593144717183481556893 28546347429268943805583835)
    ·
      refine ⟨42819521143903415708375753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28546347429268943805583835 42819521143903415708375753)
      ·
        refine ⟨32114640857927561781281815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42819521143903415708375753 32114640857927561781281815)
        ·
          refine ⟨48171961286891342671922723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32114640857927561781281815 48171961286891342671922723)
          ·
            refine ⟨72257941930337014007884085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48171961286891342671922723 72257941930337014007884085)
            ·
              refine ⟨6774182055969095063239133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 72257941930337014007884085 6774182055969095063239133)
              ·
                refine ⟨2540318270988410648714675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6774182055969095063239133 2540318270988410648714675)
                ·
                  refine ⟨3810477406482615973072013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2540318270988410648714675 3810477406482615973072013)
                  ·
                    refine ⟨1428929027430980989902005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3810477406482615973072013 1428929027430980989902005)
                    ·
                      rfl

theorem cell22_4174244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 5, 3, 1, 3].length) (baseStart_4174244 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4174244 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4174244 prefixEnd_4174244 := by exact prefixLift 4174244
  have htrace : WordTrace (prefixWord ++ tailWord_4174244) baseStart_4174244 baseEnd_4174244 := by
    simpa [prefixWord, tailWord_4174244, baseEnd_4174244] using wordTrace_append hprefix tailTrace_4174244
  have hstable : (prefixWord ++ tailWord_4174244).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4174244).length < 2 ^ (prefixWord ++ tailWord_4174244).sum := by decide
  have hdescent : baseEnd_4174244 < baseStart_4174244 := by decide
  rcases family_descends (prefixWord ++ tailWord_4174244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4174261 : List Nat := [1, 3, 3, 2, 4, 1, 1, 1, 3, 3]
def baseStart_4174261 : Nat := 118140960795 + 4174261 * 2 ^ 59
def prefixEnd_4174261 : Nat := 4983230072969 + 3 ^ 40 * 4174261 * 2
def baseEnd_4174261 : Nat := 1428934846878398612226953

theorem tailTrace_4174261 : CollatzResearch.WordTrace tailWord_4174261 prefixEnd_4174261 1428934846878398612226953 := by
  unfold tailWord_4174261
  simp only [CollatzResearch.WordTrace]
  refine ⟨152247806330372778866482637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101498537553581852577655091 152247806330372778866482637)
  ·
    refine ⟨57092927373889792074930989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152247806330372778866482637 57092927373889792074930989)
    ·
      refine ⟨21409847765208672028099121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57092927373889792074930989 21409847765208672028099121)
      ·
        refine ⟨16057385823906504021074341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21409847765208672028099121 16057385823906504021074341)
        ·
          refine ⟨3010759841982469503951439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16057385823906504021074341 3010759841982469503951439)
          ·
            refine ⟨4516139762973704255927159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3010759841982469503951439 4516139762973704255927159)
            ·
              refine ⟨6774209644460556383890739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4516139762973704255927159 6774209644460556383890739)
              ·
                refine ⟨10161314466690834575836109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6774209644460556383890739 10161314466690834575836109)
                ·
                  refine ⟨3810492925009062965938541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10161314466690834575836109 3810492925009062965938541)
                  ·
                    refine ⟨1428934846878398612226953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3810492925009062965938541 1428934846878398612226953)
                    ·
                      rfl

theorem cell22_4174261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 4, 1, 1, 1, 3, 3].length) (baseStart_4174261 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4174261 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4174261 prefixEnd_4174261 := by exact prefixLift 4174261
  have htrace : WordTrace (prefixWord ++ tailWord_4174261) baseStart_4174261 baseEnd_4174261 := by
    simpa [prefixWord, tailWord_4174261, baseEnd_4174261] using wordTrace_append hprefix tailTrace_4174261
  have hstable : (prefixWord ++ tailWord_4174261).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4174261).length < 2 ^ (prefixWord ++ tailWord_4174261).sum := by decide
  have hdescent : baseEnd_4174261 < baseStart_4174261 := by decide
  rcases family_descends (prefixWord ++ tailWord_4174261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4174315 : List Nat := [1, 1, 1, 1, 2, 3, 3, 4, 2, 4]
def baseStart_4174315 : Nat := 118140960795 + 4174315 * 2 ^ 59
def prefixEnd_4174315 : Nat := 4983230072969 + 3 ^ 40 * 4174315 * 2
def baseEnd_4174315 : Nat := 1428953332181960471376787

theorem tailTrace_4174315 : CollatzResearch.WordTrace tailWord_4174315 prefixEnd_4174315 1428953332181960471376787 := by
  unfold tailWord_4174315
  simp only [CollatzResearch.WordTrace]
  refine ⟨152249775872177146088948399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101499850581451430725965599 152249775872177146088948399)
  ·
    refine ⟨228374663808265719133422599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152249775872177146088948399 228374663808265719133422599)
    ·
      refine ⟨342561995712398578700133899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228374663808265719133422599 342561995712398578700133899)
      ·
        refine ⟨513842993568597868050200849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 342561995712398578700133899 513842993568597868050200849)
        ·
          refine ⟨385382245176448401037650637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 513842993568597868050200849 385382245176448401037650637)
          ·
            refine ⟨144518341941168150389118989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 385382245176448401037650637 144518341941168150389118989)
            ·
              refine ⟨54194378227938056395919621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 144518341941168150389118989 54194378227938056395919621)
              ·
                refine ⟨10161445917738385574234929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 54194378227938056395919621 10161445917738385574234929)
                ·
                  refine ⟨7621084438303789180676197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10161445917738385574234929 7621084438303789180676197)
                  ·
                    refine ⟨1428953332181960471376787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7621084438303789180676197 1428953332181960471376787)
                    ·
                      rfl

theorem cell22_4174315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 4, 2, 4].length) (baseStart_4174315 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4174315 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4174315 prefixEnd_4174315 := by exact prefixLift 4174315
  have htrace : WordTrace (prefixWord ++ tailWord_4174315) baseStart_4174315 baseEnd_4174315 := by
    simpa [prefixWord, tailWord_4174315, baseEnd_4174315] using wordTrace_append hprefix tailTrace_4174315
  have hstable : (prefixWord ++ tailWord_4174315).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4174315).length < 2 ^ (prefixWord ++ tailWord_4174315).sum := by decide
  have hdescent : baseEnd_4174315 < baseStart_4174315 := by decide
  rcases family_descends (prefixWord ++ tailWord_4174315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4174347 : List Nat := [1, 1, 1, 1, 7, 2, 3, 6]
def baseStart_4174347 : Nat := 118140960795 + 4174347 * 2 ^ 59
def prefixEnd_4174347 : Nat := 4983230072969 + 3 ^ 40 * 4174347 * 2
def baseEnd_4174347 : Nat := 158773809603991450508521

theorem tailTrace_4174347 : CollatzResearch.WordTrace tailWord_4174347 prefixEnd_4174347 158773809603991450508521 := by
  unfold tailWord_4174347
  simp only [CollatzResearch.WordTrace]
  refine ⟨152250943008061215554113295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101500628672040810369408863 152250943008061215554113295)
  ·
    refine ⟨228376414512091823331169943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152250943008061215554113295 228376414512091823331169943)
    ·
      refine ⟨342564621768137734996754915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228376414512091823331169943 342564621768137734996754915)
      ·
        refine ⟨513846932652206602495132373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 342564621768137734996754915 513846932652206602495132373)
        ·
          refine ⟨12043287484036092245979665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 513846932652206602495132373 12043287484036092245979665)
          ·
            refine ⟨9032465613027069184484749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12043287484036092245979665 9032465613027069184484749)
            ·
              refine ⟨3387174604885150944181781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9032465613027069184484749 3387174604885150944181781)
              ·
                refine ⟨158773809603991450508521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3387174604885150944181781 158773809603991450508521)
                ·
                  rfl

theorem cell22_4174347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 3, 6].length) (baseStart_4174347 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4174347 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4174347 prefixEnd_4174347 := by exact prefixLift 4174347
  have htrace : WordTrace (prefixWord ++ tailWord_4174347) baseStart_4174347 baseEnd_4174347 := by
    simpa [prefixWord, tailWord_4174347, baseEnd_4174347] using wordTrace_append hprefix tailTrace_4174347
  have hstable : (prefixWord ++ tailWord_4174347).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4174347).length < 2 ^ (prefixWord ++ tailWord_4174347).sum := by decide
  have hdescent : baseEnd_4174347 < baseStart_4174347 := by decide
  rcases family_descends (prefixWord ++ tailWord_4174347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4174368 : List Nat := [2, 1, 1, 6, 3, 1, 1, 2, 2, 3]
def baseStart_4174368 : Nat := 118140960795 + 4174368 * 2 ^ 59
def prefixEnd_4174368 : Nat := 4983230072969 + 3 ^ 40 * 4174368 * 2
def baseEnd_4174368 : Nat := 1428971475165085999801625

theorem tailTrace_4174368 : CollatzResearch.WordTrace tailWord_4174368 prefixEnd_4174368 1428971475165085999801625 := by
  unfold tailWord_4174368
  simp only [CollatzResearch.WordTrace]
  refine ⟨76125854470492568070313879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101501139293990090760418505 76125854470492568070313879)
  ·
    refine ⟨114188781705738852105470819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76125854470492568070313879 114188781705738852105470819)
    ·
      refine ⟨171283172558608278158206229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114188781705738852105470819 171283172558608278158206229)
      ·
        refine ⟨8028898713684763038665917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 171283172558608278158206229 8028898713684763038665917)
        ·
          refine ⟨3010837017631786139499719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8028898713684763038665917 3010837017631786139499719)
          ·
            refine ⟨4516255526447679209249579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3010837017631786139499719 4516255526447679209249579)
            ·
              refine ⟨6774383289671518813874369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4516255526447679209249579 6774383289671518813874369)
              ·
                refine ⟨5080787467253639110405777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6774383289671518813874369 5080787467253639110405777)
                ·
                  refine ⟨3810590600440229332804333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5080787467253639110405777 3810590600440229332804333)
                  ·
                    refine ⟨1428971475165085999801625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3810590600440229332804333 1428971475165085999801625)
                    ·
                      rfl

theorem cell22_4174368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 3, 1, 1, 2, 2, 3].length) (baseStart_4174368 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4174368 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4174368 prefixEnd_4174368 := by exact prefixLift 4174368
  have htrace : WordTrace (prefixWord ++ tailWord_4174368) baseStart_4174368 baseEnd_4174368 := by
    simpa [prefixWord, tailWord_4174368, baseEnd_4174368] using wordTrace_append hprefix tailTrace_4174368
  have hstable : (prefixWord ++ tailWord_4174368).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4174368).length < 2 ^ (prefixWord ++ tailWord_4174368).sum := by decide
  have hdescent : baseEnd_4174368 < baseStart_4174368 := by decide
  rcases family_descends (prefixWord ++ tailWord_4174368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4174398 : List Nat := [4, 2, 1, 4, 2, 1, 2, 6]
def baseStart_4174398 : Nat := 118140960795 + 4174398 * 2 ^ 59
def prefixEnd_4174398 : Nat := 4983230072969 + 3 ^ 40 * 4174398 * 2
def baseEnd_4174398 : Nat := 158775749419797324616837

theorem tailTrace_4174398 : CollatzResearch.WordTrace tailWord_4174398 prefixEnd_4174398 158775749419797324616837 := by
  unfold tailWord_4174398
  simp only [CollatzResearch.WordTrace]
  refine ⟨19031600391359556408027481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 101501868753917634176146565 19031600391359556408027481)
  ·
    refine ⟨14273700293519667306020611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19031600391359556408027481 14273700293519667306020611)
    ·
      refine ⟨21410550440279500959030917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14273700293519667306020611 21410550440279500959030917)
      ·
        refine ⟨4014478207552406429818297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21410550440279500959030917 4014478207552406429818297)
        ·
          refine ⟨3010858655664304822363723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4014478207552406429818297 3010858655664304822363723)
          ·
            refine ⟨4516287983496457233545585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3010858655664304822363723 4516287983496457233545585)
            ·
              refine ⟨3387215987622342925159189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4516287983496457233545585 3387215987622342925159189)
              ·
                refine ⟨158775749419797324616837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3387215987622342925159189 158775749419797324616837)
                ·
                  rfl

theorem cell22_4174398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 2, 1, 2, 6].length) (baseStart_4174398 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4174398 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4174398 prefixEnd_4174398 := by exact prefixLift 4174398
  have htrace : WordTrace (prefixWord ++ tailWord_4174398) baseStart_4174398 baseEnd_4174398 := by
    simpa [prefixWord, tailWord_4174398, baseEnd_4174398] using wordTrace_append hprefix tailTrace_4174398
  have hstable : (prefixWord ++ tailWord_4174398).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4174398).length < 2 ^ (prefixWord ++ tailWord_4174398).sum := by decide
  have hdescent : baseEnd_4174398 < baseStart_4174398 := by decide
  rcases family_descends (prefixWord ++ tailWord_4174398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4174413 : List Nat := [1, 6, 1, 1, 2, 1, 3, 3, 1, 3]
def baseStart_4174413 : Nat := 118140960795 + 4174413 * 2 ^ 59
def prefixEnd_4174413 : Nat := 4983230072969 + 3 ^ 40 * 4174413 * 2
def baseEnd_4174413 : Nat := 1428986879584720882426487

theorem tailTrace_4174413 : CollatzResearch.WordTrace tailWord_4174413 prefixEnd_4174413 1428986879584720882426487 := by
  unfold tailWord_4174413
  simp only [CollatzResearch.WordTrace]
  refine ⟨152253350225822108826015893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101502233483881405884010595 152253350225822108826015893)
  ·
    refine ⟨7136875791835411351219495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 152253350225822108826015893 7136875791835411351219495)
    ·
      refine ⟨10705313687753117026829243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7136875791835411351219495 10705313687753117026829243)
      ·
        refine ⟨16057970531629675540243865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10705313687753117026829243 16057970531629675540243865)
        ·
          refine ⟨12043477898722256655182899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16057970531629675540243865 12043477898722256655182899)
          ·
            refine ⟨18065216848083384982774349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12043477898722256655182899 18065216848083384982774349)
            ·
              refine ⟨6774456318031269368540381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18065216848083384982774349 6774456318031269368540381)
              ·
                refine ⟨2540421119261726013202643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6774456318031269368540381 2540421119261726013202643)
                ·
                  refine ⟨3810631678892589019803965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2540421119261726013202643 3810631678892589019803965)
                  ·
                    refine ⟨1428986879584720882426487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3810631678892589019803965 1428986879584720882426487)
                    ·
                      rfl

theorem cell22_4174413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 3, 3, 1, 3].length) (baseStart_4174413 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4174413 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4174413 prefixEnd_4174413 := by exact prefixLift 4174413
  have htrace : WordTrace (prefixWord ++ tailWord_4174413) baseStart_4174413 baseEnd_4174413 := by
    simpa [prefixWord, tailWord_4174413, baseEnd_4174413] using wordTrace_append hprefix tailTrace_4174413
  have hstable : (prefixWord ++ tailWord_4174413).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4174413).length < 2 ^ (prefixWord ++ tailWord_4174413).sum := by decide
  have hdescent : baseEnd_4174413 < baseStart_4174413 := by decide
  rcases family_descends (prefixWord ++ tailWord_4174413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4174467 : List Nat := [1, 1, 1, 3, 3, 1, 3, 3, 2, 4]
def baseStart_4174467 : Nat := 118140960795 + 4174467 * 2 ^ 59
def prefixEnd_4174467 : Nat := 4983230072969 + 3 ^ 40 * 4174467 * 2
def baseEnd_4174467 : Nat := 1429005364888282741576321

theorem tailTrace_4174467 : CollatzResearch.WordTrace tailWord_4174467 prefixEnd_4174467 1429005364888282741576321 := by
  unfold tailWord_4174467
  simp only [CollatzResearch.WordTrace]
  refine ⟨152255319767626476048481655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101503546511750984032321103 152255319767626476048481655)
  ·
    refine ⟨228382979651439714072722483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152255319767626476048481655 228382979651439714072722483)
    ·
      refine ⟨342574469477159571109083725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228382979651439714072722483 342574469477159571109083725)
      ·
        refine ⟨128465426053934839165906397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 342574469477159571109083725 128465426053934839165906397)
        ·
          refine ⟨48174534770225564687214899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 128465426053934839165906397 48174534770225564687214899)
          ·
            refine ⟨72261802155338347030822349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48174534770225564687214899 72261802155338347030822349)
            ·
              refine ⟨27098175808251880136558381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72261802155338347030822349 27098175808251880136558381)
              ·
                refine ⟨10161815928094455051209393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27098175808251880136558381 10161815928094455051209393)
                ·
                  refine ⟨7621361946070841288407045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10161815928094455051209393 7621361946070841288407045)
                  ·
                    refine ⟨1429005364888282741576321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7621361946070841288407045 1429005364888282741576321)
                    ·
                      rfl

theorem cell22_4174467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 3, 2, 4].length) (baseStart_4174467 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4174467 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4174467 prefixEnd_4174467 := by exact prefixLift 4174467
  have htrace : WordTrace (prefixWord ++ tailWord_4174467) baseStart_4174467 baseEnd_4174467 := by
    simpa [prefixWord, tailWord_4174467, baseEnd_4174467] using wordTrace_append hprefix tailTrace_4174467
  have hstable : (prefixWord ++ tailWord_4174467).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4174467).length < 2 ^ (prefixWord ++ tailWord_4174467).sum := by decide
  have hdescent : baseEnd_4174467 < baseStart_4174467 := by decide
  rcases family_descends (prefixWord ++ tailWord_4174467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4174482 : List Nat := [3, 2, 3, 1, 2, 11]
def baseStart_4174482 : Nat := 118140960795 + 4174482 * 2 ^ 59
def prefixEnd_4174482 : Nat := 4983230072969 + 3 ^ 40 * 4174482 * 2
def baseEnd_4174482 : Nat := 17642104934504045709275

theorem tailTrace_4174482 : CollatzResearch.WordTrace tailWord_4174482 prefixEnd_4174482 17642104934504045709275 := by
  unfold tailWord_4174482
  simp only [CollatzResearch.WordTrace]
  refine ⟨38063966715643033402569425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101503911241714755740185133 38063966715643033402569425)
  ·
    refine ⟨28547975036732275051927069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38063966715643033402569425 28547975036732275051927069)
    ·
      refine ⟨10705490638774603144472651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28547975036732275051927069 10705490638774603144472651)
      ·
        refine ⟨16058235958161904716708977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10705490638774603144472651 16058235958161904716708977)
        ·
          refine ⟨12043676968621428537531733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16058235958161904716708977 12043676968621428537531733)
          ·
            refine ⟨17642104934504045709275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 12043676968621428537531733 17642104934504045709275)
            ·
              rfl

theorem cell22_4174482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 11].length) (baseStart_4174482 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4174482 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4174482 prefixEnd_4174482 := by exact prefixLift 4174482
  have htrace : WordTrace (prefixWord ++ tailWord_4174482) baseStart_4174482 baseEnd_4174482 := by
    simpa [prefixWord, tailWord_4174482, baseEnd_4174482] using wordTrace_append hprefix tailTrace_4174482
  have hstable : (prefixWord ++ tailWord_4174482).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4174482).length < 2 ^ (prefixWord ++ tailWord_4174482).sum := by decide
  have hdescent : baseEnd_4174482 < baseStart_4174482 := by decide
  rcases family_descends (prefixWord ++ tailWord_4174482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4174548 : List Nat := [2, 4, 1, 3, 2, 1, 2, 1, 3, 3]
def baseStart_4174548 : Nat := 118140960795 + 4174548 * 2 ^ 59
def prefixEnd_4174548 : Nat := 4983230072969 + 3 ^ 40 * 4174548 * 2
def baseEnd_4174548 : Nat := 1429033092843625530301073

theorem tailTrace_4174548 : CollatzResearch.WordTrace tailWord_4174548 prefixEnd_4174548 1429033092843625530301073 := by
  unfold tailWord_4174548
  simp only [CollatzResearch.WordTrace]
  refine ⟨76129137040166513441090149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101505516053555351254786865 76129137040166513441090149)
  ·
    refine ⟨14274213195031221270204403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 76129137040166513441090149 14274213195031221270204403)
    ·
      refine ⟨21411319792546831905306605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14274213195031221270204403 21411319792546831905306605)
      ·
        refine ⟨8029244922205061964489977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21411319792546831905306605 8029244922205061964489977)
        ·
          refine ⟨6021933691653796473367483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8029244922205061964489977 6021933691653796473367483)
          ·
            refine ⟨9032900537480694710051225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6021933691653796473367483 9032900537480694710051225)
            ·
              refine ⟨6774675403110521032538419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9032900537480694710051225 6774675403110521032538419)
              ·
                refine ⟨10162013104665781548807629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6774675403110521032538419 10162013104665781548807629)
                ·
                  refine ⟨3810754914249668080802861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10162013104665781548807629 3810754914249668080802861)
                  ·
                    refine ⟨1429033092843625530301073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3810754914249668080802861 1429033092843625530301073)
                    ·
                      rfl

theorem cell22_4174548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 2, 1, 3, 3].length) (baseStart_4174548 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4174548 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4174548 prefixEnd_4174548 := by exact prefixLift 4174548
  have htrace : WordTrace (prefixWord ++ tailWord_4174548) baseStart_4174548 baseEnd_4174548 := by
    simpa [prefixWord, tailWord_4174548, baseEnd_4174548] using wordTrace_append hprefix tailTrace_4174548
  have hstable : (prefixWord ++ tailWord_4174548).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4174548).length < 2 ^ (prefixWord ++ tailWord_4174548).sum := by decide
  have hdescent : baseEnd_4174548 < baseStart_4174548 := by decide
  rcases family_descends (prefixWord ++ tailWord_4174548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4174561 : List Nat := [1, 2, 3, 1, 4, 2, 3, 1, 5]
def baseStart_4174561 : Nat := 118140960795 + 4174561 * 2 ^ 59
def prefixEnd_4174561 : Nat := 4983230072969 + 3 ^ 40 * 4174561 * 2
def baseEnd_4174561 : Nat := 476345847669765943242011

theorem tailTrace_4174561 : CollatzResearch.WordTrace tailWord_4174561 prefixEnd_4174561 476345847669765943242011 := by
  unfold tailWord_4174561
  simp only [CollatzResearch.WordTrace]
  refine ⟨152258748229285930102403537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101505832152857286734935691 152258748229285930102403537)
  ·
    refine ⟨114194061171964447576802653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152258748229285930102403537 114194061171964447576802653)
    ·
      refine ⟨42822772939486667841300995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114194061171964447576802653 42822772939486667841300995)
      ·
        refine ⟨64234159409230001761951493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42822772939486667841300995 64234159409230001761951493)
        ·
          refine ⟨12043904889230625330365905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 64234159409230001761951493 12043904889230625330365905)
          ·
            refine ⟨9032928666922968997774429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12043904889230625330365905 9032928666922968997774429)
            ·
              refine ⟨3387348250096113374165411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9032928666922968997774429 3387348250096113374165411)
              ·
                refine ⟨5081022375144170061248117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3387348250096113374165411 5081022375144170061248117)
                ·
                  refine ⟨476345847669765943242011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5081022375144170061248117 476345847669765943242011)
                  ·
                    rfl

theorem cell22_4174561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 3, 1, 5].length) (baseStart_4174561 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4174561 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4174561 prefixEnd_4174561 := by exact prefixLift 4174561
  have htrace : WordTrace (prefixWord ++ tailWord_4174561) baseStart_4174561 baseEnd_4174561 := by
    simpa [prefixWord, tailWord_4174561, baseEnd_4174561] using wordTrace_append hprefix tailTrace_4174561
  have hstable : (prefixWord ++ tailWord_4174561).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4174561).length < 2 ^ (prefixWord ++ tailWord_4174561).sum := by decide
  have hdescent : baseEnd_4174561 < baseStart_4174561 := by decide
  rcases family_descends (prefixWord ++ tailWord_4174561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4174657 : List Nat := [1, 2, 5, 3, 1, 2, 2, 2, 4]
def baseStart_4174657 : Nat := 118140960795 + 4174657 * 2 ^ 59
def prefixEnd_4174657 : Nat := 4983230072969 + 3 ^ 40 * 4174657 * 2
def baseEnd_4174657 : Nat := 476356801923728526441913

theorem tailTrace_4174657 : CollatzResearch.WordTrace tailWord_4174657 prefixEnd_4174657 476356801923728526441913 := by
  unfold tailWord_4174657
  simp only [CollatzResearch.WordTrace]
  refine ⟨152262249636938138497898225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101508166424625425665265483 152262249636938138497898225)
  ·
    refine ⟨114196687227703603873423669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152262249636938138497898225 114196687227703603873423669)
    ·
      refine ⟨10705939427597212863133469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 114196687227703603873423669 10705939427597212863133469)
      ·
        refine ⟨4014727285348954823675051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10705939427597212863133469 4014727285348954823675051)
        ·
          refine ⟨6022090928023432235512577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4014727285348954823675051 6022090928023432235512577)
          ·
            refine ⟨4516568196017574176634433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6022090928023432235512577 4516568196017574176634433)
            ·
              refine ⟨3387426147013180632475825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4516568196017574176634433 3387426147013180632475825)
              ·
                refine ⟨2540569610259885474356869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3387426147013180632475825 2540569610259885474356869)
                ·
                  refine ⟨476356801923728526441913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2540569610259885474356869 476356801923728526441913)
                  ·
                    rfl

theorem cell22_4174657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 2, 2, 2, 4].length) (baseStart_4174657 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4174657 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4174657 prefixEnd_4174657 := by exact prefixLift 4174657
  have htrace : WordTrace (prefixWord ++ tailWord_4174657) baseStart_4174657 baseEnd_4174657 := by
    simpa [prefixWord, tailWord_4174657, baseEnd_4174657] using wordTrace_append hprefix tailTrace_4174657
  have hstable : (prefixWord ++ tailWord_4174657).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4174657).length < 2 ^ (prefixWord ++ tailWord_4174657).sum := by decide
  have hdescent : baseEnd_4174657 < baseStart_4174657 := by decide
  rcases family_descends (prefixWord ++ tailWord_4174657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4174739 : List Nat := [1, 1, 1, 2, 1, 2, 1, 7, 1, 5]
def baseStart_4174739 : Nat := 118140960795 + 4174739 * 2 ^ 59
def prefixEnd_4174739 : Nat := 4983230072969 + 3 ^ 40 * 4174739 * 2
def baseEnd_4174739 : Nat := 1429098476046964698775487

theorem tailTrace_4174739 : CollatzResearch.WordTrace tailWord_4174739 prefixEnd_4174739 1429098476046964698775487 := by
  unfold tailWord_4174739
  simp only [CollatzResearch.WordTrace]
  refine ⟨152265240422641066502383271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101510160281760711001588847 152265240422641066502383271)
  ·
    refine ⟨228397860633961599753574907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152265240422641066502383271 228397860633961599753574907)
    ·
      refine ⟨342596790950942399630362361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228397860633961599753574907 342596790950942399630362361)
      ·
        refine ⟨256947593213206799722771771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 342596790950942399630362361 256947593213206799722771771)
        ·
          refine ⟨385421389819810199584157657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 256947593213206799722771771 385421389819810199584157657)
          ·
            refine ⟨289066042364857649688118243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 385421389819810199584157657 289066042364857649688118243)
            ·
              refine ⟨433599063547286474532177365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 289066042364857649688118243 433599063547286474532177365)
              ·
                refine ⟨10162478051889526746847907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 433599063547286474532177365 10162478051889526746847907)
                ·
                  refine ⟨15243717077834290120271861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10162478051889526746847907 15243717077834290120271861)
                  ·
                    refine ⟨1429098476046964698775487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15243717077834290120271861 1429098476046964698775487)
                    ·
                      rfl

theorem cell22_4174739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 7, 1, 5].length) (baseStart_4174739 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4174739 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4174739 prefixEnd_4174739 := by exact prefixLift 4174739
  have htrace : WordTrace (prefixWord ++ tailWord_4174739) baseStart_4174739 baseEnd_4174739 := by
    simpa [prefixWord, tailWord_4174739, baseEnd_4174739] using wordTrace_append hprefix tailTrace_4174739
  have hstable : (prefixWord ++ tailWord_4174739).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4174739).length < 2 ^ (prefixWord ++ tailWord_4174739).sum := by decide
  have hdescent : baseEnd_4174739 < baseStart_4174739 := by decide
  rcases family_descends (prefixWord ++ tailWord_4174739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4174756 : List Nat := [2, 3, 1, 2, 1, 2, 1, 1, 6, 3]
def baseStart_4174756 : Nat := 118140960795 + 4174756 * 2 ^ 59
def prefixEnd_4174756 : Nat := 4983230072969 + 3 ^ 40 * 4174756 * 2
def baseEnd_4174756 : Nat := 1429104295494382321100435

theorem tailTrace_4174756 : CollatzResearch.WordTrace tailWord_4174756 prefixEnd_4174756 1429104295494382321100435 := by
  unfold tailWord_4174756
  simp only [CollatzResearch.WordTrace]
  refine ⟨76132930231789739202876061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101510573642386318937168081 76132930231789739202876061)
  ·
    refine ⟨28549848836921152201078523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76132930231789739202876061 28549848836921152201078523)
    ·
      refine ⟨42824773255381728301617785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28549848836921152201078523 42824773255381728301617785)
      ·
        refine ⟨32118579941536296226213339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42824773255381728301617785 32118579941536296226213339)
        ·
          refine ⟨48177869912304444339320009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32118579941536296226213339 48177869912304444339320009)
          ·
            refine ⟨36133402434228333254490007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48177869912304444339320009 36133402434228333254490007)
            ·
              refine ⟨54200103651342499881735011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36133402434228333254490007 54200103651342499881735011)
              ·
                refine ⟨81300155477013749822602517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54200103651342499881735011 81300155477013749822602517)
                ·
                  refine ⟨3810944787985019522934493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 81300155477013749822602517 3810944787985019522934493)
                  ·
                    refine ⟨1429104295494382321100435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3810944787985019522934493 1429104295494382321100435)
                    ·
                      rfl

theorem cell22_4174756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 1, 6, 3].length) (baseStart_4174756 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4174756 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4174756 prefixEnd_4174756 := by exact prefixLift 4174756
  have htrace : WordTrace (prefixWord ++ tailWord_4174756) baseStart_4174756 baseEnd_4174756 := by
    simpa [prefixWord, tailWord_4174756, baseEnd_4174756] using wordTrace_append hprefix tailTrace_4174756
  have hstable : (prefixWord ++ tailWord_4174756).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4174756).length < 2 ^ (prefixWord ++ tailWord_4174756).sum := by decide
  have hdescent : baseEnd_4174756 < baseStart_4174756 := by decide
  rcases family_descends (prefixWord ++ tailWord_4174756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4174773 : List Nat := [1, 3, 3, 2, 1, 1, 2, 4, 2, 3]
def baseStart_4174773 : Nat := 118140960795 + 4174773 * 2 ^ 59
def prefixEnd_4174773 : Nat := 4983230072969 + 3 ^ 40 * 4174773 * 2
def baseEnd_4174773 : Nat := 1429110114941799943425383

theorem tailTrace_4174773 : CollatzResearch.WordTrace tailWord_4174773 prefixEnd_4174773 1429110114941799943425383 := by
  unfold tailWord_4174773
  simp only [CollatzResearch.WordTrace]
  refine ⟨152266480504517890309120973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101510987003011926872747315 152266480504517890309120973)
  ·
    refine ⟨57099930189194208865920365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152266480504517890309120973 57099930189194208865920365)
    ·
      refine ⟨21412473820947828324720137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57099930189194208865920365 21412473820947828324720137)
      ·
        refine ⟨16059355365710871243540103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21412473820947828324720137 16059355365710871243540103)
        ·
          refine ⟨24089033048566306865310155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16059355365710871243540103 24089033048566306865310155)
          ·
            refine ⟨36133549572849460297965233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24089033048566306865310155 36133549572849460297965233)
            ·
              refine ⟨27100162179637095223473925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36133549572849460297965233 27100162179637095223473925)
              ·
                refine ⟨5081280408681955354401361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27100162179637095223473925 5081280408681955354401361)
                ·
                  refine ⟨3810960306511466515801021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5081280408681955354401361 3810960306511466515801021)
                  ·
                    refine ⟨1429110114941799943425383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3810960306511466515801021 1429110114941799943425383)
                    ·
                      rfl

theorem cell22_4174773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 4, 2, 3].length) (baseStart_4174773 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4174773 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4174773 prefixEnd_4174773 := by exact prefixLift 4174773
  have htrace : WordTrace (prefixWord ++ tailWord_4174773) baseStart_4174773 baseEnd_4174773 := by
    simpa [prefixWord, tailWord_4174773, baseEnd_4174773] using wordTrace_append hprefix tailTrace_4174773
  have hstable : (prefixWord ++ tailWord_4174773).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4174773).length < 2 ^ (prefixWord ++ tailWord_4174773).sum := by decide
  have hdescent : baseEnd_4174773 < baseStart_4174773 := by decide
  rcases family_descends (prefixWord ++ tailWord_4174773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4174801 : List Nat := [1, 2, 2, 1, 2, 1, 4, 1, 5, 3]
def baseStart_4174801 : Nat := 118140960795 + 4174801 * 2 ^ 59
def prefixEnd_4174801 : Nat := 4983230072969 + 3 ^ 40 * 4174801 * 2
def baseEnd_4174801 : Nat := 1429119699914017203725297

theorem tailTrace_4174801 : CollatzResearch.WordTrace tailWord_4174801 prefixEnd_4174801 1429119699914017203725297 := by
  unfold tailWord_4174801
  simp only [CollatzResearch.WordTrace]
  refine ⟨152267501748416451091140257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101511667832277634060760171 152267501748416451091140257)
  ·
    refine ⟨114200626311312338318355193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152267501748416451091140257 114200626311312338318355193)
    ·
      refine ⟨85650469733484253738766395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114200626311312338318355193 85650469733484253738766395)
      ·
        refine ⟨128475704600226380608149593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85650469733484253738766395 128475704600226380608149593)
        ·
          refine ⟨96356778450169785456112195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128475704600226380608149593 96356778450169785456112195)
          ·
            refine ⟨144535167675254678184168293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96356778450169785456112195 144535167675254678184168293)
            ·
              refine ⟨27100343939110252159531555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 144535167675254678184168293 27100343939110252159531555)
              ·
                refine ⟨40650515908665378239297333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27100343939110252159531555 40650515908665378239297333)
                ·
                  refine ⟨3810985866437379209934125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 40650515908665378239297333 3810985866437379209934125)
                  ·
                    refine ⟨1429119699914017203725297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3810985866437379209934125 1429119699914017203725297)
                    ·
                      rfl

theorem cell22_4174801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 1, 5, 3].length) (baseStart_4174801 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4174801 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4174801 prefixEnd_4174801 := by exact prefixLift 4174801
  have htrace : WordTrace (prefixWord ++ tailWord_4174801) baseStart_4174801 baseEnd_4174801 := by
    simpa [prefixWord, tailWord_4174801, baseEnd_4174801] using wordTrace_append hprefix tailTrace_4174801
  have hstable : (prefixWord ++ tailWord_4174801).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4174801).length < 2 ^ (prefixWord ++ tailWord_4174801).sum := by decide
  have hdescent : baseEnd_4174801 < baseStart_4174801 := by decide
  rcases family_descends (prefixWord ++ tailWord_4174801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4174831 : List Nat := [1, 1, 2, 1, 4, 3, 1, 4, 5]
def baseStart_4174831 : Nat := 118140960795 + 4174831 * 2 ^ 59
def prefixEnd_4174831 : Nat := 4983230072969 + 3 ^ 40 * 4174831 * 2
def baseEnd_4174831 : Nat := 476376656509035708491735

theorem tailTrace_4174831 : CollatzResearch.WordTrace tailWord_4174831 prefixEnd_4174831 476376656509035708491735 := by
  unfold tailWord_4174831
  simp only [CollatzResearch.WordTrace]
  refine ⟨152268595938307766214732347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101512397292205177476488231 152268595938307766214732347)
  ·
    refine ⟨228402893907461649322098521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152268595938307766214732347 228402893907461649322098521)
    ·
      refine ⟨171302170430596236991573891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 228402893907461649322098521 171302170430596236991573891)
      ·
        refine ⟨256953255645894355487360837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171302170430596236991573891 256953255645894355487360837)
        ·
          refine ⟨48178735433605191653880157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 256953255645894355487360837 48178735433605191653880157)
          ·
            refine ⟨18067025787601946870205059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48178735433605191653880157 18067025787601946870205059)
            ·
              refine ⟨27100538681402920305307589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18067025787601946870205059 27100538681402920305307589)
              ·
                refine ⟨5081351002763047557245173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27100538681402920305307589 5081351002763047557245173)
                ·
                  refine ⟨476376656509035708491735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5081351002763047557245173 476376656509035708491735)
                  ·
                    rfl

theorem cell22_4174831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 4, 5].length) (baseStart_4174831 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4174831 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4174831 prefixEnd_4174831 := by exact prefixLift 4174831
  have htrace : WordTrace (prefixWord ++ tailWord_4174831) baseStart_4174831 baseEnd_4174831 := by
    simpa [prefixWord, tailWord_4174831, baseEnd_4174831] using wordTrace_append hprefix tailTrace_4174831
  have hstable : (prefixWord ++ tailWord_4174831).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4174831).length < 2 ^ (prefixWord ++ tailWord_4174831).sum := by decide
  have hdescent : baseEnd_4174831 < baseStart_4174831 := by decide
  rcases family_descends (prefixWord ++ tailWord_4174831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4174837 : List Nat := [1, 3, 5, 2, 2, 1, 1, 7]
def baseStart_4174837 : Nat := 118140960795 + 4174837 * 2 ^ 59
def prefixEnd_4174837 : Nat := 4983230072969 + 3 ^ 40 * 4174837 * 2
def baseEnd_4174837 : Nat := 158792447049969456647243

theorem tailTrace_4174837 : CollatzResearch.WordTrace tailWord_4174837 prefixEnd_4174837 158792447049969456647243 := by
  unfold tailWord_4174837
  simp only [CollatzResearch.WordTrace]
  refine ⟨152268814776286029239450765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101512543184190686159633843 152268814776286029239450765)
  ·
    refine ⟨57100805541107260964794037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152268814776286029239450765 57100805541107260964794037)
    ·
      refine ⟨5353200519478805715449441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 57100805541107260964794037 5353200519478805715449441)
      ·
        refine ⟨4014900389609104286587081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5353200519478805715449441 4014900389609104286587081)
        ·
          refine ⟨3011175292206828214940311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4014900389609104286587081 3011175292206828214940311)
          ·
            refine ⟨4516762938310242322410467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3011175292206828214940311 4516762938310242322410467)
            ·
              refine ⟨6775144407465363483615701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4516762938310242322410467 6775144407465363483615701)
              ·
                refine ⟨158792447049969456647243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6775144407465363483615701 158792447049969456647243)
                ·
                  rfl

theorem cell22_4174837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 2, 1, 1, 7].length) (baseStart_4174837 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4174837 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4174837 prefixEnd_4174837 := by exact prefixLift 4174837
  have htrace : WordTrace (prefixWord ++ tailWord_4174837) baseStart_4174837 baseEnd_4174837 := by
    simpa [prefixWord, tailWord_4174837, baseEnd_4174837] using wordTrace_append hprefix tailTrace_4174837
  have hstable : (prefixWord ++ tailWord_4174837).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4174837).length < 2 ^ (prefixWord ++ tailWord_4174837).sum := by decide
  have hdescent : baseEnd_4174837 < baseStart_4174837 := by decide
  rcases family_descends (prefixWord ++ tailWord_4174837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4174906 : List Nat := [3, 1, 1, 1, 3, 1, 3, 2, 1, 6]
def baseStart_4174906 : Nat := 118140960795 + 4174906 * 2 ^ 59
def prefixEnd_4174906 : Nat := 4983230072969 + 3 ^ 40 * 4174906 * 2
def baseEnd_4174906 : Nat := 1429155643559831929849975

theorem tailTrace_4174906 : CollatzResearch.WordTrace tailWord_4174906 prefixEnd_4174906 1429155643559831929849975 := by
  unfold tailWord_4174906
  simp only [CollatzResearch.WordTrace]
  refine ⟨38067832853259013505928143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101514220942024036015808381 38067832853259013505928143)
  ·
    refine ⟨57101749279888520258892215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38067832853259013505928143 57101749279888520258892215)
    ·
      refine ⟨85652623919832780388338323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57101749279888520258892215 85652623919832780388338323)
      ·
        refine ⟨128478935879749170582507485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85652623919832780388338323 128478935879749170582507485)
        ·
          refine ⟨48179600954905938968440307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 128478935879749170582507485 48179600954905938968440307)
          ·
            refine ⟨72269401432358908452660461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48179600954905938968440307 72269401432358908452660461)
            ·
              refine ⟨27101025537134590669747673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72269401432358908452660461 27101025537134590669747673)
              ·
                refine ⟨20325769152850943002310755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27101025537134590669747673 20325769152850943002310755)
                ·
                  refine ⟨30488653729276414503466133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20325769152850943002310755 30488653729276414503466133)
                  ·
                    refine ⟨1429155643559831929849975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30488653729276414503466133 1429155643559831929849975)
                    ·
                      rfl

theorem cell22_4174906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 2, 1, 6].length) (baseStart_4174906 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4174906 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4174906 prefixEnd_4174906 := by exact prefixLift 4174906
  have htrace : WordTrace (prefixWord ++ tailWord_4174906) baseStart_4174906 baseEnd_4174906 := by
    simpa [prefixWord, tailWord_4174906, baseEnd_4174906] using wordTrace_append hprefix tailTrace_4174906
  have hstable : (prefixWord ++ tailWord_4174906).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4174906).length < 2 ^ (prefixWord ++ tailWord_4174906).sum := by decide
  have hdescent : baseEnd_4174906 < baseStart_4174906 := by decide
  rcases family_descends (prefixWord ++ tailWord_4174906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4174908 : List Nat := [2, 2, 2, 2, 2, 2, 3, 1, 1, 5]
def baseStart_4174908 : Nat := 118140960795 + 4174908 * 2 ^ 59
def prefixEnd_4174908 : Nat := 4983230072969 + 3 ^ 40 * 4174908 * 2
def baseEnd_4174908 : Nat := 1429156328200704591299969

theorem tailTrace_4174908 : CollatzResearch.WordTrace tailWord_4174908 prefixEnd_4174908 1429156328200704591299969 := by
  unfold tailWord_4174908
  simp only [CollatzResearch.WordTrace]
  refine ⟨76135702179514404182642689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101514269572685872243523585 76135702179514404182642689)
  ·
    refine ⟨57101776634635803136982017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76135702179514404182642689 57101776634635803136982017)
    ·
      refine ⟨42826332475976852352736513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57101776634635803136982017 42826332475976852352736513)
      ·
        refine ⟨32119749356982639264552385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42826332475976852352736513 32119749356982639264552385)
        ·
          refine ⟨24089812017736979448414289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32119749356982639264552385 24089812017736979448414289)
          ·
            refine ⟨18067359013302734586310717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24089812017736979448414289 18067359013302734586310717)
            ·
              refine ⟨6775259629988525469866519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18067359013302734586310717 6775259629988525469866519)
              ·
                refine ⟨10162889444982788204799779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6775259629988525469866519 10162889444982788204799779)
                ·
                  refine ⟨15244334167474182307199669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10162889444982788204799779 15244334167474182307199669)
                  ·
                    refine ⟨1429156328200704591299969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15244334167474182307199669 1429156328200704591299969)
                    ·
                      rfl

theorem cell22_4174908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 3, 1, 1, 5].length) (baseStart_4174908 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4174908 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4174908 prefixEnd_4174908 := by exact prefixLift 4174908
  have htrace : WordTrace (prefixWord ++ tailWord_4174908) baseStart_4174908 baseEnd_4174908 := by
    simpa [prefixWord, tailWord_4174908, baseEnd_4174908] using wordTrace_append hprefix tailTrace_4174908
  have hstable : (prefixWord ++ tailWord_4174908).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4174908).length < 2 ^ (prefixWord ++ tailWord_4174908).sum := by decide
  have hdescent : baseEnd_4174908 < baseStart_4174908 := by decide
  rcases family_descends (prefixWord ++ tailWord_4174908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4174925 : List Nat := [1, 6, 1, 1, 1, 2, 1, 2, 4, 3]
def baseStart_4174925 : Nat := 118140960795 + 4174925 * 2 ^ 59
def prefixEnd_4174925 : Nat := 4983230072969 + 3 ^ 40 * 4174925 * 2
def baseEnd_4174925 : Nat := 1429162147648122213624917

theorem tailTrace_4174925 : CollatzResearch.WordTrace tailWord_4174925 prefixEnd_4174925 1429162147648122213624917 := by
  unfold tailWord_4174925
  simp only [CollatzResearch.WordTrace]
  refine ⟨152272024399967220268654229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101514682933311480179102819 152272024399967220268654229)
  ·
    refine ⟨7137751143748463450093167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 152272024399967220268654229 7137751143748463450093167)
    ·
      refine ⟨10706626715622695175139751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7137751143748463450093167 10706626715622695175139751)
      ·
        refine ⟨16059940073434042762709627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10706626715622695175139751 16059940073434042762709627)
        ·
          refine ⟨24089910110151064144064441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16059940073434042762709627 24089910110151064144064441)
          ·
            refine ⟨18067432582613298108048331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24089910110151064144064441 18067432582613298108048331)
            ·
              refine ⟨27101148873919947162072497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18067432582613298108048331 27101148873919947162072497)
              ·
                refine ⟨20325861655439960371554373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27101148873919947162072497 20325861655439960371554373)
                ·
                  refine ⟨3811099060394992569666445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20325861655439960371554373 3811099060394992569666445)
                  ·
                    refine ⟨1429162147648122213624917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3811099060394992569666445 1429162147648122213624917)
                    ·
                      rfl

theorem cell22_4174925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 2, 4, 3].length) (baseStart_4174925 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4174925 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4174925 prefixEnd_4174925 := by exact prefixLift 4174925
  have htrace : WordTrace (prefixWord ++ tailWord_4174925) baseStart_4174925 baseEnd_4174925 := by
    simpa [prefixWord, tailWord_4174925, baseEnd_4174925] using wordTrace_append hprefix tailTrace_4174925
  have hstable : (prefixWord ++ tailWord_4174925).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4174925).length < 2 ^ (prefixWord ++ tailWord_4174925).sum := by decide
  have hdescent : baseEnd_4174925 < baseStart_4174925 := by decide
  rcases family_descends (prefixWord ++ tailWord_4174925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4175000 : List Nat := [2, 1, 2, 4, 2, 2, 2, 2, 5]
def baseStart_4175000 : Nat := 118140960795 + 4175000 * 2 ^ 59
def prefixEnd_4175000 : Nat := 4983230072969 + 3 ^ 40 * 4175000 * 2
def baseEnd_4175000 : Nat := 476395940560282339333229

theorem tailTrace_4175000 : CollatzResearch.WordTrace tailWord_4175000 prefixEnd_4175000 476395940560282339333229 := by
  unfold tailWord_4175000
  simp only [CollatzResearch.WordTrace]
  refine ⟨76137379937347754038817227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101516506583130338718422969 76137379937347754038817227)
  ·
    refine ⟨114206069906021631058225841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76137379937347754038817227 114206069906021631058225841)
    ·
      refine ⟨85654552429516223293669381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114206069906021631058225841 85654552429516223293669381)
      ·
        refine ⟨16060228580534291867563009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 85654552429516223293669381 16060228580534291867563009)
        ·
          refine ⟨12045171435400718900672257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16060228580534291867563009 12045171435400718900672257)
          ·
            refine ⟨9033878576550539175504193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12045171435400718900672257 9033878576550539175504193)
            ·
              refine ⟨6775408932412904381628145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9033878576550539175504193 6775408932412904381628145)
              ·
                refine ⟨5081556699309678286221109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6775408932412904381628145 5081556699309678286221109)
                ·
                  refine ⟨476395940560282339333229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5081556699309678286221109 476395940560282339333229)
                  ·
                    rfl

theorem cell22_4175000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 2, 2, 5].length) (baseStart_4175000 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4175000 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4175000 prefixEnd_4175000 := by exact prefixLift 4175000
  have htrace : WordTrace (prefixWord ++ tailWord_4175000) baseStart_4175000 baseEnd_4175000 := by
    simpa [prefixWord, tailWord_4175000, baseEnd_4175000] using wordTrace_append hprefix tailTrace_4175000
  have hstable : (prefixWord ++ tailWord_4175000).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4175000).length < 2 ^ (prefixWord ++ tailWord_4175000).sum := by decide
  have hdescent : baseEnd_4175000 < baseStart_4175000 := by decide
  rcases family_descends (prefixWord ++ tailWord_4175000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4175004 : List Nat := [2, 2, 3, 2, 1, 2, 4, 2, 1, 3]
def baseStart_4175004 : Nat := 118140960795 + 4175004 * 2 ^ 59
def prefixEnd_4175004 : Nat := 4983230072969 + 3 ^ 40 * 4175004 * 2
def baseEnd_4175004 : Nat := 1429189190962592340899675

theorem tailTrace_4175004 : CollatzResearch.WordTrace tailWord_4175004 prefixEnd_4175004 1429189190962592340899675 := by
  unfold tailWord_4175004
  simp only [CollatzResearch.WordTrace]
  refine ⟨76137452883340508380390033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101516603844454011173853377 76137452883340508380390033)
  ·
    refine ⟨57103089662505381285292525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76137452883340508380390033 57103089662505381285292525)
    ·
      refine ⟨21413658623439517981984697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57103089662505381285292525 21413658623439517981984697)
      ·
        refine ⟨16060243967579638486488523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21413658623439517981984697 16060243967579638486488523)
        ·
          refine ⟨24090365951369457729732785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16060243967579638486488523 24090365951369457729732785)
          ·
            refine ⟨18067774463527093297299589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24090365951369457729732785 18067774463527093297299589)
            ·
              refine ⟨3387707711911329993243673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18067774463527093297299589 3387707711911329993243673)
              ·
                refine ⟨2540780783933497494932755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3387707711911329993243673 2540780783933497494932755)
                ·
                  refine ⟨3811171175900246242399133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2540780783933497494932755 3811171175900246242399133)
                  ·
                    refine ⟨1429189190962592340899675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3811171175900246242399133 1429189190962592340899675)
                    ·
                      rfl

theorem cell22_4175004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 4, 2, 1, 3].length) (baseStart_4175004 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4175004 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4175004 prefixEnd_4175004 := by exact prefixLift 4175004
  have htrace : WordTrace (prefixWord ++ tailWord_4175004) baseStart_4175004 baseEnd_4175004 := by
    simpa [prefixWord, tailWord_4175004, baseEnd_4175004] using wordTrace_append hprefix tailTrace_4175004
  have hstable : (prefixWord ++ tailWord_4175004).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4175004).length < 2 ^ (prefixWord ++ tailWord_4175004).sum := by decide
  have hdescent : baseEnd_4175004 < baseStart_4175004 := by decide
  rcases family_descends (prefixWord ++ tailWord_4175004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4175011 : List Nat := [1, 1, 1, 4, 1, 1, 1, 2, 10]
def baseStart_4175011 : Nat := 118140960795 + 4175011 * 2 ^ 59
def prefixEnd_4175011 : Nat := 4983230072969 + 3 ^ 40 * 4175011 * 2
def baseEnd_4175011 : Nat := 476397195735215551991551

theorem tailTrace_4175011 : CollatzResearch.WordTrace tailWord_4175011 prefixEnd_4175011 476397195735215551991551 := by
  unfold tailWord_4175011
  simp only [CollatzResearch.WordTrace]
  refine ⟨152275161077655656956284887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101516774051770437970856591 152275161077655656956284887)
  ·
    refine ⟨228412741616483485434427331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152275161077655656956284887 228412741616483485434427331)
    ·
      refine ⟨342619112424725228151640997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228412741616483485434427331 342619112424725228151640997)
      ·
        refine ⟨64241083579635980278432687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 342619112424725228151640997 64241083579635980278432687)
        ·
          refine ⟨96361625369453970417649031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64241083579635980278432687 96361625369453970417649031)
          ·
            refine ⟨144542438054180955626473547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96361625369453970417649031 144542438054180955626473547)
            ·
              refine ⟨216813657081271433439710321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144542438054180955626473547 216813657081271433439710321)
              ·
                refine ⟨162610242810953575079782741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 216813657081271433439710321 162610242810953575079782741)
                ·
                  refine ⟨476397195735215551991551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 162610242810953575079782741 476397195735215551991551)
                  ·
                    rfl

theorem cell22_4175011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 2, 10].length) (baseStart_4175011 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4175011 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4175011 prefixEnd_4175011 := by exact prefixLift 4175011
  have htrace : WordTrace (prefixWord ++ tailWord_4175011) baseStart_4175011 baseEnd_4175011 := by
    simpa [prefixWord, tailWord_4175011, baseEnd_4175011] using wordTrace_append hprefix tailTrace_4175011
  have hstable : (prefixWord ++ tailWord_4175011).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4175011).length < 2 ^ (prefixWord ++ tailWord_4175011).sum := by decide
  have hdescent : baseEnd_4175011 < baseStart_4175011 := by decide
  rcases family_descends (prefixWord ++ tailWord_4175011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4175013 : List Nat := [1, 3, 1, 2, 1, 4, 1, 2, 3, 4]
def baseStart_4175013 : Nat := 118140960795 + 4175013 * 2 ^ 59
def prefixEnd_4175013 : Nat := 4983230072969 + 3 ^ 40 * 4175013 * 2
def baseEnd_4175013 : Nat := 1429192271846519317424647

theorem tailTrace_4175013 : CollatzResearch.WordTrace tailWord_4175013 prefixEnd_4175013 1429192271846519317424647 := by
  unfold tailWord_4175013
  simp only [CollatzResearch.WordTrace]
  refine ⟨152275234023648411297857693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101516822682432274198571795 152275234023648411297857693)
  ·
    refine ⟨57103212758868154236696635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152275234023648411297857693 57103212758868154236696635)
    ·
      refine ⟨85654819138302231355044953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57103212758868154236696635 85654819138302231355044953)
      ·
        refine ⟨64241114353726673516283715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85654819138302231355044953 64241114353726673516283715)
        ·
          refine ⟨96361671530590010274425573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64241114353726673516283715 96361671530590010274425573)
          ·
            refine ⟨18067813411985626926454795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 96361671530590010274425573 18067813411985626926454795)
            ·
              refine ⟨27101720117978440389682193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18067813411985626926454795 27101720117978440389682193)
              ·
                refine ⟨20326290088483830292261645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27101720117978440389682193 20326290088483830292261645)
                ·
                  refine ⟨7622358783181436359598117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20326290088483830292261645 7622358783181436359598117)
                  ·
                    refine ⟨1429192271846519317424647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7622358783181436359598117 1429192271846519317424647)
                    ·
                      rfl

theorem cell22_4175013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 2, 3, 4].length) (baseStart_4175013 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4175013 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4175013 prefixEnd_4175013 := by exact prefixLift 4175013
  have htrace : WordTrace (prefixWord ++ tailWord_4175013) baseStart_4175013 baseEnd_4175013 := by
    simpa [prefixWord, tailWord_4175013, baseEnd_4175013] using wordTrace_append hprefix tailTrace_4175013
  have hstable : (prefixWord ++ tailWord_4175013).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4175013).length < 2 ^ (prefixWord ++ tailWord_4175013).sum := by decide
  have hdescent : baseEnd_4175013 < baseStart_4175013 := by decide
  rcases family_descends (prefixWord ++ tailWord_4175013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4175015 : List Nat := [1, 1, 6, 2, 1, 2, 1, 1, 2, 5]
def baseStart_4175015 : Nat := 118140960795 + 4175015 * 2 ^ 59
def prefixEnd_4175015 : Nat := 4983230072969 + 3 ^ 40 * 4175015 * 2
def baseEnd_4175015 : Nat := 1429192956487391978874641

theorem tailTrace_4175015 : CollatzResearch.WordTrace tailWord_4175015 prefixEnd_4175015 1429192956487391978874641 := by
  unfold tailWord_4175015
  simp only [CollatzResearch.WordTrace]
  refine ⟨152275306969641165639430499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101516871313094110426286999 152275306969641165639430499)
  ·
    refine ⟨228412960454461748459145749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152275306969641165639430499 228412960454461748459145749)
    ·
      refine ⟨10706857521302894459022457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 228412960454461748459145749 10706857521302894459022457)
      ·
        refine ⟨8030143140977170844266843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10706857521302894459022457 8030143140977170844266843)
        ·
          refine ⟨12045214711465756266400265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8030143140977170844266843 12045214711465756266400265)
          ·
            refine ⟨9033911033599317199800199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12045214711465756266400265 9033911033599317199800199)
            ·
              refine ⟨13550866550398975799700299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9033911033599317199800199 13550866550398975799700299)
              ·
                refine ⟨20326299825598463699550449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13550866550398975799700299 20326299825598463699550449)
                ·
                  refine ⟨15244724869198847774662837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20326299825598463699550449 15244724869198847774662837)
                  ·
                    refine ⟨1429192956487391978874641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15244724869198847774662837 1429192956487391978874641)
                    ·
                      rfl

theorem cell22_4175015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 1, 1, 2, 5].length) (baseStart_4175015 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4175015 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4175015 prefixEnd_4175015 := by exact prefixLift 4175015
  have htrace : WordTrace (prefixWord ++ tailWord_4175015) baseStart_4175015 baseEnd_4175015 := by
    simpa [prefixWord, tailWord_4175015, baseEnd_4175015] using wordTrace_append hprefix tailTrace_4175015
  have hstable : (prefixWord ++ tailWord_4175015).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4175015).length < 2 ^ (prefixWord ++ tailWord_4175015).sum := by decide
  have hdescent : baseEnd_4175015 < baseStart_4175015 := by decide
  rcases family_descends (prefixWord ++ tailWord_4175015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4175077 : List Nat := [1, 3, 1, 4, 3, 2, 1, 1, 1, 5]
def baseStart_4175077 : Nat := 118140960795 + 4175077 * 2 ^ 59
def prefixEnd_4175077 : Nat := 4983230072969 + 3 ^ 40 * 4175077 * 2
def baseEnd_4175077 : Nat := 1429214180354444483824451

theorem tailTrace_4175077 : CollatzResearch.WordTrace tailWord_4175077 prefixEnd_4175077 1429214180354444483824451 := by
  unfold tailWord_4175077
  simp only [CollatzResearch.WordTrace]
  refine ⟨152277568295416550228187485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101518378863611033485458323 152277568295416550228187485)
  ·
    refine ⟨57104088110781206335570307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152277568295416550228187485 57104088110781206335570307)
    ·
      refine ⟨85656132166171809503355461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57104088110781206335570307 85656132166171809503355461)
      ·
        refine ⟨16060524781157214281879149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 85656132166171809503355461 16060524781157214281879149)
        ·
          refine ⟨6022696792933955355704681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16060524781157214281879149 6022696792933955355704681)
          ·
            refine ⟨4517022594700466516778511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6022696792933955355704681 4517022594700466516778511)
            ·
              refine ⟨6775533892050699775167767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4517022594700466516778511 6775533892050699775167767)
              ·
                refine ⟨10163300838076049662751651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6775533892050699775167767 10163300838076049662751651)
                ·
                  refine ⟨15244951257114074494127477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10163300838076049662751651 15244951257114074494127477)
                  ·
                    refine ⟨1429214180354444483824451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15244951257114074494127477 1429214180354444483824451)
                    ·
                      rfl

theorem cell22_4175077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 2, 1, 1, 1, 5].length) (baseStart_4175077 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4175077 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4175077 prefixEnd_4175077 := by exact prefixLift 4175077
  have htrace : WordTrace (prefixWord ++ tailWord_4175077) baseStart_4175077 baseEnd_4175077 := by
    simpa [prefixWord, tailWord_4175077, baseEnd_4175077] using wordTrace_append hprefix tailTrace_4175077
  have hstable : (prefixWord ++ tailWord_4175077).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4175077).length < 2 ^ (prefixWord ++ tailWord_4175077).sum := by decide
  have hdescent : baseEnd_4175077 < baseStart_4175077 := by decide
  rcases family_descends (prefixWord ++ tailWord_4175077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4175090 : List Nat := [3, 2, 1, 3, 3, 1, 1, 8]
def baseStart_4175090 : Nat := 118140960795 + 4175090 * 2 ^ 59
def prefixEnd_4175090 : Nat := 4983230072969 + 3 ^ 40 * 4175090 * 2
def baseEnd_4175090 : Nat := 158802070057790753694379

theorem tailTrace_4175090 : CollatzResearch.WordTrace tailWord_4175090 prefixEnd_4175090 158802070057790753694379 := by
  unfold tailWord_4175090
  simp only [CollatzResearch.WordTrace]
  refine ⟨38069510611092363362102681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101518694962912968965607149 38069510611092363362102681)
  ·
    refine ⟨28552132958319272521577011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38069510611092363362102681 28552132958319272521577011)
    ·
      refine ⟨42828199437478908782365517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28552132958319272521577011 42828199437478908782365517)
      ·
        refine ⟨16060574789054590793387069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42828199437478908782365517 16060574789054590793387069)
        ·
          refine ⟨6022715545895471547520151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16060574789054590793387069 6022715545895471547520151)
          ·
            refine ⟨9034073318843207321280227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6022715545895471547520151 9034073318843207321280227)
            ·
              refine ⟨13551109978264810981920341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9034073318843207321280227 13551109978264810981920341)
              ·
                refine ⟨158802070057790753694379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13551109978264810981920341 158802070057790753694379)
                ·
                  rfl

theorem cell22_4175090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 1, 8].length) (baseStart_4175090 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4175090 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4175090 prefixEnd_4175090 := by exact prefixLift 4175090
  have htrace : WordTrace (prefixWord ++ tailWord_4175090) baseStart_4175090 baseEnd_4175090 := by
    simpa [prefixWord, tailWord_4175090, baseEnd_4175090] using wordTrace_append hprefix tailTrace_4175090
  have hstable : (prefixWord ++ tailWord_4175090).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4175090).length < 2 ^ (prefixWord ++ tailWord_4175090).sum := by decide
  have hdescent : baseEnd_4175090 < baseStart_4175090 := by decide
  rcases family_descends (prefixWord ++ tailWord_4175090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4175246 : List Nat := [4, 1, 1, 4, 3, 1, 1, 1, 1, 5]
def baseStart_4175246 : Nat := 118140960795 + 4175246 * 2 ^ 59
def prefixEnd_4175246 : Nat := 4983230072969 + 3 ^ 40 * 4175246 * 2
def baseEnd_4175246 : Nat := 1429272032508184376348933

theorem tailTrace_4175246 : CollatzResearch.WordTrace tailWord_4175246 prefixEnd_4175246 1429272032508184376348933 := by
  unfold tailWord_4175246
  simp only [CollatzResearch.WordTrace]
  refine ⟨19035466528975536511386199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 101522488154536194727393061 19035466528975536511386199)
  ·
    refine ⟨28553199793463304767079299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19035466528975536511386199 28553199793463304767079299)
    ·
      refine ⟨42829799690194957150618949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28553199793463304767079299 42829799690194957150618949)
      ·
        refine ⟨8030587441911554465741053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42829799690194957150618949 8030587441911554465741053)
        ·
          refine ⟨3011470290716832924652895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8030587441911554465741053 3011470290716832924652895)
          ·
            refine ⟨4517205436075249386979343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3011470290716832924652895 4517205436075249386979343)
            ·
              refine ⟨6775808154112874080469015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4517205436075249386979343 6775808154112874080469015)
              ·
                refine ⟨10163712231169311120703523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6775808154112874080469015 10163712231169311120703523)
                ·
                  refine ⟨15245568346753966681055285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10163712231169311120703523 15245568346753966681055285)
                  ·
                    refine ⟨1429272032508184376348933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15245568346753966681055285 1429272032508184376348933)
                    ·
                      rfl

theorem cell22_4175246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 3, 1, 1, 1, 1, 5].length) (baseStart_4175246 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4175246 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4175246 prefixEnd_4175246 := by exact prefixLift 4175246
  have htrace : WordTrace (prefixWord ++ tailWord_4175246) baseStart_4175246 baseEnd_4175246 := by
    simpa [prefixWord, tailWord_4175246, baseEnd_4175246] using wordTrace_append hprefix tailTrace_4175246
  have hstable : (prefixWord ++ tailWord_4175246).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4175246).length < 2 ^ (prefixWord ++ tailWord_4175246).sum := by decide
  have hdescent : baseEnd_4175246 < baseStart_4175246 := by decide
  rcases family_descends (prefixWord ++ tailWord_4175246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4175257 : List Nat := [1, 2, 1, 2, 1, 5, 2, 2, 3, 3]
def baseStart_4175257 : Nat := 118140960795 + 4175257 * 2 ^ 59
def prefixEnd_4175257 : Nat := 4983230072969 + 3 ^ 40 * 4175257 * 2
def baseEnd_4175257 : Nat := 1429275798032984014323899

theorem tailTrace_4175257 : CollatzResearch.WordTrace tailWord_4175257 prefixEnd_4175257 1429275798032984014323899 := by
  unfold tailWord_4175257
  simp only [CollatzResearch.WordTrace]
  refine ⟨152284133434764440969740025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101522755623176293979826683 152284133434764440969740025)
  ·
    refine ⟨114213100076073330727305019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152284133434764440969740025 114213100076073330727305019)
    ·
      refine ⟨171319650114109996090957529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114213100076073330727305019 171319650114109996090957529)
      ·
        refine ⟨128489737585582497068218147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171319650114109996090957529 128489737585582497068218147)
        ·
          refine ⟨192734606378373745602327221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128489737585582497068218147 192734606378373745602327221)
          ·
            refine ⟨18068869347972538650218177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 192734606378373745602327221 18068869347972538650218177)
            ·
              refine ⟨13551652010979403987663633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18068869347972538650218177 13551652010979403987663633)
              ·
                refine ⟨10163739008234552990747725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13551652010979403987663633 10163739008234552990747725)
                ·
                  refine ⟨3811402128087957371530397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10163739008234552990747725 3811402128087957371530397)
                  ·
                    refine ⟨1429275798032984014323899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3811402128087957371530397 1429275798032984014323899)
                    ·
                      rfl

theorem cell22_4175257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 2, 2, 3, 3].length) (baseStart_4175257 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4175257 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4175257 prefixEnd_4175257 := by exact prefixLift 4175257
  have htrace : WordTrace (prefixWord ++ tailWord_4175257) baseStart_4175257 baseEnd_4175257 := by
    simpa [prefixWord, tailWord_4175257, baseEnd_4175257] using wordTrace_append hprefix tailTrace_4175257
  have hstable : (prefixWord ++ tailWord_4175257).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4175257).length < 2 ^ (prefixWord ++ tailWord_4175257).sum := by decide
  have hdescent : baseEnd_4175257 < baseStart_4175257 := by decide
  rcases family_descends (prefixWord ++ tailWord_4175257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4175317 : List Nat := [1, 3, 2, 3, 1, 1, 3, 1, 3, 4]
def baseStart_4175317 : Nat := 118140960795 + 4175317 * 2 ^ 59
def prefixEnd_4175317 : Nat := 4983230072969 + 3 ^ 40 * 4175317 * 2
def baseEnd_4175317 : Nat := 1429296337259163857823715

theorem tailTrace_4175317 : CollatzResearch.WordTrace tailWord_4175317 prefixEnd_4175317 1429296337259163857823715 := by
  unfold tailWord_4175317
  simp only [CollatzResearch.WordTrace]
  refine ⟨152286321814547071216924205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101524214543031380811282803 152286321814547071216924205)
  ·
    refine ⟨57107370680455151706346577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152286321814547071216924205 57107370680455151706346577)
    ·
      refine ⟨42830528010341363779759933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57107370680455151706346577 42830528010341363779759933)
      ·
        refine ⟨16061448003878011417409975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42830528010341363779759933 16061448003878011417409975)
        ·
          refine ⟨24092172005817017126114963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16061448003878011417409975 24092172005817017126114963)
          ·
            refine ⟨36138258008725525689172445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24092172005817017126114963 36138258008725525689172445)
            ·
              refine ⟨13551846753272072133439667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36138258008725525689172445 13551846753272072133439667)
              ·
                refine ⟨20327770129908108200159501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13551846753272072133439667 20327770129908108200159501)
                ·
                  refine ⟨7622913798715540575059813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20327770129908108200159501 7622913798715540575059813)
                  ·
                    refine ⟨1429296337259163857823715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7622913798715540575059813 1429296337259163857823715)
                    ·
                      rfl

theorem cell22_4175317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 3, 1, 3, 4].length) (baseStart_4175317 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4175317 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4175317 prefixEnd_4175317 := by exact prefixLift 4175317
  have htrace : WordTrace (prefixWord ++ tailWord_4175317) baseStart_4175317 baseEnd_4175317 := by
    simpa [prefixWord, tailWord_4175317, baseEnd_4175317] using wordTrace_append hprefix tailTrace_4175317
  have hstable : (prefixWord ++ tailWord_4175317).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4175317).length < 2 ^ (prefixWord ++ tailWord_4175317).sum := by decide
  have hdescent : baseEnd_4175317 < baseStart_4175317 := by decide
  rcases family_descends (prefixWord ++ tailWord_4175317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4175377 : List Nat := [1, 2, 2, 1, 1, 2, 7, 6]
def baseStart_4175377 : Nat := 118140960795 + 4175377 * 2 ^ 59
def prefixEnd_4175377 : Nat := 4983230072969 + 3 ^ 40 * 4175377 * 2
def baseEnd_4175377 : Nat := 158812986276149300147059

theorem tailTrace_4175377 : CollatzResearch.WordTrace tailWord_4175377 prefixEnd_4175377 158812986276149300147059 := by
  unfold tailWord_4175377
  simp only [CollatzResearch.WordTrace]
  refine ⟨152288510194329701464108385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101525673462886467642738923 152288510194329701464108385)
  ·
    refine ⟨114216382645747276098081289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152288510194329701464108385 114216382645747276098081289)
    ·
      refine ⟨85662286984310457073560967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114216382645747276098081289 85662286984310457073560967)
      ·
        refine ⟨128493430476465685610341451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85662286984310457073560967 128493430476465685610341451)
        ·
          refine ⟨192740145714698528415512177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128493430476465685610341451 192740145714698528415512177)
          ·
            refine ⟨144555109286023896311634133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 192740145714698528415512177 144555109286023896311634133)
            ·
              refine ⟨3388010373891185069803925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 144555109286023896311634133 3388010373891185069803925)
              ·
                refine ⟨158812986276149300147059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3388010373891185069803925 158812986276149300147059)
                ·
                  rfl

theorem cell22_4175377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 7, 6].length) (baseStart_4175377 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4175377 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4175377 prefixEnd_4175377 := by exact prefixLift 4175377
  have htrace : WordTrace (prefixWord ++ tailWord_4175377) baseStart_4175377 baseEnd_4175377 := by
    simpa [prefixWord, tailWord_4175377, baseEnd_4175377] using wordTrace_append hprefix tailTrace_4175377
  have hstable : (prefixWord ++ tailWord_4175377).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4175377).length < 2 ^ (prefixWord ++ tailWord_4175377).sum := by decide
  have hdescent : baseEnd_4175377 < baseStart_4175377 := by decide
  rcases family_descends (prefixWord ++ tailWord_4175377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4175379 : List Nat := [1, 1, 1, 2, 1, 8, 1, 1, 2, 4]
def baseStart_4175379 : Nat := 118140960795 + 4175379 * 2 ^ 59
def prefixEnd_4175379 : Nat := 4983230072969 + 3 ^ 40 * 4175379 * 2
def baseEnd_4175379 : Nat := 1429317561126216362773525

theorem tailTrace_4175379 : CollatzResearch.WordTrace tailWord_4175379 prefixEnd_4175379 1429317561126216362773525 := by
  unfold tailWord_4175379
  simp only [CollatzResearch.WordTrace]
  refine ⟨152288583140322455805681191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101525722093548303870454127 152288583140322455805681191)
  ·
    refine ⟨228432874710483683708521787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152288583140322455805681191 228432874710483683708521787)
    ·
      refine ⟨342649312065725525562782681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228432874710483683708521787 342649312065725525562782681)
      ·
        refine ⟨256986984049294144172087011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 342649312065725525562782681 256986984049294144172087011)
        ·
          refine ⟨385480476073941216258130517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 256986984049294144172087011 385480476073941216258130517)
          ·
            refine ⟨4517349328991498628024967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 385480476073941216258130517 4517349328991498628024967)
            ·
              refine ⟨6776023993487247942037451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4517349328991498628024967 6776023993487247942037451)
              ·
                refine ⟨10164035990230871913056177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6776023993487247942037451 10164035990230871913056177)
                ·
                  refine ⟨7623026992673153934792133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10164035990230871913056177 7623026992673153934792133)
                  ·
                    refine ⟨1429317561126216362773525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7623026992673153934792133 1429317561126216362773525)
                    ·
                      rfl

theorem cell22_4175379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 8, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 8, 1, 1, 2, 4].length) (baseStart_4175379 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4175379 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4175379 prefixEnd_4175379 := by exact prefixLift 4175379
  have htrace : WordTrace (prefixWord ++ tailWord_4175379) baseStart_4175379 baseEnd_4175379 := by
    simpa [prefixWord, tailWord_4175379, baseEnd_4175379] using wordTrace_append hprefix tailTrace_4175379
  have hstable : (prefixWord ++ tailWord_4175379).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4175379).length < 2 ^ (prefixWord ++ tailWord_4175379).sum := by decide
  have hdescent : baseEnd_4175379 < baseStart_4175379 := by decide
  rcases family_descends (prefixWord ++ tailWord_4175379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4175497 : List Nat := [1, 2, 1, 1, 4, 1, 2, 3, 1, 6]
def baseStart_4175497 : Nat := 118140960795 + 4175497 * 2 ^ 59
def prefixEnd_4175497 : Nat := 4983230072969 + 3 ^ 40 * 4175497 * 2
def baseEnd_4175497 : Nat := 1429357954937703388323163

theorem tailTrace_4175497 : CollatzResearch.WordTrace tailWord_4175497 prefixEnd_4175497 1429357954937703388323163 := by
  unfold tailWord_4175497
  simp only [CollatzResearch.WordTrace]
  refine ⟨152292886953894961958476745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101528591302596641305651163 152292886953894961958476745)
  ·
    refine ⟨114219665215421221468857559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152292886953894961958476745 114219665215421221468857559)
    ·
      refine ⟨171329497823131832203286339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114219665215421221468857559 171329497823131832203286339)
      ·
        refine ⟨256994246734697748304929509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171329497823131832203286339 256994246734697748304929509)
        ·
          refine ⟨48186421262755827807174283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 256994246734697748304929509 48186421262755827807174283)
          ·
            refine ⟨72279631894133741710761425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48186421262755827807174283 72279631894133741710761425)
            ·
              refine ⟨54209723920600306283071069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72279631894133741710761425 54209723920600306283071069)
              ·
                refine ⟨20328646470225114856151651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54209723920600306283071069 20328646470225114856151651)
                ·
                  refine ⟨30492969705337672284227477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20328646470225114856151651 30492969705337672284227477)
                  ·
                    refine ⟨1429357954937703388323163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30492969705337672284227477 1429357954937703388323163)
                    ·
                      rfl

theorem cell22_4175497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 3, 1, 6].length) (baseStart_4175497 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4175497 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4175497 prefixEnd_4175497 := by exact prefixLift 4175497
  have htrace : WordTrace (prefixWord ++ tailWord_4175497) baseStart_4175497 baseEnd_4175497 := by
    simpa [prefixWord, tailWord_4175497, baseEnd_4175497] using wordTrace_append hprefix tailTrace_4175497
  have hstable : (prefixWord ++ tailWord_4175497).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4175497).length < 2 ^ (prefixWord ++ tailWord_4175497).sum := by decide
  have hdescent : baseEnd_4175497 < baseStart_4175497 := by decide
  rcases family_descends (prefixWord ++ tailWord_4175497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4175512 : List Nat := [2, 1, 2, 4, 1, 12]
def baseStart_4175512 : Nat := 118140960795 + 4175512 * 2 ^ 59
def prefixEnd_4175512 : Nat := 4983230072969 + 3 ^ 40 * 4175512 * 2
def baseEnd_4175512 : Nat := 17646457898077140113557

theorem tailTrace_4175512 : CollatzResearch.WordTrace tailWord_4175512 prefixEnd_4175512 17646457898077140113557 := by
  unfold tailWord_4175512
  simp only [CollatzResearch.WordTrace]
  refine ⟨76146717024420309760136395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101528956032560413013515193 76146717024420309760136395)
  ·
    refine ⟨114220075536630464640204593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76146717024420309760136395 114220075536630464640204593)
    ·
      refine ⟨85665056652472848480153445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114220075536630464640204593 85665056652472848480153445)
      ·
        refine ⟨16062198122338659090028771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 85665056652472848480153445 16062198122338659090028771)
        ·
          refine ⟨24093297183507988635043157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16062198122338659090028771 24093297183507988635043157)
          ·
            refine ⟨17646457898077140113557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 24093297183507988635043157 17646457898077140113557)
            ·
              rfl

theorem cell22_4175512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 12].length) (baseStart_4175512 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4175512 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4175512 prefixEnd_4175512 := by exact prefixLift 4175512
  have htrace : WordTrace (prefixWord ++ tailWord_4175512) baseStart_4175512 baseEnd_4175512 := by
    simpa [prefixWord, tailWord_4175512, baseEnd_4175512] using wordTrace_append hprefix tailTrace_4175512
  have hstable : (prefixWord ++ tailWord_4175512).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4175512).length < 2 ^ (prefixWord ++ tailWord_4175512).sum := by decide
  have hdescent : baseEnd_4175512 < baseStart_4175512 := by decide
  rcases family_descends (prefixWord ++ tailWord_4175512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4175518 : List Nat := [4, 3, 1, 1, 1, 3, 1, 4, 4]
def baseStart_4175518 : Nat := 118140960795 + 4175518 * 2 ^ 59
def prefixEnd_4175518 : Nat := 4983230072969 + 3 ^ 40 * 4175518 * 2
def baseEnd_4175518 : Nat := 476455047888955444516033

theorem tailTrace_4175518 : CollatzResearch.WordTrace tailWord_4175518 prefixEnd_4175518 476455047888955444516033 := by
  unfold tailWord_4175518
  simp only [CollatzResearch.WordTrace]
  refine ⟨19036706610852360318123901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 101529101924545921696660805 19036706610852360318123901)
  ·
    refine ⟨7138764979069635119296463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19036706610852360318123901 7138764979069635119296463)
    ·
      refine ⟨10708147468604452678944695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7138764979069635119296463 10708147468604452678944695)
      ·
        refine ⟨16062221202906679018417043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10708147468604452678944695 16062221202906679018417043)
        ·
          refine ⟨24093331804360018527625565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16062221202906679018417043 24093331804360018527625565)
          ·
            refine ⟨9034999426635006947859587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24093331804360018527625565 9034999426635006947859587)
            ·
              refine ⟨13552499139952510421789381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9034999426635006947859587 13552499139952510421789381)
              ·
                refine ⟨2541093588741095704085509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13552499139952510421789381 2541093588741095704085509)
                ·
                  refine ⟨476455047888955444516033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2541093588741095704085509 476455047888955444516033)
                  ·
                    rfl

theorem cell22_4175518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 1, 4, 4].length) (baseStart_4175518 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4175518 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4175518 prefixEnd_4175518 := by exact prefixLift 4175518
  have htrace : WordTrace (prefixWord ++ tailWord_4175518) baseStart_4175518 baseEnd_4175518 := by
    simpa [prefixWord, tailWord_4175518, baseEnd_4175518] using wordTrace_append hprefix tailTrace_4175518
  have hstable : (prefixWord ++ tailWord_4175518).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4175518).length < 2 ^ (prefixWord ++ tailWord_4175518).sum := by decide
  have hdescent : baseEnd_4175518 < baseStart_4175518 := by decide
  rcases family_descends (prefixWord ++ tailWord_4175518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4175554 : List Nat := [3, 5, 1, 2, 1, 2, 2, 1, 1, 4]
def baseStart_4175554 : Nat := 118140960795 + 4175554 * 2 ^ 59
def prefixEnd_4175554 : Nat := 4983230072969 + 3 ^ 40 * 4175554 * 2
def baseEnd_4175554 : Nat := 1429377467202574239647989

theorem tailTrace_4175554 : CollatzResearch.WordTrace tailWord_4175554 prefixEnd_4175554 1429377467202574239647989 := by
  unfold tailWord_4175554
  simp only [CollatzResearch.WordTrace]
  refine ⟨38073741478672115173325429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101529977276458973795534477 38073741478672115173325429)
  ·
    refine ⟨3569413263625510797499259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 38073741478672115173325429 3569413263625510797499259)
    ·
      refine ⟨5354119895438266196248889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3569413263625510797499259 5354119895438266196248889)
      ·
        refine ⟨4015589921578699647186667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5354119895438266196248889 4015589921578699647186667)
        ·
          refine ⟨6023384882368049470780001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4015589921578699647186667 6023384882368049470780001)
          ·
            refine ⟨4517538661776037103085001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6023384882368049470780001 4517538661776037103085001)
            ·
              refine ⟨3388153996332027827313751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4517538661776037103085001 3388153996332027827313751)
              ·
                refine ⟨5082230994498041740970627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3388153996332027827313751 5082230994498041740970627)
                ·
                  refine ⟨7623346491747062611455941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5082230994498041740970627 7623346491747062611455941)
                  ·
                    refine ⟨1429377467202574239647989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7623346491747062611455941 1429377467202574239647989)
                    ·
                      rfl

theorem cell22_4175554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 2, 2, 1, 1, 4].length) (baseStart_4175554 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4175554 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4175554 prefixEnd_4175554 := by exact prefixLift 4175554
  have htrace : WordTrace (prefixWord ++ tailWord_4175554) baseStart_4175554 baseEnd_4175554 := by
    simpa [prefixWord, tailWord_4175554, baseEnd_4175554] using wordTrace_append hprefix tailTrace_4175554
  have hstable : (prefixWord ++ tailWord_4175554).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4175554).length < 2 ^ (prefixWord ++ tailWord_4175554).sum := by decide
  have hdescent : baseEnd_4175554 < baseStart_4175554 := by decide
  rcases family_descends (prefixWord ++ tailWord_4175554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4175557 : List Nat := [1, 3, 1, 1, 1, 1, 2, 3, 9]
def baseStart_4175557 : Nat := 118140960795 + 4175557 * 2 ^ 59
def prefixEnd_4175557 : Nat := 4983230072969 + 3 ^ 40 * 4175557 * 2
def baseEnd_4175557 : Nat := 476459498054627743940993

theorem tailTrace_4175557 : CollatzResearch.WordTrace tailWord_4175557 prefixEnd_4175557 476459498054627743940993 := by
  unfold tailWord_4175557
  simp only [CollatzResearch.WordTrace]
  refine ⟨152295075333677592205660925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101530050222451728137107283 152295075333677592205660925)
  ·
    refine ⟨57110653250129097077122847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152295075333677592205660925 57110653250129097077122847)
    ·
      refine ⟨85665979875193645615684271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57110653250129097077122847 85665979875193645615684271)
      ·
        refine ⟨128498969812790468423526407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85665979875193645615684271 128498969812790468423526407)
        ·
          refine ⟨192748454719185702635289611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128498969812790468423526407 192748454719185702635289611)
          ·
            refine ⟨289122682078778553952934417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192748454719185702635289611 289122682078778553952934417)
            ·
              refine ⟨216842011559083915464700813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 289122682078778553952934417 216842011559083915464700813)
              ·
                refine ⟨81315754334656468299262805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 216842011559083915464700813 81315754334656468299262805)
                ·
                  refine ⟨476459498054627743940993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 81315754334656468299262805 476459498054627743940993)
                  ·
                    rfl

theorem cell22_4175557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 3, 9].length) (baseStart_4175557 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4175557 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4175557 prefixEnd_4175557 := by exact prefixLift 4175557
  have htrace : WordTrace (prefixWord ++ tailWord_4175557) baseStart_4175557 baseEnd_4175557 := by
    simpa [prefixWord, tailWord_4175557, baseEnd_4175557] using wordTrace_append hprefix tailTrace_4175557
  have hstable : (prefixWord ++ tailWord_4175557).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4175557).length < 2 ^ (prefixWord ++ tailWord_4175557).sum := by decide
  have hdescent : baseEnd_4175557 < baseStart_4175557 := by decide
  rcases family_descends (prefixWord ++ tailWord_4175557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4175578 : List Nat := [3, 1, 1, 2, 2, 3, 2, 4, 1, 3]
def baseStart_4175578 : Nat := 118140960795 + 4175578 * 2 ^ 59
def prefixEnd_4175578 : Nat := 4983230072969 + 3 ^ 40 * 4175578 * 2
def baseEnd_4175578 : Nat := 1429385682893046177047915

theorem tailTrace_4175578 : CollatzResearch.WordTrace tailWord_4175578 prefixEnd_4175578 1429385682893046177047915 := by
  unfold tailWord_4175578
  simp only [CollatzResearch.WordTrace]
  refine ⟨38073960316650378198043847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101530560844401008528116925 38073960316650378198043847)
  ·
    refine ⟨57110940474975567297065771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38073960316650378198043847 57110940474975567297065771)
    ·
      refine ⟨85666410712463350945598657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57110940474975567297065771 85666410712463350945598657)
      ·
        refine ⟨64249808034347513209198993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85666410712463350945598657 64249808034347513209198993)
        ·
          refine ⟨48187356025760634906899245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64249808034347513209198993 48187356025760634906899245)
          ·
            refine ⟨18070258509660238090087217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48187356025760634906899245 18070258509660238090087217)
            ·
              refine ⟨13552693882245178567565413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18070258509660238090087217 13552693882245178567565413)
              ·
                refine ⟨2541130102920970981418515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13552693882245178567565413 2541130102920970981418515)
                ·
                  refine ⟨3811695154381456472127773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2541130102920970981418515 3811695154381456472127773)
                  ·
                    refine ⟨1429385682893046177047915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3811695154381456472127773 1429385682893046177047915)
                    ·
                      rfl

theorem cell22_4175578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 2, 4, 1, 3].length) (baseStart_4175578 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4175578 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4175578 prefixEnd_4175578 := by exact prefixLift 4175578
  have htrace : WordTrace (prefixWord ++ tailWord_4175578) baseStart_4175578 baseEnd_4175578 := by
    simpa [prefixWord, tailWord_4175578, baseEnd_4175578] using wordTrace_append hprefix tailTrace_4175578
  have hstable : (prefixWord ++ tailWord_4175578).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4175578).length < 2 ^ (prefixWord ++ tailWord_4175578).sum := by decide
  have hdescent : baseEnd_4175578 < baseStart_4175578 := by decide
  rcases family_descends (prefixWord ++ tailWord_4175578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4175589 : List Nat := [1, 3, 1, 4, 1, 1, 1, 3, 2, 5]
def baseStart_4175589 : Nat := 118140960795 + 4175589 * 2 ^ 59
def prefixEnd_4175589 : Nat := 4983230072969 + 3 ^ 40 * 4175589 * 2
def baseEnd_4175589 : Nat := 1429389448417845815022881

theorem tailTrace_4175589 : CollatzResearch.WordTrace tailWord_4175589 prefixEnd_4175589 1429389448417845815022881 := by
  unfold tailWord_4175589
  simp only [CollatzResearch.WordTrace]
  refine ⟨152296242469561661670825821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101530828313041107780550547 152296242469561661670825821)
  ·
    refine ⟨57111090926085623126559683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152296242469561661670825821 57111090926085623126559683)
    ·
      refine ⟨85666636389128434689839525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57111090926085623126559683 85666636389128434689839525)
      ·
        refine ⟨16062494322961581504344911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 85666636389128434689839525 16062494322961581504344911)
        ·
          refine ⟨24093741484442372256517367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16062494322961581504344911 24093741484442372256517367)
          ·
            refine ⟨36140612226663558384776051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24093741484442372256517367 36140612226663558384776051)
            ·
              refine ⟨54210918339995337577164077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36140612226663558384776051 54210918339995337577164077)
              ·
                refine ⟨20329094377498251591436529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54210918339995337577164077 20329094377498251591436529)
                ·
                  refine ⟨15246820783123688693577397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20329094377498251591436529 15246820783123688693577397)
                  ·
                    refine ⟨1429389448417845815022881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15246820783123688693577397 1429389448417845815022881)
                    ·
                      rfl

theorem cell22_4175589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 3, 2, 5].length) (baseStart_4175589 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4175589 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4175589 prefixEnd_4175589 := by exact prefixLift 4175589
  have htrace : WordTrace (prefixWord ++ tailWord_4175589) baseStart_4175589 baseEnd_4175589 := by
    simpa [prefixWord, tailWord_4175589, baseEnd_4175589] using wordTrace_append hprefix tailTrace_4175589
  have hstable : (prefixWord ++ tailWord_4175589).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4175589).length < 2 ^ (prefixWord ++ tailWord_4175589).sum := by decide
  have hdescent : baseEnd_4175589 < baseStart_4175589 := by decide
  rcases family_descends (prefixWord ++ tailWord_4175589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4175666 : List Nat := [3, 2, 1, 1, 3, 2, 1, 3, 2, 4]
def baseStart_4175666 : Nat := 118140960795 + 4175666 * 2 ^ 59
def prefixEnd_4175666 : Nat := 4983230072969 + 3 ^ 40 * 4175666 * 2
def baseEnd_4175666 : Nat := 1429415807091443280847645

theorem tailTrace_4175666 : CollatzResearch.WordTrace tailWord_4175666 prefixEnd_4175666 1429415807091443280847645 := by
  unfold tailWord_4175666
  simp only [CollatzResearch.WordTrace]
  refine ⟨38074762722570675955344713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101532700593521802547585901 38074762722570675955344713)
  ·
    refine ⟨28556072041928006966508535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38074762722570675955344713 28556072041928006966508535)
    ·
      refine ⟨42834108062892010449762803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28556072041928006966508535 42834108062892010449762803)
      ·
        refine ⟨64251162094338015674644205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42834108062892010449762803 64251162094338015674644205)
        ·
          refine ⟨24094185785376755877991577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64251162094338015674644205 24094185785376755877991577)
          ·
            refine ⟨18070639339032566908493683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24094185785376755877991577 18070639339032566908493683)
            ·
              refine ⟨27105959008548850362740525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18070639339032566908493683 27105959008548850362740525)
              ·
                refine ⟨10164734628205818886027697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27105959008548850362740525 10164734628205818886027697)
                ·
                  refine ⟨7623550971154364164520773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10164734628205818886027697 7623550971154364164520773)
                  ·
                    refine ⟨1429415807091443280847645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7623550971154364164520773 1429415807091443280847645)
                    ·
                      rfl

theorem cell22_4175666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 3, 2, 4].length) (baseStart_4175666 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4175666 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4175666 prefixEnd_4175666 := by exact prefixLift 4175666
  have htrace : WordTrace (prefixWord ++ tailWord_4175666) baseStart_4175666 baseEnd_4175666 := by
    simpa [prefixWord, tailWord_4175666, baseEnd_4175666] using wordTrace_append hprefix tailTrace_4175666
  have hstable : (prefixWord ++ tailWord_4175666).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4175666).length < 2 ^ (prefixWord ++ tailWord_4175666).sum := by decide
  have hdescent : baseEnd_4175666 < baseStart_4175666 := by decide
  rcases family_descends (prefixWord ++ tailWord_4175666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4175668 : List Nat := [2, 5, 1, 1, 2, 2, 1, 2, 1, 5]
def baseStart_4175668 : Nat := 118140960795 + 4175668 * 2 ^ 59
def prefixEnd_4175668 : Nat := 4983230072969 + 3 ^ 40 * 4175668 * 2
def baseEnd_4175668 : Nat := 1429416491732315942297639

theorem tailTrace_4175668 : CollatzResearch.WordTrace tailWord_4175668 prefixEnd_4175668 1429416491732315942297639 := by
  unfold tailWord_4175668
  simp only [CollatzResearch.WordTrace]
  refine ⟨76149561918137729081475829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101532749224183638775301105 76149561918137729081475829)
  ·
    refine ⟨7139021429825412101388359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 76149561918137729081475829 7139021429825412101388359)
    ·
      refine ⟨10708532144738118152082539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7139021429825412101388359 10708532144738118152082539)
      ·
        refine ⟨16062798217107177228123809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10708532144738118152082539 16062798217107177228123809)
        ·
          refine ⟨12047098662830382921092857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16062798217107177228123809 12047098662830382921092857)
          ·
            refine ⟨9035323997122787190819643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12047098662830382921092857 9035323997122787190819643)
            ·
              refine ⟨13552985995684180786229465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9035323997122787190819643 13552985995684180786229465)
              ·
                refine ⟨10164739496763135589672099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13552985995684180786229465 10164739496763135589672099)
                ·
                  refine ⟨15247109245144703384508149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10164739496763135589672099 15247109245144703384508149)
                  ·
                    refine ⟨1429416491732315942297639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15247109245144703384508149 1429416491732315942297639)
                    ·
                      rfl

theorem cell22_4175668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 1, 2, 1, 5].length) (baseStart_4175668 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4175668 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4175668 prefixEnd_4175668 := by exact prefixLift 4175668
  have htrace : WordTrace (prefixWord ++ tailWord_4175668) baseStart_4175668 baseEnd_4175668 := by
    simpa [prefixWord, tailWord_4175668, baseEnd_4175668] using wordTrace_append hprefix tailTrace_4175668
  have hstable : (prefixWord ++ tailWord_4175668).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4175668).length < 2 ^ (prefixWord ++ tailWord_4175668).sum := by decide
  have hdescent : baseEnd_4175668 < baseStart_4175668 := by decide
  rcases family_descends (prefixWord ++ tailWord_4175668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4175696 : List Nat := [2, 1, 1, 1, 1, 4, 1, 5, 3, 3]
def baseStart_4175696 : Nat := 118140960795 + 4175696 * 2 ^ 59
def prefixEnd_4175696 : Nat := 4983230072969 + 3 ^ 40 * 4175696 * 2
def baseEnd_4175696 : Nat := 1429426076704533202597553

theorem tailTrace_4175696 : CollatzResearch.WordTrace tailWord_4175696 prefixEnd_4175696 1429426076704533202597553 := by
  unfold tailWord_4175696
  simp only [CollatzResearch.WordTrace]
  refine ⟨76150072540087009472485471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101533430053449345963313961 76150072540087009472485471)
  ·
    refine ⟨114225108810130514208728207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76150072540087009472485471 114225108810130514208728207)
    ·
      refine ⟨171337663215195771313092311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114225108810130514208728207 171337663215195771313092311)
      ·
        refine ⟨257006494822793656969638467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171337663215195771313092311 257006494822793656969638467)
        ·
          refine ⟨385509742234190485454457701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 257006494822793656969638467 385509742234190485454457701)
          ·
            refine ⟨72283076668910716022710819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 385509742234190485454457701 72283076668910716022710819)
            ·
              refine ⟨108424615003366074034066229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72283076668910716022710819 108424615003366074034066229)
              ·
                refine ⟨10164807656565569440693709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 108424615003366074034066229 10164807656565569440693709)
                ·
                  refine ⟨3811802871212088540260141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10164807656565569440693709 3811802871212088540260141)
                  ·
                    refine ⟨1429426076704533202597553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3811802871212088540260141 1429426076704533202597553)
                    ·
                      rfl

theorem cell22_4175696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 5, 3, 3].length) (baseStart_4175696 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4175696 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4175696 prefixEnd_4175696 := by exact prefixLift 4175696
  have htrace : WordTrace (prefixWord ++ tailWord_4175696) baseStart_4175696 baseEnd_4175696 := by
    simpa [prefixWord, tailWord_4175696, baseEnd_4175696] using wordTrace_append hprefix tailTrace_4175696
  have hstable : (prefixWord ++ tailWord_4175696).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4175696).length < 2 ^ (prefixWord ++ tailWord_4175696).sum := by decide
  have hdescent : baseEnd_4175696 < baseStart_4175696 := by decide
  rcases family_descends (prefixWord ++ tailWord_4175696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4175773 : List Nat := [1, 4, 2, 1, 2, 2, 1, 4, 1, 4]
def baseStart_4175773 : Nat := 118140960795 + 4175773 * 2 ^ 59
def prefixEnd_4175773 : Nat := 4983230072969 + 3 ^ 40 * 4175773 * 2
def baseEnd_4175773 : Nat := 1429452435378130668422317

theorem tailTrace_4175773 : CollatzResearch.WordTrace tailWord_4175773 prefixEnd_4175773 1429452435378130668422317 := by
  unfold tailWord_4175773
  simp only [CollatzResearch.WordTrace]
  refine ⟨152302953500895061095523973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101535302333930040730349315 152302953500895061095523973)
  ·
    refine ⟨28556803781417823955410745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 152302953500895061095523973 28556803781417823955410745)
    ·
      refine ⟨21417602836063367966558059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28556803781417823955410745 21417602836063367966558059)
      ·
        refine ⟨32126404254095051949837089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21417602836063367966558059 32126404254095051949837089)
        ·
          refine ⟨24094803190571288962377817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32126404254095051949837089 24094803190571288962377817)
          ·
            refine ⟨18071102392928466721783363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24094803190571288962377817 18071102392928466721783363)
            ·
              refine ⟨27106653589392700082675045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18071102392928466721783363 27106653589392700082675045)
              ·
                refine ⟨5082497548011131265501571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27106653589392700082675045 5082497548011131265501571)
                ·
                  refine ⟨7623746322016696898252357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5082497548011131265501571 7623746322016696898252357)
                  ·
                    refine ⟨1429452435378130668422317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7623746322016696898252357 1429452435378130668422317)
                    ·
                      rfl

theorem cell22_4175773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 4, 1, 4].length) (baseStart_4175773 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4175773 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4175773 prefixEnd_4175773 := by exact prefixLift 4175773
  have htrace : WordTrace (prefixWord ++ tailWord_4175773) baseStart_4175773 baseEnd_4175773 := by
    simpa [prefixWord, tailWord_4175773, baseEnd_4175773] using wordTrace_append hprefix tailTrace_4175773
  have hstable : (prefixWord ++ tailWord_4175773).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4175773).length < 2 ^ (prefixWord ++ tailWord_4175773).sum := by decide
  have hdescent : baseEnd_4175773 < baseStart_4175773 := by decide
  rcases family_descends (prefixWord ++ tailWord_4175773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4175816 : List Nat := [2, 1, 3, 1, 4, 1, 1, 9]
def baseStart_4175816 : Nat := 118140960795 + 4175816 * 2 ^ 59
def prefixEnd_4175816 : Nat := 4983230072969 + 3 ^ 40 * 4175816 * 2
def baseEnd_4175816 : Nat := 158829683906321432177465

theorem tailTrace_4175816 : CollatzResearch.WordTrace tailWord_4175816 prefixEnd_4175816 158829683906321432177465 := by
  unfold tailWord_4175816
  simp only [CollatzResearch.WordTrace]
  refine ⟨76152260919869639719669651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101536347893159519626226201 76152260919869639719669651)
  ·
    refine ⟨114228391379804459579504477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76152260919869639719669651 114228391379804459579504477)
    ·
      refine ⟨42835646767426672342314179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114228391379804459579504477 42835646767426672342314179)
      ·
        refine ⟨64253470151140008513471269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42835646767426672342314179 64253470151140008513471269)
        ·
          refine ⟨12047525653338751596275863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 64253470151140008513471269 12047525653338751596275863)
          ·
            refine ⟨18071288480008127394413795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12047525653338751596275863 18071288480008127394413795)
            ·
              refine ⟨27106932720012191091620693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18071288480008127394413795 27106932720012191091620693)
              ·
                refine ⟨158829683906321432177465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 27106932720012191091620693 158829683906321432177465)
                ·
                  rfl

theorem cell22_4175816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 9].length) (baseStart_4175816 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4175816 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4175816 prefixEnd_4175816 := by exact prefixLift 4175816
  have htrace : WordTrace (prefixWord ++ tailWord_4175816) baseStart_4175816 baseEnd_4175816 := by
    simpa [prefixWord, tailWord_4175816, baseEnd_4175816] using wordTrace_append hprefix tailTrace_4175816
  have hstable : (prefixWord ++ tailWord_4175816).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4175816).length < 2 ^ (prefixWord ++ tailWord_4175816).sum := by decide
  have hdescent : baseEnd_4175816 < baseStart_4175816 := by decide
  rcases family_descends (prefixWord ++ tailWord_4175816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4175820 : List Nat := [2, 2, 1, 4, 1, 3, 1, 3, 2, 3]
def baseStart_4175820 : Nat := 118140960795 + 4175820 * 2 ^ 59
def prefixEnd_4175820 : Nat := 4983230072969 + 3 ^ 40 * 4175820 * 2
def baseEnd_4175820 : Nat := 1429468524438638212497173

theorem tailTrace_4175820 : CollatzResearch.WordTrace tailWord_4175820 prefixEnd_4175820 1429468524438638212497173 := by
  unfold tailWord_4175820
  simp only [CollatzResearch.WordTrace]
  refine ⟨76152333865862394061242457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101536445154483192081656609 76152333865862394061242457)
  ·
    refine ⟨57114250399396795545931843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76152333865862394061242457 57114250399396795545931843)
    ·
      refine ⟨85671375599095193318897765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57114250399396795545931843 85671375599095193318897765)
      ·
        refine ⟨16063382924830348747293331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 85671375599095193318897765 16063382924830348747293331)
        ·
          refine ⟨24095074387245523120939997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16063382924830348747293331 24095074387245523120939997)
          ·
            refine ⟨9035652895217071170352499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24095074387245523120939997 9035652895217071170352499)
            ·
              refine ⟨13553479342825606755528749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9035652895217071170352499 13553479342825606755528749)
              ·
                refine ⟨5082554753559602533323281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13553479342825606755528749 5082554753559602533323281)
                ·
                  refine ⟨3811916065169701899992461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5082554753559602533323281 3811916065169701899992461)
                  ·
                    refine ⟨1429468524438638212497173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3811916065169701899992461 1429468524438638212497173)
                    ·
                      rfl

theorem cell22_4175820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 1, 3, 2, 3].length) (baseStart_4175820 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4175820 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4175820 prefixEnd_4175820 := by exact prefixLift 4175820
  have htrace : WordTrace (prefixWord ++ tailWord_4175820) baseStart_4175820 baseEnd_4175820 := by
    simpa [prefixWord, tailWord_4175820, baseEnd_4175820] using wordTrace_append hprefix tailTrace_4175820
  have hstable : (prefixWord ++ tailWord_4175820).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4175820).length < 2 ^ (prefixWord ++ tailWord_4175820).sum := by decide
  have hdescent : baseEnd_4175820 < baseStart_4175820 := by decide
  rcases family_descends (prefixWord ++ tailWord_4175820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4175951 : List Nat := [1, 1, 2, 1, 1, 2, 2, 12]
def baseStart_4175951 : Nat := 118140960795 + 4175951 * 2 ^ 59
def prefixEnd_4175951 : Nat := 4983230072969 + 3 ^ 40 * 4175951 * 2
def baseEnd_4175951 : Nat := 158834818712866393052419

theorem tailTrace_4175951 : CollatzResearch.WordTrace tailWord_4175951 prefixEnd_4175951 158834818712866393052419 := by
  unfold tailWord_4175951
  simp only [CollatzResearch.WordTrace]
  refine ⟨152309445694250197495503707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101539630462833464997002471 152309445694250197495503707)
  ·
    refine ⟨228464168541375296243255561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152309445694250197495503707 228464168541375296243255561)
    ·
      refine ⟨171348126406031472182441671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 228464168541375296243255561 171348126406031472182441671)
      ·
        refine ⟨257022189609047208273662507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171348126406031472182441671 257022189609047208273662507)
        ·
          refine ⟨385533284413570812410493761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 257022189609047208273662507 385533284413570812410493761)
          ·
            refine ⟨289149963310178109307870321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 385533284413570812410493761 289149963310178109307870321)
            ·
              refine ⟨216862472482633581980902741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 289149963310178109307870321 216862472482633581980902741)
              ·
                refine ⟨158834818712866393052419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 216862472482633581980902741 158834818712866393052419)
                ·
                  rfl

theorem cell22_4175951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 12].length) (baseStart_4175951 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4175951 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4175951 prefixEnd_4175951 := by exact prefixLift 4175951
  have htrace : WordTrace (prefixWord ++ tailWord_4175951) baseStart_4175951 baseEnd_4175951 := by
    simpa [prefixWord, tailWord_4175951, baseEnd_4175951] using wordTrace_append hprefix tailTrace_4175951
  have hstable : (prefixWord ++ tailWord_4175951).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4175951).length < 2 ^ (prefixWord ++ tailWord_4175951).sum := by decide
  have hdescent : baseEnd_4175951 < baseStart_4175951 := by decide
  rcases family_descends (prefixWord ++ tailWord_4175951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4175953 : List Nat := [1, 2, 2, 1, 3, 1, 1, 5, 2, 4]
def baseStart_4175953 : Nat := 118140960795 + 4175953 * 2 ^ 59
def prefixEnd_4175953 : Nat := 4983230072969 + 3 ^ 40 * 4175953 * 2
def baseEnd_4175953 : Nat := 1429514053056670198921765

theorem tailTrace_4175953 : CollatzResearch.WordTrace tailWord_4175953 prefixEnd_4175953 1429514053056670198921765 := by
  unfold tailWord_4175953
  simp only [CollatzResearch.WordTrace]
  refine ⟨152309518640242951837076513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101539679093495301224717675 152309518640242951837076513)
  ·
    refine ⟨114232138980182213877807385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152309518640242951837076513 114232138980182213877807385)
    ·
      refine ⟨85674104235136660408355539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114232138980182213877807385 85674104235136660408355539)
      ·
        refine ⟨128511156352704990612533309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85674104235136660408355539 128511156352704990612533309)
        ·
          refine ⟨48191683632264371479699991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 128511156352704990612533309 48191683632264371479699991)
          ·
            refine ⟨72287525448396557219549987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48191683632264371479699991 72287525448396557219549987)
            ·
              refine ⟨108431288172594835829324981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72287525448396557219549987 108431288172594835829324981)
              ·
                refine ⟨10165433266180765858999217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 108431288172594835829324981 10165433266180765858999217)
                ·
                  refine ⟨7624074949635574394249413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10165433266180765858999217 7624074949635574394249413)
                  ·
                    refine ⟨1429514053056670198921765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7624074949635574394249413 1429514053056670198921765)
                    ·
                      rfl

theorem cell22_4175953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 5, 2, 4].length) (baseStart_4175953 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4175953 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4175953 prefixEnd_4175953 := by exact prefixLift 4175953
  have htrace : WordTrace (prefixWord ++ tailWord_4175953) baseStart_4175953 baseEnd_4175953 := by
    simpa [prefixWord, tailWord_4175953, baseEnd_4175953] using wordTrace_append hprefix tailTrace_4175953
  have hstable : (prefixWord ++ tailWord_4175953).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4175953).length < 2 ^ (prefixWord ++ tailWord_4175953).sum := by decide
  have hdescent : baseEnd_4175953 < baseStart_4175953 := by decide
  rcases family_descends (prefixWord ++ tailWord_4175953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4175957 : List Nat := [1, 3, 2, 2, 1, 5, 1, 3, 4]
def baseStart_4175957 : Nat := 118140960795 + 4175957 * 2 ^ 59
def prefixEnd_4175957 : Nat := 4983230072969 + 3 ^ 40 * 4175957 * 2
def baseEnd_4175957 : Nat := 476505140779471840607251

theorem tailTrace_4175957 : CollatzResearch.WordTrace tailWord_4175957 prefixEnd_4175957 476505140779471840607251 := by
  unfold tailWord_4175957
  simp only [CollatzResearch.WordTrace]
  refine ⟨152309664532228460520222125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101539776354818973680148083 152309664532228460520222125)
  ·
    refine ⟨57116124199585672695083297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152309664532228460520222125 57116124199585672695083297)
    ·
      refine ⟨42837093149689254521312473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57116124199585672695083297 42837093149689254521312473)
      ·
        refine ⟨32127819862266940890984355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42837093149689254521312473 32127819862266940890984355)
        ·
          refine ⟨48191729793400411336476533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32127819862266940890984355 48191729793400411336476533)
          ·
            refine ⟨4517974668131288562794675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 48191729793400411336476533 4517974668131288562794675)
            ·
              refine ⟨6776962002196932844192013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4517974668131288562794675 6776962002196932844192013)
              ·
                refine ⟨2541360750823849816572005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6776962002196932844192013 2541360750823849816572005)
                ·
                  refine ⟨476505140779471840607251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2541360750823849816572005 476505140779471840607251)
                  ·
                    rfl

theorem cell22_4175957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 5, 1, 3, 4].length) (baseStart_4175957 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4175957 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4175957 prefixEnd_4175957 := by exact prefixLift 4175957
  have htrace : WordTrace (prefixWord ++ tailWord_4175957) baseStart_4175957 baseEnd_4175957 := by
    simpa [prefixWord, tailWord_4175957, baseEnd_4175957] using wordTrace_append hprefix tailTrace_4175957
  have hstable : (prefixWord ++ tailWord_4175957).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4175957).length < 2 ^ (prefixWord ++ tailWord_4175957).sum := by decide
  have hdescent : baseEnd_4175957 < baseStart_4175957 := by decide
  rcases family_descends (prefixWord ++ tailWord_4175957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4175968 : List Nat := [2, 1, 1, 3, 2, 5, 8]
def baseStart_4175968 : Nat := 118140960795 + 4175968 * 2 ^ 59
def prefixEnd_4175968 : Nat := 4983230072969 + 3 ^ 40 * 4175968 * 2
def baseEnd_4175968 : Nat := 52945155106045005918397

theorem tailTrace_4175968 : CollatzResearch.WordTrace tailWord_4175968 prefixEnd_4175968 52945155106045005918397 := by
  unfold tailWord_4175968
  simp only [CollatzResearch.WordTrace]
  refine ⟨76155032867594304699436279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101540043823459072932581705 76155032867594304699436279)
  ·
    refine ⟨114232549301391457049154419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76155032867594304699436279 114232549301391457049154419)
    ·
      refine ⟨171348823952087185573731629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114232549301391457049154419 171348823952087185573731629)
      ·
        refine ⟨64255808982032694590149361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 171348823952087185573731629 64255808982032694590149361)
        ·
          refine ⟨48191856736524520942612021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64255808982032694590149361 48191856736524520942612021)
          ·
            refine ⟨4517986569049173838369877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 48191856736524520942612021 4517986569049173838369877)
            ·
              refine ⟨52945155106045005918397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4517986569049173838369877 52945155106045005918397)
              ·
                rfl

theorem cell22_4175968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 5, 8].length) (baseStart_4175968 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4175968 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4175968 prefixEnd_4175968 := by exact prefixLift 4175968
  have htrace : WordTrace (prefixWord ++ tailWord_4175968) baseStart_4175968 baseEnd_4175968 := by
    simpa [prefixWord, tailWord_4175968, baseEnd_4175968] using wordTrace_append hprefix tailTrace_4175968
  have hstable : (prefixWord ++ tailWord_4175968).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4175968).length < 2 ^ (prefixWord ++ tailWord_4175968).sum := by decide
  have hdescent : baseEnd_4175968 < baseStart_4175968 := by decide
  rcases family_descends (prefixWord ++ tailWord_4175968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4176045 : List Nat := [1, 5, 2, 1, 2, 1, 1, 1, 1, 7]
def baseStart_4176045 : Nat := 118140960795 + 4176045 * 2 ^ 59
def prefixEnd_4176045 : Nat := 4983230072969 + 3 ^ 40 * 4176045 * 2
def baseEnd_4176045 : Nat := 1429545546536812625621483

theorem tailTrace_4176045 : CollatzResearch.WordTrace tailWord_4176045 prefixEnd_4176045 1429545546536812625621483 := by
  unfold tailWord_4176045
  simp only [CollatzResearch.WordTrace]
  refine ⟨152312874155909651549425589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101541916103939767699617059 152312874155909651549425589)
  ·
    refine ⟨14279331952116529832758649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 152312874155909651549425589 14279331952116529832758649)
    ·
      refine ⟨10709498964087397374568987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14279331952116529832758649 10709498964087397374568987)
      ·
        refine ⟨16064248446131096061853481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10709498964087397374568987 16064248446131096061853481)
        ·
          refine ⟨12048186334598322046390111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16064248446131096061853481 12048186334598322046390111)
          ·
            refine ⟨18072279501897483069585167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12048186334598322046390111 18072279501897483069585167)
            ·
              refine ⟨27108419252846224604377751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18072279501897483069585167 27108419252846224604377751)
              ·
                refine ⟨40662628879269336906566627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27108419252846224604377751 40662628879269336906566627)
                ·
                  refine ⟨60993943318904005359849941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40662628879269336906566627 60993943318904005359849941)
                  ·
                    refine ⟨1429545546536812625621483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 60993943318904005359849941 1429545546536812625621483)
                    ·
                      rfl

theorem cell22_4176045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 1, 1, 7].length) (baseStart_4176045 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4176045 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4176045 prefixEnd_4176045 := by exact prefixLift 4176045
  have htrace : WordTrace (prefixWord ++ tailWord_4176045) baseStart_4176045 baseEnd_4176045 := by
    simpa [prefixWord, tailWord_4176045, baseEnd_4176045] using wordTrace_append hprefix tailTrace_4176045
  have hstable : (prefixWord ++ tailWord_4176045).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4176045).length < 2 ^ (prefixWord ++ tailWord_4176045).sum := by decide
  have hdescent : baseEnd_4176045 < baseStart_4176045 := by decide
  rcases family_descends (prefixWord ++ tailWord_4176045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4176058 : List Nat := [3, 1, 1, 1, 2, 2, 3, 1, 8]
def baseStart_4176058 : Nat := 118140960795 + 4176058 * 2 ^ 59
def prefixEnd_4176058 : Nat := 4983230072969 + 3 ^ 40 * 4176058 * 2
def baseEnd_4176058 : Nat := 476516665567494975015481

theorem tailTrace_4176058 : CollatzResearch.WordTrace tailWord_4176058 prefixEnd_4176058 476516665567494975015481 := by
  unfold tailWord_4176058
  simp only [CollatzResearch.WordTrace]
  refine ⟨38078337076215638692412207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101542232203241703179765885 38078337076215638692412207)
  ·
    refine ⟨57117505614323458038618311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38078337076215638692412207 57117505614323458038618311)
    ·
      refine ⟨85676258421485187057927467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57117505614323458038618311 85676258421485187057927467)
      ·
        refine ⟨128514387632227780586891201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85676258421485187057927467 128514387632227780586891201)
        ·
          refine ⟨96385790724170835440168401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128514387632227780586891201 96385790724170835440168401)
          ·
            refine ⟨72289343043128126580126301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96385790724170835440168401 72289343043128126580126301)
            ·
              refine ⟨27108503641173047467547363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72289343043128126580126301 27108503641173047467547363)
              ·
                refine ⟨40662755461759571201321045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27108503641173047467547363 40662755461759571201321045)
                ·
                  refine ⟨476516665567494975015481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 40662755461759571201321045 476516665567494975015481)
                  ·
                    rfl

theorem cell22_4176058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 1, 8].length) (baseStart_4176058 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4176058 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4176058 prefixEnd_4176058 := by exact prefixLift 4176058
  have htrace : WordTrace (prefixWord ++ tailWord_4176058) baseStart_4176058 baseEnd_4176058 := by
    simpa [prefixWord, tailWord_4176058, baseEnd_4176058] using wordTrace_append hprefix tailTrace_4176058
  have hstable : (prefixWord ++ tailWord_4176058).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4176058).length < 2 ^ (prefixWord ++ tailWord_4176058).sum := by decide
  have hdescent : baseEnd_4176058 < baseStart_4176058 := by decide
  rcases family_descends (prefixWord ++ tailWord_4176058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4176073 : List Nat := [1, 2, 1, 1, 2, 1, 1, 5, 3, 5]
def baseStart_4176073 : Nat := 118140960795 + 4176073 * 2 ^ 59
def prefixEnd_4176073 : Nat := 4983230072969 + 3 ^ 40 * 4176073 * 2
def baseEnd_4176073 : Nat := 1429555131509029885921397

theorem tailTrace_4176073 : CollatzResearch.WordTrace tailWord_4176073 prefixEnd_4176073 1429555131509029885921397 := by
  unfold tailWord_4176073
  simp only [CollatzResearch.WordTrace]
  refine ⟨152313895399808212331444873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101542596933205474887629915 152313895399808212331444873)
  ·
    refine ⟨114235421549856159248583655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152313895399808212331444873 114235421549856159248583655)
    ·
      refine ⟨171353132324784238872875483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114235421549856159248583655 171353132324784238872875483)
      ·
        refine ⟨257029698487176358309313225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171353132324784238872875483 257029698487176358309313225)
        ·
          refine ⟨192772273865382268731984919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 257029698487176358309313225 192772273865382268731984919)
          ·
            refine ⟨289158410798073403097977379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192772273865382268731984919 289158410798073403097977379)
            ·
              refine ⟨433737616197110104646966069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 289158410798073403097977379 433737616197110104646966069)
              ·
                refine ⟨40662901518479072310653069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 433737616197110104646966069 40662901518479072310653069)
                ·
                  refine ⟨15248588069429652116494901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40662901518479072310653069 15248588069429652116494901)
                  ·
                    refine ⟨1429555131509029885921397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15248588069429652116494901 1429555131509029885921397)
                    ·
                      rfl

theorem cell22_4176073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 5, 3, 5].length) (baseStart_4176073 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4176073 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4176073 prefixEnd_4176073 := by exact prefixLift 4176073
  have htrace : WordTrace (prefixWord ++ tailWord_4176073) baseStart_4176073 baseEnd_4176073 := by
    simpa [prefixWord, tailWord_4176073, baseEnd_4176073] using wordTrace_append hprefix tailTrace_4176073
  have hstable : (prefixWord ++ tailWord_4176073).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4176073).length < 2 ^ (prefixWord ++ tailWord_4176073).sum := by decide
  have hdescent : baseEnd_4176073 < baseStart_4176073 := by decide
  rcases family_descends (prefixWord ++ tailWord_4176073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4176098 : List Nat := [3, 3, 4, 1, 1, 1, 3, 1, 5]
def baseStart_4176098 : Nat := 118140960795 + 4176098 * 2 ^ 59
def prefixEnd_4176098 : Nat := 4983230072969 + 3 ^ 40 * 4176098 * 2
def baseEnd_4176098 : Nat := 476521229839979384682107

theorem tailTrace_4176098 : CollatzResearch.WordTrace tailWord_4176098 prefixEnd_4176098 476521229839979384682107 := by
  unfold tailWord_4176098
  simp only [CollatzResearch.WordTrace]
  refine ⟨38078701806179410400276237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101543204816478427734069965 38078701806179410400276237)
  ·
    refine ⟨14279513177317278900103589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38078701806179410400276237 14279513177317278900103589)
    ·
      refine ⟨2677408720746989793769423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14279513177317278900103589 2677408720746989793769423)
      ·
        refine ⟨4016113081120484690654135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2677408720746989793769423 4016113081120484690654135)
        ·
          refine ⟨6024169621680727035981203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4016113081120484690654135 6024169621680727035981203)
          ·
            refine ⟨9036254432521090553971805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6024169621680727035981203 9036254432521090553971805)
            ·
              refine ⟨3388595412195408957739427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9036254432521090553971805 3388595412195408957739427)
              ·
                refine ⟨5082893118293113436609141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3388595412195408957739427 5082893118293113436609141)
                ·
                  refine ⟨476521229839979384682107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5082893118293113436609141 476521229839979384682107)
                  ·
                    rfl

theorem cell22_4176098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 3, 1, 5].length) (baseStart_4176098 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4176098 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4176098 prefixEnd_4176098 := by exact prefixLift 4176098
  have htrace : WordTrace (prefixWord ++ tailWord_4176098) baseStart_4176098 baseEnd_4176098 := by
    simpa [prefixWord, tailWord_4176098, baseEnd_4176098] using wordTrace_append hprefix tailTrace_4176098
  have hstable : (prefixWord ++ tailWord_4176098).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4176098).length < 2 ^ (prefixWord ++ tailWord_4176098).sum := by decide
  have hdescent : baseEnd_4176098 < baseStart_4176098 := by decide
  rcases family_descends (prefixWord ++ tailWord_4176098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4176158 : List Nat := [4, 3, 2, 1, 1, 1, 4, 1, 2, 3]
def baseStart_4176158 : Nat := 118140960795 + 4176158 * 2 ^ 59
def prefixEnd_4176158 : Nat := 4983230072969 + 3 ^ 40 * 4176158 * 2
def baseEnd_4176158 : Nat := 1429584228746117997546137

theorem tailTrace_4176158 : CollatzResearch.WordTrace tailWord_4176158 prefixEnd_4176158 1429584228746117997546137 := by
  unfold tailWord_4176158
  simp only [CollatzResearch.WordTrace]
  refine ⟨19039624450562533981036141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 101544663736333514565526085 19039624450562533981036141)
  ·
    refine ⟨7139859168960950242888553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19039624450562533981036141 7139859168960950242888553)
    ·
      refine ⟨5354894376720712682166415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7139859168960950242888553 5354894376720712682166415)
      ·
        refine ⟨8032341565081069023249623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5354894376720712682166415 8032341565081069023249623)
        ·
          refine ⟨12048512347621603534874435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8032341565081069023249623 12048512347621603534874435)
          ·
            refine ⟨18072768521432405302311653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12048512347621603534874435 18072768521432405302311653)
            ·
              refine ⟨3388644097768575994183435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18072768521432405302311653 3388644097768575994183435)
              ·
                refine ⟨5082966146652863991275153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3388644097768575994183435 5082966146652863991275153)
                ·
                  refine ⟨3812224609989647993456365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5082966146652863991275153 3812224609989647993456365)
                  ·
                    refine ⟨1429584228746117997546137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3812224609989647993456365 1429584228746117997546137)
                    ·
                      rfl

theorem cell22_4176158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 4, 1, 2, 3].length) (baseStart_4176158 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4176158 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4176158 prefixEnd_4176158 := by exact prefixLift 4176158
  have htrace : WordTrace (prefixWord ++ tailWord_4176158) baseStart_4176158 baseEnd_4176158 := by
    simpa [prefixWord, tailWord_4176158, baseEnd_4176158] using wordTrace_append hprefix tailTrace_4176158
  have hstable : (prefixWord ++ tailWord_4176158).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4176158).length < 2 ^ (prefixWord ++ tailWord_4176158).sum := by decide
  have hdescent : baseEnd_4176158 < baseStart_4176158 := by decide
  rcases family_descends (prefixWord ++ tailWord_4176158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4176212 : List Nat := [2, 4, 1, 1, 2, 2, 1, 2, 3, 4]
def baseStart_4176212 : Nat := 118140960795 + 4176212 * 2 ^ 59
def prefixEnd_4176212 : Nat := 4983230072969 + 3 ^ 40 * 4176212 * 2
def baseEnd_4176212 : Nat := 1429602714049679856695971

theorem tailTrace_4176212 : CollatzResearch.WordTrace tailWord_4176212 prefixEnd_4176212 1429602714049679856695971 := by
  unfold tailWord_4176212
  simp only [CollatzResearch.WordTrace]
  refine ⟨76159482573152319535377445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101545976764203092713836593 76159482573152319535377445)
  ·
    refine ⟨14279902982466059912883271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 76159482573152319535377445 14279902982466059912883271)
    ·
      refine ⟨21419854473699089869324907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14279902982466059912883271 21419854473699089869324907)
      ·
        refine ⟨32129781710548634803987361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21419854473699089869324907 32129781710548634803987361)
        ·
          refine ⟨24097336282911476102990521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32129781710548634803987361 24097336282911476102990521)
          ·
            refine ⟨18073002212183607077242891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24097336282911476102990521 18073002212183607077242891)
            ·
              refine ⟨27109503318275410615864337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18073002212183607077242891 27109503318275410615864337)
              ·
                refine ⟨20332127488706557961898253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27109503318275410615864337 20332127488706557961898253)
                ·
                  refine ⟨7624547808264959235711845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20332127488706557961898253 7624547808264959235711845)
                  ·
                    refine ⟨1429602714049679856695971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7624547808264959235711845 1429602714049679856695971)
                    ·
                      rfl

theorem cell22_4176212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 2, 3, 4].length) (baseStart_4176212 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4176212 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4176212 prefixEnd_4176212 := by exact prefixLift 4176212
  have htrace : WordTrace (prefixWord ++ tailWord_4176212) baseStart_4176212 baseEnd_4176212 := by
    simpa [prefixWord, tailWord_4176212, baseEnd_4176212] using wordTrace_append hprefix tailTrace_4176212
  have hstable : (prefixWord ++ tailWord_4176212).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4176212).length < 2 ^ (prefixWord ++ tailWord_4176212).sum := by decide
  have hdescent : baseEnd_4176212 < baseStart_4176212 := by decide
  rcases family_descends (prefixWord ++ tailWord_4176212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4176242 : List Nat := [3, 2, 1, 2, 1, 3, 2, 2, 1, 5]
def baseStart_4176242 : Nat := 118140960795 + 4176242 * 2 ^ 59
def prefixEnd_4176242 : Nat := 4983230072969 + 3 ^ 40 * 4176242 * 2
def baseEnd_4176242 : Nat := 1429612983662769778445879

theorem tailTrace_4176242 : CollatzResearch.WordTrace tailWord_4176242 prefixEnd_4176242 1429612983662769778445879 := by
  unfold tailWord_4176242
  simp only [CollatzResearch.WordTrace]
  refine ⟨38080014834048988548586745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101546706224130636129564653 38080014834048988548586745)
  ·
    refine ⟨28560011125536741411440059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38080014834048988548586745 28560011125536741411440059)
    ·
      refine ⟨42840016688305112117160089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28560011125536741411440059 42840016688305112117160089)
      ·
        refine ⟨32130012516228834087870067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42840016688305112117160089 32130012516228834087870067)
        ·
          refine ⟨48195018774343251131805101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32130012516228834087870067 48195018774343251131805101)
          ·
            refine ⟨18073132040378719174426913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48195018774343251131805101 18073132040378719174426913)
            ·
              refine ⟨13554849030284039380820185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18073132040378719174426913 13554849030284039380820185)
              ·
                refine ⟨10166136772713029535615139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13554849030284039380820185 10166136772713029535615139)
                ·
                  refine ⟨15249205159069544303422709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10166136772713029535615139 15249205159069544303422709)
                  ·
                    refine ⟨1429612983662769778445879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15249205159069544303422709 1429612983662769778445879)
                    ·
                      rfl

theorem cell22_4176242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 2, 2, 1, 5].length) (baseStart_4176242 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4176242 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4176242 prefixEnd_4176242 := by exact prefixLift 4176242
  have htrace : WordTrace (prefixWord ++ tailWord_4176242) baseStart_4176242 baseEnd_4176242 := by
    simpa [prefixWord, tailWord_4176242, baseEnd_4176242] using wordTrace_append hprefix tailTrace_4176242
  have hstable : (prefixWord ++ tailWord_4176242).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4176242).length < 2 ^ (prefixWord ++ tailWord_4176242).sum := by decide
  have hdescent : baseEnd_4176242 < baseStart_4176242 := by decide
  rcases family_descends (prefixWord ++ tailWord_4176242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4176259 : List Nat := [1, 1, 1, 3, 6, 1, 1, 1, 4, 3]
def baseStart_4176259 : Nat := 118140960795 + 4176259 * 2 ^ 59
def prefixEnd_4176259 : Nat := 4983230072969 + 3 ^ 40 * 4176259 * 2
def baseEnd_4176259 : Nat := 1429618803110187400770827

theorem tailTrace_4176259 : CollatzResearch.WordTrace tailWord_4176259 prefixEnd_4176259 1429618803110187400770827 := by
  unfold tailWord_4176259
  simp only [CollatzResearch.WordTrace]
  refine ⟨152320679377134366097715831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101547119584756244065143887 152320679377134366097715831)
  ·
    refine ⟨228481019065701549146573747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152320679377134366097715831 228481019065701549146573747)
    ·
      refine ⟨342721528598552323719860621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228481019065701549146573747 342721528598552323719860621)
      ·
        refine ⟨128520573224457121394947733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 342721528598552323719860621 128520573224457121394947733)
        ·
          refine ⟨6024401869896427565388175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 128520573224457121394947733 6024401869896427565388175)
          ·
            refine ⟨9036602804844641348082263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6024401869896427565388175 9036602804844641348082263)
            ·
              refine ⟨13554904207266962022123395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9036602804844641348082263 13554904207266962022123395)
              ·
                refine ⟨20332356310900443033185093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13554904207266962022123395 20332356310900443033185093)
                ·
                  refine ⟨3812316808293833068722205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20332356310900443033185093 3812316808293833068722205)
                  ·
                    refine ⟨1429618803110187400770827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3812316808293833068722205 1429618803110187400770827)
                    ·
                      rfl

theorem cell22_4176259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 1, 1, 4, 3].length) (baseStart_4176259 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4176259 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4176259 prefixEnd_4176259 := by exact prefixLift 4176259
  have htrace : WordTrace (prefixWord ++ tailWord_4176259) baseStart_4176259 baseEnd_4176259 := by
    simpa [prefixWord, tailWord_4176259, baseEnd_4176259] using wordTrace_append hprefix tailTrace_4176259
  have hstable : (prefixWord ++ tailWord_4176259).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4176259).length < 2 ^ (prefixWord ++ tailWord_4176259).sum := by decide
  have hdescent : baseEnd_4176259 < baseStart_4176259 := by decide
  rcases family_descends (prefixWord ++ tailWord_4176259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4176276 : List Nat := [2, 4, 2, 1, 3, 2, 1, 1, 1, 5]
def baseStart_4176276 : Nat := 118140960795 + 4176276 * 2 ^ 59
def prefixEnd_4176276 : Nat := 4983230072969 + 3 ^ 40 * 4176276 * 2
def baseEnd_4176276 : Nat := 1429624622557605023095775

theorem tailTrace_4176276 : CollatzResearch.WordTrace tailWord_4176276 prefixEnd_4176276 1429624622557605023095775 := by
  unfold tailWord_4176276
  simp only [CollatzResearch.WordTrace]
  refine ⟨76160649709036389000542341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101547532945381852000723121 76160649709036389000542341)
  ·
    refine ⟨14280121820444322937601689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 76160649709036389000542341 14280121820444322937601689)
    ·
      refine ⟨10710091365333242203201267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14280121820444322937601689 10710091365333242203201267)
      ·
        refine ⟨16065137047999863304801901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10710091365333242203201267 16065137047999863304801901)
        ·
          refine ⟨6024426392999948739300713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16065137047999863304801901 6024426392999948739300713)
          ·
            refine ⟨4518319794749961554475535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6024426392999948739300713 4518319794749961554475535)
            ·
              refine ⟨6777479692124942331713303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4518319794749961554475535 6777479692124942331713303)
              ·
                refine ⟨10166219538187413497569955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6777479692124942331713303 10166219538187413497569955)
                ·
                  refine ⟨15249329307281120246354933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10166219538187413497569955 15249329307281120246354933)
                  ·
                    refine ⟨1429624622557605023095775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15249329307281120246354933 1429624622557605023095775)
                    ·
                      rfl

theorem cell22_4176276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 2, 1, 1, 1, 5].length) (baseStart_4176276 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4176276 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4176276 prefixEnd_4176276 := by exact prefixLift 4176276
  have htrace : WordTrace (prefixWord ++ tailWord_4176276) baseStart_4176276 baseEnd_4176276 := by
    simpa [prefixWord, tailWord_4176276, baseEnd_4176276] using wordTrace_append hprefix tailTrace_4176276
  have hstable : (prefixWord ++ tailWord_4176276).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4176276).length < 2 ^ (prefixWord ++ tailWord_4176276).sum := by decide
  have hdescent : baseEnd_4176276 < baseStart_4176276 := by decide
  rcases family_descends (prefixWord ++ tailWord_4176276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4176289 : List Nat := [1, 2, 3, 5, 1, 1, 1, 8]
def baseStart_4176289 : Nat := 118140960795 + 4176289 * 2 ^ 59
def prefixEnd_4176289 : Nat := 4983230072969 + 3 ^ 40 * 4176289 * 2
def baseEnd_4176289 : Nat := 158847674747030813613415

theorem tailTrace_4176289 : CollatzResearch.WordTrace tailWord_4176289 prefixEnd_4176289 158847674747030813613415 := by
  unfold tailWord_4176289
  simp only [CollatzResearch.WordTrace]
  refine ⟨152321773567025681221307921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101547849044683787480871947 152321773567025681221307921)
  ·
    refine ⟨114241330175269260915980941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152321773567025681221307921 114241330175269260915980941)
    ·
      refine ⟨42840498815725972843492853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114241330175269260915980941 42840498815725972843492853)
      ·
        refine ⟨4016296763974309954077455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 42840498815725972843492853 4016296763974309954077455)
        ·
          refine ⟨6024445145961464931116183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4016296763974309954077455 6024445145961464931116183)
          ·
            refine ⟨9036667718942197396674275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6024445145961464931116183 9036667718942197396674275)
            ·
              refine ⟨13555001578413296095011413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9036667718942197396674275 13555001578413296095011413)
              ·
                refine ⟨158847674747030813613415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13555001578413296095011413 158847674747030813613415)
                ·
                  rfl

theorem cell22_4176289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 1, 8].length) (baseStart_4176289 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4176289 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4176289 prefixEnd_4176289 := by exact prefixLift 4176289
  have htrace : WordTrace (prefixWord ++ tailWord_4176289) baseStart_4176289 baseEnd_4176289 := by
    simpa [prefixWord, tailWord_4176289, baseEnd_4176289] using wordTrace_append hprefix tailTrace_4176289
  have hstable : (prefixWord ++ tailWord_4176289).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4176289).length < 2 ^ (prefixWord ++ tailWord_4176289).sum := by decide
  have hdescent : baseEnd_4176289 < baseStart_4176289 := by decide
  rcases family_descends (prefixWord ++ tailWord_4176289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4176308 : List Nat := [2, 5, 2, 2, 1, 1, 1, 2, 2, 4]
def baseStart_4176308 : Nat := 118140960795 + 4176308 * 2 ^ 59
def prefixEnd_4176308 : Nat := 4983230072969 + 3 ^ 40 * 4176308 * 2
def baseEnd_4176308 : Nat := 1429635576811567606295677

theorem tailTrace_4176308 : CollatzResearch.WordTrace tailWord_4176308 prefixEnd_4176308 1429635576811567606295677 := by
  unfold tailWord_4176308
  simp only [CollatzResearch.WordTrace]
  refine ⟨76161233276978423733124789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101548311035971231644166385 76161233276978423733124789)
  ·
    refine ⟨7140115619716727224980449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 76161233276978423733124789 7140115619716727224980449)
    ·
      refine ⟨5355086714787545418735337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7140115619716727224980449 5355086714787545418735337)
      ·
        refine ⟨4016315036090659064051503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5355086714787545418735337 4016315036090659064051503)
        ·
          refine ⟨6024472554135988596077255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4016315036090659064051503 6024472554135988596077255)
          ·
            refine ⟨9036708831203982894115883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6024472554135988596077255 9036708831203982894115883)
            ·
              refine ⟨13555063246805974341173825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9036708831203982894115883 13555063246805974341173825)
              ·
                refine ⟨10166297435104480755880369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13555063246805974341173825 10166297435104480755880369)
                ·
                  refine ⟨7624723076328360566910277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10166297435104480755880369 7624723076328360566910277)
                  ·
                    refine ⟨1429635576811567606295677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7624723076328360566910277 1429635576811567606295677)
                    ·
                      rfl

theorem cell22_4176308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 1, 2, 2, 4].length) (baseStart_4176308 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4176308 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4176308 prefixEnd_4176308 := by exact prefixLift 4176308
  have htrace : WordTrace (prefixWord ++ tailWord_4176308) baseStart_4176308 baseEnd_4176308 := by
    simpa [prefixWord, tailWord_4176308, baseEnd_4176308] using wordTrace_append hprefix tailTrace_4176308
  have hstable : (prefixWord ++ tailWord_4176308).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4176308).length < 2 ^ (prefixWord ++ tailWord_4176308).sum := by decide
  have hdescent : baseEnd_4176308 < baseStart_4176308 := by decide
  rcases family_descends (prefixWord ++ tailWord_4176308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4176315 : List Nat := [1, 1, 1, 1, 1, 2, 2, 1, 5, 7]
def baseStart_4176315 : Nat := 118140960795 + 4176315 * 2 ^ 59
def prefixEnd_4176315 : Nat := 4983230072969 + 3 ^ 40 * 4176315 * 2
def baseEnd_4176315 : Nat := 1429637973054621921370655

theorem tailTrace_4176315 : CollatzResearch.WordTrace tailWord_4176315 prefixEnd_4176315 1429637973054621921370655 := by
  unfold tailWord_4176315
  simp only [CollatzResearch.WordTrace]
  refine ⟨152322721864931487661754399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101548481243287658441169599 152322721864931487661754399)
  ·
    refine ⟨228484082797397231492631599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152322721864931487661754399 228484082797397231492631599)
    ·
      refine ⟨342726124196095847238947399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228484082797397231492631599 342726124196095847238947399)
      ·
        refine ⟨514089186294143770858421099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 342726124196095847238947399 514089186294143770858421099)
        ·
          refine ⟨771133779441215656287631649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 514089186294143770858421099 771133779441215656287631649)
          ·
            refine ⟨578350334580911742215723737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 771133779441215656287631649 578350334580911742215723737)
            ·
              refine ⟨433762750935683806661792803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 578350334580911742215723737 433762750935683806661792803)
              ·
                refine ⟨650644126403525709992689205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 433762750935683806661792803 650644126403525709992689205)
                ·
                  refine ⟨60997886850330535311814613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 650644126403525709992689205 60997886850330535311814613)
                  ·
                    refine ⟨1429637973054621921370655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 60997886850330535311814613 1429637973054621921370655)
                    ·
                      rfl

theorem cell22_4176315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 5, 7].length) (baseStart_4176315 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4176315 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4176315 prefixEnd_4176315 := by exact prefixLift 4176315
  have htrace : WordTrace (prefixWord ++ tailWord_4176315) baseStart_4176315 baseEnd_4176315 := by
    simpa [prefixWord, tailWord_4176315, baseEnd_4176315] using wordTrace_append hprefix tailTrace_4176315
  have hstable : (prefixWord ++ tailWord_4176315).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4176315).length < 2 ^ (prefixWord ++ tailWord_4176315).sum := by decide
  have hdescent : baseEnd_4176315 < baseStart_4176315 := by decide
  rcases family_descends (prefixWord ++ tailWord_4176315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4176317 : List Nat := [1, 4, 1, 2, 2, 2, 2, 1, 7]
def baseStart_4176317 : Nat := 118140960795 + 4176317 * 2 ^ 59
def prefixEnd_4176317 : Nat := 4983230072969 + 3 ^ 40 * 4176317 * 2
def baseEnd_4176317 : Nat := 476546219231831527606883

theorem tailTrace_4176317 : CollatzResearch.WordTrace tailWord_4176317 prefixEnd_4176317 476546219231831527606883 := by
  unfold tailWord_4176317
  simp only [CollatzResearch.WordTrace]
  refine ⟨152322794810924242003327205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101548529873949494668884803 152322794810924242003327205)
  ·
    refine ⟨28560524027048295375623851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 152322794810924242003327205 28560524027048295375623851)
    ·
      refine ⟨42840786040572443063435777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28560524027048295375623851 42840786040572443063435777)
      ·
        refine ⟨32130589530429332297576833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42840786040572443063435777 32130589530429332297576833)
        ·
          refine ⟨24097942147821999223182625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32130589530429332297576833 24097942147821999223182625)
          ·
            refine ⟨18073456610866499417386969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24097942147821999223182625 18073456610866499417386969)
            ·
              refine ⟨13555092458149874563040227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18073456610866499417386969 13555092458149874563040227)
              ·
                refine ⟨20332638687224811844560341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13555092458149874563040227 20332638687224811844560341)
                ·
                  refine ⟨476546219231831527606883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20332638687224811844560341 476546219231831527606883)
                  ·
                    rfl

theorem cell22_4176317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 2, 1, 7].length) (baseStart_4176317 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4176317 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4176317 prefixEnd_4176317 := by exact prefixLift 4176317
  have htrace : WordTrace (prefixWord ++ tailWord_4176317) baseStart_4176317 baseEnd_4176317 := by
    simpa [prefixWord, tailWord_4176317, baseEnd_4176317] using wordTrace_append hprefix tailTrace_4176317
  have hstable : (prefixWord ++ tailWord_4176317).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4176317).length < 2 ^ (prefixWord ++ tailWord_4176317).sum := by decide
  have hdescent : baseEnd_4176317 < baseStart_4176317 := by decide
  rcases family_descends (prefixWord ++ tailWord_4176317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4176392 : List Nat := [2, 1, 3, 2, 1, 1, 1, 4, 1, 6]
def baseStart_4176392 : Nat := 118140960795 + 4176392 * 2 ^ 59
def prefixEnd_4176392 : Nat := 4983230072969 + 3 ^ 40 * 4176392 * 2
def baseEnd_4176392 : Nat := 1429664331728219387195419

theorem tailTrace_4176392 : CollatzResearch.WordTrace tailWord_4176392 prefixEnd_4176392 1429664331728219387195419 := by
  unfold tailWord_4176392
  simp only [CollatzResearch.WordTrace]
  refine ⟨76162765142826264906153715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101550353523768353208204953 76162765142826264906153715)
  ·
    refine ⟨114244147714239397359230573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76162765142826264906153715 114244147714239397359230573)
    ·
      refine ⟨42841555392839774009711465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114244147714239397359230573 42841555392839774009711465)
      ·
        refine ⟨32131166544629830507283599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42841555392839774009711465 32131166544629830507283599)
        ·
          refine ⟨48196749816944745760925399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32131166544629830507283599 48196749816944745760925399)
          ·
            refine ⟨72295124725417118641388099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48196749816944745760925399 72295124725417118641388099)
            ·
              refine ⟨108442687088125677962082149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72295124725417118641388099 108442687088125677962082149)
              ·
                refine ⟨20333003829023564617890403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 108442687088125677962082149 20333003829023564617890403)
                ·
                  refine ⟨30499505743535346926835605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20333003829023564617890403 30499505743535346926835605)
                  ·
                    refine ⟨1429664331728219387195419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30499505743535346926835605 1429664331728219387195419)
                    ·
                      rfl

theorem cell22_4176392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 4, 1, 6].length) (baseStart_4176392 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4176392 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4176392 prefixEnd_4176392 := by exact prefixLift 4176392
  have htrace : WordTrace (prefixWord ++ tailWord_4176392) baseStart_4176392 baseEnd_4176392 := by
    simpa [prefixWord, tailWord_4176392, baseEnd_4176392] using wordTrace_append hprefix tailTrace_4176392
  have hstable : (prefixWord ++ tailWord_4176392).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4176392).length < 2 ^ (prefixWord ++ tailWord_4176392).sum := by decide
  have hdescent : baseEnd_4176392 < baseStart_4176392 := by decide
  rcases family_descends (prefixWord ++ tailWord_4176392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4176394 : List Nat := [3, 1, 2, 2, 2, 1, 4, 1, 1, 5]
def baseStart_4176394 : Nat := 118140960795 + 4176394 * 2 ^ 59
def prefixEnd_4176394 : Nat := 4983230072969 + 3 ^ 40 * 4176394 * 2
def baseEnd_4176394 : Nat := 1429665016369092048645413

theorem tailTrace_4176394 : CollatzResearch.WordTrace tailWord_4176394 prefixEnd_4176394 1429665016369092048645413 := by
  unfold tailWord_4176394
  simp only [CollatzResearch.WordTrace]
  refine ⟨38081400807911321038470059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101550402154430189435920157 38081400807911321038470059)
  ·
    refine ⟨57122101211866981557705089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38081400807911321038470059 57122101211866981557705089)
    ·
      refine ⟨42841575908900236168278817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57122101211866981557705089 42841575908900236168278817)
      ·
        refine ⟨32131181931675177126209113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42841575908900236168278817 32131181931675177126209113)
        ·
          refine ⟨24098386448756382844656835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32131181931675177126209113 24098386448756382844656835)
          ·
            refine ⟨36147579673134574266985253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24098386448756382844656835 36147579673134574266985253)
            ·
              refine ⟨6777671188712732675059735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36147579673134574266985253 6777671188712732675059735)
              ·
                refine ⟨10166506783069099012589603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6777671188712732675059735 10166506783069099012589603)
                ·
                  refine ⟨15249760174603648518884405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10166506783069099012589603 15249760174603648518884405)
                  ·
                    refine ⟨1429665016369092048645413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15249760174603648518884405 1429665016369092048645413)
                    ·
                      rfl

theorem cell22_4176394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 4, 1, 1, 5].length) (baseStart_4176394 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4176394 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4176394 prefixEnd_4176394 := by exact prefixLift 4176394
  have htrace : WordTrace (prefixWord ++ tailWord_4176394) baseStart_4176394 baseEnd_4176394 := by
    simpa [prefixWord, tailWord_4176394, baseEnd_4176394] using wordTrace_append hprefix tailTrace_4176394
  have hstable : (prefixWord ++ tailWord_4176394).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4176394).length < 2 ^ (prefixWord ++ tailWord_4176394).sum := by decide
  have hdescent : baseEnd_4176394 < baseStart_4176394 := by decide
  rcases family_descends (prefixWord ++ tailWord_4176394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4176424 : List Nat := [2, 1, 5, 2, 1, 2, 9]
def baseStart_4176424 : Nat := 118140960795 + 4176424 * 2 ^ 59
def prefixEnd_4176424 : Nat := 4983230072969 + 3 ^ 40 * 4176424 * 2
def baseEnd_4176424 : Nat := 52950936517858591496123

theorem tailTrace_4176424 : CollatzResearch.WordTrace tailWord_4176424 prefixEnd_4176424 52950936517858591496123 := by
  unfold tailWord_4176424
  simp only [CollatzResearch.WordTrace]
  refine ⟨76163348710768299638736163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101551131614357732851648217 76163348710768299638736163)
  ·
    refine ⟨114245023066152449458104245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76163348710768299638736163 114245023066152449458104245)
    ·
      refine ⟨10710470912451792136697273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 114245023066152449458104245 10710470912451792136697273)
      ·
        refine ⟨8032853184338844102522955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10710470912451792136697273 8032853184338844102522955)
        ·
          refine ⟨12049279776508266153784433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8032853184338844102522955 12049279776508266153784433)
          ·
            refine ⟨9036959832381199615338325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12049279776508266153784433 9036959832381199615338325)
            ·
              refine ⟨52950936517858591496123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 9036959832381199615338325 52950936517858591496123)
              ·
                rfl

theorem cell22_4176424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 9].length) (baseStart_4176424 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4176424 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4176424 prefixEnd_4176424 := by exact prefixLift 4176424
  have htrace : WordTrace (prefixWord ++ tailWord_4176424) baseStart_4176424 baseEnd_4176424 := by
    simpa [prefixWord, tailWord_4176424, baseEnd_4176424] using wordTrace_append hprefix tailTrace_4176424
  have hstable : (prefixWord ++ tailWord_4176424).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4176424).length < 2 ^ (prefixWord ++ tailWord_4176424).sum := by decide
  have hdescent : baseEnd_4176424 < baseStart_4176424 := by decide
  rcases family_descends (prefixWord ++ tailWord_4176424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4176490 : List Nat := [3, 1, 3, 2, 1, 1, 5, 2, 1, 3]
def baseStart_4176490 : Nat := 118140960795 + 4176490 * 2 ^ 59
def prefixEnd_4176490 : Nat := 4983230072969 + 3 ^ 40 * 4176490 * 2
def baseEnd_4176490 : Nat := 1429697879130979798245119

theorem tailTrace_4176490 : CollatzResearch.WordTrace tailWord_4176490 prefixEnd_4176490 1429697879130979798245119 := by
  unfold tailWord_4176490
  simp only [CollatzResearch.WordTrace]
  refine ⟨38082276159824373137343731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101552736426198328366249949 38082276159824373137343731)
  ·
    refine ⟨57123414239736559706015597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38082276159824373137343731 57123414239736559706015597)
    ·
      refine ⟨21421280339901209889755849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57123414239736559706015597 21421280339901209889755849)
      ·
        refine ⟨16065960254925907417316887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21421280339901209889755849 16065960254925907417316887)
        ·
          refine ⟨24098940382388861125975331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16065960254925907417316887 24098940382388861125975331)
          ·
            refine ⟨36148410573583291688962997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24098940382388861125975331 36148410573583291688962997)
            ·
              refine ⟨3388913491273433595840281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 36148410573583291688962997 3388913491273433595840281)
              ·
                refine ⟨2541685118455075196880211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3388913491273433595840281 2541685118455075196880211)
                ·
                  refine ⟨3812527677682612795320317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2541685118455075196880211 3812527677682612795320317)
                  ·
                    refine ⟨1429697879130979798245119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3812527677682612795320317 1429697879130979798245119)
                    ·
                      rfl

theorem cell22_4176490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 5, 2, 1, 3].length) (baseStart_4176490 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4176490 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4176490 prefixEnd_4176490 := by exact prefixLift 4176490
  have htrace : WordTrace (prefixWord ++ tailWord_4176490) baseStart_4176490 baseEnd_4176490 := by
    simpa [prefixWord, tailWord_4176490, baseEnd_4176490] using wordTrace_append hprefix tailTrace_4176490
  have hstable : (prefixWord ++ tailWord_4176490).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4176490).length < 2 ^ (prefixWord ++ tailWord_4176490).sum := by decide
  have hdescent : baseEnd_4176490 < baseStart_4176490 := by decide
  rcases family_descends (prefixWord ++ tailWord_4176490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4176516 : List Nat := [2, 3, 2, 1, 3, 2, 1, 1, 3, 4]
def baseStart_4176516 : Nat := 118140960795 + 4176516 * 2 ^ 59
def prefixEnd_4176516 : Nat := 4983230072969 + 3 ^ 40 * 4176516 * 2
def baseEnd_4176516 : Nat := 1429706779462324397095039

theorem tailTrace_4176516 : CollatzResearch.WordTrace tailWord_4176516 prefixEnd_4176516 1429706779462324397095039 := by
  unfold tailWord_4176516
  simp only [CollatzResearch.WordTrace]
  refine ⟨76165026468601649494910701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101553368624802199326547601 76165026468601649494910701)
  ·
    refine ⟨28561884925725618560591513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76165026468601649494910701 28561884925725618560591513)
    ·
      refine ⟨21421413694294213920443635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28561884925725618560591513 21421413694294213920443635)
      ·
        refine ⟨32132120541441320880665453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21421413694294213920443635 32132120541441320880665453)
        ·
          refine ⟨12049545203040495330249545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32132120541441320880665453 12049545203040495330249545)
          ·
            refine ⟨9037158902280371497687159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12049545203040495330249545 9037158902280371497687159)
            ·
              refine ⟨13555738353420557246530739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9037158902280371497687159 13555738353420557246530739)
              ·
                refine ⟨20333607530130835869796109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13555738353420557246530739 20333607530130835869796109)
                ·
                  refine ⟨7625102823799063451173541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20333607530130835869796109 7625102823799063451173541)
                  ·
                    refine ⟨1429706779462324397095039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7625102823799063451173541 1429706779462324397095039)
                    ·
                      rfl

theorem cell22_4176516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 1, 1, 3, 4].length) (baseStart_4176516 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4176516 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4176516 prefixEnd_4176516 := by exact prefixLift 4176516
  have htrace : WordTrace (prefixWord ++ tailWord_4176516) baseStart_4176516 baseEnd_4176516 := by
    simpa [prefixWord, tailWord_4176516, baseEnd_4176516] using wordTrace_append hprefix tailTrace_4176516
  have hstable : (prefixWord ++ tailWord_4176516).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4176516).length < 2 ^ (prefixWord ++ tailWord_4176516).sum := by decide
  have hdescent : baseEnd_4176516 < baseStart_4176516 := by decide
  rcases family_descends (prefixWord ++ tailWord_4176516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4176559 : List Nat := [1, 1, 2, 1, 2, 5, 3, 7]
def baseStart_4176559 : Nat := 118140960795 + 4176559 * 2 ^ 59
def prefixEnd_4176559 : Nat := 4983230072969 + 3 ^ 40 * 4176559 * 2
def baseEnd_4176559 : Nat := 158857944360120735363323

theorem tailTrace_4176559 : CollatzResearch.WordTrace tailWord_4176559 prefixEnd_4176559 158857944360120735363323 := by
  unfold tailWord_4176559
  simp only [CollatzResearch.WordTrace]
  refine ⟨152331621276047517333636731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101554414184031678222424487 152331621276047517333636731)
  ·
    refine ⟨228497431914071276000455097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152331621276047517333636731 228497431914071276000455097)
    ·
      refine ⟨171373073935553457000341323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 228497431914071276000455097 171373073935553457000341323)
      ·
        refine ⟨257059610903330185500511985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171373073935553457000341323 257059610903330185500511985)
        ·
          refine ⟨192794708177497639125383989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 257059610903330185500511985 192794708177497639125383989)
          ·
            refine ⟨18074503891640403668004749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 192794708177497639125383989 18074503891640403668004749)
            ·
              refine ⟨6777938959365151375501781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18074503891640403668004749 6777938959365151375501781)
              ·
                refine ⟨158857944360120735363323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6777938959365151375501781 158857944360120735363323)
                ·
                  rfl

theorem cell22_4176559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 3, 7].length) (baseStart_4176559 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4176559 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4176559 prefixEnd_4176559 := by exact prefixLift 4176559
  have htrace : WordTrace (prefixWord ++ tailWord_4176559) baseStart_4176559 baseEnd_4176559 := by
    simpa [prefixWord, tailWord_4176559, baseEnd_4176559] using wordTrace_append hprefix tailTrace_4176559
  have hstable : (prefixWord ++ tailWord_4176559).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4176559).length < 2 ^ (prefixWord ++ tailWord_4176559).sum := by decide
  have hdescent : baseEnd_4176559 < baseStart_4176559 := by decide
  rcases family_descends (prefixWord ++ tailWord_4176559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4176576 : List Nat := [2, 1, 1, 2, 4, 3, 3, 6]
def baseStart_4176576 : Nat := 118140960795 + 4176576 * 2 ^ 59
def prefixEnd_4176576 : Nat := 4983230072969 + 3 ^ 40 * 4176576 * 2
def baseEnd_4176576 : Nat := 158858590965389360066095

theorem tailTrace_4176576 : CollatzResearch.WordTrace tailWord_4176576 prefixEnd_4176576 158858590965389360066095 := by
  unfold tailWord_4176576
  simp only [CollatzResearch.WordTrace]
  refine ⟨76166120658492964618502791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101554827544657286158003721 76166120658492964618502791)
  ·
    refine ⟨114249180987739446927754187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76166120658492964618502791 114249180987739446927754187)
    ·
      refine ⟨171373771481609170391631281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114249180987739446927754187 171373771481609170391631281)
      ·
        refine ⟨128530328611206877793723461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171373771481609170391631281 128530328611206877793723461)
        ·
          refine ⟨24099436614601289586323149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 128530328611206877793723461 24099436614601289586323149)
          ·
            refine ⟨9037288730475483594871181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24099436614601289586323149 9037288730475483594871181)
            ·
              refine ⟨3388983273928306348076693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9037288730475483594871181 3388983273928306348076693)
              ·
                refine ⟨158858590965389360066095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3388983273928306348076693 158858590965389360066095)
                ·
                  rfl

theorem cell22_4176576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 3, 6].length) (baseStart_4176576 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4176576 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4176576 prefixEnd_4176576 := by exact prefixLift 4176576
  have htrace : WordTrace (prefixWord ++ tailWord_4176576) baseStart_4176576 baseEnd_4176576 := by
    simpa [prefixWord, tailWord_4176576, baseEnd_4176576] using wordTrace_append hprefix tailTrace_4176576
  have hstable : (prefixWord ++ tailWord_4176576).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4176576).length < 2 ^ (prefixWord ++ tailWord_4176576).sum := by decide
  have hdescent : baseEnd_4176576 < baseStart_4176576 := by decide
  rcases family_descends (prefixWord ++ tailWord_4176576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4176597 : List Nat := [1, 3, 2, 5, 1, 2, 1, 2, 2, 3]
def baseStart_4176597 : Nat := 118140960795 + 4176597 * 2 ^ 59
def prefixEnd_4176597 : Nat := 4983230072969 + 3 ^ 40 * 4176597 * 2
def baseEnd_4176597 : Nat := 1429734507417667185819791

theorem tailTrace_4176597 : CollatzResearch.WordTrace tailWord_4176597 prefixEnd_4176597 1429734507417667185819791 := by
  unfold tailWord_4176597
  simp only [CollatzResearch.WordTrace]
  refine ⟨152333007249909849823520045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101555338166606566549013363 152333007249909849823520045)
  ·
    refine ⟨57124877718716193683820017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152333007249909849823520045 57124877718716193683820017)
    ·
      refine ⟨42843658289037145262865013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57124877718716193683820017 42843658289037145262865013)
      ·
        refine ⟨4016592964597232368393595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 42843658289037145262865013 4016592964597232368393595)
        ·
          refine ⟨6024889446895848552590393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4016592964597232368393595 6024889446895848552590393)
          ·
            refine ⟨4518667085171886414442795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6024889446895848552590393 4518667085171886414442795)
            ·
              refine ⟨6778000627757829621664193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4518667085171886414442795 6778000627757829621664193)
              ·
                refine ⟨5083500470818372216248145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6778000627757829621664193 5083500470818372216248145)
                ·
                  refine ⟨3812625353113779162186109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5083500470818372216248145 3812625353113779162186109)
                  ·
                    refine ⟨1429734507417667185819791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3812625353113779162186109 1429734507417667185819791)
                    ·
                      rfl

theorem cell22_4176597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 2, 1, 2, 2, 3].length) (baseStart_4176597 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4176597 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4176597 prefixEnd_4176597 := by exact prefixLift 4176597
  have htrace : WordTrace (prefixWord ++ tailWord_4176597) baseStart_4176597 baseEnd_4176597 := by
    simpa [prefixWord, tailWord_4176597, baseEnd_4176597] using wordTrace_append hprefix tailTrace_4176597
  have hstable : (prefixWord ++ tailWord_4176597).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4176597).length < 2 ^ (prefixWord ++ tailWord_4176597).sum := by decide
  have hdescent : baseEnd_4176597 < baseStart_4176597 := by decide
  rcases family_descends (prefixWord ++ tailWord_4176597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4176642 : List Nat := [3, 4, 1, 1, 1, 2, 3, 3, 1, 3]
def baseStart_4176642 : Nat := 118140960795 + 4176642 * 2 ^ 59
def prefixEnd_4176642 : Nat := 4983230072969 + 3 ^ 40 * 4176642 * 2
def baseEnd_4176642 : Nat := 1429749911837302068444653

theorem tailTrace_4176642 : CollatzResearch.WordTrace tailWord_4176642 prefixEnd_4176642 1429749911837302068444653 := by
  unfold tailWord_4176642
  simp only [CollatzResearch.WordTrace]
  refine ⟨38083662133686705627227045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101556432356497881672605453 38083662133686705627227045)
  ·
    refine ⟨7140686650066257305105071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38083662133686705627227045 7140686650066257305105071)
    ·
      refine ⟨10711029975099385957657607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7140686650066257305105071 10711029975099385957657607)
      ·
        refine ⟨16066544962649078936486411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10711029975099385957657607 16066544962649078936486411)
        ·
          refine ⟨24099817443973618404729617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16066544962649078936486411 24099817443973618404729617)
          ·
            refine ⟨18074863082980213803547213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24099817443973618404729617 18074863082980213803547213)
            ·
              refine ⟨6778073656117580176330205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18074863082980213803547213 6778073656117580176330205)
              ·
                refine ⟨2541777621044092566123827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6778073656117580176330205 2541777621044092566123827)
                ·
                  refine ⟨3812666431566138849185741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2541777621044092566123827 3812666431566138849185741)
                  ·
                    refine ⟨1429749911837302068444653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3812666431566138849185741 1429749911837302068444653)
                    ·
                      rfl

theorem cell22_4176642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 3, 3, 1, 3].length) (baseStart_4176642 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4176642 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4176642 prefixEnd_4176642 := by exact prefixLift 4176642
  have htrace : WordTrace (prefixWord ++ tailWord_4176642) baseStart_4176642 baseEnd_4176642 := by
    simpa [prefixWord, tailWord_4176642, baseEnd_4176642] using wordTrace_append hprefix tailTrace_4176642
  have hstable : (prefixWord ++ tailWord_4176642).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4176642).length < 2 ^ (prefixWord ++ tailWord_4176642).sum := by decide
  have hdescent : baseEnd_4176642 < baseStart_4176642 := by decide
  rcases family_descends (prefixWord ++ tailWord_4176642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4176649 : List Nat := [1, 2, 1, 1, 3, 2, 2, 2, 8]
def baseStart_4176649 : Nat := 118140960795 + 4176649 * 2 ^ 59
def prefixEnd_4176649 : Nat := 4983230072969 + 3 ^ 40 * 4176649 * 2
def baseEnd_4176649 : Nat := 476584102693452127839877

theorem tailTrace_4176649 : CollatzResearch.WordTrace tailWord_4176649 prefixEnd_4176649 476584102693452127839877 := by
  unfold tailWord_4176649
  simp only [CollatzResearch.WordTrace]
  refine ⟨152334903845721462704413001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101556602563814308469608667 152334903845721462704413001)
  ·
    refine ⟨114251177884291097028309751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152334903845721462704413001 114251177884291097028309751)
    ·
      refine ⟨171376766826436645542464627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114251177884291097028309751 171376766826436645542464627)
      ·
        refine ⟨257065150239654968313696941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171376766826436645542464627 257065150239654968313696941)
        ·
          refine ⟨96399431339870613117636353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 257065150239654968313696941 96399431339870613117636353)
          ·
            refine ⟨72299573504902959838227265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96399431339870613117636353 72299573504902959838227265)
            ·
              refine ⟨54224680128677219878670449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72299573504902959838227265 54224680128677219878670449)
              ·
                refine ⟨40668510096507914909002837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54224680128677219878670449 40668510096507914909002837)
                ·
                  refine ⟨476584102693452127839877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 40668510096507914909002837 476584102693452127839877)
                  ·
                    rfl

theorem cell22_4176649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 2, 8].length) (baseStart_4176649 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4176649 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4176649 prefixEnd_4176649 := by exact prefixLift 4176649
  have htrace : WordTrace (prefixWord ++ tailWord_4176649) baseStart_4176649 baseEnd_4176649 := by
    simpa [prefixWord, tailWord_4176649, baseEnd_4176649] using wordTrace_append hprefix tailTrace_4176649
  have hstable : (prefixWord ++ tailWord_4176649).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4176649).length < 2 ^ (prefixWord ++ tailWord_4176649).sum := by decide
  have hdescent : baseEnd_4176649 < baseStart_4176649 := by decide
  rcases family_descends (prefixWord ++ tailWord_4176649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4176698 : List Nat := [3, 1, 1, 1, 6, 1, 1, 2, 1, 5]
def baseStart_4176698 : Nat := 118140960795 + 4176698 * 2 ^ 59
def prefixEnd_4176698 : Nat := 4983230072969 + 3 ^ 40 * 4176698 * 2
def baseEnd_4176698 : Nat := 1429769081781736589044481

theorem tailTrace_4176698 : CollatzResearch.WordTrace tailWord_4176698 prefixEnd_4176698 1429769081781736589044481 := by
  unfold tailWord_4176698
  simp only [CollatzResearch.WordTrace]
  refine ⟨38084172755635986018236687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101557794015029296048631165 38084172755635986018236687)
  ·
    refine ⟨57126259133453979027355031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38084172755635986018236687 57126259133453979027355031)
    ·
      refine ⟨85689388700180968541032547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57126259133453979027355031 85689388700180968541032547)
      ·
        refine ⟨128534083050271452811548821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85689388700180968541032547 128534083050271452811548821)
        ·
          refine ⟨6025035142981474350541351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 128534083050271452811548821 6025035142981474350541351)
          ·
            refine ⟨9037552714472211525812027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6025035142981474350541351 9037552714472211525812027)
            ·
              refine ⟨13556329071708317288718041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9037552714472211525812027 13556329071708317288718041)
              ·
                refine ⟨10167246803781237966538531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13556329071708317288718041 10167246803781237966538531)
                ·
                  refine ⟨15250870205671856949807797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10167246803781237966538531 15250870205671856949807797)
                  ·
                    refine ⟨1429769081781736589044481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15250870205671856949807797 1429769081781736589044481)
                    ·
                      rfl

theorem cell22_4176698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 1, 2, 1, 5].length) (baseStart_4176698 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4176698 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4176698 prefixEnd_4176698 := by exact prefixLift 4176698
  have htrace : WordTrace (prefixWord ++ tailWord_4176698) baseStart_4176698 baseEnd_4176698 := by
    simpa [prefixWord, tailWord_4176698, baseEnd_4176698] using wordTrace_append hprefix tailTrace_4176698
  have hstable : (prefixWord ++ tailWord_4176698).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4176698).length < 2 ^ (prefixWord ++ tailWord_4176698).sum := by decide
  have hdescent : baseEnd_4176698 < baseStart_4176698 := by decide
  rcases family_descends (prefixWord ++ tailWord_4176698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4176702 : List Nat := [4, 2, 1, 2, 3, 1, 3, 1, 1, 4]
def baseStart_4176702 : Nat := 118140960795 + 4176702 * 2 ^ 59
def prefixEnd_4176702 : Nat := 4983230072969 + 3 ^ 40 * 4176702 * 2
def baseEnd_4176702 : Nat := 1429770451063481911944469

theorem tailTrace_4176702 : CollatzResearch.WordTrace tailWord_4176702 prefixEnd_4176702 1429770451063481911944469 := by
  unfold tailWord_4176702
  simp only [CollatzResearch.WordTrace]
  refine ⟨19042104614316181594511545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 101557891276352968504061573 19042104614316181594511545)
  ·
    refine ⟨14281578460737136195883659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19042104614316181594511545 14281578460737136195883659)
    ·
      refine ⟨21422367691105704293825489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14281578460737136195883659 21422367691105704293825489)
      ·
        refine ⟨16066775768329278220369117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21422367691105704293825489 16066775768329278220369117)
        ·
          refine ⟨6025040913123479332638419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16066775768329278220369117 6025040913123479332638419)
          ·
            refine ⟨9037561369685218998957629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6025040913123479332638419 9037561369685218998957629)
            ·
              refine ⟨3389085513631957124609111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9037561369685218998957629 3389085513631957124609111)
              ·
                refine ⟨5083628270447935686913667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3389085513631957124609111 5083628270447935686913667)
                ·
                  refine ⟨7625442405671903530370501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5083628270447935686913667 7625442405671903530370501)
                  ·
                    refine ⟨1429770451063481911944469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7625442405671903530370501 1429770451063481911944469)
                    ·
                      rfl

theorem cell22_4176702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 3, 1, 1, 4].length) (baseStart_4176702 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4176702 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4176702 prefixEnd_4176702 := by exact prefixLift 4176702
  have htrace : WordTrace (prefixWord ++ tailWord_4176702) baseStart_4176702 baseEnd_4176702 := by
    simpa [prefixWord, tailWord_4176702, baseEnd_4176702] using wordTrace_append hprefix tailTrace_4176702
  have hstable : (prefixWord ++ tailWord_4176702).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4176702).length < 2 ^ (prefixWord ++ tailWord_4176702).sum := by decide
  have hdescent : baseEnd_4176702 < baseStart_4176702 := by decide
  rcases family_descends (prefixWord ++ tailWord_4176702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4176717 : List Nat := [1, 6, 1, 2, 2, 1, 1, 4, 4]
def baseStart_4176717 : Nat := 118140960795 + 4176717 * 2 ^ 59
def prefixEnd_4176717 : Nat := 4983230072969 + 3 ^ 40 * 4176717 * 2
def baseEnd_4176717 : Nat := 476591861956675624273141

theorem tailTrace_4176717 : CollatzResearch.WordTrace tailWord_4176717 prefixEnd_4176717 476591861956675624273141 := by
  unfold tailWord_4176717
  simp only [CollatzResearch.WordTrace]
  refine ⟨152337384009475110317888405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101558256006316740211925603 152337384009475110317888405)
  ·
    refine ⟨7140814875444145796151019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 152337384009475110317888405 7140814875444145796151019)
    ·
      refine ⟨10711222313166218694226529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7140814875444145796151019 10711222313166218694226529)
      ·
        refine ⟨8033416734874664020669897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10711222313166218694226529 8033416734874664020669897)
        ·
          refine ⟨6025062551155998015502423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8033416734874664020669897 6025062551155998015502423)
          ·
            refine ⟨9037593826733997023253635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6025062551155998015502423 9037593826733997023253635)
            ·
              refine ⟨13556390740100995534880453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9037593826733997023253635 13556390740100995534880453)
              ·
                refine ⟨2541823263768936662790085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13556390740100995534880453 2541823263768936662790085)
                ·
                  refine ⟨476591861956675624273141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2541823263768936662790085 476591861956675624273141)
                  ·
                    rfl

theorem cell22_4176717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 1, 4, 4].length) (baseStart_4176717 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4176717 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4176717 prefixEnd_4176717 := by exact prefixLift 4176717
  have htrace : WordTrace (prefixWord ++ tailWord_4176717) baseStart_4176717 baseEnd_4176717 := by
    simpa [prefixWord, tailWord_4176717, baseEnd_4176717] using wordTrace_append hprefix tailTrace_4176717
  have hstable : (prefixWord ++ tailWord_4176717).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4176717).length < 2 ^ (prefixWord ++ tailWord_4176717).sum := by decide
  have hdescent : baseEnd_4176717 < baseStart_4176717 := by decide
  rcases family_descends (prefixWord ++ tailWord_4176717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4176743 : List Nat := [1, 1, 5, 1, 2, 2, 1, 1, 5, 3]
def baseStart_4176743 : Nat := 118140960795 + 4176743 * 2 ^ 59
def prefixEnd_4176743 : Nat := 4983230072969 + 3 ^ 40 * 4176743 * 2
def baseEnd_4176743 : Nat := 1429784486201371471669343

theorem tailTrace_4176743 : CollatzResearch.WordTrace tailWord_4176743 prefixEnd_4176743 1429784486201371471669343 := by
  unfold tailWord_4176743
  simp only [CollatzResearch.WordTrace]
  refine ⟨152338332307380916758334883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101558888204920611172223255 152338332307380916758334883)
  ·
    refine ⟨228507498461071375137502325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152338332307380916758334883 228507498461071375137502325)
    ·
      refine ⟨21422577980725441419140843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 228507498461071375137502325 21422577980725441419140843)
      ·
        refine ⟨32133866971088162128711265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21422577980725441419140843 32133866971088162128711265)
        ·
          refine ⟨24100400228316121596533449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32133866971088162128711265 24100400228316121596533449)
          ·
            refine ⟨18075300171237091197400087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24100400228316121596533449 18075300171237091197400087)
            ·
              refine ⟨27112950256855636796100131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18075300171237091197400087 27112950256855636796100131)
              ·
                refine ⟨40669425385283455194150197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27112950256855636796100131 40669425385283455194150197)
                ·
                  refine ⟨3812758629870323924451581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 40669425385283455194150197 3812758629870323924451581)
                  ·
                    refine ⟨1429784486201371471669343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3812758629870323924451581 1429784486201371471669343)
                    ·
                      rfl

theorem cell22_4176743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 1, 5, 3].length) (baseStart_4176743 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4176743 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4176743 prefixEnd_4176743 := by exact prefixLift 4176743
  have htrace : WordTrace (prefixWord ++ tailWord_4176743) baseStart_4176743 baseEnd_4176743 := by
    simpa [prefixWord, tailWord_4176743, baseEnd_4176743] using wordTrace_append hprefix tailTrace_4176743
  have hstable : (prefixWord ++ tailWord_4176743).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4176743).length < 2 ^ (prefixWord ++ tailWord_4176743).sum := by decide
  have hdescent : baseEnd_4176743 < baseStart_4176743 := by decide
  rcases family_descends (prefixWord ++ tailWord_4176743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4176766 : List Nat := [4, 2, 3, 1, 3, 1, 1, 2, 2, 3]
def baseStart_4176766 : Nat := 118140960795 + 4176766 * 2 ^ 59
def prefixEnd_4176766 : Nat := 4983230072969 + 3 ^ 40 * 4176766 * 2
def baseEnd_4176766 : Nat := 1429792359571407078344273

theorem tailTrace_4176766 : CollatzResearch.WordTrace tailWord_4176766 prefixEnd_4176766 1429792359571407078344273 := by
  unfold tailWord_4176766
  simp only [CollatzResearch.WordTrace]
  refine ⟨19042396398287198960802769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 101559447457531727790948101 19042396398287198960802769)
  ·
    refine ⟨14281797298715399220602077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19042396398287198960802769 14281797298715399220602077)
    ·
      refine ⟨5355673987018274707725779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14281797298715399220602077 5355673987018274707725779)
      ·
        refine ⟨8033510980527412061588669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5355673987018274707725779 8033510980527412061588669)
        ·
          refine ⟨3012566617697779523095751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8033510980527412061588669 3012566617697779523095751)
          ·
            refine ⟨4518849926546669284643627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3012566617697779523095751 4518849926546669284643627)
            ·
              refine ⟨6778274889820003926965441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4518849926546669284643627 6778274889820003926965441)
              ·
                refine ⟨5083706167365002945224081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6778274889820003926965441 5083706167365002945224081)
                ·
                  refine ⟨3812779625523752208918061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5083706167365002945224081 3812779625523752208918061)
                  ·
                    refine ⟨1429792359571407078344273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3812779625523752208918061 1429792359571407078344273)
                    ·
                      rfl

theorem cell22_4176766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 3, 1, 1, 2, 2, 3].length) (baseStart_4176766 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4176766 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4176766 prefixEnd_4176766 := by exact prefixLift 4176766
  have htrace : WordTrace (prefixWord ++ tailWord_4176766) baseStart_4176766 baseEnd_4176766 := by
    simpa [prefixWord, tailWord_4176766, baseEnd_4176766] using wordTrace_append hprefix tailTrace_4176766
  have hstable : (prefixWord ++ tailWord_4176766).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4176766).length < 2 ^ (prefixWord ++ tailWord_4176766).sum := by decide
  have hdescent : baseEnd_4176766 < baseStart_4176766 := by decide
  rcases family_descends (prefixWord ++ tailWord_4176766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4176771 : List Nat := [1, 1, 1, 3, 4, 1, 1, 1, 4, 5]
def baseStart_4176771 : Nat := 118140960795 + 4176771 * 2 ^ 59
def prefixEnd_4176771 : Nat := 4983230072969 + 3 ^ 40 * 4176771 * 2
def baseEnd_4176771 : Nat := 1429794071173588731969257

theorem tailTrace_4176771 : CollatzResearch.WordTrace tailWord_4176771 prefixEnd_4176771 1429794071173588731969257 := by
  unfold tailWord_4176771
  simp only [CollatzResearch.WordTrace]
  refine ⟨152339353551279477540354167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101559569034186318360236111 152339353551279477540354167)
  ·
    refine ⟨228509030326919216310531251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152339353551279477540354167 228509030326919216310531251)
    ·
      refine ⟨342763545490378824465796877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228509030326919216310531251 342763545490378824465796877)
      ·
        refine ⟨128536329558892059174673829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 342763545490378824465796877 128536329558892059174673829)
        ·
          refine ⟨24100561792292261095251343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 128536329558892059174673829 24100561792292261095251343)
          ·
            refine ⟨36150842688438391642877015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24100561792292261095251343 36150842688438391642877015)
            ·
              refine ⟨54226264032657587464315523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36150842688438391642877015 54226264032657587464315523)
              ·
                refine ⟨81339396048986381196473285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54226264032657587464315523 81339396048986381196473285)
                ·
                  refine ⟨15251136759184946474338741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 81339396048986381196473285 15251136759184946474338741)
                  ·
                    refine ⟨1429794071173588731969257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15251136759184946474338741 1429794071173588731969257)
                    ·
                      rfl

theorem cell22_4176771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 1, 4, 5].length) (baseStart_4176771 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4176771 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4176771 prefixEnd_4176771 := by exact prefixLift 4176771
  have htrace : WordTrace (prefixWord ++ tailWord_4176771) baseStart_4176771 baseEnd_4176771 := by
    simpa [prefixWord, tailWord_4176771, baseEnd_4176771] using wordTrace_append hprefix tailTrace_4176771
  have hstable : (prefixWord ++ tailWord_4176771).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4176771).length < 2 ^ (prefixWord ++ tailWord_4176771).sum := by decide
  have hdescent : baseEnd_4176771 < baseStart_4176771 := by decide
  rcases family_descends (prefixWord ++ tailWord_4176771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4176773 : List Nat := [1, 3, 1, 1, 3, 3, 3, 2, 5]
def baseStart_4176773 : Nat := 118140960795 + 4176773 * 2 ^ 59
def prefixEnd_4176773 : Nat := 4983230072969 + 3 ^ 40 * 4176773 * 2
def baseEnd_4176773 : Nat := 476598251938153797806417

theorem tailTrace_4176773 : CollatzResearch.WordTrace tailWord_4176773 prefixEnd_4176773 476598251938153797806417 := by
  unfold tailWord_4176773
  simp only [CollatzResearch.WordTrace]
  refine ⟨152339426497272231881926973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101559617664848154587951315 152339426497272231881926973)
  ·
    refine ⟨57127284936477086955722615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152339426497272231881926973 57127284936477086955722615)
    ·
      refine ⟨85690927404715630433583923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57127284936477086955722615 85690927404715630433583923)
      ·
        refine ⟨128536391107073445650375885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85690927404715630433583923 128536391107073445650375885)
        ·
          refine ⟨48201146665152542118890957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 128536391107073445650375885 48201146665152542118890957)
          ·
            refine ⟨18075429999432203294584109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48201146665152542118890957 18075429999432203294584109)
            ·
              refine ⟨6778286249787076235469041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18075429999432203294584109 6778286249787076235469041)
              ·
                refine ⟨5083714687340307176601781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6778286249787076235469041 5083714687340307176601781)
                ·
                  refine ⟨476598251938153797806417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5083714687340307176601781 476598251938153797806417)
                  ·
                    rfl

theorem cell22_4176773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 3, 2, 5].length) (baseStart_4176773 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4176773 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4176773 prefixEnd_4176773 := by exact prefixLift 4176773
  have htrace : WordTrace (prefixWord ++ tailWord_4176773) baseStart_4176773 baseEnd_4176773 := by
    simpa [prefixWord, tailWord_4176773, baseEnd_4176773] using wordTrace_append hprefix tailTrace_4176773
  have hstable : (prefixWord ++ tailWord_4176773).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4176773).length < 2 ^ (prefixWord ++ tailWord_4176773).sum := by decide
  have hdescent : baseEnd_4176773 < baseStart_4176773 := by decide
  rcases family_descends (prefixWord ++ tailWord_4176773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4176788 : List Nat := [2, 4, 2, 1, 1, 1, 1, 3, 2, 5]
def baseStart_4176788 : Nat := 118140960795 + 4176788 * 2 ^ 59
def prefixEnd_4176788 : Nat := 4983230072969 + 3 ^ 40 * 4176788 * 2
def baseEnd_4176788 : Nat := 1429799890621006354294205

theorem tailTrace_4176788 : CollatzResearch.WordTrace tailWord_4176788 prefixEnd_4176788 1429799890621006354294205 := by
  unfold tailWord_4176788
  simp only [CollatzResearch.WordTrace]
  refine ⟨76169986796108944721861509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101559982394811926295815345 76169986796108944721861509)
  ·
    refine ⟨14281872524270427135349033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 76169986796108944721861509 14281872524270427135349033)
    ·
      refine ⟨10711404393202820351511775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14281872524270427135349033 10711404393202820351511775)
      ·
        refine ⟨16067106589804230527267663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10711404393202820351511775 16067106589804230527267663)
        ·
          refine ⟨24100659884706345790901495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16067106589804230527267663 24100659884706345790901495)
          ·
            refine ⟨36150989827059518686352243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24100659884706345790901495 36150989827059518686352243)
            ·
              refine ⟨54226484740589278029528365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36150989827059518686352243 54226484740589278029528365)
              ·
                refine ⟨20334931777720979261073137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54226484740589278029528365 20334931777720979261073137)
                ·
                  refine ⟨15251198833290734445804853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20334931777720979261073137 15251198833290734445804853)
                  ·
                    refine ⟨1429799890621006354294205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15251198833290734445804853 1429799890621006354294205)
                    ·
                      rfl

theorem cell22_4176788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 3, 2, 5].length) (baseStart_4176788 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4176788 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4176788 prefixEnd_4176788 := by exact prefixLift 4176788
  have htrace : WordTrace (prefixWord ++ tailWord_4176788) baseStart_4176788 baseEnd_4176788 := by
    simpa [prefixWord, tailWord_4176788, baseEnd_4176788] using wordTrace_append hprefix tailTrace_4176788
  have hstable : (prefixWord ++ tailWord_4176788).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4176788).length < 2 ^ (prefixWord ++ tailWord_4176788).sum := by decide
  have hdescent : baseEnd_4176788 < baseStart_4176788 := by decide
  rcases family_descends (prefixWord ++ tailWord_4176788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4176803 : List Nat := [1, 1, 1, 4, 1, 2, 3, 4, 1, 4]
def baseStart_4176803 : Nat := 118140960795 + 4176803 * 2 ^ 59
def prefixEnd_4176803 : Nat := 4983230072969 + 3 ^ 40 * 4176803 * 2
def baseEnd_4176803 : Nat := 1429805025427551315169159

theorem tailTrace_4176803 : CollatzResearch.WordTrace tailWord_4176803 prefixEnd_4176803 1429805025427551315169159 := by
  unfold tailWord_4176803
  simp only [CollatzResearch.WordTrace]
  refine ⟨152340520687163547005519063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101560347124775698003679375 152340520687163547005519063)
  ·
    refine ⟨228510781030745320508278595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152340520687163547005519063 228510781030745320508278595)
    ·
      refine ⟨342766171546117980762417893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228510781030745320508278595 342766171546117980762417893)
      ·
        refine ⟨64268657164897121392953355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 342766171546117980762417893 64268657164897121392953355)
        ·
          refine ⟨96402985747345682089430033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64268657164897121392953355 96402985747345682089430033)
          ·
            refine ⟨72302239310509261567072525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96402985747345682089430033 72302239310509261567072525)
            ·
              refine ⟨27113339741440973087652197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72302239310509261567072525 27113339741440973087652197)
              ·
                refine ⟨5083751201520182453934787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27113339741440973087652197 5083751201520182453934787)
                ·
                  refine ⟨7625626802280273680902181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5083751201520182453934787 7625626802280273680902181)
                  ·
                    refine ⟨1429805025427551315169159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7625626802280273680902181 1429805025427551315169159)
                    ·
                      rfl

theorem cell22_4176803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 4, 1, 4].length) (baseStart_4176803 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4176803 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4176803 prefixEnd_4176803 := by exact prefixLift 4176803
  have htrace : WordTrace (prefixWord ++ tailWord_4176803) baseStart_4176803 baseEnd_4176803 := by
    simpa [prefixWord, tailWord_4176803, baseEnd_4176803] using wordTrace_append hprefix tailTrace_4176803
  have hstable : (prefixWord ++ tailWord_4176803).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4176803).length < 2 ^ (prefixWord ++ tailWord_4176803).sum := by decide
  have hdescent : baseEnd_4176803 < baseStart_4176803 := by decide
  rcases family_descends (prefixWord ++ tailWord_4176803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4176831 : List Nat := [1, 1, 2, 2, 2, 1, 2, 2, 3, 6]
def baseStart_4176831 : Nat := 118140960795 + 4176831 * 2 ^ 59
def prefixEnd_4176831 : Nat := 4983230072969 + 3 ^ 40 * 4176831 * 2
def baseEnd_4176831 : Nat := 1429814610399768575469073

theorem tailTrace_4176831 : CollatzResearch.WordTrace tailWord_4176831 prefixEnd_4176831 1429814610399768575469073 := by
  unfold tailWord_4176831
  simp only [CollatzResearch.WordTrace]
  refine ⟨152341541931062107787538347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101561027954041405191692231 152341541931062107787538347)
  ·
    refine ⟨228512312896593161681307521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152341541931062107787538347 228512312896593161681307521)
    ·
      refine ⟨171384234672444871260980641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 228512312896593161681307521 171384234672444871260980641)
      ·
        refine ⟨128538176004333653445735481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171384234672444871260980641 128538176004333653445735481)
        ·
          refine ⟨96403632003250240084301611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128538176004333653445735481 96403632003250240084301611)
          ·
            refine ⟨144605448004875360126452417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96403632003250240084301611 144605448004875360126452417)
            ·
              refine ⟨108454086003656520094839313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 144605448004875360126452417 108454086003656520094839313)
              ·
                refine ⟨81340564502742390071129485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 108454086003656520094839313 81340564502742390071129485)
                ·
                  refine ⟨30502711688528396276673557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 81340564502742390071129485 30502711688528396276673557)
                  ·
                    refine ⟨1429814610399768575469073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30502711688528396276673557 1429814610399768575469073)
                    ·
                      rfl

theorem cell22_4176831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 2, 3, 6].length) (baseStart_4176831 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4176831 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4176831 prefixEnd_4176831 := by exact prefixLift 4176831
  have htrace : WordTrace (prefixWord ++ tailWord_4176831) baseStart_4176831 baseEnd_4176831 := by
    simpa [prefixWord, tailWord_4176831, baseEnd_4176831] using wordTrace_append hprefix tailTrace_4176831
  have hstable : (prefixWord ++ tailWord_4176831).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4176831).length < 2 ^ (prefixWord ++ tailWord_4176831).sum := by decide
  have hdescent : baseEnd_4176831 < baseStart_4176831 := by decide
  rcases family_descends (prefixWord ++ tailWord_4176831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4176854 : List Nat := [5, 2, 1, 1, 2, 3, 1, 2, 1, 4]
def baseStart_4176854 : Nat := 118140960795 + 4176854 * 2 ^ 59
def prefixEnd_4176854 : Nat := 4983230072969 + 3 ^ 40 * 4176854 * 2
def baseEnd_4176854 : Nat := 1429822483769804182144003

theorem tailTrace_4176854 : CollatzResearch.WordTrace tailWord_4176854 prefixEnd_4176854 1429822483769804182144003 := by
  unfold tailWord_4176854
  simp only [CollatzResearch.WordTrace]
  refine ⟨9521398800623673919726601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 101561587206652521810417077 9521398800623673919726601)
  ·
    refine ⟨7141049100467755439794951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9521398800623673919726601 7141049100467755439794951)
    ·
      refine ⟨10711573650701633159692427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7141049100467755439794951 10711573650701633159692427)
      ·
        refine ⟨16067360476052449739538641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10711573650701633159692427 16067360476052449739538641)
        ·
          refine ⟨12050520357039337304653981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16067360476052449739538641 12050520357039337304653981)
          ·
            refine ⟨4518945133889751489245243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12050520357039337304653981 4518945133889751489245243)
            ·
              refine ⟨6778417700834627233867865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4518945133889751489245243 6778417700834627233867865)
              ·
                refine ⟨5083813275625970425400899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6778417700834627233867865 5083813275625970425400899)
                ·
                  refine ⟨7625719913438955638101349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5083813275625970425400899 7625719913438955638101349)
                  ·
                    refine ⟨1429822483769804182144003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7625719913438955638101349 1429822483769804182144003)
                    ·
                      rfl

theorem cell22_4176854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 3, 1, 2, 1, 4].length) (baseStart_4176854 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4176854 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4176854 prefixEnd_4176854 := by exact prefixLift 4176854
  have htrace : WordTrace (prefixWord ++ tailWord_4176854) baseStart_4176854 baseEnd_4176854 := by
    simpa [prefixWord, tailWord_4176854, baseEnd_4176854] using wordTrace_append hprefix tailTrace_4176854
  have hstable : (prefixWord ++ tailWord_4176854).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4176854).length < 2 ^ (prefixWord ++ tailWord_4176854).sum := by decide
  have hdescent : baseEnd_4176854 < baseStart_4176854 := by decide
  rcases family_descends (prefixWord ++ tailWord_4176854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4176929 : List Nat := [1, 2, 3, 2, 3, 2, 2, 3, 1, 3]
def baseStart_4176929 : Nat := 118140960795 + 4176929 * 2 ^ 59
def prefixEnd_4176929 : Nat := 4983230072969 + 3 ^ 40 * 4176929 * 2
def baseEnd_4176929 : Nat := 1429848157802528986518773

theorem tailTrace_4176929 : CollatzResearch.WordTrace tailWord_4176929 prefixEnd_4176929 1429848157802528986518773 := by
  unfold tailWord_4176929
  simp only [CollatzResearch.WordTrace]
  refine ⟨152345116284707070524605841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101563410856471380349737227 152345116284707070524605841)
  ·
    refine ⟨114258837213530302893454381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152345116284707070524605841 114258837213530302893454381)
    ·
      refine ⟨42847063955073863585045393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114258837213530302893454381 42847063955073863585045393)
      ·
        refine ⟨32135297966305397688784045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42847063955073863585045393 32135297966305397688784045)
        ·
          refine ⟨12050736737364524133294017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32135297966305397688784045 12050736737364524133294017)
          ·
            refine ⟨9038052553023393099970513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12050736737364524133294017 9038052553023393099970513)
            ·
              refine ⟨6778539414767544824977885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9038052553023393099970513 6778539414767544824977885)
              ·
                refine ⟨2541952280537829309366707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6778539414767544824977885 2541952280537829309366707)
                ·
                  refine ⟨3812928420806743964050061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2541952280537829309366707 3812928420806743964050061)
                  ·
                    refine ⟨1429848157802528986518773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3812928420806743964050061 1429848157802528986518773)
                    ·
                      rfl

theorem cell22_4176929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 2, 3, 1, 3].length) (baseStart_4176929 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4176929 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4176929 prefixEnd_4176929 := by exact prefixLift 4176929
  have htrace : WordTrace (prefixWord ++ tailWord_4176929) baseStart_4176929 baseEnd_4176929 := by
    simpa [prefixWord, tailWord_4176929, baseEnd_4176929] using wordTrace_append hprefix tailTrace_4176929
  have hstable : (prefixWord ++ tailWord_4176929).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4176929).length < 2 ^ (prefixWord ++ tailWord_4176929).sum := by decide
  have hdescent : baseEnd_4176929 < baseStart_4176929 := by decide
  rcases family_descends (prefixWord ++ tailWord_4176929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4177002 : List Nat := [3, 1, 3, 2, 2, 1, 2, 1, 4, 3]
def baseStart_4177002 : Nat := 118140960795 + 4177002 * 2 ^ 59
def prefixEnd_4177002 : Nat := 4983230072969 + 3 ^ 40 * 4177002 * 2
def baseEnd_4177002 : Nat := 1429873147194381129443549

theorem tailTrace_4177002 : CollatzResearch.WordTrace tailWord_4177002 prefixEnd_4177002 1429873147194381129443549 := by
  unfold tailWord_4177002
  simp only [CollatzResearch.WordTrace]
  refine ⟨38086944703360650998003315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101565185875628402661342173 38086944703360650998003315)
  ·
    refine ⟨57130417055040976497004973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38086944703360650998003315 57130417055040976497004973)
    ·
      refine ⟨21423906395640366186376865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57130417055040976497004973 21423906395640366186376865)
      ·
        refine ⟨16067929796730274639782649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21423906395640366186376865 16067929796730274639782649)
        ·
          refine ⟨12050947347547705979836987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16067929796730274639782649 12050947347547705979836987)
          ·
            refine ⟨18076421021321558969755481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12050947347547705979836987 18076421021321558969755481)
            ·
              refine ⟨13557315765991169227316611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18076421021321558969755481 13557315765991169227316611)
              ·
                refine ⟨20335973648986753840974917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13557315765991169227316611 20335973648986753840974917)
                ·
                  refine ⟨3812995059185016345182797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20335973648986753840974917 3812995059185016345182797)
                  ·
                    refine ⟨1429873147194381129443549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3812995059185016345182797 1429873147194381129443549)
                    ·
                      rfl

theorem cell22_4177002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 2, 1, 4, 3].length) (baseStart_4177002 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4177002 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4177002 prefixEnd_4177002 := by exact prefixLift 4177002
  have htrace : WordTrace (prefixWord ++ tailWord_4177002) baseStart_4177002 baseEnd_4177002 := by
    simpa [prefixWord, tailWord_4177002, baseEnd_4177002] using wordTrace_append hprefix tailTrace_4177002
  have hstable : (prefixWord ++ tailWord_4177002).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4177002).length < 2 ^ (prefixWord ++ tailWord_4177002).sum := by decide
  have hdescent : baseEnd_4177002 < baseStart_4177002 := by decide
  rcases family_descends (prefixWord ++ tailWord_4177002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4177043 : List Nat := [1, 1, 1, 2, 1, 2, 4, 1, 9]
def baseStart_4177043 : Nat := 118140960795 + 4177043 * 2 ^ 59
def prefixEnd_4177043 : Nat := 4983230072969 + 3 ^ 40 * 4177043 * 2
def baseEnd_4177043 : Nat := 476629060777423563056141

theorem tailTrace_4177043 : CollatzResearch.WordTrace tailWord_4177043 prefixEnd_4177043 476629060777423563056141 := by
  unfold tailWord_4177043
  simp only [CollatzResearch.WordTrace]
  refine ⟨152349274206294067994255783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101566182804196045329503855 152349274206294067994255783)
  ·
    refine ⟨228523911309441101991383675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152349274206294067994255783 228523911309441101991383675)
    ·
      refine ⟨342785866964161652987075513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228523911309441101991383675 342785866964161652987075513)
      ·
        refine ⟨257089400223121239740306635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 342785866964161652987075513 257089400223121239740306635)
        ·
          refine ⟨385634100334681859610459953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 257089400223121239740306635 385634100334681859610459953)
          ·
            refine ⟨289225575251011394707844965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 385634100334681859610459953 289225575251011394707844965)
            ·
              refine ⟨54229795359564636507720931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 289225575251011394707844965 54229795359564636507720931)
              ·
                refine ⟨81344693039346954761581397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54229795359564636507720931 81344693039346954761581397)
                ·
                  refine ⟨476629060777423563056141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 81344693039346954761581397 476629060777423563056141)
                  ·
                    rfl

theorem cell22_4177043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 1, 9].length) (baseStart_4177043 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4177043 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4177043 prefixEnd_4177043 := by exact prefixLift 4177043
  have htrace : WordTrace (prefixWord ++ tailWord_4177043) baseStart_4177043 baseEnd_4177043 := by
    simpa [prefixWord, tailWord_4177043, baseEnd_4177043] using wordTrace_append hprefix tailTrace_4177043
  have hstable : (prefixWord ++ tailWord_4177043).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4177043).length < 2 ^ (prefixWord ++ tailWord_4177043).sum := by decide
  have hdescent : baseEnd_4177043 < baseStart_4177043 := by decide
  rcases family_descends (prefixWord ++ tailWord_4177043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4177156 : List Nat := [2, 3, 2, 2, 2, 3, 1, 3, 4]
def baseStart_4177156 : Nat := 118140960795 + 4177156 * 2 ^ 59
def prefixEnd_4177156 : Nat := 4983230072969 + 3 ^ 40 * 4177156 * 2
def baseEnd_4177156 : Nat := 476641954847192020364359

theorem tailTrace_4177156 : CollatzResearch.WordTrace tailWord_4177156 prefixEnd_4177156 476641954847192020364359 := by
  unfold tailWord_4177156
  simp only [CollatzResearch.WordTrace]
  refine ⟨76176697827442344146559661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101568930436589792195412881 76176697827442344146559661)
  ·
    refine ⟨28566261685290879054959873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76176697827442344146559661 28566261685290879054959873)
    ·
      refine ⟨21424696263968159291219905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28566261685290879054959873 21424696263968159291219905)
      ·
        refine ⟨16068522197976119468414929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21424696263968159291219905 16068522197976119468414929)
        ·
          refine ⟨12051391648482089601311197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16068522197976119468414929 12051391648482089601311197)
          ·
            refine ⟨4519271868180783600491699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12051391648482089601311197 4519271868180783600491699)
            ·
              refine ⟨6778907802271175400737549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4519271868180783600491699 6778907802271175400737549)
              ·
                refine ⟨2542090425851690775276581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6778907802271175400737549 2542090425851690775276581)
                ·
                  refine ⟨476641954847192020364359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2542090425851690775276581 476641954847192020364359)
                  ·
                    rfl

theorem cell22_4177156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 3, 1, 3, 4].length) (baseStart_4177156 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4177156 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4177156 prefixEnd_4177156 := by exact prefixLift 4177156
  have htrace : WordTrace (prefixWord ++ tailWord_4177156) baseStart_4177156 baseEnd_4177156 := by
    simpa [prefixWord, tailWord_4177156, baseEnd_4177156] using wordTrace_append hprefix tailTrace_4177156
  have hstable : (prefixWord ++ tailWord_4177156).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4177156).length < 2 ^ (prefixWord ++ tailWord_4177156).sum := by decide
  have hdescent : baseEnd_4177156 < baseStart_4177156 := by decide
  rcases family_descends (prefixWord ++ tailWord_4177156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4177242 : List Nat := [3, 1, 1, 2, 1, 2, 3, 2, 3, 4]
def baseStart_4177242 : Nat := 118140960795 + 4177242 * 2 ^ 59
def prefixEnd_4177242 : Nat := 4983230072969 + 3 ^ 40 * 4177242 * 2
def baseEnd_4177242 : Nat := 1429955304099100503442813

theorem tailTrace_4177242 : CollatzResearch.WordTrace tailWord_4177242 prefixEnd_4177242 1429955304099100503442813 := by
  unfold tailWord_4177242
  simp only [CollatzResearch.WordTrace]
  refine ⟨38089133083143281245187495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101571021555048749987166653 38089133083143281245187495)
  ·
    refine ⟨57133699624714921867781243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38089133083143281245187495 57133699624714921867781243)
    ·
      refine ⟨85700549437072382801671865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57133699624714921867781243 85700549437072382801671865)
      ·
        refine ⟨64275412077804287101253899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85700549437072382801671865 64275412077804287101253899)
        ·
          refine ⟨96413118116706430651880849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64275412077804287101253899 96413118116706430651880849)
          ·
            refine ⟨72309838587529822988910637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96413118116706430651880849 72309838587529822988910637)
            ·
              refine ⟨27116189470323683620841489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72309838587529822988910637 27116189470323683620841489)
              ·
                refine ⟨20337142102742762715631117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27116189470323683620841489 20337142102742762715631117)
                ·
                  refine ⟨7626428288528536018361669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20337142102742762715631117 7626428288528536018361669)
                  ·
                    refine ⟨1429955304099100503442813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7626428288528536018361669 1429955304099100503442813)
                    ·
                      rfl

theorem cell22_4177242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 2, 3, 4].length) (baseStart_4177242 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4177242 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4177242 prefixEnd_4177242 := by exact prefixLift 4177242
  have htrace : WordTrace (prefixWord ++ tailWord_4177242) baseStart_4177242 baseEnd_4177242 := by
    simpa [prefixWord, tailWord_4177242, baseEnd_4177242] using wordTrace_append hprefix tailTrace_4177242
  have hstable : (prefixWord ++ tailWord_4177242).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4177242).length < 2 ^ (prefixWord ++ tailWord_4177242).sum := by decide
  have hdescent : baseEnd_4177242 < baseStart_4177242 := by decide
  rcases family_descends (prefixWord ++ tailWord_4177242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4177347 : List Nat := [1, 1, 1, 3, 1, 1, 6, 1, 7]
def baseStart_4177347 : Nat := 118140960795 + 4177347 * 2 ^ 59
def prefixEnd_4177347 : Nat := 4983230072969 + 3 ^ 40 * 4177347 * 2
def baseEnd_4177347 : Nat := 476663749248305076522497

theorem tailTrace_4177347 : CollatzResearch.WordTrace tailWord_4177347 prefixEnd_4177347 476663749248305076522497 := by
  unfold tailWord_4177347
  simp only [CollatzResearch.WordTrace]
  refine ⟨152360361997192727913322295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101573574664795151942214863 152360361997192727913322295)
  ·
    refine ⟨228540542995789091869983443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152360361997192727913322295 228540542995789091869983443)
    ·
      refine ⟨342810814493683637804975165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228540542995789091869983443 342810814493683637804975165)
      ·
        refine ⟨128554055435131364176865687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 342810814493683637804975165 128554055435131364176865687)
        ·
          refine ⟨192831083152697046265298531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128554055435131364176865687 192831083152697046265298531)
          ·
            refine ⟨289246624729045569397947797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192831083152697046265298531 289246624729045569397947797)
            ·
              refine ⟨13558435534174011065528803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 289246624729045569397947797 13558435534174011065528803)
              ·
                refine ⟨20337653301261016598293205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13558435534174011065528803 20337653301261016598293205)
                ·
                  refine ⟨476663749248305076522497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20337653301261016598293205 476663749248305076522497)
                  ·
                    rfl

theorem cell22_4177347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 6, 1, 7].length) (baseStart_4177347 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4177347 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4177347 prefixEnd_4177347 := by exact prefixLift 4177347
  have htrace : WordTrace (prefixWord ++ tailWord_4177347) baseStart_4177347 baseEnd_4177347 := by
    simpa [prefixWord, tailWord_4177347, baseEnd_4177347] using wordTrace_append hprefix tailTrace_4177347
  have hstable : (prefixWord ++ tailWord_4177347).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4177347).length < 2 ^ (prefixWord ++ tailWord_4177347).sum := by decide
  have hdescent : baseEnd_4177347 < baseStart_4177347 := by decide
  rcases family_descends (prefixWord ++ tailWord_4177347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4177443 : List Nat := [1, 1, 1, 4, 5, 1, 2, 3, 4]
def baseStart_4177443 : Nat := 118140960795 + 4177443 * 2 ^ 59
def prefixEnd_4177443 : Nat := 4983230072969 + 3 ^ 40 * 4177443 * 2
def baseEnd_4177443 : Nat := 476674703502267659722399

theorem tailTrace_4177443 : CollatzResearch.WordTrace tailWord_4177443 prefixEnd_4177443 476674703502267659722399 := by
  unfold tailWord_4177443
  simp only [CollatzResearch.WordTrace]
  refine ⟨152363863404844936308816983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101575908936563290872544655 152363863404844936308816983)
  ·
    refine ⟨228545795107267404463225475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152363863404844936308816983 228545795107267404463225475)
    ·
      refine ⟨342818692660901106694838213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228545795107267404463225475 342818692660901106694838213)
      ·
        refine ⟨64278504873918957505282165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 342818692660901106694838213 64278504873918957505282165)
        ·
          refine ⟨6026109831929902266120203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 64278504873918957505282165 6026109831929902266120203)
          ·
            refine ⟨9039164747894853399180305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6026109831929902266120203 9039164747894853399180305)
            ·
              refine ⟨6779373560921140049385229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9039164747894853399180305 6779373560921140049385229)
              ·
                refine ⟨2542265085345427518519461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6779373560921140049385229 2542265085345427518519461)
                ·
                  refine ⟨476674703502267659722399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2542265085345427518519461 476674703502267659722399)
                  ·
                    rfl

theorem cell22_4177443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 2, 3, 4].length) (baseStart_4177443 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4177443 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4177443 prefixEnd_4177443 := by exact prefixLift 4177443
  have htrace : WordTrace (prefixWord ++ tailWord_4177443) baseStart_4177443 baseEnd_4177443 := by
    simpa [prefixWord, tailWord_4177443, baseEnd_4177443] using wordTrace_append hprefix tailTrace_4177443
  have hstable : (prefixWord ++ tailWord_4177443).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4177443).length < 2 ^ (prefixWord ++ tailWord_4177443).sum := by decide
  have hdescent : baseEnd_4177443 < baseStart_4177443 := by decide
  rcases family_descends (prefixWord ++ tailWord_4177443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4177494 : List Nat := [5, 2, 2, 2, 1, 2, 1, 3, 4]
def baseStart_4177494 : Nat := 118140960795 + 4177494 * 2 ^ 59
def prefixEnd_4177494 : Nat := 4983230072969 + 3 ^ 40 * 4177494 * 2
def baseEnd_4177494 : Nat := 476680522949685282047347

theorem tailTrace_4177494 : CollatzResearch.WordTrace tailWord_4177494 prefixEnd_4177494 476680522949685282047347 := by
  unfold tailWord_4177494
  simp only [CollatzResearch.WordTrace]
  refine ⟨9522857720478760751182721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 101577149018440114679282357 9522857720478760751182721)
  ·
    refine ⟨7142143290359070563387041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9522857720478760751182721 7142143290359070563387041)
    ·
      refine ⟨5356607467769302922540281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7142143290359070563387041 5356607467769302922540281)
      ·
        refine ⟨4017455600826977191905211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5356607467769302922540281 4017455600826977191905211)
        ·
          refine ⟨6026183401240465787857817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4017455600826977191905211 6026183401240465787857817)
          ·
            refine ⟨4519637550930349340893363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6026183401240465787857817 4519637550930349340893363)
            ·
              refine ⟨6779456326395524011340045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4519637550930349340893363 6779456326395524011340045)
              ·
                refine ⟨2542296122398321504252517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6779456326395524011340045 2542296122398321504252517)
                ·
                  refine ⟨476680522949685282047347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2542296122398321504252517 476680522949685282047347)
                  ·
                    rfl

theorem cell22_4177494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 2, 1, 3, 4].length) (baseStart_4177494 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4177494 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4177494 prefixEnd_4177494 := by exact prefixLift 4177494
  have htrace : WordTrace (prefixWord ++ tailWord_4177494) baseStart_4177494 baseEnd_4177494 := by
    simpa [prefixWord, tailWord_4177494, baseEnd_4177494] using wordTrace_append hprefix tailTrace_4177494
  have hstable : (prefixWord ++ tailWord_4177494).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4177494).length < 2 ^ (prefixWord ++ tailWord_4177494).sum := by decide
  have hdescent : baseEnd_4177494 < baseStart_4177494 := by decide
  rcases family_descends (prefixWord ++ tailWord_4177494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4177533 : List Nat := [1, 4, 1, 1, 4, 1, 4, 1, 5]
def baseStart_4177533 : Nat := 118140960795 + 4177533 * 2 ^ 59
def prefixEnd_4177533 : Nat := 4983230072969 + 3 ^ 40 * 4177533 * 2
def baseEnd_4177533 : Nat := 476684973115357581472307

theorem tailTrace_4177533 : CollatzResearch.WordTrace tailWord_4177533 prefixEnd_4177533 476684973115357581472307 := by
  unfold tailWord_4177533
  simp only [CollatzResearch.WordTrace]
  refine ⟨152367145974518881679593253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101578097316345921119728835 152367145974518881679593253)
  ·
    refine ⟨28568839870222290314923735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 152367145974518881679593253 28568839870222290314923735)
    ·
      refine ⟨42853259805333435472385603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28568839870222290314923735 42853259805333435472385603)
      ·
        refine ⟨64279889708000153208578405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42853259805333435472385603 64279889708000153208578405)
        ·
          refine ⟨12052479320250028726608451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 64279889708000153208578405 12052479320250028726608451)
          ·
            refine ⟨18078718980375043089912677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12052479320250028726608451 18078718980375043089912677)
            ·
              refine ⟨3389759808820320579358627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18078718980375043089912677 3389759808820320579358627)
              ·
                refine ⟨5084639713230480869037941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3389759808820320579358627 5084639713230480869037941)
                ·
                  refine ⟨476684973115357581472307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5084639713230480869037941 476684973115357581472307)
                  ·
                    rfl

theorem cell22_4177533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 4, 1, 5].length) (baseStart_4177533 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4177533 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4177533 prefixEnd_4177533 := by exact prefixLift 4177533
  have htrace : WordTrace (prefixWord ++ tailWord_4177533) baseStart_4177533 baseEnd_4177533 := by
    simpa [prefixWord, tailWord_4177533, baseEnd_4177533] using wordTrace_append hprefix tailTrace_4177533
  have hstable : (prefixWord ++ tailWord_4177533).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4177533).length < 2 ^ (prefixWord ++ tailWord_4177533).sum := by decide
  have hdescent : baseEnd_4177533 < baseStart_4177533 := by decide
  rcases family_descends (prefixWord ++ tailWord_4177533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4177593 : List Nat := [1, 2, 1, 4, 1, 1, 4, 3, 2, 3]
def baseStart_4177593 : Nat := 118140960795 + 4177593 * 2 ^ 59
def prefixEnd_4177593 : Nat := 4983230072969 + 3 ^ 40 * 4177593 * 2
def baseEnd_4177593 : Nat := 1430075458572252587916737

theorem tailTrace_4177593 : CollatzResearch.WordTrace tailWord_4177593 prefixEnd_4177593 1430075458572252587916737 := by
  unfold tailWord_4177593
  simp only [CollatzResearch.WordTrace]
  refine ⟨152369334354301511926777433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101579556236201007951184955 152369334354301511926777433)
  ·
    refine ⟨114277000765726133945083075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152369334354301511926777433 114277000765726133945083075)
    ·
      refine ⟨171415501148589200917624613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114277000765726133945083075 171415501148589200917624613)
      ·
        refine ⟨32140406465360475172054615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 171415501148589200917624613 32140406465360475172054615)
        ·
          refine ⟨48210609698040712758081923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32140406465360475172054615 48210609698040712758081923)
          ·
            refine ⟨72315914547061069137122885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48210609698040712758081923 72315914547061069137122885)
            ·
              refine ⟨13559233977573950463210541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 72315914547061069137122885 13559233977573950463210541)
              ·
                refine ⟨5084712741590231423703953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13559233977573950463210541 5084712741590231423703953)
                ·
                  refine ⟨3813534556192673567777965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5084712741590231423703953 3813534556192673567777965)
                  ·
                    refine ⟨1430075458572252587916737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3813534556192673567777965 1430075458572252587916737)
                    ·
                      rfl

theorem cell22_4177593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 4, 3, 2, 3].length) (baseStart_4177593 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4177593 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4177593 prefixEnd_4177593 := by exact prefixLift 4177593
  have htrace : WordTrace (prefixWord ++ tailWord_4177593) baseStart_4177593 baseEnd_4177593 := by
    simpa [prefixWord, tailWord_4177593, baseEnd_4177593] using wordTrace_append hprefix tailTrace_4177593
  have hstable : (prefixWord ++ tailWord_4177593).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4177593).length < 2 ^ (prefixWord ++ tailWord_4177593).sum := by decide
  have hdescent : baseEnd_4177593 < baseStart_4177593 := by decide
  rcases family_descends (prefixWord ++ tailWord_4177593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4177651 : List Nat := [1, 1, 1, 2, 2, 3, 2, 5, 5]
def baseStart_4177651 : Nat := 118140960795 + 4177651 * 2 ^ 59
def prefixEnd_4177651 : Nat := 4983230072969 + 3 ^ 40 * 4177651 * 2
def baseEnd_4177651 : Nat := 476698437719186589988853

theorem tailTrace_4177651 : CollatzResearch.WordTrace tailWord_4177651 prefixEnd_4177651 476698437719186589988853 := by
  unfold tailWord_4177651
  simp only [CollatzResearch.WordTrace]
  refine ⟨152371449788091387832388807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101580966525394258554925871 152371449788091387832388807)
  ·
    refine ⟨228557174682137081748583211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152371449788091387832388807 228557174682137081748583211)
    ·
      refine ⟨342835762023205622622874817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228557174682137081748583211 342835762023205622622874817)
      ·
        refine ⟨257126821517404216967156113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 342835762023205622622874817 257126821517404216967156113)
        ·
          refine ⟨192845116138053162725367085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 257126821517404216967156113 192845116138053162725367085)
          ·
            refine ⟨72316918551769936022012657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 192845116138053162725367085 72316918551769936022012657)
            ·
              refine ⟨54237688913827452016509493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72316918551769936022012657 54237688913827452016509493)
              ·
                refine ⟨5084783335671323626547765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 54237688913827452016509493 5084783335671323626547765)
                ·
                  refine ⟨476698437719186589988853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5084783335671323626547765 476698437719186589988853)
                  ·
                    rfl

theorem cell22_4177651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 5, 5].length) (baseStart_4177651 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4177651 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4177651 prefixEnd_4177651 := by exact prefixLift 4177651
  have htrace : WordTrace (prefixWord ++ tailWord_4177651) baseStart_4177651 baseEnd_4177651 := by
    simpa [prefixWord, tailWord_4177651, baseEnd_4177651] using wordTrace_append hprefix tailTrace_4177651
  have hstable : (prefixWord ++ tailWord_4177651).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4177651).length < 2 ^ (prefixWord ++ tailWord_4177651).sum := by decide
  have hdescent : baseEnd_4177651 < baseStart_4177651 := by decide
  rcases family_descends (prefixWord ++ tailWord_4177651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4177681 : List Nat := [1, 2, 2, 1, 1, 3, 1, 2, 5, 4]
def baseStart_4177681 : Nat := 118140960795 + 4177681 * 2 ^ 59
def prefixEnd_4177681 : Nat := 4983230072969 + 3 ^ 40 * 4177681 * 2
def baseEnd_4177681 : Nat := 1430105582770649691716467

theorem tailTrace_4177681 : CollatzResearch.WordTrace tailWord_4177681 prefixEnd_4177681 1430105582770649691716467 := by
  unfold tailWord_4177681
  simp only [CollatzResearch.WordTrace]
  refine ⟨152372543977982702955980897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101581695985321801970653931 152372543977982702955980897)
  ·
    refine ⟨114279407983487027216985673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152372543977982702955980897 114279407983487027216985673)
    ·
      refine ⟨85709555987615270412739255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114279407983487027216985673 85709555987615270412739255)
      ·
        refine ⟨128564333981422905619108883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85709555987615270412739255 128564333981422905619108883)
        ·
          refine ⟨192846500972134358428663325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128564333981422905619108883 192846500972134358428663325)
          ·
            refine ⟨72317437864550384410748747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 192846500972134358428663325 72317437864550384410748747)
            ·
              refine ⟨108476156796825576616123121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72317437864550384410748747 108476156796825576616123121)
              ·
                refine ⟨81357117597619182462092341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 108476156796825576616123121 81357117597619182462092341)
                ·
                  refine ⟨7627229774776798355821157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 81357117597619182462092341 7627229774776798355821157)
                  ·
                    refine ⟨1430105582770649691716467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7627229774776798355821157 1430105582770649691716467)
                    ·
                      rfl

theorem cell22_4177681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 4].length) (baseStart_4177681 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4177681 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4177681 prefixEnd_4177681 := by exact prefixLift 4177681
  have htrace : WordTrace (prefixWord ++ tailWord_4177681) baseStart_4177681 baseEnd_4177681 := by
    simpa [prefixWord, tailWord_4177681, baseEnd_4177681] using wordTrace_append hprefix tailTrace_4177681
  have hstable : (prefixWord ++ tailWord_4177681).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4177681).length < 2 ^ (prefixWord ++ tailWord_4177681).sum := by decide
  have hdescent : baseEnd_4177681 < baseStart_4177681 := by decide
  rcases family_descends (prefixWord ++ tailWord_4177681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4177698 : List Nat := [3, 3, 1, 1, 2, 1, 2, 2, 3, 4]
def baseStart_4177698 : Nat := 118140960795 + 4177698 * 2 ^ 59
def prefixEnd_4177698 : Nat := 4983230072969 + 3 ^ 40 * 4177698 * 2
def baseEnd_4177698 : Nat := 1430111402218067314041415

theorem tailTrace_4177698 : CollatzResearch.WordTrace tailWord_4177698 prefixEnd_4177698 1430111402218067314041415 := by
  unfold tailWord_4177698
  simp only [CollatzResearch.WordTrace]
  refine ⟨38093291004730278714837437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101582109345947409906233165 38093291004730278714837437)
  ·
    refine ⟨14284984126773854518064039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38093291004730278714837437 14284984126773854518064039)
    ·
      refine ⟨21427476190160781777096059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14284984126773854518064039 21427476190160781777096059)
      ·
        refine ⟨32141214285241172665644089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21427476190160781777096059 32141214285241172665644089)
        ·
          refine ⟨24105910713930879499233067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32141214285241172665644089 24105910713930879499233067)
          ·
            refine ⟨36158866070896319248849601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24105910713930879499233067 36158866070896319248849601)
            ·
              refine ⟨27119149553172239436637201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36158866070896319248849601 27119149553172239436637201)
              ·
                refine ⟨20339362164879179577477901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27119149553172239436637201 20339362164879179577477901)
                ·
                  refine ⟨7627260811829692341554213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20339362164879179577477901 7627260811829692341554213)
                  ·
                    refine ⟨1430111402218067314041415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7627260811829692341554213 1430111402218067314041415)
                    ·
                      rfl

theorem cell22_4177698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 2, 3, 4].length) (baseStart_4177698 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4177698 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4177698 prefixEnd_4177698 := by exact prefixLift 4177698
  have htrace : WordTrace (prefixWord ++ tailWord_4177698) baseStart_4177698 baseEnd_4177698 := by
    simpa [prefixWord, tailWord_4177698, baseEnd_4177698] using wordTrace_append hprefix tailTrace_4177698
  have hstable : (prefixWord ++ tailWord_4177698).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4177698).length < 2 ^ (prefixWord ++ tailWord_4177698).sum := by decide
  have hdescent : baseEnd_4177698 < baseStart_4177698 := by decide
  rcases family_descends (prefixWord ++ tailWord_4177698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4177745 : List Nat := [1, 2, 2, 1, 5, 1, 1, 4, 2, 3]
def baseStart_4177745 : Nat := 118140960795 + 4177745 * 2 ^ 59
def prefixEnd_4177745 : Nat := 4983230072969 + 3 ^ 40 * 4177745 * 2
def baseEnd_4177745 : Nat := 1430127491278574858116271

theorem tailTrace_4177745 : CollatzResearch.WordTrace tailWord_4177745 prefixEnd_4177745 1430127491278574858116271 := by
  unfold tailWord_4177745
  simp only [CollatzResearch.WordTrace]
  refine ⟨152374878249750841886310689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101583252166500561257540459 152374878249750841886310689)
  ·
    refine ⟨114281158687313131414733017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152374878249750841886310689 114281158687313131414733017)
    ·
      refine ⟨85710869015484848561049763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114281158687313131414733017 85710869015484848561049763)
      ·
        refine ⟨128566303523227272841574645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85710869015484848561049763 128566303523227272841574645)
        ·
          refine ⟨12053090955302556828897623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 128566303523227272841574645 12053090955302556828897623)
          ·
            refine ⟨18079636432953835243346435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12053090955302556828897623 18079636432953835243346435)
            ·
              refine ⟨27119454649430752865019653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18079636432953835243346435 27119454649430752865019653)
              ·
                refine ⟨5084897746768266162191185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27119454649430752865019653 5084897746768266162191185)
                ·
                  refine ⟨3813673310076199621643389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5084897746768266162191185 3813673310076199621643389)
                  ·
                    refine ⟨1430127491278574858116271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3813673310076199621643389 1430127491278574858116271)
                    ·
                      rfl

theorem cell22_4177745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 4, 2, 3].length) (baseStart_4177745 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4177745 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4177745 prefixEnd_4177745 := by exact prefixLift 4177745
  have htrace : WordTrace (prefixWord ++ tailWord_4177745) baseStart_4177745 baseEnd_4177745 := by
    simpa [prefixWord, tailWord_4177745, baseEnd_4177745] using wordTrace_append hprefix tailTrace_4177745
  have hstable : (prefixWord ++ tailWord_4177745).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4177745).length < 2 ^ (prefixWord ++ tailWord_4177745).sum := by decide
  have hdescent : baseEnd_4177745 < baseStart_4177745 := by decide
  rcases family_descends (prefixWord ++ tailWord_4177745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4177762 : List Nat := [3, 3, 2, 1, 2, 1, 2, 3, 2, 3]
def baseStart_4177762 : Nat := 118140960795 + 4177762 * 2 ^ 59
def prefixEnd_4177762 : Nat := 4983230072969 + 3 ^ 40 * 4177762 * 2
def baseEnd_4177762 : Nat := 1430133310725992480441219

theorem tailTrace_4177762 : CollatzResearch.WordTrace tailWord_4177762 prefixEnd_4177762 1430133310725992480441219 := by
  unfold tailWord_4177762
  simp only [CollatzResearch.WordTrace]
  refine ⟨38093874572672313447419885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101583665527126169193119693 38093874572672313447419885)
  ·
    refine ⟨14285202964752117542782457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38093874572672313447419885 14285202964752117542782457)
    ·
      refine ⟨10713902223564088157086843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14285202964752117542782457 10713902223564088157086843)
      ·
        refine ⟨16070853335346132235630265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10713902223564088157086843 16070853335346132235630265)
        ·
          refine ⟨12053140001509599176722699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16070853335346132235630265 12053140001509599176722699)
          ·
            refine ⟨18079710002264398765084049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12053140001509599176722699 18079710002264398765084049)
            ·
              refine ⟨13559782501698299073813037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18079710002264398765084049 13559782501698299073813037)
              ·
                refine ⟨5084918438136862152679889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13559782501698299073813037 5084918438136862152679889)
                ·
                  refine ⟨3813688828602646614509917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5084918438136862152679889 3813688828602646614509917)
                  ·
                    refine ⟨1430133310725992480441219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3813688828602646614509917 1430133310725992480441219)
                    ·
                      rfl

theorem cell22_4177762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 2, 3, 2, 3].length) (baseStart_4177762 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4177762 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4177762 prefixEnd_4177762 := by exact prefixLift 4177762
  have htrace : WordTrace (prefixWord ++ tailWord_4177762) baseStart_4177762 baseEnd_4177762 := by
    simpa [prefixWord, tailWord_4177762, baseEnd_4177762] using wordTrace_append hprefix tailTrace_4177762
  have hstable : (prefixWord ++ tailWord_4177762).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4177762).length < 2 ^ (prefixWord ++ tailWord_4177762).sum := by decide
  have hdescent : baseEnd_4177762 < baseStart_4177762 := by decide
  rcases family_descends (prefixWord ++ tailWord_4177762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4177771 : List Nat := [1, 1, 1, 1, 2, 2, 3, 1, 4, 6]
def baseStart_4177771 : Nat := 118140960795 + 4177771 * 2 ^ 59
def prefixEnd_4177771 : Nat := 4983230072969 + 3 ^ 40 * 4177771 * 2
def baseEnd_4177771 : Nat := 1430136391609919456966191

theorem tailTrace_4177771 : CollatzResearch.WordTrace tailWord_4177771 prefixEnd_4177771 1430136391609919456966191 := by
  unfold tailWord_4177771
  simp only [CollatzResearch.WordTrace]
  refine ⟨152375826547656648326757167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101583884365104432217838111 152375826547656648326757167)
  ·
    refine ⟨228563739821484972490135751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152375826547656648326757167 228563739821484972490135751)
    ·
      refine ⟨342845609732227458735203627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228563739821484972490135751 342845609732227458735203627)
      ·
        refine ⟨514268414598341188102805441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 342845609732227458735203627 514268414598341188102805441)
        ·
          refine ⟨385701310948755891077104081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 514268414598341188102805441 385701310948755891077104081)
          ·
            refine ⟨289275983211566918307828061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 385701310948755891077104081 289275983211566918307828061)
            ·
              refine ⟨108478493704337594365435523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 289275983211566918307828061 108478493704337594365435523)
              ·
                refine ⟨162717740556506391548153285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108478493704337594365435523 162717740556506391548153285)
                ·
                  refine ⟨30509576354344948415278741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 162717740556506391548153285 30509576354344948415278741)
                  ·
                    refine ⟨1430136391609919456966191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30509576354344948415278741 1430136391609919456966191)
                    ·
                      rfl

theorem cell22_4177771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 1, 4, 6].length) (baseStart_4177771 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4177771 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4177771 prefixEnd_4177771 := by exact prefixLift 4177771
  have htrace : WordTrace (prefixWord ++ tailWord_4177771) baseStart_4177771 baseEnd_4177771 := by
    simpa [prefixWord, tailWord_4177771, baseEnd_4177771] using wordTrace_append hprefix tailTrace_4177771
  have hstable : (prefixWord ++ tailWord_4177771).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4177771).length < 2 ^ (prefixWord ++ tailWord_4177771).sum := by decide
  have hdescent : baseEnd_4177771 < baseStart_4177771 := by decide
  rcases family_descends (prefixWord ++ tailWord_4177771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4177901 : List Nat := [1, 5, 1, 4, 1, 1, 3, 1, 1, 4]
def baseStart_4177901 : Nat := 118140960795 + 4177901 * 2 ^ 59
def prefixEnd_4177901 : Nat := 4983230072969 + 3 ^ 40 * 4177901 * 2
def baseEnd_4177901 : Nat := 1430180893266642451215793

theorem tailTrace_4177901 : CollatzResearch.WordTrace tailWord_4177901 prefixEnd_4177901 1430180893266642451215793 := by
  unfold tailWord_4177901
  simp only [CollatzResearch.WordTrace]
  refine ⟨152380568037185680528989557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101587045358123787019326371 152380568037185680528989557)
  ·
    refine ⟨14285678253486157549592771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 152380568037185680528989557 14285678253486157549592771)
    ·
      refine ⟨21428517380229236324389157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14285678253486157549592771 21428517380229236324389157)
      ·
        refine ⟨4017847008792981810822967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21428517380229236324389157 4017847008792981810822967)
        ·
          refine ⟨6026770513189472716234451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4017847008792981810822967 6026770513189472716234451)
          ·
            refine ⟨9040155769784209074351677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6026770513189472716234451 9040155769784209074351677)
            ·
              refine ⟨3390058413669078402881879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9040155769784209074351677 3390058413669078402881879)
              ·
                refine ⟨5085087620503617604322819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3390058413669078402881879 5085087620503617604322819)
                ·
                  refine ⟨7627631430755426406484229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5085087620503617604322819 7627631430755426406484229)
                  ·
                    refine ⟨1430180893266642451215793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7627631430755426406484229 1430180893266642451215793)
                    ·
                      rfl

theorem cell22_4177901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 3, 1, 1, 4].length) (baseStart_4177901 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4177901 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4177901 prefixEnd_4177901 := by exact prefixLift 4177901
  have htrace : WordTrace (prefixWord ++ tailWord_4177901) baseStart_4177901 baseEnd_4177901 := by
    simpa [prefixWord, tailWord_4177901, baseEnd_4177901] using wordTrace_append hprefix tailTrace_4177901
  have hstable : (prefixWord ++ tailWord_4177901).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4177901).length < 2 ^ (prefixWord ++ tailWord_4177901).sum := by decide
  have hdescent : baseEnd_4177901 < baseStart_4177901 := by decide
  rcases family_descends (prefixWord ++ tailWord_4177901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4177910 : List Nat := [5, 1, 1, 1, 4, 10]
def baseStart_4177910 : Nat := 118140960795 + 4177910 * 2 ^ 59
def prefixEnd_4177910 : Nat := 4983230072969 + 3 ^ 40 * 4177910 * 2
def baseEnd_4177910 : Nat := 17656592273463820095565

theorem tailTrace_4177910 : CollatzResearch.WordTrace tailWord_4177910 prefixEnd_4177910 17656592273463820095565 := by
  unfold tailWord_4177910
  simp only [CollatzResearch.WordTrace]
  refine ⟨9523806018384567191629199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 101587264196102050044044789 9523806018384567191629199)
  ·
    refine ⟨14285709027576850787443799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9523806018384567191629199 14285709027576850787443799)
    ·
      refine ⟨21428563541365276181165699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14285709027576850787443799 21428563541365276181165699)
      ·
        refine ⟨32142845312047914271748549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21428563541365276181165699 32142845312047914271748549)
        ·
          refine ⟨6026783496008983925952853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32142845312047914271748549 6026783496008983925952853)
          ·
            refine ⟨17656592273463820095565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 6026783496008983925952853 17656592273463820095565)
            ·
              rfl

theorem cell22_4177910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 10].length) (baseStart_4177910 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4177910 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4177910 prefixEnd_4177910 := by exact prefixLift 4177910
  have htrace : WordTrace (prefixWord ++ tailWord_4177910) baseStart_4177910 baseEnd_4177910 := by
    simpa [prefixWord, tailWord_4177910, baseEnd_4177910] using wordTrace_append hprefix tailTrace_4177910
  have hstable : (prefixWord ++ tailWord_4177910).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4177910).length < 2 ^ (prefixWord ++ tailWord_4177910).sum := by decide
  have hdescent : baseEnd_4177910 < baseStart_4177910 := by decide
  rcases family_descends (prefixWord ++ tailWord_4177910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4177970 : List Nat := [3, 2, 1, 1, 2, 3, 1, 2, 2, 5]
def baseStart_4177970 : Nat := 118140960795 + 4177970 * 2 ^ 59
def prefixEnd_4177970 : Nat := 4983230072969 + 3 ^ 40 * 4177970 * 2
def baseEnd_4177970 : Nat := 1430204513376749271240581

theorem tailTrace_4177970 : CollatzResearch.WordTrace tailWord_4177970 prefixEnd_4177970 1430204513376749271240581 := by
  unfold tailWord_4177970
  simp only [CollatzResearch.WordTrace]
  refine ⟨38095771168483926328312841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101588723115957136875500909 38095771168483926328312841)
  ·
    refine ⟨28571828376362944746234631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38095771168483926328312841 28571828376362944746234631)
    ·
      refine ⟨42857742564544417119351947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28571828376362944746234631 42857742564544417119351947)
      ·
        refine ⟨64286613846816625679027921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42857742564544417119351947 64286613846816625679027921)
        ·
          refine ⟨48214960385112469259270941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64286613846816625679027921 48214960385112469259270941)
          ·
            refine ⟨18080610144417175972226603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48214960385112469259270941 18080610144417175972226603)
            ·
              refine ⟨27120915216625763958339905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18080610144417175972226603 27120915216625763958339905)
              ·
                refine ⟨20340686412469322968754929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27120915216625763958339905 20340686412469322968754929)
                ·
                  refine ⟨15255514809351992226566197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20340686412469322968754929 15255514809351992226566197)
                  ·
                    refine ⟨1430204513376749271240581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15255514809351992226566197 1430204513376749271240581)
                    ·
                      rfl

theorem cell22_4177970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 2, 2, 5].length) (baseStart_4177970 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4177970 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4177970 prefixEnd_4177970 := by exact prefixLift 4177970
  have htrace : WordTrace (prefixWord ++ tailWord_4177970) baseStart_4177970 baseEnd_4177970 := by
    simpa [prefixWord, tailWord_4177970, baseEnd_4177970] using wordTrace_append hprefix tailTrace_4177970
  have hstable : (prefixWord ++ tailWord_4177970).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4177970).length < 2 ^ (prefixWord ++ tailWord_4177970).sum := by decide
  have hdescent : baseEnd_4177970 < baseStart_4177970 := by decide
  rcases family_descends (prefixWord ++ tailWord_4177970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4178032 : List Nat := [2, 1, 1, 1, 5, 2, 2, 1, 4, 3]
def baseStart_4178032 : Nat := 118140960795 + 4178032 * 2 ^ 59
def prefixEnd_4178032 : Nat := 4983230072969 + 3 ^ 40 * 4178032 * 2
def baseEnd_4178032 : Nat := 1430225737243801776190391

theorem tailTrace_4178032 : CollatzResearch.WordTrace tailWord_4178032 prefixEnd_4178032 1430225737243801776190391 := by
  unfold tailWord_4178032
  simp only [CollatzResearch.WordTrace]
  refine ⟨76192672999855544951004175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101590230666474059934672233 76192672999855544951004175)
  ·
    refine ⟨114289009499783317426506263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76192672999855544951004175 114289009499783317426506263)
    ·
      refine ⟨171433514249674976139759395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114289009499783317426506263 171433514249674976139759395)
      ·
        refine ⟨257150271374512464209639093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171433514249674976139759395 257150271374512464209639093)
        ·
          refine ⟨24107837941360543519653665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 257150271374512464209639093 24107837941360543519653665)
          ·
            refine ⟨18080878456020407639740249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24107837941360543519653665 18080878456020407639740249)
            ·
              refine ⟨13560658842015305729805187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18080878456020407639740249 13560658842015305729805187)
              ·
                refine ⟨20340988263022958594707781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13560658842015305729805187 20340988263022958594707781)
                ·
                  refine ⟨3813935299316804736507709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20340988263022958594707781 3813935299316804736507709)
                  ·
                    refine ⟨1430225737243801776190391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3813935299316804736507709 1430225737243801776190391)
                    ·
                      rfl

theorem cell22_4178032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 2, 1, 4, 3].length) (baseStart_4178032 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4178032 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4178032 prefixEnd_4178032 := by exact prefixLift 4178032
  have htrace : WordTrace (prefixWord ++ tailWord_4178032) baseStart_4178032 baseEnd_4178032 := by
    simpa [prefixWord, tailWord_4178032, baseEnd_4178032] using wordTrace_append hprefix tailTrace_4178032
  have hstable : (prefixWord ++ tailWord_4178032).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4178032).length < 2 ^ (prefixWord ++ tailWord_4178032).sum := by decide
  have hdescent : baseEnd_4178032 < baseStart_4178032 := by decide
  rcases family_descends (prefixWord ++ tailWord_4178032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4178045 : List Nat := [1, 4, 1, 1, 3, 2, 1, 9]
def baseStart_4178045 : Nat := 118140960795 + 4178045 * 2 ^ 59
def prefixEnd_4178045 : Nat := 4983230072969 + 3 ^ 40 * 4178045 * 2
def baseEnd_4178045 : Nat := 158914465267719341735039

theorem tailTrace_4178045 : CollatzResearch.WordTrace tailWord_4178045 prefixEnd_4178045 158914465267719341735039 := by
  unfold tailWord_4178045
  simp only [CollatzResearch.WordTrace]
  refine ⟨152385820148663993122231589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101590546765775995414821059 152385820148663993122231589)
  ·
    refine ⟨28572341277874498710418423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 152385820148663993122231589 28572341277874498710418423)
    ·
      refine ⟨42858511916811748065627635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28572341277874498710418423 42858511916811748065627635)
      ·
        refine ⟨64287767875217622098441453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42858511916811748065627635 64287767875217622098441453)
        ·
          refine ⟨24107912953206608286915545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64287767875217622098441453 24107912953206608286915545)
          ·
            refine ⟨18080934714904956215186659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24107912953206608286915545 18080934714904956215186659)
            ·
              refine ⟨27121402072357434322779989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18080934714904956215186659 27121402072357434322779989)
              ·
                refine ⟨158914465267719341735039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 27121402072357434322779989 158914465267719341735039)
                ·
                  rfl

theorem cell22_4178045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 9].length) (baseStart_4178045 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4178045 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4178045 prefixEnd_4178045 := by exact prefixLift 4178045
  have htrace : WordTrace (prefixWord ++ tailWord_4178045) baseStart_4178045 baseEnd_4178045 := by
    simpa [prefixWord, tailWord_4178045, baseEnd_4178045] using wordTrace_append hprefix tailTrace_4178045
  have hstable : (prefixWord ++ tailWord_4178045).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4178045).length < 2 ^ (prefixWord ++ tailWord_4178045).sum := by decide
  have hdescent : baseEnd_4178045 < baseStart_4178045 := by decide
  rcases family_descends (prefixWord ++ tailWord_4178045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4178135 : List Nat := [1, 1, 3, 2, 1, 2, 1, 1, 10]
def baseStart_4178135 : Nat := 118140960795 + 4178135 * 2 ^ 59
def prefixEnd_4178135 : Nat := 4983230072969 + 3 ^ 40 * 4178135 * 2
def baseEnd_4178135 : Nat := 476753665416247946955025

theorem tailTrace_4178135 : CollatzResearch.WordTrace tailWord_4178135 prefixEnd_4178135 476753665416247946955025 := by
  unfold tailWord_4178135
  simp only [CollatzResearch.WordTrace]
  refine ⟨152389102718337938493007859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101592735145558625662005239 152389102718337938493007859)
  ·
    refine ⟨228583654077506907739511789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152389102718337938493007859 228583654077506907739511789)
    ·
      refine ⟨85718870279065090402316921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 228583654077506907739511789 85718870279065090402316921)
      ·
        refine ⟨64289152709298817801737691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85718870279065090402316921 64289152709298817801737691)
        ·
          refine ⟨96433729063948226702606537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64289152709298817801737691 96433729063948226702606537)
          ·
            refine ⟨72325296797961170026954903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96433729063948226702606537 72325296797961170026954903)
            ·
              refine ⟨108487945196941755040432355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72325296797961170026954903 108487945196941755040432355)
              ·
                refine ⟨162731917795412632560648533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108487945196941755040432355 162731917795412632560648533)
                ·
                  refine ⟨476753665416247946955025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 162731917795412632560648533 476753665416247946955025)
                  ·
                    rfl

theorem cell22_4178135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 1, 10].length) (baseStart_4178135 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4178135 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4178135 prefixEnd_4178135 := by exact prefixLift 4178135
  have htrace : WordTrace (prefixWord ++ tailWord_4178135) baseStart_4178135 baseEnd_4178135 := by
    simpa [prefixWord, tailWord_4178135, baseEnd_4178135] using wordTrace_append hprefix tailTrace_4178135
  have hstable : (prefixWord ++ tailWord_4178135).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4178135).length < 2 ^ (prefixWord ++ tailWord_4178135).sum := by decide
  have hdescent : baseEnd_4178135 < baseStart_4178135 := by decide
  rcases family_descends (prefixWord ++ tailWord_4178135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4178141 : List Nat := [1, 4, 3, 2, 1, 3, 1, 2, 5]
def baseStart_4178141 : Nat := 118140960795 + 4178141 * 2 ^ 59
def prefixEnd_4178141 : Nat := 4983230072969 + 3 ^ 40 * 4178141 * 2
def baseEnd_4178141 : Nat := 476754350057120608405019

theorem tailTrace_4178141 : CollatzResearch.WordTrace tailWord_4178141 prefixEnd_4178141 476754350057120608405019 := by
  unfold tailWord_4178141
  simp only [CollatzResearch.WordTrace]
  refine ⟨152389321556316201517726277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101592881037544134345150851 152389321556316201517726277)
  ·
    refine ⟨28572997791809287784573677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 152389321556316201517726277 28572997791809287784573677)
    ·
      refine ⟨10714874171928482919215129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28572997791809287784573677 10714874171928482919215129)
      ·
        refine ⟨8036155628946362189411347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10714874171928482919215129 8036155628946362189411347)
        ·
          refine ⟨12054233443419543284117021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8036155628946362189411347 12054233443419543284117021)
          ·
            refine ⟨4520337541282328731543883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12054233443419543284117021 4520337541282328731543883)
            ·
              refine ⟨6780506311923493097315825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4520337541282328731543883 6780506311923493097315825)
              ·
                refine ⟨5085379733942619822986869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6780506311923493097315825 5085379733942619822986869)
                ·
                  refine ⟨476754350057120608405019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5085379733942619822986869 476754350057120608405019)
                  ·
                    rfl

theorem cell22_4178141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 3, 1, 2, 5].length) (baseStart_4178141 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4178141 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4178141 prefixEnd_4178141 := by exact prefixLift 4178141
  have htrace : WordTrace (prefixWord ++ tailWord_4178141) baseStart_4178141 baseEnd_4178141 := by
    simpa [prefixWord, tailWord_4178141, baseEnd_4178141] using wordTrace_append hprefix tailTrace_4178141
  have hstable : (prefixWord ++ tailWord_4178141).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4178141).length < 2 ^ (prefixWord ++ tailWord_4178141).sum := by decide
  have hdescent : baseEnd_4178141 < baseStart_4178141 := by decide
  rcases family_descends (prefixWord ++ tailWord_4178141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4178152 : List Nat := [2, 1, 4, 1, 2, 2, 1, 3, 6]
def baseStart_4178152 : Nat := 118140960795 + 4178152 * 2 ^ 59
def prefixEnd_4178152 : Nat := 4983230072969 + 3 ^ 40 * 4178152 * 2
def baseEnd_4178152 : Nat := 476755605232053821063341

theorem tailTrace_4178152 : CollatzResearch.WordTrace tailWord_4178152 prefixEnd_4178152 476755605232053821063341 := by
  unfold tailWord_4178152
  simp only [CollatzResearch.WordTrace]
  refine ⟨76194861379638175198188355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101593148506184233597584473 76194861379638175198188355)
  ·
    refine ⟨114292292069457262797282533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76194861379638175198188355 114292292069457262797282533)
    ·
      refine ⟨21429804763023236774490475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 114292292069457262797282533 21429804763023236774490475)
      ·
        refine ⟨32144707144534855161735713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21429804763023236774490475 32144707144534855161735713)
        ·
          refine ⟨24108530358401141371301785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32144707144534855161735713 24108530358401141371301785)
          ·
            refine ⟨18081397768800856028476339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24108530358401141371301785 18081397768800856028476339)
            ·
              refine ⟨27122096653201284042714509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18081397768800856028476339 27122096653201284042714509)
              ·
                refine ⟨10170786244950481516017941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27122096653201284042714509 10170786244950481516017941)
                ·
                  refine ⟨476755605232053821063341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10170786244950481516017941 476755605232053821063341)
                  ·
                    rfl

theorem cell22_4178152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 3, 6].length) (baseStart_4178152 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4178152 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4178152 prefixEnd_4178152 := by exact prefixLift 4178152
  have htrace : WordTrace (prefixWord ++ tailWord_4178152) baseStart_4178152 baseEnd_4178152 := by
    simpa [prefixWord, tailWord_4178152, baseEnd_4178152] using wordTrace_append hprefix tailTrace_4178152
  have hstable : (prefixWord ++ tailWord_4178152).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4178152).length < 2 ^ (prefixWord ++ tailWord_4178152).sum := by decide
  have hdescent : baseEnd_4178152 < baseStart_4178152 := by decide
  rcases family_descends (prefixWord ++ tailWord_4178152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4178167 : List Nat := [1, 1, 3, 1, 1, 1, 2, 1, 8, 3]
def baseStart_4178167 : Nat := 118140960795 + 4178167 * 2 ^ 59
def prefixEnd_4178167 : Nat := 4983230072969 + 3 ^ 40 * 4178167 * 2
def baseEnd_4178167 : Nat := 1430271950502706424064977

theorem tailTrace_4178167 : CollatzResearch.WordTrace tailWord_4178167 prefixEnd_4178167 1430271950502706424064977 := by
  unfold tailWord_4178167
  simp only [CollatzResearch.WordTrace]
  refine ⟨152390269854222007958172755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101593513236148005305448503 152390269854222007958172755)
  ·
    refine ⟨228585404781333011937259133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152390269854222007958172755 228585404781333011937259133)
    ·
      refine ⟨85719526792999879476472175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 228585404781333011937259133 85719526792999879476472175)
      ·
        refine ⟨128579290189499819214708263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85719526792999879476472175 128579290189499819214708263)
        ·
          refine ⟨192868935284249728822062395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128579290189499819214708263 192868935284249728822062395)
          ·
            refine ⟨289303402926374593233093593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192868935284249728822062395 289303402926374593233093593)
            ·
              refine ⟨216977552194780944924820195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 289303402926374593233093593 216977552194780944924820195)
              ·
                refine ⟨325466328292171417387230293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 216977552194780944924820195 325466328292171417387230293)
                ·
                  refine ⟨3814058534673883797506605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 325466328292171417387230293 3814058534673883797506605)
                  ·
                    refine ⟨1430271950502706424064977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3814058534673883797506605 1430271950502706424064977)
                    ·
                      rfl

theorem cell22_4178167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 1, 8, 3].length) (baseStart_4178167 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4178167 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4178167 prefixEnd_4178167 := by exact prefixLift 4178167
  have htrace : WordTrace (prefixWord ++ tailWord_4178167) baseStart_4178167 baseEnd_4178167 := by
    simpa [prefixWord, tailWord_4178167, baseEnd_4178167] using wordTrace_append hprefix tailTrace_4178167
  have hstable : (prefixWord ++ tailWord_4178167).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4178167).length < 2 ^ (prefixWord ++ tailWord_4178167).sum := by decide
  have hdescent : baseEnd_4178167 < baseStart_4178167 := by decide
  rcases family_descends (prefixWord ++ tailWord_4178167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4178184 : List Nat := [2, 1, 3, 2, 3, 1, 1, 2, 4, 3]
def baseStart_4178184 : Nat := 118140960795 + 4178184 * 2 ^ 59
def prefixEnd_4178184 : Nat := 4983230072969 + 3 ^ 40 * 4178184 * 2
def baseEnd_4178184 : Nat := 1430277769950124046389925

theorem tailTrace_4178184 : CollatzResearch.WordTrace tailWord_4178184 prefixEnd_4178184 1430277769950124046389925 := by
  unfold tailWord_4178184
  simp only [CollatzResearch.WordTrace]
  refine ⟨76195444947580209930770803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101593926596773613241027737 76195444947580209930770803)
  ·
    refine ⟨114293167421370314896156205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76195444947580209930770803 114293167421370314896156205)
    ·
      refine ⟨42859937783013868086058577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114293167421370314896156205 42859937783013868086058577)
      ·
        refine ⟨32144953337260401064543933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42859937783013868086058577 32144953337260401064543933)
        ·
          refine ⟨12054357501472650399203975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32144953337260401064543933 12054357501472650399203975)
          ·
            refine ⟨18081536252208975598805963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12054357501472650399203975 18081536252208975598805963)
            ·
              refine ⟨27122304378313463398208945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18081536252208975598805963 27122304378313463398208945)
              ·
                refine ⟨20341728283735097548656709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27122304378313463398208945 20341728283735097548656709)
                ·
                  refine ⟨3814074053200330790373133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20341728283735097548656709 3814074053200330790373133)
                  ·
                    refine ⟨1430277769950124046389925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3814074053200330790373133 1430277769950124046389925)
                    ·
                      rfl

theorem cell22_4178184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 2, 4, 3].length) (baseStart_4178184 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4178184 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4178184 prefixEnd_4178184 := by exact prefixLift 4178184
  have htrace : WordTrace (prefixWord ++ tailWord_4178184) baseStart_4178184 baseEnd_4178184 := by
    simpa [prefixWord, tailWord_4178184, baseEnd_4178184] using wordTrace_append hprefix tailTrace_4178184
  have hstable : (prefixWord ++ tailWord_4178184).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4178184).length < 2 ^ (prefixWord ++ tailWord_4178184).sum := by decide
  have hdescent : baseEnd_4178184 < baseStart_4178184 := by decide
  rcases family_descends (prefixWord ++ tailWord_4178184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4178199 : List Nat := [1, 1, 3, 4, 1, 3, 1, 2, 2, 4]
def baseStart_4178199 : Nat := 118140960795 + 4178199 * 2 ^ 59
def prefixEnd_4178199 : Nat := 4983230072969 + 3 ^ 40 * 4178199 * 2
def baseEnd_4178199 : Nat := 1430282904756669007264879

theorem tailTrace_4178199 : CollatzResearch.WordTrace tailWord_4178199 prefixEnd_4178199 1430282904756669007264879 := by
  unfold tailWord_4178199
  simp only [CollatzResearch.WordTrace]
  refine ⟨152391436990106077423337651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101594291326737384948891767 152391436990106077423337651)
  ·
    refine ⟨228587155485159116135006477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152391436990106077423337651 228587155485159116135006477)
    ·
      refine ⟨85720183306934668550627429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 228587155485159116135006477 85720183306934668550627429)
      ·
        refine ⟨16072534370050250353242643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 85720183306934668550627429 16072534370050250353242643)
        ·
          refine ⟨24108801555075375529863965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16072534370050250353242643 24108801555075375529863965)
          ·
            refine ⟨9040800583153265823698987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24108801555075375529863965 9040800583153265823698987)
            ·
              refine ⟨13561200874729898735548481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9040800583153265823698987 13561200874729898735548481)
              ·
                refine ⟨10170900656047424051661361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13561200874729898735548481 10170900656047424051661361)
                ·
                  refine ⟨7628175492035568038746021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10170900656047424051661361 7628175492035568038746021)
                  ·
                    refine ⟨1430282904756669007264879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7628175492035568038746021 1430282904756669007264879)
                    ·
                      rfl

theorem cell22_4178199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 1, 2, 2, 4].length) (baseStart_4178199 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4178199 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4178199 prefixEnd_4178199 := by exact prefixLift 4178199
  have htrace : WordTrace (prefixWord ++ tailWord_4178199) baseStart_4178199 baseEnd_4178199 := by
    simpa [prefixWord, tailWord_4178199, baseEnd_4178199] using wordTrace_append hprefix tailTrace_4178199
  have hstable : (prefixWord ++ tailWord_4178199).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4178199).length < 2 ^ (prefixWord ++ tailWord_4178199).sum := by decide
  have hdescent : baseEnd_4178199 < baseStart_4178199 := by decide
  rcases family_descends (prefixWord ++ tailWord_4178199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4178218 : List Nat := [3, 1, 4, 2, 2, 1, 1, 3, 2, 3]
def baseStart_4178218 : Nat := 118140960795 + 4178218 * 2 ^ 59
def prefixEnd_4178218 : Nat := 4983230072969 + 3 ^ 40 * 4178218 * 2
def baseEnd_4178218 : Nat := 1430289408844959291039821

theorem tailTrace_4178218 : CollatzResearch.WordTrace tailWord_4178218 prefixEnd_4178218 1430289408844959291039821 := by
  unfold tailWord_4178218
  simp only [CollatzResearch.WordTrace]
  refine ⟨38098032494259310917069827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101594753318024829112186205 38098032494259310917069827)
  ·
    refine ⟨57147048741388966375604741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38098032494259310917069827 57147048741388966375604741)
    ·
      refine ⟨10715071639010431195425889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 57147048741388966375604741 10715071639010431195425889)
      ·
        refine ⟨8036303729257823396569417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10715071639010431195425889 8036303729257823396569417)
        ·
          refine ⟨6027227796943367547427063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8036303729257823396569417 6027227796943367547427063)
          ·
            refine ⟨9040841695415051321140595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6027227796943367547427063 9040841695415051321140595)
            ·
              refine ⟨13561262543122576981710893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9040841695415051321140595 13561262543122576981710893)
              ·
                refine ⟨5085473453670966368141585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13561262543122576981710893 5085473453670966368141585)
                ·
                  refine ⟨3814105090253224776106189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5085473453670966368141585 3814105090253224776106189)
                  ·
                    refine ⟨1430289408844959291039821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3814105090253224776106189 1430289408844959291039821)
                    ·
                      rfl

theorem cell22_4178218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 1, 3, 2, 3].length) (baseStart_4178218 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4178218 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4178218 prefixEnd_4178218 := by exact prefixLift 4178218
  have htrace : WordTrace (prefixWord ++ tailWord_4178218) baseStart_4178218 baseEnd_4178218 := by
    simpa [prefixWord, tailWord_4178218, baseEnd_4178218] using wordTrace_append hprefix tailTrace_4178218
  have hstable : (prefixWord ++ tailWord_4178218).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4178218).length < 2 ^ (prefixWord ++ tailWord_4178218).sum := by decide
  have hdescent : baseEnd_4178218 < baseStart_4178218 := by decide
  rcases family_descends (prefixWord ++ tailWord_4178218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4178229 : List Nat := [1, 3, 3, 1, 2, 1, 2, 1, 5, 3]
def baseStart_4178229 : Nat := 118140960795 + 4178229 * 2 ^ 59
def prefixEnd_4178229 : Nat := 4983230072969 + 3 ^ 40 * 4178229 * 2
def baseEnd_4178229 : Nat := 1430293174369758929014787

theorem tailTrace_4178229 : CollatzResearch.WordTrace tailWord_4178229 prefixEnd_4178229 1430293174369758929014787 := by
  unfold tailWord_4178229
  simp only [CollatzResearch.WordTrace]
  refine ⟨152392531179997392546929741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101595020786664928364619827 152392531179997392546929741)
  ·
    refine ⟨57147199192499022205098653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152392531179997392546929741 57147199192499022205098653)
    ·
      refine ⟨21430199697187133326911995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57147199192499022205098653 21430199697187133326911995)
      ·
        refine ⟨32145299545780699990367993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21430199697187133326911995 32145299545780699990367993)
        ·
          refine ⟨24108974659335524992775995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32145299545780699990367993 24108974659335524992775995)
          ·
            refine ⟨36163461989003287489163993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24108974659335524992775995 36163461989003287489163993)
            ·
              refine ⟨27122596491752465616872995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36163461989003287489163993 27122596491752465616872995)
              ·
                refine ⟨40683894737628698425309493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27122596491752465616872995 40683894737628698425309493)
                ·
                  refine ⟨3814115131652690477372765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 40683894737628698425309493 3814115131652690477372765)
                  ·
                    refine ⟨1430293174369758929014787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3814115131652690477372765 1430293174369758929014787)
                    ·
                      rfl

theorem cell22_4178229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 1, 5, 3].length) (baseStart_4178229 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4178229 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4178229 prefixEnd_4178229 := by exact prefixLift 4178229
  have htrace : WordTrace (prefixWord ++ tailWord_4178229) baseStart_4178229 baseEnd_4178229 := by
    simpa [prefixWord, tailWord_4178229, baseEnd_4178229] using wordTrace_append hprefix tailTrace_4178229
  have hstable : (prefixWord ++ tailWord_4178229).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4178229).length < 2 ^ (prefixWord ++ tailWord_4178229).sum := by decide
  have hdescent : baseEnd_4178229 < baseStart_4178229 := by decide
  rcases family_descends (prefixWord ++ tailWord_4178229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4178274 : List Nat := [3, 3, 2, 1, 1, 2, 1, 1, 1, 7]
def baseStart_4178274 : Nat := 118140960795 + 4178274 * 2 ^ 59
def prefixEnd_4178274 : Nat := 4983230072969 + 3 ^ 40 * 4178274 * 2
def baseEnd_4178274 : Nat := 1430308578789393811639649

theorem tailTrace_4178274 : CollatzResearch.WordTrace tailWord_4178274 prefixEnd_4178274 1430308578789393811639649 := by
  unfold tailWord_4178274
  simp only [CollatzResearch.WordTrace]
  refine ⟨38098543116208591308079469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101596114976556243488211917 38098543116208591308079469)
  ·
    refine ⟨14286953668578221740529801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38098543116208591308079469 14286953668578221740529801)
    ·
      refine ⟨10715215251433666305397351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14286953668578221740529801 10715215251433666305397351)
      ·
        refine ⟨16072822877150499458096027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10715215251433666305397351 16072822877150499458096027)
        ·
          refine ⟨24109234315725749187144041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16072822877150499458096027 24109234315725749187144041)
          ·
            refine ⟨18081925736794311890358031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24109234315725749187144041 18081925736794311890358031)
            ·
              refine ⟨27122888605191467835537047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18081925736794311890358031 27122888605191467835537047)
              ·
                refine ⟨40684332907787201753305571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27122888605191467835537047 40684332907787201753305571)
                ·
                  refine ⟨61026499361680802629958357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40684332907787201753305571 61026499361680802629958357)
                  ·
                    refine ⟨1430308578789393811639649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 61026499361680802629958357 1430308578789393811639649)
                    ·
                      rfl

theorem cell22_4178274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 1, 1, 7].length) (baseStart_4178274 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4178274 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4178274 prefixEnd_4178274 := by exact prefixLift 4178274
  have htrace : WordTrace (prefixWord ++ tailWord_4178274) baseStart_4178274 baseEnd_4178274 := by
    simpa [prefixWord, tailWord_4178274, baseEnd_4178274] using wordTrace_append hprefix tailTrace_4178274
  have hstable : (prefixWord ++ tailWord_4178274).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4178274).length < 2 ^ (prefixWord ++ tailWord_4178274).sum := by decide
  have hdescent : baseEnd_4178274 < baseStart_4178274 := by decide
  rcases family_descends (prefixWord ++ tailWord_4178274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4178289 : List Nat := [1, 2, 2, 2, 1, 2, 1, 6, 1, 4]
def baseStart_4178289 : Nat := 118140960795 + 4178289 * 2 ^ 59
def prefixEnd_4178289 : Nat := 4983230072969 + 3 ^ 40 * 4178289 * 2
def baseEnd_4178289 : Nat := 1430313713595938772514603

theorem tailTrace_4178289 : CollatzResearch.WordTrace tailWord_4178289 prefixEnd_4178289 1430313713595938772514603 := by
  unfold tailWord_4178289
  simp only [CollatzResearch.WordTrace]
  refine ⟨152394719559780022794113921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101596479706520015196075947 152394719559780022794113921)
  ·
    refine ⟨114296039669835017095585441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152394719559780022794113921 114296039669835017095585441)
    ·
      refine ⟨85722029752376262821689081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114296039669835017095585441 85722029752376262821689081)
      ·
        refine ⟨64291522314282197116266811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85722029752376262821689081 64291522314282197116266811)
        ·
          refine ⟨96437283471423295674400217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64291522314282197116266811 96437283471423295674400217)
          ·
            refine ⟨72327962603567471755800163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96437283471423295674400217 72327962603567471755800163)
            ·
              refine ⟨108491943905351207633700245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72327962603567471755800163 108491943905351207633700245)
              ·
                refine ⟨5085559870563337857829699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 108491943905351207633700245 5085559870563337857829699)
                ·
                  refine ⟨7628339805845006786744549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5085559870563337857829699 7628339805845006786744549)
                  ·
                    refine ⟨1430313713595938772514603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7628339805845006786744549 1430313713595938772514603)
                    ·
                      rfl

theorem cell22_4178289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 6, 1, 4].length) (baseStart_4178289 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4178289 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4178289 prefixEnd_4178289 := by exact prefixLift 4178289
  have htrace : WordTrace (prefixWord ++ tailWord_4178289) baseStart_4178289 baseEnd_4178289 := by
    simpa [prefixWord, tailWord_4178289, baseEnd_4178289] using wordTrace_append hprefix tailTrace_4178289
  have hstable : (prefixWord ++ tailWord_4178289).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4178289).length < 2 ^ (prefixWord ++ tailWord_4178289).sum := by decide
  have hdescent : baseEnd_4178289 < baseStart_4178289 := by decide
  rcases family_descends (prefixWord ++ tailWord_4178289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4178336 : List Nat := [2, 1, 1, 4, 1, 5, 1, 1, 1, 5]
def baseStart_4178336 : Nat := 118140960795 + 4178336 * 2 ^ 59
def prefixEnd_4178336 : Nat := 4983230072969 + 3 ^ 40 * 4178336 * 2
def baseEnd_4178336 : Nat := 1430329802656446316589459

theorem tailTrace_4178336 : CollatzResearch.WordTrace tailWord_4178336 prefixEnd_4178336 1430329802656446316589459 := by
  unfold tailWord_4178336
  simp only [CollatzResearch.WordTrace]
  refine ⟨76198216895304874910537431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101597622527073166547383241 76198216895304874910537431)
  ·
    refine ⟨114297325342957312365806147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76198216895304874910537431 114297325342957312365806147)
    ·
      refine ⟨171445988014435968548709221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114297325342957312365806147 171445988014435968548709221)
      ·
        refine ⟨32146122752706744102882979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 171445988014435968548709221 32146122752706744102882979)
        ·
          refine ⟨48219184129060116154324469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32146122752706744102882979 48219184129060116154324469)
          ·
            refine ⟨4520548512099385889467919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 48219184129060116154324469 4520548512099385889467919)
            ·
              refine ⟨6780822768149078834201879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4520548512099385889467919 6780822768149078834201879)
              ·
                refine ⟨10171234152223618251302819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6780822768149078834201879 10171234152223618251302819)
                ·
                  refine ⟨15256851228335427376954229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10171234152223618251302819 15256851228335427376954229)
                  ·
                    refine ⟨1430329802656446316589459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15256851228335427376954229 1430329802656446316589459)
                    ·
                      rfl

theorem cell22_4178336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 5, 1, 1, 1, 5].length) (baseStart_4178336 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4178336 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4178336 prefixEnd_4178336 := by exact prefixLift 4178336
  have htrace : WordTrace (prefixWord ++ tailWord_4178336) baseStart_4178336 baseEnd_4178336 := by
    simpa [prefixWord, tailWord_4178336, baseEnd_4178336] using wordTrace_append hprefix tailTrace_4178336
  have hstable : (prefixWord ++ tailWord_4178336).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4178336).length < 2 ^ (prefixWord ++ tailWord_4178336).sum := by decide
  have hdescent : baseEnd_4178336 < baseStart_4178336 := by decide
  rcases family_descends (prefixWord ++ tailWord_4178336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4178445 : List Nat := [1, 7, 1, 1, 1, 1, 2, 3, 5]
def baseStart_4178445 : Nat := 118140960795 + 4178445 * 2 ^ 59
def prefixEnd_4178445 : Nat := 4983230072969 + 3 ^ 40 * 4178445 * 2
def baseEnd_4178445 : Nat := 476789038528002121871375

theorem tailTrace_4178445 : CollatzResearch.WordTrace tailWord_4178445 prefixEnd_4178445 476789038528002121871375 := by
  unfold tailWord_4178445
  simp only [CollatzResearch.WordTrace]
  refine ⟨152400409347214861436792789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101600272898143240957861859 152400409347214861436792789)
  ·
    refine ⟨3571884594075348314924831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 152400409347214861436792789 3571884594075348314924831)
    ·
      refine ⟨5357826891113022472387247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3571884594075348314924831 5357826891113022472387247)
      ·
        refine ⟨8036740336669533708580871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5357826891113022472387247 8036740336669533708580871)
        ·
          refine ⟨12055110505004300562871307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8036740336669533708580871 12055110505004300562871307)
          ·
            refine ⟨18082665757506450844306961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12055110505004300562871307 18082665757506450844306961)
            ·
              refine ⟨13561999318129838133230221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18082665757506450844306961 13561999318129838133230221)
              ·
                refine ⟨5085749744298689299961333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13561999318129838133230221 5085749744298689299961333)
                ·
                  refine ⟨476789038528002121871375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5085749744298689299961333 476789038528002121871375)
                  ·
                    rfl

theorem cell22_4178445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 2, 3, 5].length) (baseStart_4178445 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4178445 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4178445 prefixEnd_4178445 := by exact prefixLift 4178445
  have htrace : WordTrace (prefixWord ++ tailWord_4178445) baseStart_4178445 baseEnd_4178445 := by
    simpa [prefixWord, tailWord_4178445, baseEnd_4178445] using wordTrace_append hprefix tailTrace_4178445
  have hstable : (prefixWord ++ tailWord_4178445).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4178445).length < 2 ^ (prefixWord ++ tailWord_4178445).sum := by decide
  have hdescent : baseEnd_4178445 < baseStart_4178445 := by decide
  rcases family_descends (prefixWord ++ tailWord_4178445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4178456 : List Nat := [2, 1, 2, 3, 3, 2, 1, 2, 6]
def baseStart_4178456 : Nat := 118140960795 + 4178456 * 2 ^ 59
def prefixEnd_4178456 : Nat := 4983230072969 + 3 ^ 40 * 4178456 * 2
def baseEnd_4178456 : Nat := 476790293702935334529697

theorem tailTrace_4178456 : CollatzResearch.WordTrace tailWord_4178456 prefixEnd_4178456 476790293702935334529697 := by
  unfold tailWord_4178456
  simp only [CollatzResearch.WordTrace]
  refine ⟨76200405275087505157721611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101600540366783340210295481 76200405275087505157721611)
  ·
    refine ⟨114300607912631257736582417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76200405275087505157721611 114300607912631257736582417)
    ·
      refine ⟨85725455934473443302436813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114300607912631257736582417 85725455934473443302436813)
      ·
        refine ⟨32147045975427541238413805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85725455934473443302436813 32147045975427541238413805)
        ·
          refine ⟨12055142240785327964405177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32147045975427541238413805 12055142240785327964405177)
          ·
            refine ⟨9041356680588995973303883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12055142240785327964405177 9041356680588995973303883)
            ·
              refine ⟨13562035020883493959955825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9041356680588995973303883 13562035020883493959955825)
              ·
                refine ⟨10171526265662620469966869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13562035020883493959955825 10171526265662620469966869)
                ·
                  refine ⟨476790293702935334529697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10171526265662620469966869 476790293702935334529697)
                  ·
                    rfl

theorem cell22_4178456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 1, 2, 6].length) (baseStart_4178456 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4178456 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4178456 prefixEnd_4178456 := by exact prefixLift 4178456
  have htrace : WordTrace (prefixWord ++ tailWord_4178456) baseStart_4178456 baseEnd_4178456 := by
    simpa [prefixWord, tailWord_4178456, baseEnd_4178456] using wordTrace_append hprefix tailTrace_4178456
  have hstable : (prefixWord ++ tailWord_4178456).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4178456).length < 2 ^ (prefixWord ++ tailWord_4178456).sum := by decide
  have hdescent : baseEnd_4178456 < baseStart_4178456 := by decide
  rcases family_descends (prefixWord ++ tailWord_4178456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4178561 : List Nat := [1, 2, 4, 2, 1, 1, 2, 1, 1, 7]
def baseStart_4178561 : Nat := 118140960795 + 4178561 * 2 ^ 59
def prefixEnd_4178561 : Nat := 4983230072969 + 3 ^ 40 * 4178561 * 2
def baseEnd_4178561 : Nat := 1430406824754620729713769

theorem tailTrace_4178561 : CollatzResearch.WordTrace tailWord_4178561 prefixEnd_4178561 1430406824754620729713769 := by
  unfold tailWord_4178561
  simp only [CollatzResearch.WordTrace]
  refine ⟨152404640214794613248015537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101603093476529742165343691 152404640214794613248015537)
  ·
    refine ⟨114303480161095959936011653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152404640214794613248015537 114303480161095959936011653)
    ·
      refine ⟨21431902530205492488002185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 114303480161095959936011653 21431902530205492488002185)
      ·
        refine ⟨16073926897654119366001639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21431902530205492488002185 16073926897654119366001639)
        ·
          refine ⟨24110890346481179049002459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16073926897654119366001639 24110890346481179049002459)
          ·
            refine ⟨36166335519721768573503689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24110890346481179049002459 36166335519721768573503689)
            ·
              refine ⟨27124751639791326430127767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36166335519721768573503689 27124751639791326430127767)
              ·
                refine ⟨40687127459686989645191651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27124751639791326430127767 40687127459686989645191651)
                ·
                  refine ⟨61030691189530484467787477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40687127459686989645191651 61030691189530484467787477)
                  ·
                    refine ⟨1430406824754620729713769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 61030691189530484467787477 1430406824754620729713769)
                    ·
                      rfl

theorem cell22_4178561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 1, 1, 7].length) (baseStart_4178561 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4178561 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4178561 prefixEnd_4178561 := by exact prefixLift 4178561
  have htrace : WordTrace (prefixWord ++ tailWord_4178561) baseStart_4178561 baseEnd_4178561 := by
    simpa [prefixWord, tailWord_4178561, baseEnd_4178561] using wordTrace_append hprefix tailTrace_4178561
  have hstable : (prefixWord ++ tailWord_4178561).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4178561).length < 2 ^ (prefixWord ++ tailWord_4178561).sum := by decide
  have hdescent : baseEnd_4178561 < baseStart_4178561 := by decide
  rcases family_descends (prefixWord ++ tailWord_4178561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4178563 : List Nat := [1, 1, 1, 3, 3, 1, 6, 1, 5]
def baseStart_4178563 : Nat := 118140960795 + 4178563 * 2 ^ 59
def prefixEnd_4178563 : Nat := 4983230072969 + 3 ^ 40 * 4178563 * 2
def baseEnd_4178563 : Nat := 476802503131831130387921

theorem tailTrace_4178563 : CollatzResearch.WordTrace tailWord_4178563 prefixEnd_4178563 476802503131831130387921 := by
  unfold tailWord_4178563
  simp only [CollatzResearch.WordTrace]
  refine ⟨152404713160787367589588343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101603142107191578393058895 152404713160787367589588343)
  ·
    refine ⟨228607069741181051384382515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152404713160787367589588343 228607069741181051384382515)
    ·
      refine ⟨342910604611771577076573773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228607069741181051384382515 342910604611771577076573773)
      ·
        refine ⟨128591476729414341403715165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 342910604611771577076573773 128591476729414341403715165)
        ·
          refine ⟨48221803773530378026393187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 128591476729414341403715165 48221803773530378026393187)
          ·
            refine ⟨72332705660295567039589781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48221803773530378026393187 72332705660295567039589781)
            ·
              refine ⟨3390595577826354704980771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 72332705660295567039589781 3390595577826354704980771)
              ·
                refine ⟨5085893366739532057471157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3390595577826354704980771 5085893366739532057471157)
                ·
                  refine ⟨476802503131831130387921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5085893366739532057471157 476802503131831130387921)
                  ·
                    rfl

theorem cell22_4178563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 6, 1, 5].length) (baseStart_4178563 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4178563 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4178563 prefixEnd_4178563 := by exact prefixLift 4178563
  have htrace : WordTrace (prefixWord ++ tailWord_4178563) baseStart_4178563 baseEnd_4178563 := by
    simpa [prefixWord, tailWord_4178563, baseEnd_4178563] using wordTrace_append hprefix tailTrace_4178563
  have hstable : (prefixWord ++ tailWord_4178563).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4178563).length < 2 ^ (prefixWord ++ tailWord_4178563).sum := by decide
  have hdescent : baseEnd_4178563 < baseStart_4178563 := by decide
  rcases family_descends (prefixWord ++ tailWord_4178563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4178623 : List Nat := [1, 1, 2, 2, 2, 5, 2, 1, 1, 5]
def baseStart_4178623 : Nat := 118140960795 + 4178623 * 2 ^ 59
def prefixEnd_4178623 : Nat := 4983230072969 + 3 ^ 40 * 4178623 * 2
def baseEnd_4178623 : Nat := 1430428048621673234663579

theorem tailTrace_4178623 : CollatzResearch.WordTrace tailWord_4178623 prefixEnd_4178623 1430428048621673234663579 := by
  unfold tailWord_4178623
  simp only [CollatzResearch.WordTrace]
  refine ⟨152406901540569997836772523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101604601027046665224515015 152406901540569997836772523)
  ·
    refine ⟨228610352310854996755158785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152406901540569997836772523 228610352310854996755158785)
    ·
      refine ⟨171457764233141247566369089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 228610352310854996755158785 171457764233141247566369089)
      ·
        refine ⟨128593323174855935674776817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171457764233141247566369089 128593323174855935674776817)
        ·
          refine ⟨96444992381141951756082613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128593323174855935674776817 96444992381141951756082613)
          ·
            refine ⟨9041718035732057977132745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 96444992381141951756082613 9041718035732057977132745)
            ·
              refine ⟨6781288526799043482849559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9041718035732057977132745 6781288526799043482849559)
              ·
                refine ⟨10171932790198565224274339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6781288526799043482849559 10171932790198565224274339)
                ·
                  refine ⟨15257899185297847836411509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10171932790198565224274339 15257899185297847836411509)
                  ·
                    refine ⟨1430428048621673234663579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15257899185297847836411509 1430428048621673234663579)
                    ·
                      rfl

theorem cell22_4178623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 2, 1, 1, 5].length) (baseStart_4178623 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4178623 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4178623 prefixEnd_4178623 := by exact prefixLift 4178623
  have htrace : WordTrace (prefixWord ++ tailWord_4178623) baseStart_4178623 baseEnd_4178623 := by
    simpa [prefixWord, tailWord_4178623, baseEnd_4178623] using wordTrace_append hprefix tailTrace_4178623
  have hstable : (prefixWord ++ tailWord_4178623).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4178623).length < 2 ^ (prefixWord ++ tailWord_4178623).sum := by decide
  have hdescent : baseEnd_4178623 < baseStart_4178623 := by decide
  rcases family_descends (prefixWord ++ tailWord_4178623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4178638 : List Nat := [4, 1, 1, 1, 3, 3, 1, 1, 1, 6]
def baseStart_4178638 : Nat := 118140960795 + 4178638 * 2 ^ 59
def prefixEnd_4178638 : Nat := 4983230072969 + 3 ^ 40 * 4178638 * 2
def baseEnd_4178638 : Nat := 1430433183428218195538533

theorem tailTrace_4178638 : CollatzResearch.WordTrace tailWord_4178638 prefixEnd_4178638 1430433183428218195538533 := by
  unfold tailWord_4178638
  simp only [CollatzResearch.WordTrace]
  refine ⟨19050931079439456924821071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 101604965757010436932379045 19050931079439456924821071)
  ·
    refine ⟨28576396619159185387231607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19050931079439456924821071 28576396619159185387231607)
    ·
      refine ⟨42864594928738778080847411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28576396619159185387231607 42864594928738778080847411)
      ·
        refine ⟨64296892393108167121271117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42864594928738778080847411 64296892393108167121271117)
        ·
          refine ⟨24111334647415562670476669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64296892393108167121271117 24111334647415562670476669)
          ·
            refine ⟨9041750492780836001428751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24111334647415562670476669 9041750492780836001428751)
            ·
              refine ⟨13562625739171254002143127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9041750492780836001428751 13562625739171254002143127)
              ·
                refine ⟨20343938608756881003214691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13562625739171254002143127 20343938608756881003214691)
                ·
                  refine ⟨30515907913135321504822037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20343938608756881003214691 30515907913135321504822037)
                  ·
                    refine ⟨1430433183428218195538533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30515907913135321504822037 1430433183428218195538533)
                    ·
                      rfl

theorem cell22_4178638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 1, 1, 1, 6].length) (baseStart_4178638 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4178638 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4178638 prefixEnd_4178638 := by exact prefixLift 4178638
  have htrace : WordTrace (prefixWord ++ tailWord_4178638) baseStart_4178638 baseEnd_4178638 := by
    simpa [prefixWord, tailWord_4178638, baseEnd_4178638] using wordTrace_append hprefix tailTrace_4178638
  have hstable : (prefixWord ++ tailWord_4178638).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4178638).length < 2 ^ (prefixWord ++ tailWord_4178638).sum := by decide
  have hdescent : baseEnd_4178638 < baseStart_4178638 := by decide
  rcases family_descends (prefixWord ++ tailWord_4178638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4178642 : List Nat := [3, 2, 2, 2, 3, 1, 2, 3, 4]
def baseStart_4178642 : Nat := 118140960795 + 4178642 * 2 ^ 59
def prefixEnd_4178642 : Nat := 4983230072969 + 3 ^ 40 * 4178642 * 2
def baseEnd_4178642 : Nat := 476811517569987839479507

theorem tailTrace_4178642 : CollatzResearch.WordTrace tailWord_4178642 prefixEnd_4178642 476811517569987839479507 := by
  unfold tailWord_4178642
  simp only [CollatzResearch.WordTrace]
  refine ⟨38101898631875291020428545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101605063018334109387809453 38101898631875291020428545)
  ·
    refine ⟨28576423973906468265321409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38101898631875291020428545 28576423973906468265321409)
    ·
      refine ⟨21432317980429851198991057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28576423973906468265321409 21432317980429851198991057)
      ·
        refine ⟨16074238485322388399243293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21432317980429851198991057 16074238485322388399243293)
        ·
          refine ⟨6027839431995895649716235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16074238485322388399243293 6027839431995895649716235)
          ·
            refine ⟨9041759147993843474574353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6027839431995895649716235 9041759147993843474574353)
            ·
              refine ⟨6781319360995382605930765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9041759147993843474574353 6781319360995382605930765)
              ·
                refine ⟨2542994760373268477224037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6781319360995382605930765 2542994760373268477224037)
                ·
                  refine ⟨476811517569987839479507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2542994760373268477224037 476811517569987839479507)
                  ·
                    rfl

theorem cell22_4178642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 2, 3, 4].length) (baseStart_4178642 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4178642 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4178642 prefixEnd_4178642 := by exact prefixLift 4178642
  have htrace : WordTrace (prefixWord ++ tailWord_4178642) baseStart_4178642 baseEnd_4178642 := by
    simpa [prefixWord, tailWord_4178642, baseEnd_4178642] using wordTrace_append hprefix tailTrace_4178642
  have hstable : (prefixWord ++ tailWord_4178642).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4178642).length < 2 ^ (prefixWord ++ tailWord_4178642).sum := by decide
  have hdescent : baseEnd_4178642 < baseStart_4178642 := by decide
  rcases family_descends (prefixWord ++ tailWord_4178642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4178644 : List Nat := [2, 4, 1, 3, 2, 2, 2, 1, 1, 4]
def baseStart_4178644 : Nat := 118140960795 + 4178644 * 2 ^ 59
def prefixEnd_4178644 : Nat := 4983230072969 + 3 ^ 40 * 4178644 * 2
def baseEnd_4178644 : Nat := 1430435237350836179888515

theorem tailTrace_4178644 : CollatzResearch.WordTrace tailWord_4178644 prefixEnd_4178644 1430435237350836179888515 := by
  unfold tailWord_4178644
  simp only [CollatzResearch.WordTrace]
  refine ⟨76203833736746959211643493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101605111648995945615524657 76203833736746959211643493)
  ·
    refine ⟨14288218825640054852183155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 76203833736746959211643493 14288218825640054852183155)
    ·
      refine ⟨21432328238460082278274733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14288218825640054852183155 21432328238460082278274733)
      ·
        refine ⟨8037123089422530854353025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21432328238460082278274733 8037123089422530854353025)
        ·
          refine ⟨6027842317066898140764769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8037123089422530854353025 6027842317066898140764769)
          ·
            refine ⟨4520881737800173605573577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6027842317066898140764769 4520881737800173605573577)
            ·
              refine ⟨3390661303350130204180183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4520881737800173605573577 3390661303350130204180183)
              ·
                refine ⟨5085991955025195306270275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3390661303350130204180183 5085991955025195306270275)
                ·
                  refine ⟨7628987932537792959405413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5085991955025195306270275 7628987932537792959405413)
                  ·
                    refine ⟨1430435237350836179888515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7628987932537792959405413 1430435237350836179888515)
                    ·
                      rfl

theorem cell22_4178644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 2, 2, 1, 1, 4].length) (baseStart_4178644 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4178644 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4178644 prefixEnd_4178644 := by exact prefixLift 4178644
  have htrace : WordTrace (prefixWord ++ tailWord_4178644) baseStart_4178644 baseEnd_4178644 := by
    simpa [prefixWord, tailWord_4178644, baseEnd_4178644] using wordTrace_append hprefix tailTrace_4178644
  have hstable : (prefixWord ++ tailWord_4178644).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4178644).length < 2 ^ (prefixWord ++ tailWord_4178644).sum := by decide
  have hdescent : baseEnd_4178644 < baseStart_4178644 := by decide
  rcases family_descends (prefixWord ++ tailWord_4178644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4178657 : List Nat := [1, 2, 3, 1, 4, 3, 1, 2, 2, 3]
def baseStart_4178657 : Nat := 118140960795 + 4178657 * 2 ^ 59
def prefixEnd_4178657 : Nat := 4983230072969 + 3 ^ 40 * 4178657 * 2
def baseEnd_4178657 : Nat := 1430439687516508479313475

theorem tailTrace_4178657 : CollatzResearch.WordTrace tailWord_4178657 prefixEnd_4178657 1430439687516508479313475 := by
  unfold tailWord_4178657
  simp only [CollatzResearch.WordTrace]
  refine ⟨152408141622446821643510225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101605427748297881095673483 152408141622446821643510225)
  ·
    refine ⟨114306106216835116232632669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152408141622446821643510225 114306106216835116232632669)
    ·
      refine ⟨42864789831313168587237251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114306106216835116232632669 42864789831313168587237251)
      ·
        refine ⟨64297184746969752880855877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42864789831313168587237251 64297184746969752880855877)
        ·
          refine ⟨12055722140056828665160477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 64297184746969752880855877 12055722140056828665160477)
          ·
            refine ⟨4520895802521310749435179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12055722140056828665160477 4520895802521310749435179)
            ·
              refine ⟨6781343703781966124152769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4520895802521310749435179 6781343703781966124152769)
              ·
                refine ⟨5086007777836474593114577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6781343703781966124152769 5086007777836474593114577)
                ·
                  refine ⟨3814505833377355944835933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5086007777836474593114577 3814505833377355944835933)
                  ·
                    refine ⟨1430439687516508479313475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3814505833377355944835933 1430439687516508479313475)
                    ·
                      rfl

theorem cell22_4178657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 3, 1, 2, 2, 3].length) (baseStart_4178657 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4178657 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4178657 prefixEnd_4178657 := by exact prefixLift 4178657
  have htrace : WordTrace (prefixWord ++ tailWord_4178657) baseStart_4178657 baseEnd_4178657 := by
    simpa [prefixWord, tailWord_4178657, baseEnd_4178657] using wordTrace_append hprefix tailTrace_4178657
  have hstable : (prefixWord ++ tailWord_4178657).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4178657).length < 2 ^ (prefixWord ++ tailWord_4178657).sum := by decide
  have hdescent : baseEnd_4178657 < baseStart_4178657 := by decide
  rcases family_descends (prefixWord ++ tailWord_4178657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4178719 : List Nat := [1, 1, 2, 4, 2, 3, 3, 2, 1, 3]
def baseStart_4178719 : Nat := 118140960795 + 4178719 * 2 ^ 59
def prefixEnd_4178719 : Nat := 4983230072969 + 3 ^ 40 * 4178719 * 2
def baseEnd_4178719 : Nat := 1430460911383560984263285

theorem tailTrace_4178719 : CollatzResearch.WordTrace tailWord_4178719 prefixEnd_4178719 1430460911383560984263285 := by
  unfold tailWord_4178719
  simp only [CollatzResearch.WordTrace]
  refine ⟨152410402948222206232267211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101606935298814804154844807 152410402948222206232267211)
  ·
    refine ⟨228615604422333309348400817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152410402948222206232267211 228615604422333309348400817)
    ·
      refine ⟨171461703316749982011300613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 228615604422333309348400817 171461703316749982011300613)
      ·
        refine ⟨32149069371890621627118865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 171461703316749982011300613 32149069371890621627118865)
        ·
          refine ⟨24111802028917966220339149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32149069371890621627118865 24111802028917966220339149)
          ·
            refine ⟨9041925760844237332627181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24111802028917966220339149 9041925760844237332627181)
            ·
              refine ⟨3390722160316588999735193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9041925760844237332627181 3390722160316588999735193)
              ·
                refine ⟨2543041620237441749801395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3390722160316588999735193 2543041620237441749801395)
                ·
                  refine ⟨3814562430356162624702093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2543041620237441749801395 3814562430356162624702093)
                  ·
                    refine ⟨1430460911383560984263285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3814562430356162624702093 1430460911383560984263285)
                    ·
                      rfl

theorem cell22_4178719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 3, 2, 1, 3].length) (baseStart_4178719 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4178719 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4178719 prefixEnd_4178719 := by exact prefixLift 4178719
  have htrace : WordTrace (prefixWord ++ tailWord_4178719) baseStart_4178719 baseEnd_4178719 := by
    simpa [prefixWord, tailWord_4178719, baseEnd_4178719] using wordTrace_append hprefix tailTrace_4178719
  have hstable : (prefixWord ++ tailWord_4178719).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4178719).length < 2 ^ (prefixWord ++ tailWord_4178719).sum := by decide
  have hdescent : baseEnd_4178719 < baseStart_4178719 := by decide
  rcases family_descends (prefixWord ++ tailWord_4178719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4178760 : List Nat := [2, 1, 3, 1, 1, 3, 2, 5, 4]
def baseStart_4178760 : Nat := 118140960795 + 4178760 * 2 ^ 59
def prefixEnd_4178760 : Nat := 4983230072969 + 3 ^ 40 * 4178760 * 2
def baseEnd_4178760 : Nat := 476824982173816847996053

theorem tailTrace_4178760 : CollatzResearch.WordTrace tailWord_4178760 prefixEnd_4178760 476824982173816847996053 := by
  unfold tailWord_4178760
  simp only [CollatzResearch.WordTrace]
  refine ⟨76205949170536835117254867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101607932227382446823006489 76205949170536835117254867)
  ·
    refine ⟨114308923755805252675882301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76205949170536835117254867 114308923755805252675882301)
    ·
      refine ⟨42865846408426969753455863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114308923755805252675882301 42865846408426969753455863)
      ·
        refine ⟨64298769612640454630183795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42865846408426969753455863 64298769612640454630183795)
        ·
          refine ⟨96448154418960681945275693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64298769612640454630183795 96448154418960681945275693)
          ·
            refine ⟨36168057907110255729478385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96448154418960681945275693 36168057907110255729478385)
            ·
              refine ⟨27126043430332691797108789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36168057907110255729478385 27126043430332691797108789)
              ·
                refine ⟨2543066571593689855978949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 27126043430332691797108789 2543066571593689855978949)
                ·
                  refine ⟨476824982173816847996053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2543066571593689855978949 476824982173816847996053)
                  ·
                    rfl

theorem cell22_4178760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 5, 4].length) (baseStart_4178760 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4178760 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4178760 prefixEnd_4178760 := by exact prefixLift 4178760
  have htrace : WordTrace (prefixWord ++ tailWord_4178760) baseStart_4178760 baseEnd_4178760 := by
    simpa [prefixWord, tailWord_4178760, baseEnd_4178760] using wordTrace_append hprefix tailTrace_4178760
  have hstable : (prefixWord ++ tailWord_4178760).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4178760).length < 2 ^ (prefixWord ++ tailWord_4178760).sum := by decide
  have hdescent : baseEnd_4178760 < baseStart_4178760 := by decide
  rcases family_descends (prefixWord ++ tailWord_4178760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4178777 : List Nat := [1, 2, 1, 2, 2, 4, 4, 2, 4]
def baseStart_4178777 : Nat := 118140960795 + 4178777 * 2 ^ 59
def prefixEnd_4178777 : Nat := 4983230072969 + 3 ^ 40 * 4178777 * 2
def baseEnd_4178777 : Nat := 476826921989622722104369

theorem tailTrace_4178777 : CollatzResearch.WordTrace tailWord_4178777 prefixEnd_4178777 476826921989622722104369 := by
  unfold tailWord_4178777
  simp only [CollatzResearch.WordTrace]
  refine ⟨152412518382012082137878585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101608345588008054758585723 152412518382012082137878585)
  ·
    refine ⟨114309388786509061603408939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152412518382012082137878585 114309388786509061603408939)
    ·
      refine ⟨171464083179763592405113409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114309388786509061603408939 171464083179763592405113409)
      ·
        refine ⟨128598062384822694303835057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171464083179763592405113409 128598062384822694303835057)
        ·
          refine ⟨96448546788617020727876293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128598062384822694303835057 96448546788617020727876293)
          ·
            refine ⟨18084102522865691386476805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 96448546788617020727876293 18084102522865691386476805)
            ·
              refine ⟨3390769223037317134964401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18084102522865691386476805 3390769223037317134964401)
              ·
                refine ⟨2543076917277987851223301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3390769223037317134964401 2543076917277987851223301)
                ·
                  refine ⟨476826921989622722104369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2543076917277987851223301 476826921989622722104369)
                  ·
                    rfl

theorem cell22_4178777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 4, 2, 4].length) (baseStart_4178777 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4178777 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4178777 prefixEnd_4178777 := by exact prefixLift 4178777
  have htrace : WordTrace (prefixWord ++ tailWord_4178777) baseStart_4178777 baseEnd_4178777 := by
    simpa [prefixWord, tailWord_4178777, baseEnd_4178777] using wordTrace_append hprefix tailTrace_4178777
  have hstable : (prefixWord ++ tailWord_4178777).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4178777).length < 2 ^ (prefixWord ++ tailWord_4178777).sum := by decide
  have hdescent : baseEnd_4178777 < baseStart_4178777 := by decide
  rcases family_descends (prefixWord ++ tailWord_4178777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4178792 : List Nat := [2, 1, 4, 2, 1, 2, 2, 3, 2, 3]
def baseStart_4178792 : Nat := 118140960795 + 4178792 * 2 ^ 59
def prefixEnd_4178792 : Nat := 4983230072969 + 3 ^ 40 * 4178792 * 2
def baseEnd_4178792 : Nat := 1430485900775413127188061

theorem tailTrace_4178792 : CollatzResearch.WordTrace tailWord_4178792 prefixEnd_4178792 1430485900775413127188061 := by
  unfold tailWord_4178792
  simp only [CollatzResearch.WordTrace]
  refine ⟨76206532738478869849837315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101608710317971826466449753 76206532738478869849837315)
  ·
    refine ⟨114309799107718304774755973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76206532738478869849837315 114309799107718304774755973)
    ·
      refine ⟨21433087332697182145266745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 114309799107718304774755973 21433087332697182145266745)
      ·
        refine ⟨16074815499522886608950059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21433087332697182145266745 16074815499522886608950059)
        ·
          refine ⟨24112223249284329913425089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16074815499522886608950059 24112223249284329913425089)
          ·
            refine ⟨18084167436963247435068817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24112223249284329913425089 18084167436963247435068817)
            ·
              refine ⟨13563125577722435576301613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18084167436963247435068817 13563125577722435576301613)
              ·
                refine ⟨5086172091645913341113105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13563125577722435576301613 5086172091645913341113105)
                ·
                  refine ⟨3814629068734435005834829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5086172091645913341113105 3814629068734435005834829)
                  ·
                    refine ⟨1430485900775413127188061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3814629068734435005834829 1430485900775413127188061)
                    ·
                      rfl

theorem cell22_4178792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 2, 3, 2, 3].length) (baseStart_4178792 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4178792 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4178792 prefixEnd_4178792 := by exact prefixLift 4178792
  have htrace : WordTrace (prefixWord ++ tailWord_4178792) baseStart_4178792 baseEnd_4178792 := by
    simpa [prefixWord, tailWord_4178792, baseEnd_4178792] using wordTrace_append hprefix tailTrace_4178792
  have hstable : (prefixWord ++ tailWord_4178792).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4178792).length < 2 ^ (prefixWord ++ tailWord_4178792).sum := by decide
  have hdescent : baseEnd_4178792 < baseStart_4178792 := by decide
  rcases family_descends (prefixWord ++ tailWord_4178792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4178820 : List Nat := [2, 3, 2, 1, 1, 1, 1, 1, 7, 3]
def baseStart_4178820 : Nat := 118140960795 + 4178820 * 2 ^ 59
def prefixEnd_4178820 : Nat := 4983230072969 + 3 ^ 40 * 4178820 * 2
def baseEnd_4178820 : Nat := 1430495485747630387487975

theorem tailTrace_4178820 : CollatzResearch.WordTrace tailWord_4178820 prefixEnd_4178820 1430495485747630387487975 := by
  unfold tailWord_4178820
  simp only [CollatzResearch.WordTrace]
  refine ⟨76207043360428150240846957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101609391147237533654462609 76207043360428150240846957)
  ·
    refine ⟨28577641260160556340317609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76207043360428150240846957 28577641260160556340317609)
    ·
      refine ⟨21433230945120417255238207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28577641260160556340317609 21433230945120417255238207)
      ·
        refine ⟨32149846417680625882857311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21433230945120417255238207 32149846417680625882857311)
        ·
          refine ⟨48224769626520938824285967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32149846417680625882857311 48224769626520938824285967)
          ·
            refine ⟨72337154439781408236428951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48224769626520938824285967 72337154439781408236428951)
            ·
              refine ⟨108505731659672112354643427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72337154439781408236428951 108505731659672112354643427)
              ·
                refine ⟨162758597489508168531965141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108505731659672112354643427 162758597489508168531965141)
                ·
                  refine ⟨3814654628660347699967933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 162758597489508168531965141 3814654628660347699967933)
                  ·
                    refine ⟨1430495485747630387487975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3814654628660347699967933 1430495485747630387487975)
                    ·
                      rfl

theorem cell22_4178820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 1, 7, 3].length) (baseStart_4178820 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4178820 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4178820 prefixEnd_4178820 := by exact prefixLift 4178820
  have htrace : WordTrace (prefixWord ++ tailWord_4178820) baseStart_4178820 baseEnd_4178820 := by
    simpa [prefixWord, tailWord_4178820, baseEnd_4178820] using wordTrace_append hprefix tailTrace_4178820
  have hstable : (prefixWord ++ tailWord_4178820).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4178820).length < 2 ^ (prefixWord ++ tailWord_4178820).sum := by decide
  have hdescent : baseEnd_4178820 < baseStart_4178820 := by decide
  rcases family_descends (prefixWord ++ tailWord_4178820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4178837 : List Nat := [1, 3, 2, 1, 1, 5, 2, 1, 3, 3]
def baseStart_4178837 : Nat := 118140960795 + 4178837 * 2 ^ 59
def prefixEnd_4178837 : Nat := 4983230072969 + 3 ^ 40 * 4178837 * 2
def baseEnd_4178837 : Nat := 1430501305195048009812923

theorem tailTrace_4178837 : CollatzResearch.WordTrace tailWord_4178837 prefixEnd_4178837 1430501305195048009812923 := by
  unfold tailWord_4178837
  simp only [CollatzResearch.WordTrace]
  refine ⟨152414706761794712385062765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101609804507863141590041843 152414706761794712385062765)
  ·
    refine ⟨57155515035673017144398537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152414706761794712385062765 57155515035673017144398537)
    ·
      refine ⟨42866636276754762858298903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57155515035673017144398537 42866636276754762858298903)
      ·
        refine ⟨64299954415132144287448355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42866636276754762858298903 64299954415132144287448355)
        ·
          refine ⟨96449931622698216431172533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64299954415132144287448355 96449931622698216431172533)
          ·
            refine ⟨9042181089627957790422425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 96449931622698216431172533 9042181089627957790422425)
            ·
              refine ⟨6781635817220968342816819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9042181089627957790422425 6781635817220968342816819)
              ·
                refine ⟨10172453725831452514225229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6781635817220968342816819 10172453725831452514225229)
                ·
                  refine ⟨3814670147186794692834461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10172453725831452514225229 3814670147186794692834461)
                  ·
                    refine ⟨1430501305195048009812923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3814670147186794692834461 1430501305195048009812923)
                    ·
                      rfl

theorem cell22_4178837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 2, 1, 3, 3].length) (baseStart_4178837 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4178837 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4178837 prefixEnd_4178837 := by exact prefixLift 4178837
  have htrace : WordTrace (prefixWord ++ tailWord_4178837) baseStart_4178837 baseEnd_4178837 := by
    simpa [prefixWord, tailWord_4178837, baseEnd_4178837] using wordTrace_append hprefix tailTrace_4178837
  have hstable : (prefixWord ++ tailWord_4178837).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4178837).length < 2 ^ (prefixWord ++ tailWord_4178837).sum := by decide
  have hdescent : baseEnd_4178837 < baseStart_4178837 := by decide
  rcases family_descends (prefixWord ++ tailWord_4178837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4178895 : List Nat := [1, 1, 2, 1, 1, 6, 3, 1, 6]
def baseStart_4178895 : Nat := 118140960795 + 4178895 * 2 ^ 59
def prefixEnd_4178895 : Nat := 4983230072969 + 3 ^ 40 * 4178895 * 2
def baseEnd_4178895 : Nat := 476840386593451730620915

theorem tailTrace_4178895 : CollatzResearch.WordTrace tailWord_4178895 prefixEnd_4178895 476840386593451730620915 := by
  unfold tailWord_4178895
  simp only [CollatzResearch.WordTrace]
  refine ⟨152416822195584588290674139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101611214797056392193782759 152416822195584588290674139)
  ·
    refine ⟨228625233293376882436011209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152416822195584588290674139 228625233293376882436011209)
    ·
      refine ⟨171468924970032661827008407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 228625233293376882436011209 171468924970032661827008407)
      ·
        refine ⟨257203387455048992740512611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171468924970032661827008407 257203387455048992740512611)
        ·
          refine ⟨385805081182573489110768917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 257203387455048992740512611 385805081182573489110768917)
          ·
            refine ⟨18084613180433132302067293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 385805081182573489110768917 18084613180433132302067293)
            ·
              refine ⟨6781729942662424613275235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18084613180433132302067293 6781729942662424613275235)
              ·
                refine ⟨10172594913993636919912853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6781729942662424613275235 10172594913993636919912853)
                ·
                  refine ⟨476840386593451730620915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10172594913993636919912853 476840386593451730620915)
                  ·
                    rfl

theorem cell22_4178895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 3, 1, 6].length) (baseStart_4178895 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4178895 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4178895 prefixEnd_4178895 := by exact prefixLift 4178895
  have htrace : WordTrace (prefixWord ++ tailWord_4178895) baseStart_4178895 baseEnd_4178895 := by
    simpa [prefixWord, tailWord_4178895, baseEnd_4178895] using wordTrace_append hprefix tailTrace_4178895
  have hstable : (prefixWord ++ tailWord_4178895).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4178895).length < 2 ^ (prefixWord ++ tailWord_4178895).sum := by decide
  have hdescent : baseEnd_4178895 < baseStart_4178895 := by decide
  rcases family_descends (prefixWord ++ tailWord_4178895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4178901 : List Nat := [1, 3, 2, 3, 4, 1, 2, 1, 5]
def baseStart_4178901 : Nat := 118140960795 + 4178901 * 2 ^ 59
def prefixEnd_4178901 : Nat := 4983230072969 + 3 ^ 40 * 4178901 * 2
def baseEnd_4178901 : Nat := 476841071234324392070909

theorem tailTrace_4178901 : CollatzResearch.WordTrace tailWord_4178901 prefixEnd_4178901 476841071234324392070909 := by
  unfold tailWord_4178901
  simp only [CollatzResearch.WordTrace]
  refine ⟨152417041033562851315392557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101611360689041900876928371 152417041033562851315392557)
  ·
    refine ⟨57156390387586069243272209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152417041033562851315392557 57156390387586069243272209)
    ·
      refine ⟨42867292790689551932454157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57156390387586069243272209 42867292790689551932454157)
      ·
        refine ⟨16075234796508581974670309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42867292790689551932454157 16075234796508581974670309)
        ·
          refine ⟨3014106524345359120250683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16075234796508581974670309 3014106524345359120250683)
          ·
            refine ⟨4521159786518038680376025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3014106524345359120250683 4521159786518038680376025)
            ·
              refine ⟨3390869839888529010282019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4521159786518038680376025 3390869839888529010282019)
              ·
                refine ⟨5086304759832793515423029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3390869839888529010282019 5086304759832793515423029)
                ·
                  refine ⟨476841071234324392070909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5086304759832793515423029 476841071234324392070909)
                  ·
                    rfl

theorem cell22_4178901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 4, 1, 2, 1, 5].length) (baseStart_4178901 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4178901 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4178901 prefixEnd_4178901 := by exact prefixLift 4178901
  have htrace : WordTrace (prefixWord ++ tailWord_4178901) baseStart_4178901 baseEnd_4178901 := by
    simpa [prefixWord, tailWord_4178901, baseEnd_4178901] using wordTrace_append hprefix tailTrace_4178901
  have hstable : (prefixWord ++ tailWord_4178901).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4178901).length < 2 ^ (prefixWord ++ tailWord_4178901).sum := by decide
  have hdescent : baseEnd_4178901 < baseStart_4178901 := by decide
  rcases family_descends (prefixWord ++ tailWord_4178901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4178914 : List Nat := [3, 3, 3, 1, 1, 2, 1, 1, 3, 4]
def baseStart_4178914 : Nat := 118140960795 + 4178914 * 2 ^ 59
def prefixEnd_4178914 : Nat := 4983230072969 + 3 ^ 40 * 4178914 * 2
def baseEnd_4178914 : Nat := 1430527663868645475637687

theorem tailTrace_4178914 : CollatzResearch.WordTrace tailWord_4178914 prefixEnd_4178914 1430527663868645475637687 := by
  unfold tailWord_4178914
  simp only [CollatzResearch.WordTrace]
  refine ⟨38104378795628938633903949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101611676788343836357077197 38104378795628938633903949)
  ·
    refine ⟨14289142048360851987713981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38104378795628938633903949 14289142048360851987713981)
    ·
      refine ⟨5358428268135319495392743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14289142048360851987713981 5358428268135319495392743)
      ·
        refine ⟨8037642402202979243089115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5358428268135319495392743 8037642402202979243089115)
        ·
          refine ⟨12056463603304468864633673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8037642402202979243089115 12056463603304468864633673)
          ·
            refine ⟨9042347702478351648475255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12056463603304468864633673 9042347702478351648475255)
            ·
              refine ⟨13563521553717527472712883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9042347702478351648475255 13563521553717527472712883)
              ·
                refine ⟨20345282330576291209069325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13563521553717527472712883 20345282330576291209069325)
                ·
                  refine ⟨7629480873966109203400997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20345282330576291209069325 7629480873966109203400997)
                  ·
                    refine ⟨1430527663868645475637687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7629480873966109203400997 1430527663868645475637687)
                    ·
                      rfl

theorem cell22_4178914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 1, 1, 3, 4].length) (baseStart_4178914 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4178914 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4178914 prefixEnd_4178914 := by exact prefixLift 4178914
  have htrace : WordTrace (prefixWord ++ tailWord_4178914) baseStart_4178914 baseEnd_4178914 := by
    simpa [prefixWord, tailWord_4178914, baseEnd_4178914] using wordTrace_append hprefix tailTrace_4178914
  have hstable : (prefixWord ++ tailWord_4178914).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4178914).length < 2 ^ (prefixWord ++ tailWord_4178914).sum := by decide
  have hdescent : baseEnd_4178914 < baseStart_4178914 := by decide
  rcases family_descends (prefixWord ++ tailWord_4178914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4178970 : List Nat := [3, 1, 1, 3, 1, 2, 1, 2, 2, 6]
def baseStart_4178970 : Nat := 118140960795 + 4178970 * 2 ^ 59
def prefixEnd_4178970 : Nat := 4983230072969 + 3 ^ 40 * 4178970 * 2
def baseEnd_4178970 : Nat := 1430546833813079996237515

theorem tailTrace_4178970 : CollatzResearch.WordTrace tailWord_4178970 prefixEnd_4178970 1430546833813079996237515 := by
  unfold tailWord_4178970
  simp only [CollatzResearch.WordTrace]
  refine ⟨38104889417578219024913591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101613038446875250733102909 38104889417578219024913591)
  ·
    refine ⟨57157334126367328537370387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38104889417578219024913591 57157334126367328537370387)
    ·
      refine ⟨85736001189550992806055581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57157334126367328537370387 85736001189550992806055581)
      ·
        refine ⟨32151000446081622302270843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85736001189550992806055581 32151000446081622302270843)
        ·
          refine ⟨48226500669122433453406265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32151000446081622302270843 48226500669122433453406265)
          ·
            refine ⟨36169875501841825090054699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48226500669122433453406265 36169875501841825090054699)
            ·
              refine ⟨54254813252762737635082049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36169875501841825090054699 54254813252762737635082049)
              ·
                refine ⟨40691109939572053226311537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54254813252762737635082049 40691109939572053226311537)
                ·
                  refine ⟨30518332454679039919733653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40691109939572053226311537 30518332454679039919733653)
                  ·
                    refine ⟨1430546833813079996237515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30518332454679039919733653 1430546833813079996237515)
                    ·
                      rfl

theorem cell22_4178970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 2, 2, 6].length) (baseStart_4178970 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4178970 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4178970 prefixEnd_4178970 := by exact prefixLift 4178970
  have htrace : WordTrace (prefixWord ++ tailWord_4178970) baseStart_4178970 baseEnd_4178970 := by
    simpa [prefixWord, tailWord_4178970, baseEnd_4178970] using wordTrace_append hprefix tailTrace_4178970
  have hstable : (prefixWord ++ tailWord_4178970).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4178970).length < 2 ^ (prefixWord ++ tailWord_4178970).sum := by decide
  have hdescent : baseEnd_4178970 < baseStart_4178970 := by decide
  rcases family_descends (prefixWord ++ tailWord_4178970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4178976 : List Nat := [2, 1, 1, 7, 1, 2, 1, 1, 2, 4]
def baseStart_4178976 : Nat := 118140960795 + 4178976 * 2 ^ 59
def prefixEnd_4178976 : Nat := 4983230072969 + 3 ^ 40 * 4178976 * 2
def baseEnd_4178976 : Nat := 1430548887735697980587497

theorem tailTrace_4178976 : CollatzResearch.WordTrace tailWord_4178976 prefixEnd_4178976 1430548887735697980587497 := by
  unfold tailWord_4178976
  simp only [CollatzResearch.WordTrace]
  refine ⟨76209888254145569562186391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101613184338860759416248521 76209888254145569562186391)
  ·
    refine ⟨114314832381218354343279587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76209888254145569562186391 114314832381218354343279587)
    ·
      refine ⟨171472248571827531514919381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114314832381218354343279587 171472248571827531514919381)
      ·
        refine ⟨4018880825902207769880923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 171472248571827531514919381 4018880825902207769880923)
        ·
          refine ⟨6028321238853311654821385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4018880825902207769880923 6028321238853311654821385)
          ·
            refine ⟨4521240929139983741116039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6028321238853311654821385 4521240929139983741116039)
            ·
              refine ⟨6781861393709975611674059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4521240929139983741116039 6781861393709975611674059)
              ·
                refine ⟨10172792090564963417511089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6781861393709975611674059 10172792090564963417511089)
                ·
                  refine ⟨7629594067923722563133317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10172792090564963417511089 7629594067923722563133317)
                  ·
                    refine ⟨1430548887735697980587497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7629594067923722563133317 1430548887735697980587497)
                    ·
                      rfl

theorem cell22_4178976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 2, 1, 1, 2, 4].length) (baseStart_4178976 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4178976 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4178976 prefixEnd_4178976 := by exact prefixLift 4178976
  have htrace : WordTrace (prefixWord ++ tailWord_4178976) baseStart_4178976 baseEnd_4178976 := by
    simpa [prefixWord, tailWord_4178976, baseEnd_4178976] using wordTrace_append hprefix tailTrace_4178976
  have hstable : (prefixWord ++ tailWord_4178976).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4178976).length < 2 ^ (prefixWord ++ tailWord_4178976).sum := by decide
  have hdescent : baseEnd_4178976 < baseStart_4178976 := by decide
  rcases family_descends (prefixWord ++ tailWord_4178976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4179002 : List Nat := [3, 1, 1, 1, 3, 1, 5, 2, 5]
def baseStart_4179002 : Nat := 118140960795 + 4179002 * 2 ^ 59
def prefixEnd_4179002 : Nat := 4983230072969 + 3 ^ 40 * 4179002 * 2
def baseEnd_4179002 : Nat := 476852596022347526479139

theorem tailTrace_4179002 : CollatzResearch.WordTrace tailWord_4179002 prefixEnd_4179002 476852596022347526479139 := by
  unfold tailWord_4179002
  simp only [CollatzResearch.WordTrace]
  refine ⟨38105181201549236391204815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101613816537464630376546173 38105181201549236391204815)
  ·
    refine ⟨57157771802323854586807223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38105181201549236391204815 57157771802323854586807223)
    ·
      refine ⟨85736657703485781880210835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57157771802323854586807223 85736657703485781880210835)
      ·
        refine ⟨128604986555228672820316253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85736657703485781880210835 128604986555228672820316253)
        ·
          refine ⟨48226869958210752307618595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 128604986555228672820316253 48226869958210752307618595)
          ·
            refine ⟨72340304937316128461427893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48226869958210752307618595 72340304937316128461427893)
            ·
              refine ⟨6781903587873387043258865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 72340304937316128461427893 6781903587873387043258865)
              ·
                refine ⟨5086427690905040282444149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6781903587873387043258865 5086427690905040282444149)
                ·
                  refine ⟨476852596022347526479139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5086427690905040282444149 476852596022347526479139)
                  ·
                    rfl

theorem cell22_4179002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 5, 2, 5].length) (baseStart_4179002 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4179002 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4179002 prefixEnd_4179002 := by exact prefixLift 4179002
  have htrace : WordTrace (prefixWord ++ tailWord_4179002) baseStart_4179002 baseEnd_4179002 := by
    simpa [prefixWord, tailWord_4179002, baseEnd_4179002] using wordTrace_append hprefix tailTrace_4179002
  have hstable : (prefixWord ++ tailWord_4179002).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4179002).length < 2 ^ (prefixWord ++ tailWord_4179002).sum := by decide
  have hdescent : baseEnd_4179002 < baseStart_4179002 := by decide
  rcases family_descends (prefixWord ++ tailWord_4179002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4179006 : List Nat := [4, 2, 1, 3, 1, 2, 2, 1, 3, 3]
def baseStart_4179006 : Nat := 118140960795 + 4179006 * 2 ^ 59
def prefixEnd_4179006 : Nat := 4983230072969 + 3 ^ 40 * 4179006 * 2
def baseEnd_4179006 : Nat := 1430559157348787902337405

theorem tailTrace_4179006 : CollatzResearch.WordTrace tailWord_4179006 prefixEnd_4179006 1430559157348787902337405 := by
  unfold tailWord_4179006
  simp only [CollatzResearch.WordTrace]
  refine ⟨19052608837272806780995609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 101613913798788302831976581 19052608837272806780995609)
  ·
    refine ⟨14289456627954605085746707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19052608837272806780995609 14289456627954605085746707)
    ·
      refine ⟨21434184941931907628620061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14289456627954605085746707 21434184941931907628620061)
      ·
        refine ⟨8037819353224465360732523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21434184941931907628620061 8037819353224465360732523)
        ·
          refine ⟨12056729029836698041098785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8037819353224465360732523 12056729029836698041098785)
          ·
            refine ⟨9042546772377523530824089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12056729029836698041098785 9042546772377523530824089)
            ·
              refine ⟨6781910079283142648118067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9042546772377523530824089 6781910079283142648118067)
              ·
                refine ⟨10172865118924713972177101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6781910079283142648118067 10172865118924713972177101)
                ·
                  refine ⟨3814824419596767739566413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10172865118924713972177101 3814824419596767739566413)
                  ·
                    refine ⟨1430559157348787902337405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3814824419596767739566413 1430559157348787902337405)
                    ·
                      rfl

theorem cell22_4179006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 2, 1, 3, 3].length) (baseStart_4179006 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4179006 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4179006 prefixEnd_4179006 := by exact prefixLift 4179006
  have htrace : WordTrace (prefixWord ++ tailWord_4179006) baseStart_4179006 baseEnd_4179006 := by
    simpa [prefixWord, tailWord_4179006, baseEnd_4179006] using wordTrace_append hprefix tailTrace_4179006
  have hstable : (prefixWord ++ tailWord_4179006).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4179006).length < 2 ^ (prefixWord ++ tailWord_4179006).sum := by decide
  have hdescent : baseEnd_4179006 < baseStart_4179006 := by decide
  rcases family_descends (prefixWord ++ tailWord_4179006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4179122 : List Nat := [3, 2, 1, 1, 1, 4, 1, 1, 2, 6]
def baseStart_4179122 : Nat := 118140960795 + 4179122 * 2 ^ 59
def prefixEnd_4179122 : Nat := 4983230072969 + 3 ^ 40 * 4179122 * 2
def baseEnd_4179122 : Nat := 1430598866519402266437049

theorem tailTrace_4179122 : CollatzResearch.WordTrace tailWord_4179122 prefixEnd_4179122 1430598866519402266437049 := by
  unfold tailWord_4179122
  simp only [CollatzResearch.WordTrace]
  refine ⟨38106275391440551514796905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101616734377174804039458413 38106275391440551514796905)
  ·
    refine ⟨28579706543580413636097679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38106275391440551514796905 28579706543580413636097679)
    ·
      refine ⟨42869559815370620454146519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28579706543580413636097679 42869559815370620454146519)
      ·
        refine ⟨64304339723055930681219779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42869559815370620454146519 64304339723055930681219779)
        ·
          refine ⟨96456509584583896021829669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64304339723055930681219779 96456509584583896021829669)
          ·
            refine ⟨18085595547109480504093063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 96456509584583896021829669 18085595547109480504093063)
            ·
              refine ⟨27128393320664220756139595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18085595547109480504093063 27128393320664220756139595)
              ·
                refine ⟨40692589980996331134209393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27128393320664220756139595 40692589980996331134209393)
                ·
                  refine ⟨30519442485747248350657045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40692589980996331134209393 30519442485747248350657045)
                  ·
                    refine ⟨1430598866519402266437049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30519442485747248350657045 1430598866519402266437049)
                    ·
                      rfl

theorem cell22_4179122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 1, 2, 6].length) (baseStart_4179122 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4179122 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4179122 prefixEnd_4179122 := by exact prefixLift 4179122
  have htrace : WordTrace (prefixWord ++ tailWord_4179122) baseStart_4179122 baseEnd_4179122 := by
    simpa [prefixWord, tailWord_4179122, baseEnd_4179122] using wordTrace_append hprefix tailTrace_4179122
  have hstable : (prefixWord ++ tailWord_4179122).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4179122).length < 2 ^ (prefixWord ++ tailWord_4179122).sum := by decide
  have hdescent : baseEnd_4179122 < baseStart_4179122 := by decide
  rcases family_descends (prefixWord ++ tailWord_4179122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4179201 : List Nat := [1, 2, 4, 1, 1, 4, 2, 2, 1, 4]
def baseStart_4179201 : Nat := 118140960795 + 4179201 * 2 ^ 59
def prefixEnd_4179201 : Nat := 4983230072969 + 3 ^ 40 * 4179201 * 2
def baseEnd_4179201 : Nat := 1430625909833872393711807

theorem tailTrace_4179201 : CollatzResearch.WordTrace tailWord_4179201 prefixEnd_4179201 1430625909833872393711807 := by
  unfold tailWord_4179201
  simp only [CollatzResearch.WordTrace]
  refine ⟨152427982932476002551313457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101618655288317335034208971 152427982932476002551313457)
  ·
    refine ⟨114320987199357001913485093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152427982932476002551313457 114320987199357001913485093)
    ·
      refine ⟨21435185099879437858778455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 114320987199357001913485093 21435185099879437858778455)
      ·
        refine ⟨32152777649819156788167683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21435185099879437858778455 32152777649819156788167683)
        ·
          refine ⟨48229166474728735182251525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32152777649819156788167683 48229166474728735182251525)
          ·
            refine ⟨9042968714011637846672161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48229166474728735182251525 9042968714011637846672161)
            ·
              refine ⟨6782226535508728385004121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9042968714011637846672161 6782226535508728385004121)
              ·
                refine ⟨5086669901631546288753091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6782226535508728385004121 5086669901631546288753091)
                ·
                  refine ⟨7630004852447319433129637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5086669901631546288753091 7630004852447319433129637)
                  ·
                    refine ⟨1430625909833872393711807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7630004852447319433129637 1430625909833872393711807)
                    ·
                      rfl

theorem cell22_4179201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 2, 2, 1, 4].length) (baseStart_4179201 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4179201 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4179201 prefixEnd_4179201 := by exact prefixLift 4179201
  have htrace : WordTrace (prefixWord ++ tailWord_4179201) baseStart_4179201 baseEnd_4179201 := by
    simpa [prefixWord, tailWord_4179201, baseEnd_4179201] using wordTrace_append hprefix tailTrace_4179201
  have hstable : (prefixWord ++ tailWord_4179201).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4179201).length < 2 ^ (prefixWord ++ tailWord_4179201).sum := by decide
  have hdescent : baseEnd_4179201 < baseStart_4179201 := by decide
  rcases family_descends (prefixWord ++ tailWord_4179201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4179289 : List Nat := [1, 2, 1, 2, 2, 2, 3, 4, 5]
def baseStart_4179289 : Nat := 118140960795 + 4179289 * 2 ^ 59
def prefixEnd_4179289 : Nat := 4983230072969 + 3 ^ 40 * 4179289 * 2
def baseEnd_4179289 : Nat := 476885344677423165837179

theorem tailTrace_4179289 : CollatzResearch.WordTrace tailWord_4179289 prefixEnd_4179289 476885344677423165837179 := by
  unfold tailWord_4179289
  simp only [CollatzResearch.WordTrace]
  refine ⟨152431192556157193580516921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101620795037438129053677947 152431192556157193580516921)
  ·
    refine ⟨114323394417117895185387691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152431192556157193580516921 114323394417117895185387691)
    ·
      refine ⟨171485091625676842778081537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114323394417117895185387691 171485091625676842778081537)
      ·
        refine ⟨128613818719257632083561153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171485091625676842778081537 128613818719257632083561153)
        ·
          refine ⟨96460364039443224062670865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128613818719257632083561153 96460364039443224062670865)
          ·
            refine ⟨72345273029582418047003149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96460364039443224062670865 72345273029582418047003149)
            ·
              refine ⟨27129477386093406767626181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72345273029582418047003149 27129477386093406767626181)
              ·
                refine ⟨5086777009892513768929909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27129477386093406767626181 5086777009892513768929909)
                ·
                  refine ⟨476885344677423165837179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5086777009892513768929909 476885344677423165837179)
                  ·
                    rfl

theorem cell22_4179289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 4, 5].length) (baseStart_4179289 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4179289 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4179289 prefixEnd_4179289 := by exact prefixLift 4179289
  have htrace : WordTrace (prefixWord ++ tailWord_4179289) baseStart_4179289 baseEnd_4179289 := by
    simpa [prefixWord, tailWord_4179289, baseEnd_4179289] using wordTrace_append hprefix tailTrace_4179289
  have hstable : (prefixWord ++ tailWord_4179289).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4179289).length < 2 ^ (prefixWord ++ tailWord_4179289).sum := by decide
  have hdescent : baseEnd_4179289 < baseStart_4179289 := by decide
  rcases family_descends (prefixWord ++ tailWord_4179289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4179310 : List Nat := [4, 1, 2, 4, 1, 1, 1, 2, 3, 3]
def baseStart_4179310 : Nat := 118140960795 + 4179310 * 2 ^ 59
def prefixEnd_4179310 : Nat := 4983230072969 + 3 ^ 40 * 4179310 * 2
def baseEnd_4179310 : Nat := 1430663222761432442736473

theorem tailTrace_4179310 : CollatzResearch.WordTrace tailWord_4179310 prefixEnd_4179310 1430663222761432442736473 := by
  unfold tailWord_4179310
  simp only [CollatzResearch.WordTrace]
  refine ⟨19053994811135139270878923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 101621305659387409444687589 19053994811135139270878923)
  ·
    refine ⟨28580992216702708906318385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19053994811135139270878923 28580992216702708906318385)
    ·
      refine ⟨21435744162527031679738789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28580992216702708906318385 21435744162527031679738789)
      ·
        refine ⟨4019202030473818439951023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21435744162527031679738789 4019202030473818439951023)
        ·
          refine ⟨6028803045710727659926535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4019202030473818439951023 6028803045710727659926535)
          ·
            refine ⟨9043204568566091489889803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6028803045710727659926535 9043204568566091489889803)
            ·
              refine ⟨13564806852849137234834705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9043204568566091489889803 13564806852849137234834705)
              ·
                refine ⟨10173605139636852926126029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13564806852849137234834705 10173605139636852926126029)
                ·
                  refine ⟨3815101927363819847297261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10173605139636852926126029 3815101927363819847297261)
                  ·
                    refine ⟨1430663222761432442736473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3815101927363819847297261 1430663222761432442736473)
                    ·
                      rfl

theorem cell22_4179310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 1, 2, 3, 3].length) (baseStart_4179310 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4179310 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4179310 prefixEnd_4179310 := by exact prefixLift 4179310
  have htrace : WordTrace (prefixWord ++ tailWord_4179310) baseStart_4179310 baseEnd_4179310 := by
    simpa [prefixWord, tailWord_4179310, baseEnd_4179310] using wordTrace_append hprefix tailTrace_4179310
  have hstable : (prefixWord ++ tailWord_4179310).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4179310).length < 2 ^ (prefixWord ++ tailWord_4179310).sum := by decide
  have hdescent : baseEnd_4179310 < baseStart_4179310 := by decide
  rcases family_descends (prefixWord ++ tailWord_4179310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4179319 : List Nat := [1, 1, 3, 1, 1, 2, 3, 3, 3, 4]
def baseStart_4179319 : Nat := 118140960795 + 4179319 * 2 ^ 59
def prefixEnd_4179319 : Nat := 4983230072969 + 3 ^ 40 * 4179319 * 2
def baseEnd_4179319 : Nat := 1430666303645359419261445

theorem tailTrace_4179319 : CollatzResearch.WordTrace tailWord_4179319 prefixEnd_4179319 1430666303645359419261445 := by
  unfold tailWord_4179319
  simp only [CollatzResearch.WordTrace]
  refine ⟨152432286746048508704109011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101621524497365672469406007 152432286746048508704109011)
  ·
    refine ⟨228648430119072763056163517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152432286746048508704109011 228648430119072763056163517)
    ·
      refine ⟨85743161294652286146061319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 228648430119072763056163517 85743161294652286146061319)
      ·
        refine ⟨128614741941978429219091979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85743161294652286146061319 128614741941978429219091979)
        ·
          refine ⟨192922112912967643828637969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128614741941978429219091979 192922112912967643828637969)
          ·
            refine ⟨144691584684725732871478477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 192922112912967643828637969 144691584684725732871478477)
            ·
              refine ⟨54259344256772149826804429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 144691584684725732871478477 54259344256772149826804429)
              ·
                refine ⟨20347254096289556185051661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54259344256772149826804429 20347254096289556185051661)
                ·
                  refine ⟨7630220286108583569394373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20347254096289556185051661 7630220286108583569394373)
                  ·
                    refine ⟨1430666303645359419261445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7630220286108583569394373 1430666303645359419261445)
                    ·
                      rfl

theorem cell22_4179319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 3, 3, 4].length) (baseStart_4179319 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4179319 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4179319 prefixEnd_4179319 := by exact prefixLift 4179319
  have htrace : WordTrace (prefixWord ++ tailWord_4179319) baseStart_4179319 baseEnd_4179319 := by
    simpa [prefixWord, tailWord_4179319, baseEnd_4179319] using wordTrace_append hprefix tailTrace_4179319
  have hstable : (prefixWord ++ tailWord_4179319).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4179319).length < 2 ^ (prefixWord ++ tailWord_4179319).sum := by decide
  have hdescent : baseEnd_4179319 < baseStart_4179319 := by decide
  rcases family_descends (prefixWord ++ tailWord_4179319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4179349 : List Nat := [1, 3, 2, 1, 1, 2, 2, 2, 3, 5]
def baseStart_4179349 : Nat := 118140960795 + 4179349 * 2 ^ 59
def prefixEnd_4179349 : Nat := 4983230072969 + 3 ^ 40 * 4179349 * 2
def baseEnd_4179349 : Nat := 1430676573258449341011353

theorem tailTrace_4179349 : CollatzResearch.WordTrace tailWord_4179349 prefixEnd_4179349 1430676573258449341011353 := by
  unfold tailWord_4179349
  simp only [CollatzResearch.WordTrace]
  refine ⟨152433380935939823827701101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101622253957293215885134067 152433380935939823827701101)
  ·
    refine ⟨57162517850977433935387913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152433380935939823827701101 57162517850977433935387913)
    ·
      refine ⟨42871888388233075451540935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57162517850977433935387913 42871888388233075451540935)
      ·
        refine ⟨64307832582349613177311403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42871888388233075451540935 64307832582349613177311403)
        ·
          refine ⟨96461748873524419765967105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64307832582349613177311403 96461748873524419765967105)
          ·
            refine ⟨72346311655143314824475329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96461748873524419765967105 72346311655143314824475329)
            ·
              refine ⟨54259733741357486118356497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72346311655143314824475329 54259733741357486118356497)
              ·
                refine ⟨40694800306018114588767373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54259733741357486118356497 40694800306018114588767373)
                ·
                  refine ⟨15260550114756792970787765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40694800306018114588767373 15260550114756792970787765)
                  ·
                    refine ⟨1430676573258449341011353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15260550114756792970787765 1430676573258449341011353)
                    ·
                      rfl

theorem cell22_4179349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 2, 3, 5].length) (baseStart_4179349 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4179349 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4179349 prefixEnd_4179349 := by exact prefixLift 4179349
  have htrace : WordTrace (prefixWord ++ tailWord_4179349) baseStart_4179349 baseEnd_4179349 := by
    simpa [prefixWord, tailWord_4179349, baseEnd_4179349] using wordTrace_append hprefix tailTrace_4179349
  have hstable : (prefixWord ++ tailWord_4179349).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4179349).length < 2 ^ (prefixWord ++ tailWord_4179349).sum := by decide
  have hdescent : baseEnd_4179349 < baseStart_4179349 := by decide
  rcases family_descends (prefixWord ++ tailWord_4179349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4179381 : List Nat := [1, 3, 3, 2, 2, 1, 2, 1, 1, 6]
def baseStart_4179381 : Nat := 118140960795 + 4179381 * 2 ^ 59
def prefixEnd_4179381 : Nat := 4983230072969 + 3 ^ 40 * 4179381 * 2
def baseEnd_4179381 : Nat := 1430687527512411924211255

theorem tailTrace_4179381 : CollatzResearch.WordTrace tailWord_4179381 prefixEnd_4179381 1430687527512411924211255 := by
  unfold tailWord_4179381
  simp only [CollatzResearch.WordTrace]
  refine ⟨152434548071823893292865997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101623032047882595528577331 152434548071823893292865997)
  ·
    refine ⟨57162955526933959984824749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152434548071823893292865997 57162955526933959984824749)
    ·
      refine ⟨21436108322600234994309281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57162955526933959984824749 21436108322600234994309281)
      ·
        refine ⟨16077081241950176245731961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21436108322600234994309281 16077081241950176245731961)
        ·
          refine ⟨12057810931462632184298971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16077081241950176245731961 12057810931462632184298971)
          ·
            refine ⟨18086716397193948276448457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12057810931462632184298971 18086716397193948276448457)
            ·
              refine ⟨13565037297895461207336343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18086716397193948276448457 13565037297895461207336343)
              ·
                refine ⟨20347555946843191811004515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13565037297895461207336343 20347555946843191811004515)
                ·
                  refine ⟨30521333920264787716506773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20347555946843191811004515 30521333920264787716506773)
                  ·
                    refine ⟨1430687527512411924211255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30521333920264787716506773 1430687527512411924211255)
                    ·
                      rfl

theorem cell22_4179381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 2, 1, 1, 6].length) (baseStart_4179381 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4179381 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4179381 prefixEnd_4179381 := by exact prefixLift 4179381
  have htrace : WordTrace (prefixWord ++ tailWord_4179381) baseStart_4179381 baseEnd_4179381 := by
    simpa [prefixWord, tailWord_4179381, baseEnd_4179381] using wordTrace_append hprefix tailTrace_4179381
  have hstable : (prefixWord ++ tailWord_4179381).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4179381).length < 2 ^ (prefixWord ++ tailWord_4179381).sum := by decide
  have hdescent : baseEnd_4179381 < baseStart_4179381 := by decide
  rcases family_descends (prefixWord ++ tailWord_4179381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4179385 : List Nat := [1, 2, 1, 4, 4, 2, 1, 3, 4]
def baseStart_4179385 : Nat := 118140960795 + 4179385 * 2 ^ 59
def prefixEnd_4179385 : Nat := 4983230072969 + 3 ^ 40 * 4179385 * 2
def baseEnd_4179385 : Nat := 476896298931385749037081

theorem tailTrace_4179385 : CollatzResearch.WordTrace tailWord_4179385 prefixEnd_4179385 476896298931385749037081 := by
  unfold tailWord_4179385
  simp only [CollatzResearch.WordTrace]
  refine ⟨152434693963809401976011609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101623129309206267984007739 152434693963809401976011609)
  ·
    refine ⟨114326020472857051482008707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152434693963809401976011609 114326020472857051482008707)
    ·
      refine ⟨171489030709285577223013061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114326020472857051482008707 171489030709285577223013061)
      ·
        refine ⟨32154193257991045729314949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 171489030709285577223013061 32154193257991045729314949)
        ·
          refine ⟨6028911235873321074246553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32154193257991045729314949 6028911235873321074246553)
          ·
            refine ⟨4521683426904990805684915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6028911235873321074246553 4521683426904990805684915)
            ·
              refine ⟨6782525140357486208527373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4521683426904990805684915 6782525140357486208527373)
              ·
                refine ⟨2543446927634057328197765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6782525140357486208527373 2543446927634057328197765)
                ·
                  refine ⟨476896298931385749037081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2543446927634057328197765 476896298931385749037081)
                  ·
                    rfl

theorem cell22_4179385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 2, 1, 3, 4].length) (baseStart_4179385 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4179385 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4179385 prefixEnd_4179385 := by exact prefixLift 4179385
  have htrace : WordTrace (prefixWord ++ tailWord_4179385) baseStart_4179385 baseEnd_4179385 := by
    simpa [prefixWord, tailWord_4179385, baseEnd_4179385] using wordTrace_append hprefix tailTrace_4179385
  have hstable : (prefixWord ++ tailWord_4179385).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4179385).length < 2 ^ (prefixWord ++ tailWord_4179385).sum := by decide
  have hdescent : baseEnd_4179385 < baseStart_4179385 := by decide
  rcases family_descends (prefixWord ++ tailWord_4179385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4179396 : List Nat := [2, 3, 3, 2, 1, 1, 10]
def baseStart_4179396 : Nat := 118140960795 + 4179396 * 2 ^ 59
def prefixEnd_4179396 : Nat := 4983230072969 + 3 ^ 40 * 4179396 * 2
def baseEnd_4179396 : Nat := 52988617122924329077267

theorem tailTrace_4179396 : CollatzResearch.WordTrace tailWord_4179396 prefixEnd_4179396 52988617122924329077267 := by
  unfold tailWord_4179396
  simp only [CollatzResearch.WordTrace]
  refine ⟨76217547583384775427331021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101623396777846367236441361 76217547583384775427331021)
  ·
    refine ⟨28581580343769290785249133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76217547583384775427331021 28581580343769290785249133)
    ·
      refine ⟨10718092628913484044468425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28581580343769290785249133 10718092628913484044468425)
      ·
        refine ⟨8038569471685113033351319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10718092628913484044468425 8038569471685113033351319)
        ·
          refine ⟨12057854207527669550026979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8038569471685113033351319 12057854207527669550026979)
          ·
            refine ⟨18086781311291504325040469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12057854207527669550026979 18086781311291504325040469)
            ·
              refine ⟨52988617122924329077267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 18086781311291504325040469 52988617122924329077267)
              ·
                rfl

theorem cell22_4179396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 10].length) (baseStart_4179396 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4179396 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4179396 prefixEnd_4179396 := by exact prefixLift 4179396
  have htrace : WordTrace (prefixWord ++ tailWord_4179396) baseStart_4179396 baseEnd_4179396 := by
    simpa [prefixWord, tailWord_4179396, baseEnd_4179396] using wordTrace_append hprefix tailTrace_4179396
  have hstable : (prefixWord ++ tailWord_4179396).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4179396).length < 2 ^ (prefixWord ++ tailWord_4179396).sum := by decide
  have hdescent : baseEnd_4179396 < baseStart_4179396 := by decide
  rcases family_descends (prefixWord ++ tailWord_4179396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4179424 : List Nat := [2, 1, 1, 3, 1, 1, 2, 2, 9]
def baseStart_4179424 : Nat := 118140960795 + 4179424 * 2 ^ 59
def prefixEnd_4179424 : Nat := 4983230072969 + 3 ^ 40 * 4179424 * 2
def baseEnd_4179424 : Nat := 476900749097058048462041

theorem tailTrace_4179424 : CollatzResearch.WordTrace tailWord_4179424 prefixEnd_4179424 476900749097058048462041 := by
  unfold tailWord_4179424
  simp only [CollatzResearch.WordTrace]
  refine ⟨76218058205334055818340663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101624077607112074424454217 76218058205334055818340663)
  ·
    refine ⟨114327087308001083727510995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76218058205334055818340663 114327087308001083727510995)
    ·
      refine ⟨171490630962001625591266493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114327087308001083727510995 171490630962001625591266493)
      ·
        refine ⟨64308986610750609596724935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 171490630962001625591266493 64308986610750609596724935)
        ·
          refine ⟨96463479916125914395087403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64308986610750609596724935 96463479916125914395087403)
          ·
            refine ⟨144695219874188871592631105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96463479916125914395087403 144695219874188871592631105)
            ·
              refine ⟨108521414905641653694473329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 144695219874188871592631105 108521414905641653694473329)
              ·
                refine ⟨81391061179231240270854997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 108521414905641653694473329 81391061179231240270854997)
                ·
                  refine ⟨476900749097058048462041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 81391061179231240270854997 476900749097058048462041)
                  ·
                    rfl

theorem cell22_4179424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 2, 9].length) (baseStart_4179424 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4179424 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4179424 prefixEnd_4179424 := by exact prefixLift 4179424
  have htrace : WordTrace (prefixWord ++ tailWord_4179424) baseStart_4179424 baseEnd_4179424 := by
    simpa [prefixWord, tailWord_4179424, baseEnd_4179424] using wordTrace_append hprefix tailTrace_4179424
  have hstable : (prefixWord ++ tailWord_4179424).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4179424).length < 2 ^ (prefixWord ++ tailWord_4179424).sum := by decide
  have hdescent : baseEnd_4179424 < baseStart_4179424 := by decide
  rcases family_descends (prefixWord ++ tailWord_4179424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4179488 : List Nat := [2, 1, 1, 6, 1, 1, 2, 1, 3, 4]
def baseStart_4179488 : Nat := 118140960795 + 4179488 * 2 ^ 59
def prefixEnd_4179488 : Nat := 4983230072969 + 3 ^ 40 * 4179488 * 2
def baseEnd_4179488 : Nat := 1430724155799099311785927

theorem tailTrace_4179488 : CollatzResearch.WordTrace tailWord_4179488 prefixEnd_4179488 1430724155799099311785927 := by
  unfold tailWord_4179488
  simp only [CollatzResearch.WordTrace]
  refine ⟨76219225341218125283505559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101625633788290833711340745 76219225341218125283505559)
  ·
    refine ⟨114328838011827187925258339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76219225341218125283505559 114328838011827187925258339)
    ·
      refine ⟨171493257017740781887887509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114328838011827187925258339 171493257017740781887887509)
      ·
        refine ⟨8038746422706599150994727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 171493257017740781887887509 8038746422706599150994727)
        ·
          refine ⟨12058119634059898726492091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8038746422706599150994727 12058119634059898726492091)
          ·
            refine ⟨18087179451089848089738137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12058119634059898726492091 18087179451089848089738137)
            ·
              refine ⟨13565384588317386067303603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18087179451089848089738137 13565384588317386067303603)
              ·
                refine ⟨20348076882476079100955405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13565384588317386067303603 20348076882476079100955405)
                ·
                  refine ⟨7630528830928529662858277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20348076882476079100955405 7630528830928529662858277)
                  ·
                    refine ⟨1430724155799099311785927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7630528830928529662858277 1430724155799099311785927)
                    ·
                      rfl

theorem cell22_4179488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 2, 1, 3, 4].length) (baseStart_4179488 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4179488 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4179488 prefixEnd_4179488 := by exact prefixLift 4179488
  have htrace : WordTrace (prefixWord ++ tailWord_4179488) baseStart_4179488 baseEnd_4179488 := by
    simpa [prefixWord, tailWord_4179488, baseEnd_4179488] using wordTrace_append hprefix tailTrace_4179488
  have hstable : (prefixWord ++ tailWord_4179488).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4179488).length < 2 ^ (prefixWord ++ tailWord_4179488).sum := by decide
  have hdescent : baseEnd_4179488 < baseStart_4179488 := by decide
  rcases family_descends (prefixWord ++ tailWord_4179488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4179548 : List Nat := [2, 2, 4, 1, 2, 2, 1, 8]
def baseStart_4179548 : Nat := 118140960795 + 4179548 * 2 ^ 59
def prefixEnd_4179548 : Nat := 4983230072969 + 3 ^ 40 * 4179548 * 2
def baseEnd_4179548 : Nat := 158971632780586572809527

theorem tailTrace_4179548 : CollatzResearch.WordTrace tailWord_4179548 prefixEnd_4179548 158971632780586572809527 := by
  unfold tailWord_4179548
  simp only [CollatzResearch.WordTrace]
  refine ⟨76220319531109440407097649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101627092708145920542796865 76220319531109440407097649)
  ·
    refine ⟨57165239648332080305323237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76220319531109440407097649 57165239648332080305323237)
    ·
      refine ⟨10718482434062265057248107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 57165239648332080305323237 10718482434062265057248107)
      ·
        refine ⟨16077723651093397585872161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10718482434062265057248107 16077723651093397585872161)
        ·
          refine ⟨12058292738320048189404121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16077723651093397585872161 12058292738320048189404121)
          ·
            refine ⟨9043719553740036142053091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12058292738320048189404121 9043719553740036142053091)
            ·
              refine ⟨13565579330610054213079637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9043719553740036142053091 13565579330610054213079637)
              ·
                refine ⟨158971632780586572809527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13565579330610054213079637 158971632780586572809527)
                ·
                  rfl

theorem cell22_4179548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 1, 8].length) (baseStart_4179548 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4179548 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4179548 prefixEnd_4179548 := by exact prefixLift 4179548
  have htrace : WordTrace (prefixWord ++ tailWord_4179548) baseStart_4179548 baseEnd_4179548 := by
    simpa [prefixWord, tailWord_4179548, baseEnd_4179548] using wordTrace_append hprefix tailTrace_4179548
  have hstable : (prefixWord ++ tailWord_4179548).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4179548).length < 2 ^ (prefixWord ++ tailWord_4179548).sum := by decide
  have hdescent : baseEnd_4179548 < baseStart_4179548 := by decide
  rcases family_descends (prefixWord ++ tailWord_4179548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4179565 : List Nat := [1, 5, 1, 1, 5, 1, 8]
def baseStart_4179565 : Nat := 118140960795 + 4179565 * 2 ^ 59
def prefixEnd_4179565 : Nat := 4983230072969 + 3 ^ 40 * 4179565 * 2
def baseEnd_4179565 : Nat := 52990759795285065837433

theorem tailTrace_4179565 : CollatzResearch.WordTrace tailWord_4179565 prefixEnd_4179565 52990759795285065837433 := by
  unfold tailWord_4179565
  simp only [CollatzResearch.WordTrace]
  refine ⟨152441259103157292717564149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101627506068771528478376099 152441259103157292717564149)
  ·
    refine ⟨14291368040920996192271639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 152441259103157292717564149 14291368040920996192271639)
    ·
      refine ⟨21437052061381494288407459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14291368040920996192271639 21437052061381494288407459)
      ·
        refine ⟨32155578092072241432611189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21437052061381494288407459 32155578092072241432611189)
        ·
          refine ⟨3014585446131772634307299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 32155578092072241432611189 3014585446131772634307299)
          ·
            refine ⟨4521878169197658951460949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3014585446131772634307299 4521878169197658951460949)
            ·
              refine ⟨52990759795285065837433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4521878169197658951460949 52990759795285065837433)
              ·
                rfl

theorem cell22_4179565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 5, 1, 8].length) (baseStart_4179565 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4179565 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4179565 prefixEnd_4179565 := by exact prefixLift 4179565
  have htrace : WordTrace (prefixWord ++ tailWord_4179565) baseStart_4179565 baseEnd_4179565 := by
    simpa [prefixWord, tailWord_4179565, baseEnd_4179565] using wordTrace_append hprefix tailTrace_4179565
  have hstable : (prefixWord ++ tailWord_4179565).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4179565).length < 2 ^ (prefixWord ++ tailWord_4179565).sum := by decide
  have hdescent : baseEnd_4179565 < baseStart_4179565 := by decide
  rcases family_descends (prefixWord ++ tailWord_4179565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4179713 : List Nat := [1, 2, 4, 1, 1, 1, 2, 2, 2, 6]
def baseStart_4179713 : Nat := 118140960795 + 4179713 * 2 ^ 59
def prefixEnd_4179713 : Nat := 4983230072969 + 3 ^ 40 * 4179713 * 2
def baseEnd_4179713 : Nat := 1430801177897273724910237

theorem tailTrace_4179713 : CollatzResearch.WordTrace tailWord_4179713 prefixEnd_4179713 1430801177897273724910237 := by
  unfold tailWord_4179713
  simp only [CollatzResearch.WordTrace]
  refine ⟨152446657106621113993951793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101631104737747409329301195 152446657106621113993951793)
  ·
    refine ⟨114334992829965835495463845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152446657106621113993951793 114334992829965835495463845)
    ·
      refine ⟨21437811155618594155399471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 114334992829965835495463845 21437811155618594155399471)
      ·
        refine ⟨32156716733427891233099207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21437811155618594155399471 32156716733427891233099207)
        ·
          refine ⟨48235075100141836849648811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32156716733427891233099207 48235075100141836849648811)
          ·
            refine ⟨72352612650212755274473217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48235075100141836849648811 72352612650212755274473217)
            ·
              refine ⟨54264459487659566455854913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72352612650212755274473217 54264459487659566455854913)
              ·
                refine ⟨40698344615744674841891185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54264459487659566455854913 40698344615744674841891185)
                ·
                  refine ⟨30523758461808506131418389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40698344615744674841891185 30523758461808506131418389)
                  ·
                    refine ⟨1430801177897273724910237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30523758461808506131418389 1430801177897273724910237)
                    ·
                      rfl

theorem cell22_4179713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 2, 2, 6].length) (baseStart_4179713 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4179713 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4179713 prefixEnd_4179713 := by exact prefixLift 4179713
  have htrace : WordTrace (prefixWord ++ tailWord_4179713) baseStart_4179713 baseEnd_4179713 := by
    simpa [prefixWord, tailWord_4179713, baseEnd_4179713] using wordTrace_append hprefix tailTrace_4179713
  have hstable : (prefixWord ++ tailWord_4179713).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4179713).length < 2 ^ (prefixWord ++ tailWord_4179713).sum := by decide
  have hdescent : baseEnd_4179713 < baseStart_4179713 := by decide
  rcases family_descends (prefixWord ++ tailWord_4179713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4179715 : List Nat := [1, 1, 1, 3, 2, 2, 4, 2, 3, 3]
def baseStart_4179715 : Nat := 118140960795 + 4179715 * 2 ^ 59
def prefixEnd_4179715 : Nat := 4983230072969 + 3 ^ 40 * 4179715 * 2
def baseEnd_4179715 : Nat := 1430801862538146386360231

theorem tailTrace_4179715 : CollatzResearch.WordTrace tailWord_4179715 prefixEnd_4179715 1430801862538146386360231 := by
  unfold tailWord_4179715
  simp only [CollatzResearch.WordTrace]
  refine ⟨152446730052613868335524599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101631153368409245557016399 152446730052613868335524599)
  ·
    refine ⟨228670095078920802503286899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152446730052613868335524599 228670095078920802503286899)
    ·
      refine ⟨343005142618381203754930349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228670095078920802503286899 343005142618381203754930349)
      ·
        refine ⟨128626928481892951408098881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 343005142618381203754930349 128626928481892951408098881)
        ·
          refine ⟨96470196361419713556074161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128626928481892951408098881 96470196361419713556074161)
          ·
            refine ⟨72352647271064785167055621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96470196361419713556074161 72352647271064785167055621)
            ·
              refine ⟨13566121363324647218822929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 72352647271064785167055621 13566121363324647218822929)
              ·
                refine ⟨10174591022493485414117197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13566121363324647218822929 10174591022493485414117197)
                ·
                  refine ⟨3815471633435057030293949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10174591022493485414117197 3815471633435057030293949)
                  ·
                    refine ⟨1430801862538146386360231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3815471633435057030293949 1430801862538146386360231)
                    ·
                      rfl

theorem cell22_4179715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 4, 2, 3, 3].length) (baseStart_4179715 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4179715 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4179715 prefixEnd_4179715 := by exact prefixLift 4179715
  have htrace : WordTrace (prefixWord ++ tailWord_4179715) baseStart_4179715 baseEnd_4179715 := by
    simpa [prefixWord, tailWord_4179715, baseEnd_4179715] using wordTrace_append hprefix tailTrace_4179715
  have hstable : (prefixWord ++ tailWord_4179715).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4179715).length < 2 ^ (prefixWord ++ tailWord_4179715).sum := by decide
  have hdescent : baseEnd_4179715 < baseStart_4179715 := by decide
  rcases family_descends (prefixWord ++ tailWord_4179715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4179762 : List Nat := [3, 2, 1, 1, 3, 2, 4, 1, 5]
def baseStart_4179762 : Nat := 118140960795 + 4179762 * 2 ^ 59
def prefixEnd_4179762 : Nat := 4983230072969 + 3 ^ 40 * 4179762 * 2
def baseEnd_4179762 : Nat := 476939317199551310145029

theorem tailTrace_4179762 : CollatzResearch.WordTrace tailWord_4179762 prefixEnd_4179762 476939317199551310145029 := by
  unfold tailWord_4179762
  simp only [CollatzResearch.WordTrace]
  refine ⟨38112111070860898840621385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101632296188962396908323693 38112111070860898840621385)
  ·
    refine ⟨28584083303145674130466039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38112111070860898840621385 28584083303145674130466039)
    ·
      refine ⟨42876124954718511195699059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28584083303145674130466039 42876124954718511195699059)
      ·
        refine ⟨64314187432077766793548589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42876124954718511195699059 64314187432077766793548589)
        ·
          refine ⟨24117820287029162547580721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64314187432077766793548589 24117820287029162547580721)
          ·
            refine ⟨18088365215271871910685541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24117820287029162547580721 18088365215271871910685541)
            ·
              refine ⟨3391568477863475983253539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18088365215271871910685541 3391568477863475983253539)
              ·
                refine ⟨5087352716795213974880309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3391568477863475983253539 5087352716795213974880309)
                ·
                  refine ⟨476939317199551310145029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5087352716795213974880309 476939317199551310145029)
                  ·
                    rfl

theorem cell22_4179762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 4, 1, 5].length) (baseStart_4179762 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4179762 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4179762 prefixEnd_4179762 := by exact prefixLift 4179762
  have htrace : WordTrace (prefixWord ++ tailWord_4179762) baseStart_4179762 baseEnd_4179762 := by
    simpa [prefixWord, tailWord_4179762, baseEnd_4179762] using wordTrace_append hprefix tailTrace_4179762
  have hstable : (prefixWord ++ tailWord_4179762).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4179762).length < 2 ^ (prefixWord ++ tailWord_4179762).sum := by decide
  have hdescent : baseEnd_4179762 < baseStart_4179762 := by decide
  rcases family_descends (prefixWord ++ tailWord_4179762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4179807 : List Nat := [1, 1, 2, 3, 1, 5, 1, 4, 4]
def baseStart_4179807 : Nat := 118140960795 + 4179807 * 2 ^ 59
def prefixEnd_4179807 : Nat := 4983230072969 + 3 ^ 40 * 4179807 * 2
def baseEnd_4179807 : Nat := 476944452006096271019983

theorem tailTrace_4179807 : CollatzResearch.WordTrace tailWord_4179807 prefixEnd_4179807 476944452006096271019983 := by
  unfold tailWord_4179807
  simp only [CollatzResearch.WordTrace]
  refine ⟨152450085568280568047873675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101633390378853712031915783 152450085568280568047873675)
  ·
    refine ⟨228675128352420852071810513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152450085568280568047873675 228675128352420852071810513)
    ·
      refine ⟨171506346264315639053857885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 228675128352420852071810513 171506346264315639053857885)
      ·
        refine ⟨64314879849118364645196707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 171506346264315639053857885 64314879849118364645196707)
        ·
          refine ⟨96472319773677546967795061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64314879849118364645196707 96472319773677546967795061)
          ·
            refine ⟨9044279978782270028230787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 96472319773677546967795061 9044279978782270028230787)
            ·
              refine ⟨13566419968173405042346181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9044279978782270028230787 13566419968173405042346181)
              ·
                refine ⟨2543703744032513445439909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13566419968173405042346181 2543703744032513445439909)
                ·
                  refine ⟨476944452006096271019983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2543703744032513445439909 476944452006096271019983)
                  ·
                    rfl

theorem cell22_4179807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 1, 4, 4].length) (baseStart_4179807 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4179807 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4179807 prefixEnd_4179807 := by exact prefixLift 4179807
  have htrace : WordTrace (prefixWord ++ tailWord_4179807) baseStart_4179807 baseEnd_4179807 := by
    simpa [prefixWord, tailWord_4179807, baseEnd_4179807] using wordTrace_append hprefix tailTrace_4179807
  have hstable : (prefixWord ++ tailWord_4179807).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4179807).length < 2 ^ (prefixWord ++ tailWord_4179807).sum := by decide
  have hdescent : baseEnd_4179807 < baseStart_4179807 := by decide
  rcases family_descends (prefixWord ++ tailWord_4179807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4179822 : List Nat := [4, 1, 2, 3, 1, 1, 1, 3, 1, 5]
def baseStart_4179822 : Nat := 118140960795 + 4179822 * 2 ^ 59
def prefixEnd_4179822 : Nat := 4983230072969 + 3 ^ 40 * 4179822 * 2
def baseEnd_4179822 : Nat := 1430838490824833773934903

theorem tailTrace_4179822 : CollatzResearch.WordTrace tailWord_4179822 prefixEnd_4179822 1430838490824833773934903 := by
  unfold tailWord_4179822
  simp only [CollatzResearch.WordTrace]
  refine ⟨19056329082903278201208715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 101633755108817483739779813 19056329082903278201208715)
  ·
    refine ⟨28584493624354917301813073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19056329082903278201208715 28584493624354917301813073)
    ·
      refine ⟨21438370218266187976359805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28584493624354917301813073 21438370218266187976359805)
      ·
        refine ⟨8039388831849820491134927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21438370218266187976359805 8039388831849820491134927)
        ·
          refine ⟨12059083247774730736702391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8039388831849820491134927 12059083247774730736702391)
          ·
            refine ⟨18088624871662096105053587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12059083247774730736702391 18088624871662096105053587)
            ·
              refine ⟨27132937307493144157580381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18088624871662096105053587 27132937307493144157580381)
              ·
                refine ⟨10174851490309929059092643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27132937307493144157580381 10174851490309929059092643)
                ·
                  refine ⟨15262277235464893588638965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10174851490309929059092643 15262277235464893588638965)
                  ·
                    refine ⟨1430838490824833773934903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15262277235464893588638965 1430838490824833773934903)
                    ·
                      rfl

theorem cell22_4179822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 3, 1, 5].length) (baseStart_4179822 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4179822 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4179822 prefixEnd_4179822 := by exact prefixLift 4179822
  have htrace : WordTrace (prefixWord ++ tailWord_4179822) baseStart_4179822 baseEnd_4179822 := by
    simpa [prefixWord, tailWord_4179822, baseEnd_4179822] using wordTrace_append hprefix tailTrace_4179822
  have hstable : (prefixWord ++ tailWord_4179822).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4179822).length < 2 ^ (prefixWord ++ tailWord_4179822).sum := by decide
  have hdescent : baseEnd_4179822 < baseStart_4179822 := by decide
  rcases family_descends (prefixWord ++ tailWord_4179822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4179841 : List Nat := [1, 2, 4, 4, 1, 1, 2, 3, 4]
def baseStart_4179841 : Nat := 118140960795 + 4179841 * 2 ^ 59
def prefixEnd_4179841 : Nat := 4983230072969 + 3 ^ 40 * 4179841 * 2
def baseEnd_4179841 : Nat := 476948331637708019236615

theorem tailTrace_4179841 : CollatzResearch.WordTrace tailWord_4179841 prefixEnd_4179841 476948331637708019236615 := by
  unfold tailWord_4179841
  simp only [CollatzResearch.WordTrace]
  refine ⟨152451325650157391854611377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101634217100104927903074251 152451325650157391854611377)
  ·
    refine ⟨114338494237618043890958533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152451325650157391854611377 114338494237618043890958533)
    ·
      refine ⟨21438467669553383229554725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 114338494237618043890958533 21438467669553383229554725)
      ·
        refine ⟨4019712688041259355541511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21438467669553383229554725 4019712688041259355541511)
        ·
          refine ⟨6029569032061889033312267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4019712688041259355541511 6029569032061889033312267)
          ·
            refine ⟨9044353548092833549968401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6029569032061889033312267 9044353548092833549968401)
            ·
              refine ⟨6783265161069625162476301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9044353548092833549968401 6783265161069625162476301)
              ·
                refine ⟨2543724435401109435928613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6783265161069625162476301 2543724435401109435928613)
                ·
                  refine ⟨476948331637708019236615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2543724435401109435928613 476948331637708019236615)
                  ·
                    rfl

theorem cell22_4179841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 2, 3, 4].length) (baseStart_4179841 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4179841 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4179841 prefixEnd_4179841 := by exact prefixLift 4179841
  have htrace : WordTrace (prefixWord ++ tailWord_4179841) baseStart_4179841 baseEnd_4179841 := by
    simpa [prefixWord, tailWord_4179841, baseEnd_4179841] using wordTrace_append hprefix tailTrace_4179841
  have hstable : (prefixWord ++ tailWord_4179841).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4179841).length < 2 ^ (prefixWord ++ tailWord_4179841).sum := by decide
  have hdescent : baseEnd_4179841 < baseStart_4179841 := by decide
  rcases family_descends (prefixWord ++ tailWord_4179841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4179886 : List Nat := [4, 1, 5, 1, 1, 1, 1, 8]
def baseStart_4179886 : Nat := 118140960795 + 4179886 * 2 ^ 59
def prefixEnd_4179886 : Nat := 4983230072969 + 3 ^ 40 * 4179886 * 2
def baseEnd_4179886 : Nat := 158984488814750993370523

theorem tailTrace_4179886 : CollatzResearch.WordTrace tailWord_4179886 prefixEnd_4179886 158984488814750993370523 := by
  unfold tailWord_4179886
  simp only [CollatzResearch.WordTrace]
  refine ⟨19056620866874295567499939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 101635311289996243026666341 19056620866874295567499939)
  ·
    refine ⟨28584931300311443351249909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19056620866874295567499939 28584931300311443351249909)
    ·
      refine ⟨2679837309404197814179679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 28584931300311443351249909 2679837309404197814179679)
      ·
        refine ⟨4019755964106296721269519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2679837309404197814179679 4019755964106296721269519)
        ·
          refine ⟨6029633946159445081904279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4019755964106296721269519 6029633946159445081904279)
          ·
            refine ⟨9044450919239167622856419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6029633946159445081904279 9044450919239167622856419)
            ·
              refine ⟨13566676378858751434284629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9044450919239167622856419 13566676378858751434284629)
              ·
                refine ⟨158984488814750993370523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13566676378858751434284629 158984488814750993370523)
                ·
                  rfl

theorem cell22_4179886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 1, 8].length) (baseStart_4179886 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4179886 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4179886 prefixEnd_4179886 := by exact prefixLift 4179886
  have htrace : WordTrace (prefixWord ++ tailWord_4179886) baseStart_4179886 baseEnd_4179886 := by
    simpa [prefixWord, tailWord_4179886, baseEnd_4179886] using wordTrace_append hprefix tailTrace_4179886
  have hstable : (prefixWord ++ tailWord_4179886).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4179886).length < 2 ^ (prefixWord ++ tailWord_4179886).sum := by decide
  have hdescent : baseEnd_4179886 < baseStart_4179886 := by decide
  rcases family_descends (prefixWord ++ tailWord_4179886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4179901 : List Nat := [1, 4, 1, 2, 3, 1, 3, 3, 1, 3]
def baseStart_4179901 : Nat := 118140960795 + 4179901 * 2 ^ 59
def prefixEnd_4179901 : Nat := 4983230072969 + 3 ^ 40 * 4179901 * 2
def baseEnd_4179901 : Nat := 1430865534139303901209661

theorem tailTrace_4179901 : CollatzResearch.WordTrace tailWord_4179901 prefixEnd_4179901 1430865534139303901209661 := by
  unfold tailWord_4179901
  simp only [CollatzResearch.WordTrace]
  refine ⟨152453514029940022101795557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101635676019960014734530371 152453514029940022101795557)
  ·
    refine ⟨28585033880613754144086667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 152453514029940022101795557 28585033880613754144086667)
    ·
      refine ⟨42877550820920631216130001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28585033880613754144086667 42877550820920631216130001)
      ·
        refine ⟨32158163115690473412097501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42877550820920631216130001 32158163115690473412097501)
        ·
          refine ⟨12059311168383927529536563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32158163115690473412097501 12059311168383927529536563)
          ·
            refine ⟨18088966752575891294304845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12059311168383927529536563 18088966752575891294304845)
            ·
              refine ⟨6783362532215959235364317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18088966752575891294304845 6783362532215959235364317)
              ·
                refine ⟨2543760949580984713261619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6783362532215959235364317 2543760949580984713261619)
                ·
                  refine ⟨3815641424371477069892429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2543760949580984713261619 3815641424371477069892429)
                  ·
                    refine ⟨1430865534139303901209661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3815641424371477069892429 1430865534139303901209661)
                    ·
                      rfl

theorem cell22_4179901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 3, 3, 1, 3].length) (baseStart_4179901 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4179901 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4179901 prefixEnd_4179901 := by exact prefixLift 4179901
  have htrace : WordTrace (prefixWord ++ tailWord_4179901) baseStart_4179901 baseEnd_4179901 := by
    simpa [prefixWord, tailWord_4179901, baseEnd_4179901] using wordTrace_append hprefix tailTrace_4179901
  have hstable : (prefixWord ++ tailWord_4179901).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4179901).length < 2 ^ (prefixWord ++ tailWord_4179901).sum := by decide
  have hdescent : baseEnd_4179901 < baseStart_4179901 := by decide
  rcases family_descends (prefixWord ++ tailWord_4179901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4179955 : List Nat := [1, 1, 1, 2, 2, 2, 1, 5, 1, 6]
def baseStart_4179955 : Nat := 118140960795 + 4179955 * 2 ^ 59
def prefixEnd_4179955 : Nat := 4983230072969 + 3 ^ 40 * 4179955 * 2
def baseEnd_4179955 : Nat := 1430884019442865760359495

theorem tailTrace_4179955 : CollatzResearch.WordTrace tailWord_4179955 prefixEnd_4179955 1430884019442865760359495 := by
  unfold tailWord_4179955
  simp only [CollatzResearch.WordTrace]
  refine ⟨152455483571744389324261319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101636989047829592882840879 152455483571744389324261319)
  ·
    refine ⟨228683225357616583986391979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152455483571744389324261319 228683225357616583986391979)
    ·
      refine ⟨343024838036424875979587969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228683225357616583986391979 343024838036424875979587969)
      ·
        refine ⟨257268628527318656984690977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 343024838036424875979587969 257268628527318656984690977)
        ·
          refine ⟨192951471395488992738518233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 257268628527318656984690977 192951471395488992738518233)
          ·
            refine ⟨144713603546616744553888675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 192951471395488992738518233 144713603546616744553888675)
            ·
              refine ⟨217070405319925116830833013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144713603546616744553888675 217070405319925116830833013)
              ·
                refine ⟨20350350498742979702890595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 217070405319925116830833013 20350350498742979702890595)
                ·
                  refine ⟨30525525748114469554335893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20350350498742979702890595 30525525748114469554335893)
                  ·
                    refine ⟨1430884019442865760359495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30525525748114469554335893 1430884019442865760359495)
                    ·
                      rfl

theorem cell22_4179955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 5, 1, 6].length) (baseStart_4179955 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4179955 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4179955 prefixEnd_4179955 := by exact prefixLift 4179955
  have htrace : WordTrace (prefixWord ++ tailWord_4179955) baseStart_4179955 baseEnd_4179955 := by
    simpa [prefixWord, tailWord_4179955, baseEnd_4179955] using wordTrace_append hprefix tailTrace_4179955
  have hstable : (prefixWord ++ tailWord_4179955).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4179955).length < 2 ^ (prefixWord ++ tailWord_4179955).sum := by decide
  have hdescent : baseEnd_4179955 < baseStart_4179955 := by decide
  rcases family_descends (prefixWord ++ tailWord_4179955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4179985 : List Nat := [1, 2, 2, 1, 1, 2, 1, 1, 4, 7]
def baseStart_4179985 : Nat := 118140960795 + 4179985 * 2 ^ 59
def prefixEnd_4179985 : Nat := 4983230072969 + 3 ^ 40 * 4179985 * 2
def baseEnd_4179985 : Nat := 1430894289055955682109403

theorem tailTrace_4179985 : CollatzResearch.WordTrace tailWord_4179985 prefixEnd_4179985 1430894289055955682109403 := by
  unfold tailWord_4179985
  simp only [CollatzResearch.WordTrace]
  refine ⟨152456577761635704447853409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101637718507757136298568939 152456577761635704447853409)
  ·
    refine ⟨114342433321226778335890057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152456577761635704447853409 114342433321226778335890057)
    ·
      refine ⟨85756824990920083751917543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114342433321226778335890057 85756824990920083751917543)
      ·
        refine ⟨128635237486380125627876315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85756824990920083751917543 128635237486380125627876315)
        ·
          refine ⟨192952856229570188441814473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128635237486380125627876315 192952856229570188441814473)
          ·
            refine ⟨144714642172177641331360855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 192952856229570188441814473 144714642172177641331360855)
            ·
              refine ⟨217071963258266461997041283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144714642172177641331360855 217071963258266461997041283)
              ·
                refine ⟨325607944887399692995561925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 217071963258266461997041283 325607944887399692995561925)
                ·
                  refine ⟨61051489666387442436667861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 325607944887399692995561925 61051489666387442436667861)
                  ·
                    refine ⟨1430894289055955682109403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 61051489666387442436667861 1430894289055955682109403)
                    ·
                      rfl

theorem cell22_4179985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 7].length) (baseStart_4179985 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4179985 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4179985 prefixEnd_4179985 := by exact prefixLift 4179985
  have htrace : WordTrace (prefixWord ++ tailWord_4179985) baseStart_4179985 baseEnd_4179985 := by
    simpa [prefixWord, tailWord_4179985, baseEnd_4179985] using wordTrace_append hprefix tailTrace_4179985
  have hstable : (prefixWord ++ tailWord_4179985).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4179985).length < 2 ^ (prefixWord ++ tailWord_4179985).sum := by decide
  have hdescent : baseEnd_4179985 < baseStart_4179985 := by decide
  rcases family_descends (prefixWord ++ tailWord_4179985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4180032 : List Nat := [2, 1, 1, 2, 2, 5, 1, 1, 7]
def baseStart_4180032 : Nat := 118140960795 + 4180032 * 2 ^ 59
def prefixEnd_4180032 : Nat := 4983230072969 + 3 ^ 40 * 4180032 * 2
def baseEnd_4180032 : Nat := 476970126038821075394753

theorem tailTrace_4180032 : CollatzResearch.WordTrace tailWord_4180032 prefixEnd_4180032 476970126038821075394753 := by
  unfold tailWord_4180032
  simp only [CollatzResearch.WordTrace]
  refine ⟨76229145996232715737407175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101638861328310287649876233 76229145996232715737407175)
  ·
    refine ⟨114343718994349073606110763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76229145996232715737407175 114343718994349073606110763)
    ·
      refine ⟨171515578491523610409166145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114343718994349073606110763 171515578491523610409166145)
      ·
        refine ⟨128636683868642707806874609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171515578491523610409166145 128636683868642707806874609)
        ·
          refine ⟨96477512901482030855155957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128636683868642707806874609 96477512901482030855155957)
          ·
            refine ⟨9044766834513940392670871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 96477512901482030855155957 9044766834513940392670871)
            ·
              refine ⟨13567150251770910589006307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9044766834513940392670871 13567150251770910589006307)
              ·
                refine ⟨20350725377656365883509461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13567150251770910589006307 20350725377656365883509461)
                ·
                  refine ⟨476970126038821075394753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20350725377656365883509461 476970126038821075394753)
                  ·
                    rfl

theorem cell22_4180032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 1, 1, 7].length) (baseStart_4180032 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4180032 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4180032 prefixEnd_4180032 := by exact prefixLift 4180032
  have htrace : WordTrace (prefixWord ++ tailWord_4180032) baseStart_4180032 baseEnd_4180032 := by
    simpa [prefixWord, tailWord_4180032, baseEnd_4180032] using wordTrace_append hprefix tailTrace_4180032
  have hstable : (prefixWord ++ tailWord_4180032).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4180032).length < 2 ^ (prefixWord ++ tailWord_4180032).sum := by decide
  have hdescent : baseEnd_4180032 < baseStart_4180032 := by decide
  rcases family_descends (prefixWord ++ tailWord_4180032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4180079 : List Nat := [1, 1, 2, 1, 3, 4, 2, 3, 1, 4]
def baseStart_4180079 : Nat := 118140960795 + 4180079 * 2 ^ 59
def prefixEnd_4180079 : Nat := 4983230072969 + 3 ^ 40 * 4180079 * 2
def baseEnd_4180079 : Nat := 1430926467176970770259115

theorem tailTrace_4180079 : CollatzResearch.WordTrace tailWord_4180079 prefixEnd_4180079 1430926467176970770259115 := by
  unfold tailWord_4180079
  simp only [CollatzResearch.WordTrace]
  refine ⟨152460006223295158501775291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101640004148863439001183527 152460006223295158501775291)
  ·
    refine ⟨228690009334942737752662937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152460006223295158501775291 228690009334942737752662937)
    ·
      refine ⟨171517507001207053314497203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 228690009334942737752662937 171517507001207053314497203)
      ·
        refine ⟨257276260501810579971745805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171517507001207053314497203 257276260501810579971745805)
        ·
          refine ⟨96478597688178967489404677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 257276260501810579971745805 96478597688178967489404677)
          ·
            refine ⟨18089737066533556404263377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 96478597688178967489404677 18089737066533556404263377)
            ·
              refine ⟨13567302799900167303197533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18089737066533556404263377 13567302799900167303197533)
              ·
                refine ⟨5087738549962562738699075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13567302799900167303197533 5087738549962562738699075)
                ·
                  refine ⟨7631607824943844108048613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5087738549962562738699075 7631607824943844108048613)
                  ·
                    refine ⟨1430926467176970770259115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7631607824943844108048613 1430926467176970770259115)
                    ·
                      rfl

theorem cell22_4180079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 2, 3, 1, 4].length) (baseStart_4180079 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4180079 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4180079 prefixEnd_4180079 := by exact prefixLift 4180079
  have htrace : WordTrace (prefixWord ++ tailWord_4180079) baseStart_4180079 baseEnd_4180079 := by
    simpa [prefixWord, tailWord_4180079, baseEnd_4180079] using wordTrace_append hprefix tailTrace_4180079
  have hstable : (prefixWord ++ tailWord_4180079).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4180079).length < 2 ^ (prefixWord ++ tailWord_4180079).sum := by decide
  have hdescent : baseEnd_4180079 < baseStart_4180079 := by decide
  rcases family_descends (prefixWord ++ tailWord_4180079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4180141 : List Nat := [1, 5, 2, 1, 2, 1, 2, 2, 2, 4]
def baseStart_4180141 : Nat := 118140960795 + 4180141 * 2 ^ 59
def prefixEnd_4180141 : Nat := 4983230072969 + 3 ^ 40 * 4180141 * 2
def baseEnd_4180141 : Nat := 1430947691044023275208925

theorem tailTrace_4180141 : CollatzResearch.WordTrace tailWord_4180141 prefixEnd_4180141 1430947691044023275208925 := by
  unfold tailWord_4180141
  simp only [CollatzResearch.WordTrace]
  refine ⟨152462267549070543090532277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101641511699380362060354851 152462267549070543090532277)
  ·
    refine ⟨14293337582725363414737401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 152462267549070543090532277 14293337582725363414737401)
    ·
      refine ⟨10720003187044022561053051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14293337582725363414737401 10720003187044022561053051)
      ·
        refine ⟨16080004780566033841579577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10720003187044022561053051 16080004780566033841579577)
        ·
          refine ⟨12060003585424525381184683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16080004780566033841579577 12060003585424525381184683)
          ·
            refine ⟨18090005378136788071777025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12060003585424525381184683 18090005378136788071777025)
            ·
              refine ⟨13567504033602591053832769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18090005378136788071777025 13567504033602591053832769)
              ·
                refine ⟨10175628025201943290374577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13567504033602591053832769 10175628025201943290374577)
                ·
                  refine ⟨7631721018901457467780933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10175628025201943290374577 7631721018901457467780933)
                  ·
                    refine ⟨1430947691044023275208925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7631721018901457467780933 1430947691044023275208925)
                    ·
                      rfl

theorem cell22_4180141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 2, 2, 2, 4].length) (baseStart_4180141 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4180141 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4180141 prefixEnd_4180141 := by exact prefixLift 4180141
  have htrace : WordTrace (prefixWord ++ tailWord_4180141) baseStart_4180141 baseEnd_4180141 := by
    simpa [prefixWord, tailWord_4180141, baseEnd_4180141] using wordTrace_append hprefix tailTrace_4180141
  have hstable : (prefixWord ++ tailWord_4180141).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4180141).length < 2 ^ (prefixWord ++ tailWord_4180141).sum := by decide
  have hdescent : baseEnd_4180141 < baseStart_4180141 := by decide
  rcases family_descends (prefixWord ++ tailWord_4180141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4180145 : List Nat := [1, 2, 2, 5, 2, 2, 2, 2, 4]
def baseStart_4180145 : Nat := 118140960795 + 4180145 * 2 ^ 59
def prefixEnd_4180145 : Nat := 4983230072969 + 3 ^ 40 * 4180145 * 2
def baseEnd_4180145 : Nat := 476983020108589532702971

theorem tailTrace_4180145 : CollatzResearch.WordTrace tailWord_4180145 prefixEnd_4180145 476983020108589532702971 := by
  unfold tailWord_4180145
  simp only [CollatzResearch.WordTrace]
  refine ⟨152462413441056051773677889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101641608960704034515785259 152462413441056051773677889)
  ·
    refine ⟨114346810080792038830258417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152462413441056051773677889 114346810080792038830258417)
    ·
      refine ⟨85760107560594029122693813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114346810080792038830258417 85760107560594029122693813)
      ·
        refine ⟨8040010083805690230252545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 85760107560594029122693813 8040010083805690230252545)
        ·
          refine ⟨6030007562854267672689409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8040010083805690230252545 6030007562854267672689409)
          ·
            refine ⟨4522505672140700754517057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6030007562854267672689409 4522505672140700754517057)
            ·
              refine ⟨3391879254105525565887793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4522505672140700754517057 3391879254105525565887793)
              ·
                refine ⟨2543909440579144174415845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3391879254105525565887793 2543909440579144174415845)
                ·
                  refine ⟨476983020108589532702971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2543909440579144174415845 476983020108589532702971)
                  ·
                    rfl

theorem cell22_4180145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 2, 2, 2, 4].length) (baseStart_4180145 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4180145 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4180145 prefixEnd_4180145 := by exact prefixLift 4180145
  have htrace : WordTrace (prefixWord ++ tailWord_4180145) baseStart_4180145 baseEnd_4180145 := by
    simpa [prefixWord, tailWord_4180145, baseEnd_4180145] using wordTrace_append hprefix tailTrace_4180145
  have hstable : (prefixWord ++ tailWord_4180145).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4180145).length < 2 ^ (prefixWord ++ tailWord_4180145).sum := by decide
  have hdescent : baseEnd_4180145 < baseStart_4180145 := by decide
  rcases family_descends (prefixWord ++ tailWord_4180145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4180152 : List Nat := [2, 1, 2, 1, 2, 1, 3, 1, 1, 8]
def baseStart_4180152 : Nat := 118140960795 + 4180152 * 2 ^ 59
def prefixEnd_4180152 : Nat := 4983230072969 + 3 ^ 40 * 4180152 * 2
def baseEnd_4180152 : Nat := 1430951456568822913183891

theorem tailTrace_4180152 : CollatzResearch.WordTrace tailWord_4180152 prefixEnd_4180152 1430951456568822913183891 := by
  unfold tailWord_4180152
  simp only [CollatzResearch.WordTrace]
  refine ⟨76231334376015345984591355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101641779168020461312788473 76231334376015345984591355)
  ·
    refine ⟨114347001564023018976887033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76231334376015345984591355 114347001564023018976887033)
    ·
      refine ⟨85760251173017264232665275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114347001564023018976887033 85760251173017264232665275)
      ·
        refine ⟨128640376759525896348997913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85760251173017264232665275 128640376759525896348997913)
        ·
          refine ⟨96480282569644422261748435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128640376759525896348997913 96480282569644422261748435)
          ·
            refine ⟨144720423854466633392622653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96480282569644422261748435 144720423854466633392622653)
            ·
              refine ⟨54270158945424987522233495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 144720423854466633392622653 54270158945424987522233495)
              ·
                refine ⟨81405238418137481283350243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54270158945424987522233495 81405238418137481283350243)
                ·
                  refine ⟨122107857627206221925025365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 81405238418137481283350243 122107857627206221925025365)
                  ·
                    refine ⟨1430951456568822913183891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 122107857627206221925025365 1430951456568822913183891)
                    ·
                      rfl

theorem cell22_4180152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 1, 1, 8].length) (baseStart_4180152 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4180152 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4180152 prefixEnd_4180152 := by exact prefixLift 4180152
  have htrace : WordTrace (prefixWord ++ tailWord_4180152) baseStart_4180152 baseEnd_4180152 := by
    simpa [prefixWord, tailWord_4180152, baseEnd_4180152] using wordTrace_append hprefix tailTrace_4180152
  have hstable : (prefixWord ++ tailWord_4180152).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4180152).length < 2 ^ (prefixWord ++ tailWord_4180152).sum := by decide
  have hdescent : baseEnd_4180152 < baseStart_4180152 := by decide
  rcases family_descends (prefixWord ++ tailWord_4180152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4180156 : List Nat := [2, 2, 2, 3, 3, 2, 1, 7]
def baseStart_4180156 : Nat := 118140960795 + 4180156 * 2 ^ 59
def prefixEnd_4180156 : Nat := 4983230072969 + 3 ^ 40 * 4180156 * 2
def baseEnd_4180156 : Nat := 158994758427840915120431

theorem tailTrace_4180156 : CollatzResearch.WordTrace tailWord_4180156 prefixEnd_4180156 158994758427840915120431 := by
  unfold tailWord_4180156
  simp only [CollatzResearch.WordTrace]
  refine ⟨76231407322008100326164161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101641876429344133768218881 76231407322008100326164161)
  ·
    refine ⟨57173555491506075244623121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76231407322008100326164161 57173555491506075244623121)
    ·
      refine ⟨42880166618629556433467341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57173555491506075244623121 42880166618629556433467341)
      ·
        refine ⟨16080062481986083662550253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42880166618629556433467341 16080062481986083662550253)
        ·
          refine ⟨6030023430744781373456345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16080062481986083662550253 6030023430744781373456345)
          ·
            refine ⟨4522517573058586030092259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6030023430744781373456345 4522517573058586030092259)
            ·
              refine ⟨6783776359587879045138389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4522517573058586030092259 6783776359587879045138389)
              ·
                refine ⟨158994758427840915120431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6783776359587879045138389 158994758427840915120431)
                ·
                  rfl

theorem cell22_4180156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 2, 1, 7].length) (baseStart_4180156 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4180156 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4180156 prefixEnd_4180156 := by exact prefixLift 4180156
  have htrace : WordTrace (prefixWord ++ tailWord_4180156) baseStart_4180156 baseEnd_4180156 := by
    simpa [prefixWord, tailWord_4180156, baseEnd_4180156] using wordTrace_append hprefix tailTrace_4180156
  have hstable : (prefixWord ++ tailWord_4180156).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4180156).length < 2 ^ (prefixWord ++ tailWord_4180156).sum := by decide
  have hdescent : baseEnd_4180156 < baseStart_4180156 := by decide
  rcases family_descends (prefixWord ++ tailWord_4180156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4180167 : List Nat := [1, 1, 4, 1, 1, 1, 1, 1, 11]
def baseStart_4180167 : Nat := 118140960795 + 4180167 * 2 ^ 59
def prefixEnd_4180167 : Nat := 4983230072969 + 3 ^ 40 * 4180167 * 2
def baseEnd_4180167 : Nat := 476985530458455958019615

theorem tailTrace_4180167 : CollatzResearch.WordTrace tailWord_4180167 prefixEnd_4180167 476985530458455958019615 := by
  unfold tailWord_4180167
  simp only [CollatzResearch.WordTrace]
  refine ⟨152463215846976349530978755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101642143897984233020652503 152463215846976349530978755)
  ·
    refine ⟨228694823770464524296468133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152463215846976349530978755 228694823770464524296468133)
    ·
      refine ⟨42880279456962098305587775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 228694823770464524296468133 42880279456962098305587775)
      ·
        refine ⟨64320419185443147458381663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42880279456962098305587775 64320419185443147458381663)
        ·
          refine ⟨96480628778164721187572495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64320419185443147458381663 96480628778164721187572495)
          ·
            refine ⟨144720943167247081781358743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96480628778164721187572495 144720943167247081781358743)
            ·
              refine ⟨217081414750870622672038115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144720943167247081781358743 217081414750870622672038115)
              ·
                refine ⟨325622122126305934008057173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 217081414750870622672038115 325622122126305934008057173)
                ·
                  refine ⟨476985530458455958019615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 325622122126305934008057173 476985530458455958019615)
                  ·
                    rfl

theorem cell22_4180167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 1, 11].length) (baseStart_4180167 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4180167 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4180167 prefixEnd_4180167 := by exact prefixLift 4180167
  have htrace : WordTrace (prefixWord ++ tailWord_4180167) baseStart_4180167 baseEnd_4180167 := by
    simpa [prefixWord, tailWord_4180167, baseEnd_4180167] using wordTrace_append hprefix tailTrace_4180167
  have hstable : (prefixWord ++ tailWord_4180167).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4180167).length < 2 ^ (prefixWord ++ tailWord_4180167).sum := by decide
  have hdescent : baseEnd_4180167 < baseStart_4180167 := by decide
  rcases family_descends (prefixWord ++ tailWord_4180167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
