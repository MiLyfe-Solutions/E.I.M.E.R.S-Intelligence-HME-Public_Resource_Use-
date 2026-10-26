import V185TrunkScan23Chunk1064

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_6304803 : List Nat := [1, 1, 1, 4, 3, 3, 3, 1, 2, 4]
def baseStart_6304803 : Nat := 118140960795 + 6304803 * 2 ^ 59
def prefixEnd_6304803 : Nat := 4983230072969 + 3 ^ 40 * 6304803 * 2
def baseEnd_6304803 : Nat := 1079131456969667054322415

theorem tailTrace_6304803 : CollatzResearch.WordTrace tailWord_6304803 prefixEnd_6304803 1079131456969667054322415 := by
  unfold tailWord_6304803
  simp only [CollatzResearch.WordTrace]
  refine ⟨229955056977782980471103063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153303371318521986980735375 229955056977782980471103063)
  ·
    refine ⟨344932585466674470706654595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229955056977782980471103063 344932585466674470706654595)
    ·
      refine ⟨517398878200011706059981893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 344932585466674470706654595 517398878200011706059981893)
      ·
        refine ⟨97012289662502194886246605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 517398878200011706059981893 97012289662502194886246605)
        ·
          refine ⟨36379608623438323082342477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 97012289662502194886246605 36379608623438323082342477)
          ·
            refine ⟨13642353233789371155878429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36379608623438323082342477 13642353233789371155878429)
            ·
              refine ⟨5115882462671014183454411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13642353233789371155878429 5115882462671014183454411)
              ·
                refine ⟨7673823694006521275181617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5115882462671014183454411 7673823694006521275181617)
                ·
                  refine ⟨5755367770504890956386213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7673823694006521275181617 5755367770504890956386213)
                  ·
                    refine ⟨1079131456969667054322415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5755367770504890956386213 1079131456969667054322415)
                    ·
                      rfl

theorem cell23_6304803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 3, 1, 2, 4].length) (baseStart_6304803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6304803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6304803 prefixEnd_6304803 := by exact prefixLift 6304803
  have htrace : WordTrace (prefixWord ++ tailWord_6304803) baseStart_6304803 baseEnd_6304803 := by
    simpa [prefixWord, tailWord_6304803, baseEnd_6304803] using wordTrace_append hprefix tailTrace_6304803
  have hstable : (prefixWord ++ tailWord_6304803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6304803).length < 2 ^ (prefixWord ++ tailWord_6304803).sum := by decide
  have hdescent : baseEnd_6304803 < baseStart_6304803 := by decide
  rcases family_descends (prefixWord ++ tailWord_6304803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6304826 : List Nat := [3, 1, 1, 1, 3, 1, 3, 2, 4, 1, 3]
def baseStart_6304826 : Nat := 118140960795 + 6304826 * 2 ^ 59
def prefixEnd_6304826 : Nat := 4983230072969 + 3 ^ 40 * 6304826 * 2
def baseEnd_6304826 : Nat := 3237406180964054572979639

theorem tailTrace_6304826 : CollatzResearch.WordTrace tailWord_6304826 prefixEnd_6304826 3237406180964054572979639 := by
  unfold tailWord_6304826
  simp only [CollatzResearch.WordTrace]
  refine ⟨57488973964174913849797583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153303930571133103599460221 57488973964174913849797583)
  ·
    refine ⟨86233460946262370774696375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57488973964174913849797583 86233460946262370774696375)
    ·
      refine ⟨129350191419393556162044563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86233460946262370774696375 129350191419393556162044563)
      ·
        refine ⟨194025287129090334243066845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129350191419393556162044563 194025287129090334243066845)
        ·
          refine ⟨72759482673408875341150067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 194025287129090334243066845 72759482673408875341150067)
          ·
            refine ⟨109139224010113313011725101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72759482673408875341150067 109139224010113313011725101)
            ·
              refine ⟨40927209003792492379396913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 109139224010113313011725101 40927209003792492379396913)
              ·
                refine ⟨30695406752844369284547685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40927209003792492379396913 30695406752844369284547685)
                ·
                  refine ⟨5755388766158319240852691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30695406752844369284547685 5755388766158319240852691)
                  ·
                    refine ⟨8633083149237478861279037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5755388766158319240852691 8633083149237478861279037)
                    ·
                      refine ⟨3237406180964054572979639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8633083149237478861279037 3237406180964054572979639)
                      ·
                        rfl

theorem cell23_6304826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 2, 4, 1, 3].length) (baseStart_6304826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6304826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6304826 prefixEnd_6304826 := by exact prefixLift 6304826
  have htrace : WordTrace (prefixWord ++ tailWord_6304826) baseStart_6304826 baseEnd_6304826 := by
    simpa [prefixWord, tailWord_6304826, baseEnd_6304826] using wordTrace_append hprefix tailTrace_6304826
  have hstable : (prefixWord ++ tailWord_6304826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6304826).length < 2 ^ (prefixWord ++ tailWord_6304826).sum := by decide
  have hdescent : baseEnd_6304826 < baseStart_6304826 := by decide
  rcases family_descends (prefixWord ++ tailWord_6304826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6304854 : List Nat := [5, 2, 2, 1, 2, 2, 2, 1, 2, 4]
def baseStart_6304854 : Nat := 118140960795 + 6304854 * 2 ^ 59
def prefixEnd_6304854 : Nat := 4983230072969 + 3 ^ 40 * 6304854 * 2
def baseEnd_6304854 : Nat := 1079140186140793487809837

theorem tailTrace_6304854 : CollatzResearch.WordTrace tailWord_6304854 prefixEnd_6304854 1079140186140793487809837 := by
  unfold tailWord_6304854
  simp only [CollatzResearch.WordTrace]
  refine ⟨14372307318787388511325601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 153304611400398810787473077 14372307318787388511325601)
  ·
    refine ⟨10779230489090541383494201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14372307318787388511325601 10779230489090541383494201)
    ·
      refine ⟨8084422866817906037620651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10779230489090541383494201 8084422866817906037620651)
      ·
        refine ⟨12126634300226859056430977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8084422866817906037620651 12126634300226859056430977)
        ·
          refine ⟨9094975725170144292323233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12126634300226859056430977 9094975725170144292323233)
          ·
            refine ⟨6821231793877608219242425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9094975725170144292323233 6821231793877608219242425)
            ·
              refine ⟨5115923845408206164431819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6821231793877608219242425 5115923845408206164431819)
              ·
                refine ⟨7673885768112309246647729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5115923845408206164431819 7673885768112309246647729)
                ·
                  refine ⟨5755414326084231934985797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7673885768112309246647729 5755414326084231934985797)
                  ·
                    refine ⟨1079140186140793487809837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5755414326084231934985797 1079140186140793487809837)
                    ·
                      rfl

theorem cell23_6304854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 2, 2, 1, 2, 4].length) (baseStart_6304854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6304854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6304854 prefixEnd_6304854 := by exact prefixLift 6304854
  have htrace : WordTrace (prefixWord ++ tailWord_6304854) baseStart_6304854 baseEnd_6304854 := by
    simpa [prefixWord, tailWord_6304854, baseEnd_6304854] using wordTrace_append hprefix tailTrace_6304854
  have hstable : (prefixWord ++ tailWord_6304854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6304854).length < 2 ^ (prefixWord ++ tailWord_6304854).sum := by decide
  have hdescent : baseEnd_6304854 < baseStart_6304854 := by decide
  rcases family_descends (prefixWord ++ tailWord_6304854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6304869 : List Nat := [1, 3, 1, 3, 2, 1, 1, 1, 4, 1, 5]
def baseStart_6304869 : Nat := 118140960795 + 6304869 * 2 ^ 59
def prefixEnd_6304869 : Nat := 4983230072969 + 3 ^ 40 * 6304869 * 2
def baseEnd_6304869 : Nat := 3237428260632197904741941

theorem tailTrace_6304869 : CollatzResearch.WordTrace tailWord_6304869 prefixEnd_6304869 3237428260632197904741941 := by
  unfold tailWord_6304869
  simp only [CollatzResearch.WordTrace]
  refine ⟨229957464195543873743005661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153304976130362582495337107 229957464195543873743005661)
  ·
    refine ⟨86234049073328952653627123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 229957464195543873743005661 86234049073328952653627123)
    ·
      refine ⟨129351073609993428980440685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86234049073328952653627123 129351073609993428980440685)
      ·
        refine ⟨48506652603747535867665257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 129351073609993428980440685 48506652603747535867665257)
        ·
          refine ⟨36379989452810651900748943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48506652603747535867665257 36379989452810651900748943)
          ·
            refine ⟨54569984179215977851123415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36379989452810651900748943 54569984179215977851123415)
            ·
              refine ⟨81854976268823966776685123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54569984179215977851123415 81854976268823966776685123)
              ·
                refine ⟨122782464403235950165027685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81854976268823966776685123 122782464403235950165027685)
                ·
                  refine ⟨23021712075606740655942691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 122782464403235950165027685 23021712075606740655942691)
                  ·
                    refine ⟨34532568113410110983914037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23021712075606740655942691 34532568113410110983914037)
                    ·
                      refine ⟨3237428260632197904741941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34532568113410110983914037 3237428260632197904741941)
                      ·
                        rfl

theorem cell23_6304869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 1, 4, 1, 5].length) (baseStart_6304869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6304869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6304869 prefixEnd_6304869 := by exact prefixLift 6304869
  have htrace : WordTrace (prefixWord ++ tailWord_6304869) baseStart_6304869 baseEnd_6304869 := by
    simpa [prefixWord, tailWord_6304869, baseEnd_6304869] using wordTrace_append hprefix tailTrace_6304869
  have hstable : (prefixWord ++ tailWord_6304869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6304869).length < 2 ^ (prefixWord ++ tailWord_6304869).sum := by decide
  have hdescent : baseEnd_6304869 < baseStart_6304869 := by decide
  rcases family_descends (prefixWord ++ tailWord_6304869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6304886 : List Nat := [5, 1, 1, 2, 1, 1, 1, 3, 2, 1, 5]
def baseStart_6304886 : Nat := 118140960795 + 6304886 * 2 ^ 59
def prefixEnd_6304886 : Nat := 4983230072969 + 3 ^ 40 * 6304886 * 2
def baseEnd_6304886 : Nat := 3237436989803324338229363

theorem tailTrace_6304886 : CollatzResearch.WordTrace tailWord_6304886 prefixEnd_6304886 3237436989803324338229363 := by
  unfold tailWord_6304886
  simp only [CollatzResearch.WordTrace]
  refine ⟨14372380264780142852898407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 153305389490988190430916341 14372380264780142852898407)
  ·
    refine ⟨21558570397170214279347611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14372380264780142852898407 21558570397170214279347611)
    ·
      refine ⟨32337855595755321419021417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21558570397170214279347611 32337855595755321419021417)
      ·
        refine ⟨24253391696816491064266063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32337855595755321419021417 24253391696816491064266063)
        ·
          refine ⟨36380087545224736596399095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24253391696816491064266063 36380087545224736596399095)
          ·
            refine ⟨54570131317837104894598643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36380087545224736596399095 54570131317837104894598643)
            ·
              refine ⟨81855196976755657341897965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54570131317837104894598643 81855196976755657341897965)
              ·
                refine ⟨30695698866283371503211737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 81855196976755657341897965 30695698866283371503211737)
                ·
                  refine ⟨23021774149712528627408803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30695698866283371503211737 23021774149712528627408803)
                  ·
                    refine ⟨34532661224568792941113205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23021774149712528627408803 34532661224568792941113205)
                    ·
                      refine ⟨3237436989803324338229363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34532661224568792941113205 3237436989803324338229363)
                      ·
                        rfl

theorem cell23_6304886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 3, 2, 1, 5].length) (baseStart_6304886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6304886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6304886 prefixEnd_6304886 := by exact prefixLift 6304886
  have htrace : WordTrace (prefixWord ++ tailWord_6304886) baseStart_6304886 baseEnd_6304886 := by
    simpa [prefixWord, tailWord_6304886, baseEnd_6304886] using wordTrace_append hprefix tailTrace_6304886
  have hstable : (prefixWord ++ tailWord_6304886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6304886).length < 2 ^ (prefixWord ++ tailWord_6304886).sum := by decide
  have hdescent : baseEnd_6304886 < baseStart_6304886 := by decide
  rcases family_descends (prefixWord ++ tailWord_6304886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6304900 : List Nat := [2, 3, 2, 1, 2, 2, 1, 4, 2, 2, 2]
def baseStart_6304900 : Nat := 118140960795 + 6304900 * 2 ^ 59
def prefixEnd_6304900 : Nat := 4983230072969 + 3 ^ 40 * 6304900 * 2
def baseEnd_6304900 : Nat := 3237444178532487283454299

theorem tailTrace_6304900 : CollatzResearch.WordTrace tailWord_6304900 prefixEnd_6304900 3237444178532487283454299 := by
  unfold tailWord_6304900
  simp only [CollatzResearch.WordTrace]
  refine ⟨114979297429215783018692077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153305729905621044024922769 114979297429215783018692077)
  ·
    refine ⟨43117236535955918632009529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114979297429215783018692077 43117236535955918632009529)
    ·
      refine ⟨32337927401966938974007147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43117236535955918632009529 32337927401966938974007147)
      ·
        refine ⟨48506891102950408461010721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32337927401966938974007147 48506891102950408461010721)
        ·
          refine ⟨36380168327212806345758041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48506891102950408461010721 36380168327212806345758041)
          ·
            refine ⟨27285126245409604759318531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36380168327212806345758041 27285126245409604759318531)
            ·
              refine ⟨40927689368114407138977797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27285126245409604759318531 40927689368114407138977797)
              ·
                refine ⟨7673941756521451338558337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40927689368114407138977797 7673941756521451338558337)
                ·
                  refine ⟨5755456317391088503918753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7673941756521451338558337 5755456317391088503918753)
                  ·
                    refine ⟨4316592238043316377939065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5755456317391088503918753 4316592238043316377939065)
                    ·
                      refine ⟨3237444178532487283454299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4316592238043316377939065 3237444178532487283454299)
                      ·
                        rfl

theorem cell23_6304900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 4, 2, 2, 2].length) (baseStart_6304900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6304900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6304900 prefixEnd_6304900 := by exact prefixLift 6304900
  have htrace : WordTrace (prefixWord ++ tailWord_6304900) baseStart_6304900 baseEnd_6304900 := by
    simpa [prefixWord, tailWord_6304900, baseEnd_6304900] using wordTrace_append hprefix tailTrace_6304900
  have hstable : (prefixWord ++ tailWord_6304900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6304900).length < 2 ^ (prefixWord ++ tailWord_6304900).sum := by decide
  have hdescent : baseEnd_6304900 < baseStart_6304900 := by decide
  rcases family_descends (prefixWord ++ tailWord_6304900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6304959 : List Nat := [1, 1, 2, 2, 2, 2, 2, 1, 2, 3, 5]
def baseStart_6304959 : Nat := 118140960795 + 6304959 * 2 ^ 59
def prefixEnd_6304959 : Nat := 4983230072969 + 3 ^ 40 * 6304959 * 2
def baseEnd_6304959 : Nat := 3237474473891102552616527

theorem tailTrace_6304959 : CollatzResearch.WordTrace tailWord_6304959 prefixEnd_6304959 3237474473891102552616527 := by
  unfold tailWord_6304959
  simp only [CollatzResearch.WordTrace]
  refine ⟨229960746765217819113781931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153307164510145212742521287 229960746765217819113781931)
  ·
    refine ⟨344941120147826728670672897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229960746765217819113781931 344941120147826728670672897)
    ·
      refine ⟨258705840110870046503004673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 344941120147826728670672897 258705840110870046503004673)
      ·
        refine ⟨194029380083152534877253505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 258705840110870046503004673 194029380083152534877253505)
        ·
          refine ⟨145522035062364401157940129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 194029380083152534877253505 145522035062364401157940129)
          ·
            refine ⟨109141526296773300868455097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 145522035062364401157940129 109141526296773300868455097)
            ·
              refine ⟨81856144722579975651341323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 109141526296773300868455097 81856144722579975651341323)
              ·
                refine ⟨122784217083869963477011985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81856144722579975651341323 122784217083869963477011985)
                ·
                  refine ⟨92088162812902472607758989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 122784217083869963477011985 92088162812902472607758989)
                  ·
                    refine ⟨34533061054838427227909621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 92088162812902472607758989 34533061054838427227909621)
                    ·
                      refine ⟨3237474473891102552616527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34533061054838427227909621 3237474473891102552616527)
                      ·
                        rfl

theorem cell23_6304959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 1, 2, 3, 5].length) (baseStart_6304959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6304959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6304959 prefixEnd_6304959 := by exact prefixLift 6304959
  have htrace : WordTrace (prefixWord ++ tailWord_6304959) baseStart_6304959 baseEnd_6304959 := by
    simpa [prefixWord, tailWord_6304959, baseEnd_6304959] using wordTrace_append hprefix tailTrace_6304959
  have hstable : (prefixWord ++ tailWord_6304959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6304959).length < 2 ^ (prefixWord ++ tailWord_6304959).sum := by decide
  have hdescent : baseEnd_6304959 < baseStart_6304959 := by decide
  rcases family_descends (prefixWord ++ tailWord_6304959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6305010 : List Nat := [3, 2, 1, 3, 3, 1, 1, 2, 2, 2, 3]
def baseStart_6305010 : Nat := 118140960795 + 6305010 * 2 ^ 59
def prefixEnd_6305010 : Nat := 4983230072969 + 3 ^ 40 * 6305010 * 2
def baseEnd_6305010 : Nat := 3237500661404481853078793

theorem tailTrace_6305010 : CollatzResearch.WordTrace tailWord_6305010 prefixEnd_6305010 3237500661404481853078793 := by
  unfold tailWord_6305010
  simp only [CollatzResearch.WordTrace]
  refine ⟨57490651722008263705972121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153308404592022036549258989 57490651722008263705972121)
  ·
    refine ⟨43117988791506197779479091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57490651722008263705972121 43117988791506197779479091)
    ·
      refine ⟨64676983187259296669218637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43117988791506197779479091 64676983187259296669218637)
      ·
        refine ⟨24253868695222236250956989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64676983187259296669218637 24253868695222236250956989)
        ·
          refine ⟨9095200760708338594108871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24253868695222236250956989 9095200760708338594108871)
          ·
            refine ⟨13642801141062507891163307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9095200760708338594108871 13642801141062507891163307)
            ·
              refine ⟨20464201711593761836744961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13642801141062507891163307 20464201711593761836744961)
              ·
                refine ⟨15348151283695321377558721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20464201711593761836744961 15348151283695321377558721)
                ·
                  refine ⟨11511113462771491033169041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15348151283695321377558721 11511113462771491033169041)
                  ·
                    refine ⟨8633335097078618274876781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11511113462771491033169041 8633335097078618274876781)
                    ·
                      refine ⟨3237500661404481853078793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8633335097078618274876781 3237500661404481853078793)
                      ·
                        rfl

theorem cell23_6305010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 1, 2, 2, 2, 3].length) (baseStart_6305010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6305010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6305010 prefixEnd_6305010 := by exact prefixLift 6305010
  have htrace : WordTrace (prefixWord ++ tailWord_6305010) baseStart_6305010 baseEnd_6305010 := by
    simpa [prefixWord, tailWord_6305010, baseEnd_6305010] using wordTrace_append hprefix tailTrace_6305010
  have hstable : (prefixWord ++ tailWord_6305010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6305010).length < 2 ^ (prefixWord ++ tailWord_6305010).sum := by decide
  have hdescent : baseEnd_6305010 < baseStart_6305010 := by decide
  rcases family_descends (prefixWord ++ tailWord_6305010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6305033 : List Nat := [1, 2, 1, 1, 3, 3, 1, 2, 4, 3, 2]
def baseStart_6305033 : Nat := 118140960795 + 6305033 * 2 ^ 59
def prefixEnd_6305033 : Nat := 4983230072969 + 3 ^ 40 * 6305033 * 2
def baseEnd_6305033 : Nat := 3237512471459535263091187

theorem tailTrace_6305033 : CollatzResearch.WordTrace tailWord_6305033 prefixEnd_6305033 3237512471459535263091187 := by
  unfold tailWord_6305033
  simp only [CollatzResearch.WordTrace]
  refine ⟨229963445766949729751975753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153308963844633153167983835 229963445766949729751975753)
  ·
    refine ⟨172472584325212297313981815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 229963445766949729751975753 172472584325212297313981815)
    ·
      refine ⟨258708876487818445970972723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172472584325212297313981815 258708876487818445970972723)
      ·
        refine ⟨388063314731727668956459085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 258708876487818445970972723 388063314731727668956459085)
        ·
          refine ⟨145523743024397875858672157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 388063314731727668956459085 145523743024397875858672157)
          ·
            refine ⟨54571403634149203447002059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 145523743024397875858672157 54571403634149203447002059)
            ·
              refine ⟨81857105451223805170503089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54571403634149203447002059 81857105451223805170503089)
              ·
                refine ⟨61392829088417853877877317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 81857105451223805170503089 61392829088417853877877317)
                ·
                  refine ⟨11511155454078347602101997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 61392829088417853877877317 11511155454078347602101997)
                  ·
                    refine ⟨4316683295279380350788249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11511155454078347602101997 4316683295279380350788249)
                    ·
                      refine ⟨3237512471459535263091187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4316683295279380350788249 3237512471459535263091187)
                      ·
                        rfl

theorem cell23_6305033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 2, 4, 3, 2].length) (baseStart_6305033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6305033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6305033 prefixEnd_6305033 := by exact prefixLift 6305033
  have htrace : WordTrace (prefixWord ++ tailWord_6305033) baseStart_6305033 baseEnd_6305033 := by
    simpa [prefixWord, tailWord_6305033, baseEnd_6305033] using wordTrace_append hprefix tailTrace_6305033
  have hstable : (prefixWord ++ tailWord_6305033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6305033).length < 2 ^ (prefixWord ++ tailWord_6305033).sum := by decide
  have hdescent : baseEnd_6305033 < baseStart_6305033 := by decide
  rcases family_descends (prefixWord ++ tailWord_6305033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6305050 : List Nat := [3, 1, 1, 3, 3, 1, 1, 3, 2, 3, 2]
def baseStart_6305050 : Nat := 118140960795 + 6305050 * 2 ^ 59
def prefixEnd_6305050 : Nat := 4983230072969 + 3 ^ 40 * 6305050 * 2
def baseEnd_6305050 : Nat := 3237521200630661696578609

theorem tailTrace_6305050 : CollatzResearch.WordTrace tailWord_6305050 prefixEnd_6305050 3237521200630661696578609 := by
  unfold tailWord_6305050
  simp only [CollatzResearch.WordTrace]
  refine ⟨57491016451972035413836151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153309377205258761103563069 57491016451972035413836151)
  ·
    refine ⟨86236524677958053120754227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57491016451972035413836151 86236524677958053120754227)
    ·
      refine ⟨129354787016937079681131341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86236524677958053120754227 129354787016937079681131341)
      ·
        refine ⟨48508045131351404880424253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 129354787016937079681131341 48508045131351404880424253)
        ·
          refine ⟨18190516924256776830159095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48508045131351404880424253 18190516924256776830159095)
          ·
            refine ⟨27285775386385165245238643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18190516924256776830159095 27285775386385165245238643)
            ·
              refine ⟨40928663079577747867857965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27285775386385165245238643 40928663079577747867857965)
              ·
                refine ⟨15348248654841655450446737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40928663079577747867857965 15348248654841655450446737)
                ·
                  refine ⟨11511186491131241587835053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15348248654841655450446737 11511186491131241587835053)
                  ·
                    refine ⟨4316694934174215595438145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11511186491131241587835053 4316694934174215595438145)
                    ·
                      refine ⟨3237521200630661696578609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4316694934174215595438145 3237521200630661696578609)
                      ·
                        rfl

theorem cell23_6305050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 3, 2, 3, 2].length) (baseStart_6305050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6305050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6305050 prefixEnd_6305050 := by exact prefixLift 6305050
  have htrace : WordTrace (prefixWord ++ tailWord_6305050) baseStart_6305050 baseEnd_6305050 := by
    simpa [prefixWord, tailWord_6305050, baseEnd_6305050] using wordTrace_append hprefix tailTrace_6305050
  have hstable : (prefixWord ++ tailWord_6305050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6305050).length < 2 ^ (prefixWord ++ tailWord_6305050).sum := by decide
  have hdescent : baseEnd_6305050 < baseStart_6305050 := by decide
  rcases family_descends (prefixWord ++ tailWord_6305050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6305060 : List Nat := [2, 3, 1, 3, 1, 1, 5, 1, 1, 5]
def baseStart_6305060 : Nat := 118140960795 + 6305060 * 2 ^ 59
def prefixEnd_6305060 : Nat := 4983230072969 + 3 ^ 40 * 6305060 * 2
def baseEnd_6305060 : Nat := 1079175445145735552484521

theorem tailTrace_6305060 : CollatzResearch.WordTrace tailWord_6305060 prefixEnd_6305060 1079175445145735552484521 := by
  unfold tailWord_6305060
  simp only [CollatzResearch.WordTrace]
  refine ⟨114982215268925956681604317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153309620358567942242139089 114982215268925956681604317)
  ·
    refine ⟨43118330725847233755601619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114982215268925956681604317 43118330725847233755601619)
    ·
      refine ⟨64677496088770850633402429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43118330725847233755601619 64677496088770850633402429)
      ·
        refine ⟨24254061033289068987525911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64677496088770850633402429 24254061033289068987525911)
        ·
          refine ⟨36381091549933603481288867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24254061033289068987525911 36381091549933603481288867)
          ·
            refine ⟨54571637324900405221933301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36381091549933603481288867 54571637324900405221933301)
            ·
              refine ⟨5116090999209412989556247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 54571637324900405221933301 5116090999209412989556247)
              ·
                refine ⟨7674136498814119484334371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5116090999209412989556247 7674136498814119484334371)
                ·
                  refine ⟨11511204748221179226501557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7674136498814119484334371 11511204748221179226501557)
                  ·
                    refine ⟨1079175445145735552484521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11511204748221179226501557 1079175445145735552484521)
                    ·
                      rfl

theorem cell23_6305060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 5, 1, 1, 5].length) (baseStart_6305060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6305060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6305060 prefixEnd_6305060 := by exact prefixLift 6305060
  have htrace : WordTrace (prefixWord ++ tailWord_6305060) baseStart_6305060 baseEnd_6305060 := by
    simpa [prefixWord, tailWord_6305060, baseEnd_6305060] using wordTrace_append hprefix tailTrace_6305060
  have hstable : (prefixWord ++ tailWord_6305060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6305060).length < 2 ^ (prefixWord ++ tailWord_6305060).sum := by decide
  have hdescent : baseEnd_6305060 < baseStart_6305060 := by decide
  rcases family_descends (prefixWord ++ tailWord_6305060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6305074 : List Nat := [3, 2, 1, 1, 4, 1, 4, 2, 1, 1, 3]
def baseStart_6305074 : Nat := 118140960795 + 6305074 * 2 ^ 59
def prefixEnd_6305074 : Nat := 4983230072969 + 3 ^ 40 * 6305074 * 2
def baseEnd_6305074 : Nat := 3237533524166369602678499

theorem tailTrace_6305074 : CollatzResearch.WordTrace tailWord_6305074 prefixEnd_6305074 3237533524166369602678499 := by
  unfold tailWord_6305074
  simp only [CollatzResearch.WordTrace]
  refine ⟨57491235289950298438554569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153309960773200795836145517 57491235289950298438554569)
  ·
    refine ⟨43118426467462723828915927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57491235289950298438554569 43118426467462723828915927)
    ·
      refine ⟨64677639701194085743373891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43118426467462723828915927 64677639701194085743373891)
      ·
        refine ⟨97016459551791128615060837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64677639701194085743373891 97016459551791128615060837)
        ·
          refine ⟨18190586165960836615323907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 97016459551791128615060837 18190586165960836615323907)
          ·
            refine ⟨27285879248941254922985861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18190586165960836615323907 27285879248941254922985861)
            ·
              refine ⟨5116102359176485298059849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27285879248941254922985861 5116102359176485298059849)
              ·
                refine ⟨3837076769382363973544887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5116102359176485298059849 3837076769382363973544887)
                ·
                  refine ⟨5755615154073545960317331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3837076769382363973544887 5755615154073545960317331)
                  ·
                    refine ⟨8633422731110318940475997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5755615154073545960317331 8633422731110318940475997)
                    ·
                      refine ⟨3237533524166369602678499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8633422731110318940475997 3237533524166369602678499)
                      ·
                        rfl

theorem cell23_6305074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 4, 2, 1, 1, 3].length) (baseStart_6305074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6305074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6305074 prefixEnd_6305074 := by exact prefixLift 6305074
  have htrace : WordTrace (prefixWord ++ tailWord_6305074) baseStart_6305074 baseEnd_6305074 := by
    simpa [prefixWord, tailWord_6305074, baseEnd_6305074] using wordTrace_append hprefix tailTrace_6305074
  have hstable : (prefixWord ++ tailWord_6305074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6305074).length < 2 ^ (prefixWord ++ tailWord_6305074).sum := by decide
  have hdescent : baseEnd_6305074 < baseStart_6305074 := by decide
  rcases family_descends (prefixWord ++ tailWord_6305074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6305080 : List Nat := [2, 1, 2, 1, 3, 1, 1, 5, 3, 2, 2]
def baseStart_6305080 : Nat := 118140960795 + 6305080 * 2 ^ 59
def prefixEnd_6305080 : Nat := 4983230072969 + 3 ^ 40 * 6305080 * 2
def baseEnd_6305080 : Nat := 3237536605050296579203471

theorem tailTrace_6305080 : CollatzResearch.WordTrace tailWord_6305080 prefixEnd_6305080 3237536605050296579203471 := by
  unfold tailWord_6305080
  simp only [CollatzResearch.WordTrace]
  refine ⟨114982579998889728389468347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153310106665186304519291129 114982579998889728389468347)
  ·
    refine ⟨172473869998334592584202521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114982579998889728389468347 172473869998334592584202521)
    ·
      refine ⟨129355402498750944438151891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 172473869998334592584202521 129355402498750944438151891)
      ·
        refine ⟨194033103748126416657227837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129355402498750944438151891 194033103748126416657227837)
        ·
          refine ⟨72762413905547406246460439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 194033103748126416657227837 72762413905547406246460439)
          ·
            refine ⟨109143620858321109369690659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72762413905547406246460439 109143620858321109369690659)
            ·
              refine ⟨163715431287481664054535989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109143620858321109369690659 163715431287481664054535989)
              ·
                refine ⟨15348321683201406005112749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 163715431287481664054535989 15348321683201406005112749)
                ·
                  refine ⟨5755620631200527251917281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15348321683201406005112749 5755620631200527251917281)
                  ·
                    refine ⟨4316715473400395438937961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5755620631200527251917281 4316715473400395438937961)
                    ·
                      refine ⟨3237536605050296579203471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4316715473400395438937961 3237536605050296579203471)
                      ·
                        rfl

theorem cell23_6305080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 5, 3, 2, 2].length) (baseStart_6305080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6305080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6305080 prefixEnd_6305080 := by exact prefixLift 6305080
  have htrace : WordTrace (prefixWord ++ tailWord_6305080) baseStart_6305080 baseEnd_6305080 := by
    simpa [prefixWord, tailWord_6305080, baseEnd_6305080] using wordTrace_append hprefix tailTrace_6305080
  have hstable : (prefixWord ++ tailWord_6305080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6305080).length < 2 ^ (prefixWord ++ tailWord_6305080).sum := by decide
  have hdescent : baseEnd_6305080 < baseStart_6305080 := by decide
  rcases family_descends (prefixWord ++ tailWord_6305080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6305101 : List Nat := [1, 6, 1, 3, 1, 2, 1, 1, 2, 3, 2]
def baseStart_6305101 : Nat := 118140960795 + 6305101 * 2 ^ 59
def prefixEnd_6305101 : Nat := 4983230072969 + 3 ^ 40 * 6305101 * 2
def baseEnd_6305101 : Nat := 3237547388144040997040875

theorem tailTrace_6305101 : CollatzResearch.WordTrace tailWord_6305101 prefixEnd_6305101 3237547388144040997040875 := by
  unfold tailWord_6305101
  simp only [CollatzResearch.WordTrace]
  refine ⟨229965925930703377365451157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153310617287135584910300771 229965925930703377365451157)
  ·
    refine ⟨10779652778001720814005523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 229965925930703377365451157 10779652778001720814005523)
    ·
      refine ⟨16169479167002581221008285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10779652778001720814005523 16169479167002581221008285)
      ·
        refine ⟨6063554687625967957878107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16169479167002581221008285 6063554687625967957878107)
        ·
          refine ⟨9095332031438951936817161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6063554687625967957878107 9095332031438951936817161)
          ·
            refine ⟨6821499023579213952612871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9095332031438951936817161 6821499023579213952612871)
            ·
              refine ⟨10232248535368820928919307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6821499023579213952612871 10232248535368820928919307)
              ·
                refine ⟨15348372803053231393378961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10232248535368820928919307 15348372803053231393378961)
                ·
                  refine ⟨11511279602289923545034221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15348372803053231393378961 11511279602289923545034221)
                  ·
                    refine ⟨4316729850858721329387833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11511279602289923545034221 4316729850858721329387833)
                    ·
                      refine ⟨3237547388144040997040875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4316729850858721329387833 3237547388144040997040875)
                      ·
                        rfl

theorem cell23_6305101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 2, 1, 1, 2, 3, 2].length) (baseStart_6305101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6305101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6305101 prefixEnd_6305101 := by exact prefixLift 6305101
  have htrace : WordTrace (prefixWord ++ tailWord_6305101) baseStart_6305101 baseEnd_6305101 := by
    simpa [prefixWord, tailWord_6305101, baseEnd_6305101] using wordTrace_append hprefix tailTrace_6305101
  have hstable : (prefixWord ++ tailWord_6305101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6305101).length < 2 ^ (prefixWord ++ tailWord_6305101).sum := by decide
  have hdescent : baseEnd_6305101 < baseStart_6305101 := by decide
  rcases family_descends (prefixWord ++ tailWord_6305101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6305113 : List Nat := [1, 2, 1, 2, 2, 2, 4, 2, 1, 3, 3]
def baseStart_6305113 : Nat := 118140960795 + 6305113 * 2 ^ 59
def prefixEnd_6305113 : Nat := 4983230072969 + 3 ^ 40 * 6305113 * 2
def baseEnd_6305113 : Nat := 3237553549911894950090819

theorem tailTrace_6305113 : CollatzResearch.WordTrace tailWord_6305113 prefixEnd_6305113 3237553549911894950090819 := by
  unfold tailWord_6305113
  simp only [CollatzResearch.WordTrace]
  refine ⟨229966363606659903414887993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153310909071106602276591995 229966363606659903414887993)
  ·
    refine ⟨172474772704994927561165995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 229966363606659903414887993 172474772704994927561165995)
    ·
      refine ⟨258712159057492391341748993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172474772704994927561165995 258712159057492391341748993)
      ·
        refine ⟨194034119293119293506311745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 258712159057492391341748993 194034119293119293506311745)
        ·
          refine ⟨145525589469839470129733809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 194034119293119293506311745 145525589469839470129733809)
          ·
            refine ⟨109144192102379602597300357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 145525589469839470129733809 109144192102379602597300357)
            ·
              refine ⟨20464536019196175486993817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 109144192102379602597300357 20464536019196175486993817)
              ·
                refine ⟨15348402014397131615245363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20464536019196175486993817 15348402014397131615245363)
                ·
                  refine ⟨23022603021595697422868045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15348402014397131615245363 23022603021595697422868045)
                  ·
                    refine ⟨8633476133098386533575517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23022603021595697422868045 8633476133098386533575517)
                    ·
                      refine ⟨3237553549911894950090819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8633476133098386533575517 3237553549911894950090819)
                      ·
                        rfl

theorem cell23_6305113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 4, 2, 1, 3, 3].length) (baseStart_6305113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6305113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6305113 prefixEnd_6305113 := by exact prefixLift 6305113
  have htrace : WordTrace (prefixWord ++ tailWord_6305113) baseStart_6305113 baseEnd_6305113 := by
    simpa [prefixWord, tailWord_6305113, baseEnd_6305113] using wordTrace_append hprefix tailTrace_6305113
  have hstable : (prefixWord ++ tailWord_6305113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6305113).length < 2 ^ (prefixWord ++ tailWord_6305113).sum := by decide
  have hdescent : baseEnd_6305113 < baseStart_6305113 := by decide
  rcases family_descends (prefixWord ++ tailWord_6305113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6305147 : List Nat := [1, 1, 1, 1, 1, 6, 5, 1, 2, 1, 3]
def baseStart_6305147 : Nat := 118140960795 + 6305147 * 2 ^ 59
def prefixEnd_6305147 : Nat := 4983230072969 + 3 ^ 40 * 6305147 * 2
def baseEnd_6305147 : Nat := 3237571008254147817065663

theorem tailTrace_6305147 : CollatzResearch.WordTrace tailWord_6305147 prefixEnd_6305147 3237571008254147817065663 := by
  unfold tailWord_6305147
  simp only [CollatzResearch.WordTrace]
  refine ⟨229967603688536727221625695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153311735792357818147750463 229967603688536727221625695)
  ·
    refine ⟨344951405532805090832438543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229967603688536727221625695 344951405532805090832438543)
    ·
      refine ⟨517427108299207636248657815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 344951405532805090832438543 517427108299207636248657815)
      ·
        refine ⟨776140662448811454372986723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 517427108299207636248657815 776140662448811454372986723)
        ·
          refine ⟨1164210993673217181559480085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 776140662448811454372986723 1164210993673217181559480085)
          ·
            refine ⟨54572390328432055385600629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 1164210993673217181559480085 54572390328432055385600629)
            ·
              refine ⟨5116161593290505192400059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 54572390328432055385600629 5116161593290505192400059)
              ·
                refine ⟨7674242389935757788600089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5116161593290505192400059 7674242389935757788600089)
                ·
                  refine ⟨5755681792451818341450067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7674242389935757788600089 5755681792451818341450067)
                  ·
                    refine ⟨8633522688677727512175101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5755681792451818341450067 8633522688677727512175101)
                    ·
                      refine ⟨3237571008254147817065663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8633522688677727512175101 3237571008254147817065663)
                      ·
                        rfl

theorem cell23_6305147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 5, 1, 2, 1, 3].length) (baseStart_6305147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6305147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6305147 prefixEnd_6305147 := by exact prefixLift 6305147
  have htrace : WordTrace (prefixWord ++ tailWord_6305147) baseStart_6305147 baseEnd_6305147 := by
    simpa [prefixWord, tailWord_6305147, baseEnd_6305147] using wordTrace_append hprefix tailTrace_6305147
  have hstable : (prefixWord ++ tailWord_6305147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6305147).length < 2 ^ (prefixWord ++ tailWord_6305147).sum := by decide
  have hdescent : baseEnd_6305147 < baseStart_6305147 := by decide
  rcases family_descends (prefixWord ++ tailWord_6305147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6305187 : List Nat := [1, 1, 1, 4, 1, 3, 2, 4, 2, 2, 2]
def baseStart_6305187 : Nat := 118140960795 + 6305187 * 2 ^ 59
def prefixEnd_6305187 : Nat := 4983230072969 + 3 ^ 40 * 6305187 * 2
def baseEnd_6305187 : Nat := 3237591547480327660565479

theorem tailTrace_6305187 : CollatzResearch.WordTrace tailWord_6305187 prefixEnd_6305187 3237591547480327660565479 := by
  unfold tailWord_6305187
  simp only [CollatzResearch.WordTrace]
  refine ⟨229969062608391814053081815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153312708405594542702054543 229969062608391814053081815)
  ·
    refine ⟨344953593912587721079622723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229969062608391814053081815 344953593912587721079622723)
    ·
      refine ⟨517430390868881581619434085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 344953593912587721079622723 517430390868881581619434085)
      ·
        refine ⟨97018198287915296553643891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 517430390868881581619434085 97018198287915296553643891)
        ·
          refine ⟨145527297431872944830465837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97018198287915296553643891 145527297431872944830465837)
          ·
            refine ⟨54572736536952354311424689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 145527297431872944830465837 54572736536952354311424689)
            ·
              refine ⟨40929552402714265733568517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54572736536952354311424689 40929552402714265733568517)
              ·
                refine ⟨7674291075508924825044097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40929552402714265733568517 7674291075508924825044097)
                ·
                  refine ⟨5755718306631693618783073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7674291075508924825044097 5755718306631693618783073)
                  ·
                    refine ⟨4316788729973770214087305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5755718306631693618783073 4316788729973770214087305)
                    ·
                      refine ⟨3237591547480327660565479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4316788729973770214087305 3237591547480327660565479)
                      ·
                        rfl

theorem cell23_6305187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 4, 2, 2, 2].length) (baseStart_6305187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6305187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6305187 prefixEnd_6305187 := by exact prefixLift 6305187
  have htrace : WordTrace (prefixWord ++ tailWord_6305187) baseStart_6305187 baseEnd_6305187 := by
    simpa [prefixWord, tailWord_6305187, baseEnd_6305187] using wordTrace_append hprefix tailTrace_6305187
  have hstable : (prefixWord ++ tailWord_6305187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6305187).length < 2 ^ (prefixWord ++ tailWord_6305187).sum := by decide
  have hdescent : baseEnd_6305187 < baseStart_6305187 := by decide
  rcases family_descends (prefixWord ++ tailWord_6305187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6305203 : List Nat := [1, 1, 1, 2, 3, 1, 1, 5, 2, 3, 3]
def baseStart_6305203 : Nat := 118140960795 + 6305203 * 2 ^ 59
def prefixEnd_6305203 : Nat := 4983230072969 + 3 ^ 40 * 6305203 * 2
def baseEnd_6305203 : Nat := 3237599763170799597965405

theorem tailTrace_6305203 : CollatzResearch.WordTrace tailWord_6305203 prefixEnd_6305203 3237599763170799597965405 := by
  unfold tailWord_6305203
  simp only [CollatzResearch.WordTrace]
  refine ⟨229969646176333848785664263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153313097450889232523776175 229969646176333848785664263)
  ·
    refine ⟨344954469264500773178496395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229969646176333848785664263 344954469264500773178496395)
    ·
      refine ⟨517431703896751159767744593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 344954469264500773178496395 517431703896751159767744593)
      ·
        refine ⟨388073777922563369825808445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 517431703896751159767744593 388073777922563369825808445)
        ·
          refine ⟨145527666720961263684678167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 388073777922563369825808445 145527666720961263684678167)
          ·
            refine ⟨218291500081441895527017251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 145527666720961263684678167 218291500081441895527017251)
            ·
              refine ⟨327437250122162843290525877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 218291500081441895527017251 327437250122162843290525877)
              ·
                refine ⟨30697242198952766558486801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 327437250122162843290525877 30697242198952766558486801)
                ·
                  refine ⟨23022931649214574918865101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30697242198952766558486801 23022931649214574918865101)
                  ·
                    refine ⟨8633599368455465594574413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23022931649214574918865101 8633599368455465594574413)
                    ·
                      refine ⟨3237599763170799597965405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8633599368455465594574413 3237599763170799597965405)
                      ·
                        rfl

theorem cell23_6305203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 5, 2, 3, 3].length) (baseStart_6305203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6305203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6305203 prefixEnd_6305203 := by exact prefixLift 6305203
  have htrace : WordTrace (prefixWord ++ tailWord_6305203) baseStart_6305203 baseEnd_6305203 := by
    simpa [prefixWord, tailWord_6305203, baseEnd_6305203] using wordTrace_append hprefix tailTrace_6305203
  have hstable : (prefixWord ++ tailWord_6305203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6305203).length < 2 ^ (prefixWord ++ tailWord_6305203).sum := by decide
  have hdescent : baseEnd_6305203 < baseStart_6305203 := by decide
  rcases family_descends (prefixWord ++ tailWord_6305203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6305277 : List Nat := [1, 4, 1, 1, 1, 6, 1, 1, 2, 1, 4]
def baseStart_6305277 : Nat := 118140960795 + 6305277 * 2 ^ 59
def prefixEnd_6305277 : Nat := 4983230072969 + 3 ^ 40 * 6305277 * 2
def baseEnd_6305277 : Nat := 3237637760739232308440065

theorem tailTrace_6305277 : CollatzResearch.WordTrace tailWord_6305277 prefixEnd_6305277 3237637760739232308440065 := by
  unfold tailWord_6305277
  simp only [CollatzResearch.WordTrace]
  refine ⟨229972345178065759423858085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153314896785377172949238723 229972345178065759423858085)
  ·
    refine ⟨43119814720887329891973391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 229972345178065759423858085 43119814720887329891973391)
    ·
      refine ⟨64679722081330994837960087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43119814720887329891973391 64679722081330994837960087)
      ·
        refine ⟨97019583121996492256940131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64679722081330994837960087 97019583121996492256940131)
        ·
          refine ⟨145529374682994738385410197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97019583121996492256940131 145529374682994738385410197)
          ·
            refine ⟨6821689438265378361816103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 145529374682994738385410197 6821689438265378361816103)
            ·
              refine ⟨10232534157398067542724155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6821689438265378361816103 10232534157398067542724155)
              ·
                refine ⟨15348801236097101314086233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10232534157398067542724155 15348801236097101314086233)
                ·
                  refine ⟨11511600927072825985564675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15348801236097101314086233 11511600927072825985564675)
                  ·
                    refine ⟨17267401390609238978347013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11511600927072825985564675 17267401390609238978347013)
                    ·
                      refine ⟨3237637760739232308440065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17267401390609238978347013 3237637760739232308440065)
                      ·
                        rfl

theorem cell23_6305277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 6, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 6, 1, 1, 2, 1, 4].length) (baseStart_6305277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6305277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6305277 prefixEnd_6305277 := by exact prefixLift 6305277
  have htrace : WordTrace (prefixWord ++ tailWord_6305277) baseStart_6305277 baseEnd_6305277 := by
    simpa [prefixWord, tailWord_6305277, baseEnd_6305277] using wordTrace_append hprefix tailTrace_6305277
  have hstable : (prefixWord ++ tailWord_6305277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6305277).length < 2 ^ (prefixWord ++ tailWord_6305277).sum := by decide
  have hdescent : baseEnd_6305277 < baseStart_6305277 := by decide
  rcases family_descends (prefixWord ++ tailWord_6305277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6305337 : List Nat := [1, 2, 1, 5, 1, 2, 2, 1, 1, 5, 2]
def baseStart_6305337 : Nat := 118140960795 + 6305337 * 2 ^ 59
def prefixEnd_6305337 : Nat := 4983230072969 + 3 ^ 40 * 6305337 * 2
def baseEnd_6305337 : Nat := 3237668569578502073689789

theorem tailTrace_6305337 : CollatzResearch.WordTrace tailWord_6305337 prefixEnd_6305337 3237668569578502073689789 := by
  unfold tailWord_6305337
  simp only [CollatzResearch.WordTrace]
  refine ⟨229974533557848389671042265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153316355705232259780694843 229974533557848389671042265)
  ·
    refine ⟨172480900168386292253281699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 229974533557848389671042265 172480900168386292253281699)
    ·
      refine ⟨258721350252579438379922549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172480900168386292253281699 258721350252579438379922549)
      ·
        refine ⟨24255126586179322348117739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 258721350252579438379922549 24255126586179322348117739)
        ·
          refine ⟨36382689879268983522176609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24255126586179322348117739 36382689879268983522176609)
          ·
            refine ⟨27287017409451737641632457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36382689879268983522176609 27287017409451737641632457)
            ·
              refine ⟨20465263057088803231224343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27287017409451737641632457 20465263057088803231224343)
              ·
                refine ⟨30697894585633204846836515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20465263057088803231224343 30697894585633204846836515)
                ·
                  refine ⟨46046841878449807270254773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30697894585633204846836515 46046841878449807270254773)
                  ·
                    refine ⟨4316891426104669431586385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 46046841878449807270254773 4316891426104669431586385)
                    ·
                      refine ⟨3237668569578502073689789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4316891426104669431586385 3237668569578502073689789)
                      ·
                        rfl

theorem cell23_6305337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 2, 1, 1, 5, 2].length) (baseStart_6305337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6305337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6305337 prefixEnd_6305337 := by exact prefixLift 6305337
  have htrace : WordTrace (prefixWord ++ tailWord_6305337) baseStart_6305337 baseEnd_6305337 := by
    simpa [prefixWord, tailWord_6305337, baseEnd_6305337] using wordTrace_append hprefix tailTrace_6305337
  have hstable : (prefixWord ++ tailWord_6305337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6305337).length < 2 ^ (prefixWord ++ tailWord_6305337).sum := by decide
  have hdescent : baseEnd_6305337 < baseStart_6305337 := by decide
  rcases family_descends (prefixWord ++ tailWord_6305337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6305360 : List Nat := [2, 1, 1, 1, 1, 3, 3, 3, 4, 4]
def baseStart_6305360 : Nat := 118140960795 + 6305360 * 2 ^ 59
def prefixEnd_6305360 : Nat := 4983230072969 + 3 ^ 40 * 6305360 * 2
def baseEnd_6305360 : Nat := 1079226793211185161234061

theorem tailTrace_6305360 : CollatzResearch.WordTrace tailWord_6305360 prefixEnd_6305360 1079226793211185161234061 := by
  unfold tailWord_6305360
  simp only [CollatzResearch.WordTrace]
  refine ⟨114987686218382532299564767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153316914957843376399419689 114987686218382532299564767)
  ·
    refine ⟨172481529327573798449347151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114987686218382532299564767 172481529327573798449347151)
    ·
      refine ⟨258722293991360697674020727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172481529327573798449347151 258722293991360697674020727)
      ·
        refine ⟨388083440987041046511031091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 258722293991360697674020727 388083440987041046511031091)
        ·
          refine ⟨582125161480561569766546637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 388083440987041046511031091 582125161480561569766546637)
          ·
            refine ⟨218296935555210588662454989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 582125161480561569766546637 218296935555210588662454989)
            ·
              refine ⟨81861350833203970748420621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 218296935555210588662454989 81861350833203970748420621)
              ·
                refine ⟨30698006562451489030657733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 81861350833203970748420621 30698006562451489030657733)
                ·
                  refine ⟨5755876230459654193248325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30698006562451489030657733 5755876230459654193248325)
                  ·
                    refine ⟨1079226793211185161234061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5755876230459654193248325 1079226793211185161234061)
                    ·
                      rfl

theorem cell23_6305360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 3, 4, 4].length) (baseStart_6305360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6305360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6305360 prefixEnd_6305360 := by exact prefixLift 6305360
  have htrace : WordTrace (prefixWord ++ tailWord_6305360) baseStart_6305360 baseEnd_6305360 := by
    simpa [prefixWord, tailWord_6305360, baseEnd_6305360] using wordTrace_append hprefix tailTrace_6305360
  have hstable : (prefixWord ++ tailWord_6305360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6305360).length < 2 ^ (prefixWord ++ tailWord_6305360).sum := by decide
  have hdescent : baseEnd_6305360 < baseStart_6305360 := by decide
  rcases family_descends (prefixWord ++ tailWord_6305360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6305361 : List Nat := [1, 2, 2, 1, 3, 2, 5, 2, 1, 1, 3]
def baseStart_6305361 : Nat := 118140960795 + 6305361 * 2 ^ 59
def prefixEnd_6305361 : Nat := 4983230072969 + 3 ^ 40 * 6305361 * 2
def baseEnd_6305361 : Nat := 3237680893114209979789679

theorem tailTrace_6305361 : CollatzResearch.WordTrace tailWord_6305361 prefixEnd_6305361 3237680893114209979789679 := by
  unfold tailWord_6305361
  simp only [CollatzResearch.WordTrace]
  refine ⟨229975408909761441769915937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153316939273174294513277291 229975408909761441769915937)
  ·
    refine ⟨172481556682321081327436953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 229975408909761441769915937 172481556682321081327436953)
    ·
      refine ⟨129361167511740810995577715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 172481556682321081327436953 129361167511740810995577715)
      ·
        refine ⟨194041751267611216493366573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129361167511740810995577715 194041751267611216493366573)
        ·
          refine ⟨72765656725354206185012465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 194041751267611216493366573 72765656725354206185012465)
          ·
            refine ⟨54574242544015654638759349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72765656725354206185012465 54574242544015654638759349)
            ·
              refine ⟨5116335238501467622383689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 54574242544015654638759349 5116335238501467622383689)
              ·
                refine ⟨3837251428876100716787767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5116335238501467622383689 3837251428876100716787767)
                ·
                  refine ⟨5755877143314151075181651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3837251428876100716787767 5755877143314151075181651)
                  ·
                    refine ⟨8633815714971226612772477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5755877143314151075181651 8633815714971226612772477)
                    ·
                      refine ⟨3237680893114209979789679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8633815714971226612772477 3237680893114209979789679)
                      ·
                        rfl

theorem cell23_6305361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 5, 2, 1, 1, 3].length) (baseStart_6305361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6305361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6305361 prefixEnd_6305361 := by exact prefixLift 6305361
  have htrace : WordTrace (prefixWord ++ tailWord_6305361) baseStart_6305361 baseEnd_6305361 := by
    simpa [prefixWord, tailWord_6305361, baseEnd_6305361] using wordTrace_append hprefix tailTrace_6305361
  have hstable : (prefixWord ++ tailWord_6305361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6305361).length < 2 ^ (prefixWord ++ tailWord_6305361).sum := by decide
  have hdescent : baseEnd_6305361 < baseStart_6305361 := by decide
  rcases family_descends (prefixWord ++ tailWord_6305361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6305377 : List Nat := [1, 2, 3, 1, 1, 3, 3, 3, 2, 4]
def baseStart_6305377 : Nat := 118140960795 + 6305377 * 2 ^ 59
def prefixEnd_6305377 : Nat := 4983230072969 + 3 ^ 40 * 6305377 * 2
def baseEnd_6305377 : Nat := 1079229702934893972396535

theorem tailTrace_6305377 : CollatzResearch.WordTrace tailWord_6305377 prefixEnd_6305377 1079229702934893972396535 := by
  unfold tailWord_6305377
  simp only [CollatzResearch.WordTrace]
  refine ⟨229975992477703476502498385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153317328318468984334998923 229975992477703476502498385)
  ·
    refine ⟨172481994358277607376873789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 229975992477703476502498385 172481994358277607376873789)
    ·
      refine ⟨64680747884354102766327671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 172481994358277607376873789 64680747884354102766327671)
      ·
        refine ⟨97021121826531154149491507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64680747884354102766327671 97021121826531154149491507)
        ·
          refine ⟨145531682739796731224237261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97021121826531154149491507 145531682739796731224237261)
          ·
            refine ⟨54574381027423774209088973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 145531682739796731224237261 54574381027423774209088973)
            ·
              refine ⟨20465392885283915328408365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54574381027423774209088973 20465392885283915328408365)
              ·
                refine ⟨7674522331981468248153137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20465392885283915328408365 7674522331981468248153137)
                ·
                  refine ⟨5755891748986101186114853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7674522331981468248153137 5755891748986101186114853)
                  ·
                    refine ⟨1079229702934893972396535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5755891748986101186114853 1079229702934893972396535)
                    ·
                      rfl

theorem cell23_6305377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 3, 3, 2, 4].length) (baseStart_6305377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6305377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6305377 prefixEnd_6305377 := by exact prefixLift 6305377
  have htrace : WordTrace (prefixWord ++ tailWord_6305377) baseStart_6305377 baseEnd_6305377 := by
    simpa [prefixWord, tailWord_6305377, baseEnd_6305377] using wordTrace_append hprefix tailTrace_6305377
  have hstable : (prefixWord ++ tailWord_6305377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6305377).length < 2 ^ (prefixWord ++ tailWord_6305377).sum := by decide
  have hdescent : baseEnd_6305377 < baseStart_6305377 := by decide
  rcases family_descends (prefixWord ++ tailWord_6305377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6305380 : List Nat := [2, 3, 1, 1, 2, 3, 2, 1, 1, 1, 6]
def baseStart_6305380 : Nat := 118140960795 + 6305380 * 2 ^ 59
def prefixEnd_6305380 : Nat := 4983230072969 + 3 ^ 40 * 6305380 * 2
def baseEnd_6305380 : Nat := 3237690649246645405452091

theorem tailTrace_6305380 : CollatzResearch.WordTrace tailWord_6305380 prefixEnd_6305380 3237690649246645405452091 := by
  unfold tailWord_6305380
  simp only [CollatzResearch.WordTrace]
  refine ⟨114988050948346304007428797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153317401264461738676571729 114988050948346304007428797)
  ·
    refine ⟨43120519105629864002785799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114988050948346304007428797 43120519105629864002785799)
    ·
      refine ⟨64680778658444796004178699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43120519105629864002785799 64680778658444796004178699)
      ·
        refine ⟨97021167987667194006268049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64680778658444796004178699 97021167987667194006268049)
        ·
          refine ⟨72765875990750395504701037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97021167987667194006268049 72765875990750395504701037)
          ·
            refine ⟨27287203496531398314262889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72765875990750395504701037 27287203496531398314262889)
            ·
              refine ⟨20465402622398548735697167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27287203496531398314262889 20465402622398548735697167)
              ·
                refine ⟨30698103933597823103545751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20465402622398548735697167 30698103933597823103545751)
                ·
                  refine ⟨46047155900396734655318627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30698103933597823103545751 46047155900396734655318627)
                  ·
                    refine ⟨69070733850595101982977941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 46047155900396734655318627 69070733850595101982977941)
                    ·
                      refine ⟨3237690649246645405452091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 69070733850595101982977941 3237690649246645405452091)
                      ·
                        rfl

theorem cell23_6305380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 2, 1, 1, 1, 6].length) (baseStart_6305380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6305380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6305380 prefixEnd_6305380 := by exact prefixLift 6305380
  have htrace : WordTrace (prefixWord ++ tailWord_6305380) baseStart_6305380 baseEnd_6305380 := by
    simpa [prefixWord, tailWord_6305380, baseEnd_6305380] using wordTrace_append hprefix tailTrace_6305380
  have hstable : (prefixWord ++ tailWord_6305380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6305380).length < 2 ^ (prefixWord ++ tailWord_6305380).sum := by decide
  have hdescent : baseEnd_6305380 < baseStart_6305380 := by decide
  rcases family_descends (prefixWord ++ tailWord_6305380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6305384 : List Nat := [2, 1, 4, 3, 1, 1, 3, 2, 1, 1, 4]
def baseStart_6305384 : Nat := 118140960795 + 6305384 * 2 ^ 59
def prefixEnd_6305384 : Nat := 4983230072969 + 3 ^ 40 * 6305384 * 2
def baseEnd_6305384 : Nat := 3237692703169263389802073

theorem tailTrace_6305384 : CollatzResearch.WordTrace tailWord_6305384 prefixEnd_6305384 3237692703169263389802073 := by
  unfold tailWord_6305384
  simp only [CollatzResearch.WordTrace]
  refine ⟨114988123894339058349001603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153317498525785411132002137 114988123894339058349001603)
  ·
    refine ⟨172482185841508587523502405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114988123894339058349001603 172482185841508587523502405)
    ·
      refine ⟨32340409845282860160656701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 172482185841508587523502405 32340409845282860160656701)
      ·
        refine ⟨12127653691981072560246263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32340409845282860160656701 12127653691981072560246263)
        ·
          refine ⟨18191480537971608840369395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12127653691981072560246263 18191480537971608840369395)
          ·
            refine ⟨27287220806957413260554093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18191480537971608840369395 27287220806957413260554093)
            ·
              refine ⟨10232707802609029972707785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27287220806957413260554093 10232707802609029972707785)
              ·
                refine ⟨7674530851956772479530839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10232707802609029972707785 7674530851956772479530839)
                ·
                  refine ⟨11511796277935158719296259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7674530851956772479530839 11511796277935158719296259)
                  ·
                    refine ⟨17267694416902738078944389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11511796277935158719296259 17267694416902738078944389)
                    ·
                      refine ⟨3237692703169263389802073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17267694416902738078944389 3237692703169263389802073)
                      ·
                        rfl

theorem cell23_6305384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 3, 2, 1, 1, 4].length) (baseStart_6305384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6305384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6305384 prefixEnd_6305384 := by exact prefixLift 6305384
  have htrace : WordTrace (prefixWord ++ tailWord_6305384) baseStart_6305384 baseEnd_6305384 := by
    simpa [prefixWord, tailWord_6305384, baseEnd_6305384] using wordTrace_append hprefix tailTrace_6305384
  have hstable : (prefixWord ++ tailWord_6305384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6305384).length < 2 ^ (prefixWord ++ tailWord_6305384).sum := by decide
  have hdescent : baseEnd_6305384 < baseStart_6305384 := by decide
  rcases family_descends (prefixWord ++ tailWord_6305384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6305397 : List Nat := [1, 3, 4, 2, 1, 1, 1, 1, 3, 2, 4]
def baseStart_6305397 : Nat := 118140960795 + 6305397 * 2 ^ 59
def prefixEnd_6305397 : Nat := 4983230072969 + 3 ^ 40 * 6305397 * 2
def baseEnd_6305397 : Nat := 3237699378417771838939513

theorem tailTrace_6305397 : CollatzResearch.WordTrace tailWord_6305397 prefixEnd_6305397 3237699378417771838939513 := by
  unfold tailWord_6305397
  simp only [CollatzResearch.WordTrace]
  refine ⟨229976721937631019918226445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153317814625087346612150963 229976721937631019918226445)
  ·
    refine ⟨86241270726611632469334917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 229976721937631019918226445 86241270726611632469334917)
    ·
      refine ⟨16170238261239681088000297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 86241270726611632469334917 16170238261239681088000297)
      ·
        refine ⟨12127678695929760816000223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16170238261239681088000297 12127678695929760816000223)
        ·
          refine ⟨18191518043894641224000335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12127678695929760816000223 18191518043894641224000335)
          ·
            refine ⟨27287277065841961836000503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18191518043894641224000335 27287277065841961836000503)
            ·
              refine ⟨40930915598762942754000755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27287277065841961836000503 40930915598762942754000755)
              ·
                refine ⟨61396373398144414131001133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40930915598762942754000755 61396373398144414131001133)
                ·
                  refine ⟨23023640024304155299125425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 61396373398144414131001133 23023640024304155299125425)
                  ·
                    refine ⟨17267730018228116474344069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23023640024304155299125425 17267730018228116474344069)
                    ·
                      refine ⟨3237699378417771838939513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17267730018228116474344069 3237699378417771838939513)
                      ·
                        rfl

theorem cell23_6305397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 1, 3, 2, 4].length) (baseStart_6305397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6305397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6305397 prefixEnd_6305397 := by exact prefixLift 6305397
  have htrace : WordTrace (prefixWord ++ tailWord_6305397) baseStart_6305397 baseEnd_6305397 := by
    simpa [prefixWord, tailWord_6305397, baseEnd_6305397] using wordTrace_append hprefix tailTrace_6305397
  have hstable : (prefixWord ++ tailWord_6305397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6305397).length < 2 ^ (prefixWord ++ tailWord_6305397).sum := by decide
  have hdescent : baseEnd_6305397 < baseStart_6305397 := by decide
  rcases family_descends (prefixWord ++ tailWord_6305397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6305401 : List Nat := [1, 2, 1, 3, 3, 1, 2, 5, 1, 2, 2]
def baseStart_6305401 : Nat := 118140960795 + 6305401 * 2 ^ 59
def prefixEnd_6305401 : Nat := 4983230072969 + 3 ^ 40 * 6305401 * 2
def baseEnd_6305401 : Nat := 3237701432340389823289495

theorem tailTrace_6305401 : CollatzResearch.WordTrace tailWord_6305401 prefixEnd_6305401 3237701432340389823289495 := by
  unfold tailWord_6305401
  simp only [CollatzResearch.WordTrace]
  refine ⟨229976867829616528601372057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153317911886411019067581371 229976867829616528601372057)
  ·
    refine ⟨172482650872212396451029043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 229976867829616528601372057 172482650872212396451029043)
    ·
      refine ⟨258723976308318594676543565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172482650872212396451029043 258723976308318594676543565)
      ·
        refine ⟨97021491115619473003703837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 258723976308318594676543565 97021491115619473003703837)
        ·
          refine ⟨36383059168357302376388939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 97021491115619473003703837 36383059168357302376388939)
          ·
            refine ⟨54574588752535953564583409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36383059168357302376388939 54574588752535953564583409)
            ·
              refine ⟨40930941564401965173437557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54574588752535953564583409 40930941564401965173437557)
              ·
                refine ⟨3837275771662684235009771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 40930941564401965173437557 3837275771662684235009771)
                ·
                  refine ⟨5755913657494026352514657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3837275771662684235009771 5755913657494026352514657)
                  ·
                    refine ⟨4316935243120519764385993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5755913657494026352514657 4316935243120519764385993)
                    ·
                      refine ⟨3237701432340389823289495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4316935243120519764385993 3237701432340389823289495)
                      ·
                        rfl

theorem cell23_6305401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 5, 1, 2, 2].length) (baseStart_6305401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6305401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6305401 prefixEnd_6305401 := by exact prefixLift 6305401
  have htrace : WordTrace (prefixWord ++ tailWord_6305401) baseStart_6305401 baseEnd_6305401 := by
    simpa [prefixWord, tailWord_6305401, baseEnd_6305401] using wordTrace_append hprefix tailTrace_6305401
  have hstable : (prefixWord ++ tailWord_6305401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6305401).length < 2 ^ (prefixWord ++ tailWord_6305401).sum := by decide
  have hdescent : baseEnd_6305401 < baseStart_6305401 := by decide
  rcases family_descends (prefixWord ++ tailWord_6305401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6305417 : List Nat := [1, 2, 1, 1, 4, 1, 2, 3, 4, 1, 3]
def baseStart_6305417 : Nat := 118140960795 + 6305417 * 2 ^ 59
def prefixEnd_6305417 : Nat := 4983230072969 + 3 ^ 40 * 6305417 * 2
def baseEnd_6305417 : Nat := 3237709648030861760689421

theorem tailTrace_6305417 : CollatzResearch.WordTrace tailWord_6305417 prefixEnd_6305417 3237709648030861760689421 := by
  unfold tailWord_6305417
  simp only [CollatzResearch.WordTrace]
  refine ⟨229977451397558563333954505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153318300931705708889303003 229977451397558563333954505)
  ·
    refine ⟨172483088548168922500465879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 229977451397558563333954505 172483088548168922500465879)
    ·
      refine ⟨258724632822253383750698819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172483088548168922500465879 258724632822253383750698819)
      ·
        refine ⟨388086949233380075626048229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 258724632822253383750698819 388086949233380075626048229)
        ·
          refine ⟨72766302981258764179884043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 388086949233380075626048229 72766302981258764179884043)
          ·
            refine ⟨109149454471888146269826065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72766302981258764179884043 109149454471888146269826065)
            ·
              refine ⟨81862090853916109702369549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 109149454471888146269826065 81862090853916109702369549)
              ·
                refine ⟨30698284070218541138388581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 81862090853916109702369549 30698284070218541138388581)
                ·
                  refine ⟨5755928263165976463447859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30698284070218541138388581 5755928263165976463447859)
                  ·
                    refine ⟨8633892394748964695171789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5755928263165976463447859 8633892394748964695171789)
                    ·
                      refine ⟨3237709648030861760689421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8633892394748964695171789 3237709648030861760689421)
                      ·
                        rfl

theorem cell23_6305417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 3, 4, 1, 3].length) (baseStart_6305417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6305417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6305417 prefixEnd_6305417 := by exact prefixLift 6305417
  have htrace : WordTrace (prefixWord ++ tailWord_6305417) baseStart_6305417 baseEnd_6305417 := by
    simpa [prefixWord, tailWord_6305417, baseEnd_6305417] using wordTrace_append hprefix tailTrace_6305417
  have hstable : (prefixWord ++ tailWord_6305417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6305417).length < 2 ^ (prefixWord ++ tailWord_6305417).sum := by decide
  have hdescent : baseEnd_6305417 < baseStart_6305417 := by decide
  rcases family_descends (prefixWord ++ tailWord_6305417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6305418 : List Nat := [3, 1, 2, 3, 2, 2, 1, 4, 1, 2, 2]
def baseStart_6305418 : Nat := 118140960795 + 6305418 * 2 ^ 59
def prefixEnd_6305418 : Nat := 4983230072969 + 3 ^ 40 * 6305418 * 2
def baseEnd_6305418 : Nat := 3237710161511516256776917

theorem tailTrace_6305418 : CollatzResearch.WordTrace tailWord_6305418 prefixEnd_6305418 3237710161511516256776917 := by
  unfold tailWord_6305418
  simp only [CollatzResearch.WordTrace]
  refine ⟨57494371967638735126185227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153318325247036627003160605 57494371967638735126185227)
  ·
    refine ⟨86241557951458102689277841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57494371967638735126185227 86241557951458102689277841)
    ·
      refine ⟨64681168463593577016958381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86241557951458102689277841 64681168463593577016958381)
      ·
        refine ⟨24255438173847591381359393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64681168463593577016958381 24255438173847591381359393)
        ·
          refine ⟨18191578630385693536019545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24255438173847591381359393 18191578630385693536019545)
          ·
            refine ⟨13643683972789270152014659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18191578630385693536019545 13643683972789270152014659)
            ·
              refine ⟨20465525959183905228021989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13643683972789270152014659 20465525959183905228021989)
              ·
                refine ⟨3837286117346982230254123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20465525959183905228021989 3837286117346982230254123)
                ·
                  refine ⟨5755929176020473345381185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3837286117346982230254123 5755929176020473345381185)
                  ·
                    refine ⟨4316946882015355009035889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5755929176020473345381185 4316946882015355009035889)
                    ·
                      refine ⟨3237710161511516256776917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4316946882015355009035889 3237710161511516256776917)
                      ·
                        rfl

theorem cell23_6305418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 1, 4, 1, 2, 2].length) (baseStart_6305418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6305418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6305418 prefixEnd_6305418 := by exact prefixLift 6305418
  have htrace : WordTrace (prefixWord ++ tailWord_6305418) baseStart_6305418 baseEnd_6305418 := by
    simpa [prefixWord, tailWord_6305418, baseEnd_6305418] using wordTrace_append hprefix tailTrace_6305418
  have hstable : (prefixWord ++ tailWord_6305418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6305418).length < 2 ^ (prefixWord ++ tailWord_6305418).sum := by decide
  have hdescent : baseEnd_6305418 < baseStart_6305418 := by decide
  rcases family_descends (prefixWord ++ tailWord_6305418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6305444 : List Nat := [2, 3, 1, 2, 2, 2, 2, 1, 3, 3, 2]
def baseStart_6305444 : Nat := 118140960795 + 6305444 * 2 ^ 59
def prefixEnd_6305444 : Nat := 4983230072969 + 3 ^ 40 * 6305444 * 2
def baseEnd_6305444 : Nat := 3237723512008533155051797

theorem tailTrace_6305444 : CollatzResearch.WordTrace tailWord_6305444 prefixEnd_6305444 3237723512008533155051797 := by
  unfold tailWord_6305444
  simp only [CollatzResearch.WordTrace]
  refine ⟨114989218084230373472593693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153318957445640497963458257 114989218084230373472593693)
  ·
    refine ⟨43120956781586390052222635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114989218084230373472593693 43120956781586390052222635)
    ·
      refine ⟨64681435172379585078333953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43120956781586390052222635 64681435172379585078333953)
      ·
        refine ⟨48511076379284688808750465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64681435172379585078333953 48511076379284688808750465)
        ·
          refine ⟨36383307284463516606562849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48511076379284688808750465 36383307284463516606562849)
          ·
            refine ⟨27287480463347637454922137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36383307284463516606562849 27287480463347637454922137)
            ·
              refine ⟨20465610347510728091191603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27287480463347637454922137 20465610347510728091191603)
              ·
                refine ⟨30698415521266092136787405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20465610347510728091191603 30698415521266092136787405)
                ·
                  refine ⟨11511905820474784551295277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30698415521266092136787405 11511905820474784551295277)
                  ·
                    refine ⟨4316964682678044206735729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11511905820474784551295277 4316964682678044206735729)
                    ·
                      refine ⟨3237723512008533155051797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4316964682678044206735729 3237723512008533155051797)
                      ·
                        rfl

theorem cell23_6305444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 2, 1, 3, 3, 2].length) (baseStart_6305444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6305444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6305444 prefixEnd_6305444 := by exact prefixLift 6305444
  have htrace : WordTrace (prefixWord ++ tailWord_6305444) baseStart_6305444 baseEnd_6305444 := by
    simpa [prefixWord, tailWord_6305444, baseEnd_6305444] using wordTrace_append hprefix tailTrace_6305444
  have hstable : (prefixWord ++ tailWord_6305444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6305444).length < 2 ^ (prefixWord ++ tailWord_6305444).sum := by decide
  have hdescent : baseEnd_6305444 < baseStart_6305444 := by decide
  rcases family_descends (prefixWord ++ tailWord_6305444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6305485 : List Nat := [1, 6, 2, 1, 1, 2, 3, 1, 2, 1, 3]
def baseStart_6305485 : Nat := 118140960795 + 6305485 * 2 ^ 59
def prefixEnd_6305485 : Nat := 4983230072969 + 3 ^ 40 * 6305485 * 2
def baseEnd_6305485 : Nat := 3237744564715367494639109

theorem tailTrace_6305485 : CollatzResearch.WordTrace tailWord_6305485 prefixEnd_6305485 3237744564715367494639109 := by
  unfold tailWord_6305485
  simp only [CollatzResearch.WordTrace]
  refine ⟨229979931561312210947429909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153319954374208140631619939 229979931561312210947429909)
  ·
    refine ⟨10780309291936509888160777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 229979931561312210947429909 10780309291936509888160777)
    ·
      refine ⟨8085231968952382416120583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10780309291936509888160777 8085231968952382416120583)
      ·
        refine ⟨12127847953428573624180875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8085231968952382416120583 12127847953428573624180875)
        ·
          refine ⟨18191771930142860436271313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12127847953428573624180875 18191771930142860436271313)
          ·
            refine ⟨13643828947607145327203485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18191771930142860436271313 13643828947607145327203485)
            ·
              refine ⟨5116435855352679497701307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13643828947607145327203485 5116435855352679497701307)
              ·
                refine ⟨7674653783029019246551961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5116435855352679497701307 7674653783029019246551961)
                ·
                  refine ⟨5755990337271764434913971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7674653783029019246551961 5755990337271764434913971)
                  ·
                    refine ⟨8633985505907646652370957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5755990337271764434913971 8633985505907646652370957)
                    ·
                      refine ⟨3237744564715367494639109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8633985505907646652370957 3237744564715367494639109)
                      ·
                        rfl

theorem cell23_6305485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 3, 1, 2, 1, 3].length) (baseStart_6305485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6305485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6305485 prefixEnd_6305485 := by exact prefixLift 6305485
  have htrace : WordTrace (prefixWord ++ tailWord_6305485) baseStart_6305485 baseEnd_6305485 := by
    simpa [prefixWord, tailWord_6305485, baseEnd_6305485] using wordTrace_append hprefix tailTrace_6305485
  have hstable : (prefixWord ++ tailWord_6305485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6305485).length < 2 ^ (prefixWord ++ tailWord_6305485).sum := by decide
  have hdescent : baseEnd_6305485 < baseStart_6305485 := by decide
  rcases family_descends (prefixWord ++ tailWord_6305485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6305514 : List Nat := [3, 1, 3, 1, 1, 1, 5, 3, 5]
def baseStart_6305514 : Nat := 118140960795 + 6305514 * 2 ^ 59
def prefixEnd_6305514 : Nat := 4983230072969 + 3 ^ 40 * 6305514 * 2
def baseEnd_6305514 : Nat := 359751050628260875686275

theorem tailTrace_6305514 : CollatzResearch.WordTrace tailWord_6305514 prefixEnd_6305514 359751050628260875686275 := by
  unfold tailWord_6305514
  simp only [CollatzResearch.WordTrace]
  refine ⟨57495247319551787225058899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153320659518804765933490397 57495247319551787225058899)
  ·
    refine ⟨86242870979327680837588349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57495247319551787225058899 86242870979327680837588349)
    ·
      refine ⟨32341076617247880314095631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86242870979327680837588349 32341076617247880314095631)
      ·
        refine ⟨48511614925871820471143447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32341076617247880314095631 48511614925871820471143447)
        ·
          refine ⟨72767422388807730706715171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48511614925871820471143447 72767422388807730706715171)
          ·
            refine ⟨109151133583211596060072757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72767422388807730706715171 109151133583211596060072757)
            ·
              refine ⟨10232918773426087130631821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 109151133583211596060072757 10232918773426087130631821)
              ·
                refine ⟨3837344540034782673986933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10232918773426087130631821 3837344540034782673986933)
                ·
                  refine ⟨359751050628260875686275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3837344540034782673986933 359751050628260875686275)
                  ·
                    rfl

theorem cell23_6305514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 5, 3, 5].length) (baseStart_6305514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6305514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6305514 prefixEnd_6305514 := by exact prefixLift 6305514
  have htrace : WordTrace (prefixWord ++ tailWord_6305514) baseStart_6305514 baseEnd_6305514 := by
    simpa [prefixWord, tailWord_6305514, baseEnd_6305514] using wordTrace_append hprefix tailTrace_6305514
  have hstable : (prefixWord ++ tailWord_6305514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6305514).length < 2 ^ (prefixWord ++ tailWord_6305514).sum := by decide
  have hdescent : baseEnd_6305514 < baseStart_6305514 := by decide
  rcases family_descends (prefixWord ++ tailWord_6305514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6305564 : List Nat := [2, 2, 3, 1, 1, 2, 4, 1, 2, 1, 4]
def baseStart_6305564 : Nat := 118140960795 + 6305564 * 2 ^ 59
def prefixEnd_6305564 : Nat := 4983230072969 + 3 ^ 40 * 6305564 * 2
def baseEnd_6305564 : Nat := 3237785129687072685551245

theorem tailTrace_6305564 : CollatzResearch.WordTrace tailWord_6305564 prefixEnd_6305564 3237785129687072685551245 := by
  unfold tailWord_6305564
  simp only [CollatzResearch.WordTrace]
  refine ⟨114991406464013003719777873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153321875285350671626370497 114991406464013003719777873)
  ·
    refine ⟨86243554848009752789833405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114991406464013003719777873 86243554848009752789833405)
    ·
      refine ⟨32341333068003657296187527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86243554848009752789833405 32341333068003657296187527)
      ·
        refine ⟨48511999602005485944281291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32341333068003657296187527 48511999602005485944281291)
        ·
          refine ⟨72767999403008228916421937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48511999602005485944281291 72767999403008228916421937)
          ·
            refine ⟨54575999552256171687316453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72767999403008228916421937 54575999552256171687316453)
            ·
              refine ⟨10232999916048032191371835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 54575999552256171687316453 10232999916048032191371835)
              ·
                refine ⟨15349499874072048287057753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10232999916048032191371835 15349499874072048287057753)
                ·
                  refine ⟨11512124905554036215293315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15349499874072048287057753 11512124905554036215293315)
                  ·
                    refine ⟨17268187358331054322939973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11512124905554036215293315 17268187358331054322939973)
                    ·
                      refine ⟨3237785129687072685551245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17268187358331054322939973 3237785129687072685551245)
                      ·
                        rfl

theorem cell23_6305564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 4, 1, 2, 1, 4].length) (baseStart_6305564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6305564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6305564 prefixEnd_6305564 := by exact prefixLift 6305564
  have htrace : WordTrace (prefixWord ++ tailWord_6305564) baseStart_6305564 baseEnd_6305564 := by
    simpa [prefixWord, tailWord_6305564, baseEnd_6305564] using wordTrace_append hprefix tailTrace_6305564
  have hstable : (prefixWord ++ tailWord_6305564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6305564).length < 2 ^ (prefixWord ++ tailWord_6305564).sum := by decide
  have hdescent : baseEnd_6305564 < baseStart_6305564 := by decide
  rcases family_descends (prefixWord ++ tailWord_6305564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6305682 : List Nat := [3, 2, 3, 2, 1, 3, 1, 3, 1, 1, 3]
def baseStart_6305682 : Nat := 118140960795 + 6305682 * 2 ^ 59
def prefixEnd_6305682 : Nat := 4983230072969 + 3 ^ 40 * 6305682 * 2
def baseEnd_6305682 : Nat := 3237845720404303223875703

theorem tailTrace_6305682 : CollatzResearch.WordTrace tailWord_6305682 prefixEnd_6305682 3237845720404303223875703 := by
  unfold tailWord_6305682
  simp only [CollatzResearch.WordTrace]
  refine ⟨57496779185399628398087825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153324744494399009061567533 57496779185399628398087825)
  ·
    refine ⟨43122584389049721298565869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57496779185399628398087825 43122584389049721298565869)
    ·
      refine ⟨16170969145893645486962201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43122584389049721298565869 16170969145893645486962201)
      ·
        refine ⟨12128226859420234115221651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16170969145893645486962201 12128226859420234115221651)
        ·
          refine ⟨18192340289130351172832477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12128226859420234115221651 18192340289130351172832477)
          ·
            refine ⟨6822127608423881689812179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18192340289130351172832477 6822127608423881689812179)
            ·
              refine ⟨10233191412635822534718269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6822127608423881689812179 10233191412635822534718269)
              ·
                refine ⟨3837446779738433450519351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10233191412635822534718269 3837446779738433450519351)
                ·
                  refine ⟨5756170169607650175779027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3837446779738433450519351 5756170169607650175779027)
                  ·
                    refine ⟨8634255254411475263668541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5756170169607650175779027 8634255254411475263668541)
                    ·
                      refine ⟨3237845720404303223875703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8634255254411475263668541 3237845720404303223875703)
                      ·
                        rfl

theorem cell23_6305682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 3, 1, 3, 1, 1, 3].length) (baseStart_6305682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6305682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6305682 prefixEnd_6305682 := by exact prefixLift 6305682
  have htrace : WordTrace (prefixWord ++ tailWord_6305682) baseStart_6305682 baseEnd_6305682 := by
    simpa [prefixWord, tailWord_6305682, baseEnd_6305682] using wordTrace_append hprefix tailTrace_6305682
  have hstable : (prefixWord ++ tailWord_6305682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6305682).length < 2 ^ (prefixWord ++ tailWord_6305682).sum := by decide
  have hdescent : baseEnd_6305682 < baseStart_6305682 := by decide
  rcases family_descends (prefixWord ++ tailWord_6305682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6305737 : List Nat := [1, 2, 1, 1, 2, 1, 2, 4, 1, 8]
def baseStart_6305737 : Nat := 118140960795 + 6305737 * 2 ^ 59
def prefixEnd_6305737 : Nat := 4983230072969 + 3 ^ 40 * 6305737 * 2
def baseEnd_6305737 : Nat := 1079291320613433502895983

theorem tailTrace_6305737 : CollatzResearch.WordTrace tailWord_6305737 prefixEnd_6305737 1079291320613433502895983 := by
  unfold tailWord_6305737
  simp only [CollatzResearch.WordTrace]
  refine ⟨229989122756399257985603465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153326081837599505323735643 229989122756399257985603465)
  ·
    refine ⟨172491842067299443489202599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 229989122756399257985603465 172491842067299443489202599)
    ·
      refine ⟨258737763100949165233803899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172491842067299443489202599 258737763100949165233803899)
      ·
        refine ⟨388106644651423747850705849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 258737763100949165233803899 388106644651423747850705849)
        ·
          refine ⟨291079983488567810888029387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 388106644651423747850705849 291079983488567810888029387)
          ·
            refine ⟨436619975232851716332044081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 291079983488567810888029387 436619975232851716332044081)
            ·
              refine ⟨327464981424638787249033061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 436619975232851716332044081 327464981424638787249033061)
              ·
                refine ⟨61399684017119772609193699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 327464981424638787249033061 61399684017119772609193699)
                ·
                  refine ⟨92099526025679658913790549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61399684017119772609193699 92099526025679658913790549)
                  ·
                    refine ⟨1079291320613433502895983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 92099526025679658913790549 1079291320613433502895983)
                    ·
                      rfl

theorem cell23_6305737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 4, 1, 8].length) (baseStart_6305737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6305737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6305737 prefixEnd_6305737 := by exact prefixLift 6305737
  have htrace : WordTrace (prefixWord ++ tailWord_6305737) baseStart_6305737 baseEnd_6305737 := by
    simpa [prefixWord, tailWord_6305737, baseEnd_6305737] using wordTrace_append hprefix tailTrace_6305737
  have hstable : (prefixWord ++ tailWord_6305737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6305737).length < 2 ^ (prefixWord ++ tailWord_6305737).sum := by decide
  have hdescent : baseEnd_6305737 < baseStart_6305737 := by decide
  rcases family_descends (prefixWord ++ tailWord_6305737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6305756 : List Nat := [2, 2, 6, 1, 1, 1, 1, 4, 1, 2, 2]
def baseStart_6305756 : Nat := 118140960795 + 6305756 * 2 ^ 59
def prefixEnd_6305756 : Nat := 4983230072969 + 3 ^ 40 * 6305756 * 2
def baseEnd_6305756 : Nat := 3237883717972735934350363

theorem tailTrace_6305756 : CollatzResearch.WordTrace tailWord_6305756 prefixEnd_6305756 3237883717972735934350363 := by
  unfold tailWord_6305756
  simp only [CollatzResearch.WordTrace]
  refine ⟨114994907871665212115272561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153326543828886949487030081 114994907871665212115272561)
  ·
    refine ⟨86246180903748909086454421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114994907871665212115272561 86246180903748909086454421)
    ·
      refine ⟨4042789729863230113427551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 86246180903748909086454421 4042789729863230113427551)
      ·
        refine ⟨6064184594794845170141327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4042789729863230113427551 6064184594794845170141327)
        ·
          refine ⟨9096276892192267755211991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6064184594794845170141327 9096276892192267755211991)
          ·
            refine ⟨13644415338288401632817987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9096276892192267755211991 13644415338288401632817987)
            ·
              refine ⟨20466623007432602449226981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13644415338288401632817987 20466623007432602449226981)
              ·
                refine ⟨3837491813893612959230059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20466623007432602449226981 3837491813893612959230059)
                ·
                  refine ⟨5756237720840419438845089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3837491813893612959230059 5756237720840419438845089)
                  ·
                    refine ⟨4317178290630314579133817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5756237720840419438845089 4317178290630314579133817)
                    ·
                      refine ⟨3237883717972735934350363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4317178290630314579133817 3237883717972735934350363)
                      ·
                        rfl

theorem cell23_6305756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 1, 4, 1, 2, 2].length) (baseStart_6305756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6305756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6305756 prefixEnd_6305756 := by exact prefixLift 6305756
  have htrace : WordTrace (prefixWord ++ tailWord_6305756) baseStart_6305756 baseEnd_6305756 := by
    simpa [prefixWord, tailWord_6305756, baseEnd_6305756] using wordTrace_append hprefix tailTrace_6305756
  have hstable : (prefixWord ++ tailWord_6305756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6305756).length < 2 ^ (prefixWord ++ tailWord_6305756).sum := by decide
  have hdescent : baseEnd_6305756 < baseStart_6305756 := by decide
  rcases family_descends (prefixWord ++ tailWord_6305756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6305764 : List Nat := [2, 3, 1, 1, 1, 1, 3, 1, 1, 6, 3]
def baseStart_6305764 : Nat := 118140960795 + 6305764 * 2 ^ 59
def prefixEnd_6305764 : Nat := 4983230072969 + 3 ^ 40 * 6305764 * 2
def baseEnd_6305764 : Nat := 3237887825817971903050325

theorem tailTrace_6305764 : CollatzResearch.WordTrace tailWord_6305764 prefixEnd_6305764 3237887825817971903050325 := by
  unfold tailWord_6305764
  simp only [CollatzResearch.WordTrace]
  refine ⟨114995053763650720798418173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153326738351534294397890897 114995053763650720798418173)
  ·
    refine ⟨43123145161369020299406815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114995053763650720798418173 43123145161369020299406815)
    ·
      refine ⟨64684717742053530449110223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43123145161369020299406815 64684717742053530449110223)
      ·
        refine ⟨97027076613080295673665335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64684717742053530449110223 97027076613080295673665335)
        ·
          refine ⟨145540614919620443510498003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97027076613080295673665335 145540614919620443510498003)
          ·
            refine ⟨218310922379430665265747005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 145540614919620443510498003 218310922379430665265747005)
            ·
              refine ⟨81866595892286499474655127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 218310922379430665265747005 81866595892286499474655127)
              ·
                refine ⟨122799893838429749211982691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81866595892286499474655127 122799893838429749211982691)
                ·
                  refine ⟨184199840757644623817974037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 122799893838429749211982691 184199840757644623817974037)
                  ·
                    refine ⟨8634367535514591741467533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 184199840757644623817974037 8634367535514591741467533)
                    ·
                      refine ⟨3237887825817971903050325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8634367535514591741467533 3237887825817971903050325)
                      ·
                        rfl

theorem cell23_6305764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 1, 1, 6, 3].length) (baseStart_6305764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6305764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6305764 prefixEnd_6305764 := by exact prefixLift 6305764
  have htrace : WordTrace (prefixWord ++ tailWord_6305764) baseStart_6305764 baseEnd_6305764 := by
    simpa [prefixWord, tailWord_6305764, baseEnd_6305764] using wordTrace_append hprefix tailTrace_6305764
  have hstable : (prefixWord ++ tailWord_6305764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6305764).length < 2 ^ (prefixWord ++ tailWord_6305764).sum := by decide
  have hdescent : baseEnd_6305764 < baseStart_6305764 := by decide
  rcases family_descends (prefixWord ++ tailWord_6305764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6305864 : List Nat := [2, 1, 3, 1, 1, 1, 2, 3, 2, 1, 6]
def baseStart_6305864 : Nat := 118140960795 + 6305864 * 2 ^ 59
def prefixEnd_6305864 : Nat := 4983230072969 + 3 ^ 40 * 6305864 * 2
def baseEnd_6305864 : Nat := 3237939173883421511799865

theorem tailTrace_6305864 : CollatzResearch.WordTrace tailWord_6305864 prefixEnd_6305864 3237939173883421511799865 := by
  unfold tailWord_6305864
  simp only [CollatzResearch.WordTrace]
  refine ⟨114996877413469579337738323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153329169884626105783651097 114996877413469579337738323)
  ·
    refine ⟨172495316120204369006607485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114996877413469579337738323 172495316120204369006607485)
    ·
      refine ⟨64685743545076638377477807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 172495316120204369006607485 64685743545076638377477807)
      ·
        refine ⟨97028615317614957566216711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64685743545076638377477807 97028615317614957566216711)
        ·
          refine ⟨145542922976422436349325067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97028615317614957566216711 145542922976422436349325067)
          ·
            refine ⟨218314384464633654523987601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 145542922976422436349325067 218314384464633654523987601)
            ·
              refine ⟨163735788348475240892990701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 218314384464633654523987601 163735788348475240892990701)
              ·
                refine ⟨61400920630678215334871513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 163735788348475240892990701 61400920630678215334871513)
                ·
                  refine ⟨46050690473008661501153635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 61400920630678215334871513 46050690473008661501153635)
                  ·
                    refine ⟨69076035709512992251730453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 46050690473008661501153635 69076035709512992251730453)
                    ·
                      refine ⟨3237939173883421511799865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 69076035709512992251730453 3237939173883421511799865)
                      ·
                        rfl

theorem cell23_6305864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 3, 2, 1, 6].length) (baseStart_6305864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6305864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6305864 prefixEnd_6305864 := by exact prefixLift 6305864
  have htrace : WordTrace (prefixWord ++ tailWord_6305864) baseStart_6305864 baseEnd_6305864 := by
    simpa [prefixWord, tailWord_6305864, baseEnd_6305864] using wordTrace_append hprefix tailTrace_6305864
  have hstable : (prefixWord ++ tailWord_6305864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6305864).length < 2 ^ (prefixWord ++ tailWord_6305864).sum := by decide
  have hdescent : baseEnd_6305864 < baseStart_6305864 := by decide
  rcases family_descends (prefixWord ++ tailWord_6305864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6305871 : List Nat := [1, 1, 2, 1, 1, 2, 2, 6, 2, 2, 3]
def baseStart_6305871 : Nat := 118140960795 + 6305871 * 2 ^ 59
def prefixEnd_6305871 : Nat := 4983230072969 + 3 ^ 40 * 6305871 * 2
def baseEnd_6305871 : Nat := 3237942768248002984412333

theorem tailTrace_6305871 : CollatzResearch.WordTrace tailWord_6305871 prefixEnd_6305871 3237942768248002984412333 := by
  unfold tailWord_6305871
  simp only [CollatzResearch.WordTrace]
  refine ⟨229994010137913798870981467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153329340091942532580654311 229994010137913798870981467)
  ·
    refine ⟨344991015206870698306472201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229994010137913798870981467 344991015206870698306472201)
    ·
      refine ⟨258743261405153023729854151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 344991015206870698306472201 258743261405153023729854151)
      ·
        refine ⟨388114892107729535594781227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 258743261405153023729854151 388114892107729535594781227)
        ·
          refine ⟨582172338161594303392171841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 388114892107729535594781227 582172338161594303392171841)
          ·
            refine ⟨436629253621195727544128881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 582172338161594303392171841 436629253621195727544128881)
            ·
              refine ⟨327471940215896795658096661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 436629253621195727544128881 327471940215896795658096661)
              ·
                refine ⟨15350247197620162296473281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 327471940215896795658096661 15350247197620162296473281)
                ·
                  refine ⟨11512685398215121722354961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15350247197620162296473281 11512685398215121722354961)
                  ·
                    refine ⟨8634514048661341291766221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11512685398215121722354961 8634514048661341291766221)
                    ·
                      refine ⟨3237942768248002984412333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8634514048661341291766221 3237942768248002984412333)
                      ·
                        rfl

theorem cell23_6305871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 6, 2, 2, 3].length) (baseStart_6305871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6305871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6305871 prefixEnd_6305871 := by exact prefixLift 6305871
  have htrace : WordTrace (prefixWord ++ tailWord_6305871) baseStart_6305871 baseEnd_6305871 := by
    simpa [prefixWord, tailWord_6305871, baseEnd_6305871] using wordTrace_append hprefix tailTrace_6305871
  have hstable : (prefixWord ++ tailWord_6305871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6305871).length < 2 ^ (prefixWord ++ tailWord_6305871).sum := by decide
  have hdescent : baseEnd_6305871 < baseStart_6305871 := by decide
  rcases family_descends (prefixWord ++ tailWord_6305871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6305914 : List Nat := [3, 1, 1, 1, 1, 1, 1, 1, 3, 3, 7]
def baseStart_6305914 : Nat := 118140960795 + 6305914 * 2 ^ 59
def prefixEnd_6305914 : Nat := 4983230072969 + 3 ^ 40 * 6305914 * 2
def baseEnd_6305914 : Nat := 3237964847916146316174635

theorem tailTrace_6305914 : CollatzResearch.WordTrace tailWord_6305914 prefixEnd_6305914 3237964847916146316174635 := by
  unfold tailWord_6305914
  simp only [CollatzResearch.WordTrace]
  refine ⟨57498894619189504303699199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153330385651172011476531197 57498894619189504303699199)
  ·
    refine ⟨86248341928784256455548799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57498894619189504303699199 86248341928784256455548799)
    ·
      refine ⟨129372512893176384683323199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86248341928784256455548799 129372512893176384683323199)
      ·
        refine ⟨194058769339764577024984799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129372512893176384683323199 194058769339764577024984799)
        ·
          refine ⟨291088154009646865537477199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 194058769339764577024984799 291088154009646865537477199)
          ·
            refine ⟨436632231014470298306215799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 291088154009646865537477199 436632231014470298306215799)
            ·
              refine ⟨654948346521705447459323699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 436632231014470298306215799 654948346521705447459323699)
              ·
                refine ⟨982422519782558171188985549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 654948346521705447459323699 982422519782558171188985549)
                ·
                  refine ⟨368408444918459314195869581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 982422519782558171188985549 368408444918459314195869581)
                  ·
                    refine ⟨138153166844422242823451093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 368408444918459314195869581 138153166844422242823451093)
                    ·
                      refine ⟨3237964847916146316174635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 138153166844422242823451093 3237964847916146316174635)
                      ·
                        rfl

theorem cell23_6305914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 3, 3, 7].length) (baseStart_6305914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6305914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6305914 prefixEnd_6305914 := by exact prefixLift 6305914
  have htrace : WordTrace (prefixWord ++ tailWord_6305914) baseStart_6305914 baseEnd_6305914 := by
    simpa [prefixWord, tailWord_6305914, baseEnd_6305914] using wordTrace_append hprefix tailTrace_6305914
  have hstable : (prefixWord ++ tailWord_6305914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6305914).length < 2 ^ (prefixWord ++ tailWord_6305914).sum := by decide
  have hdescent : baseEnd_6305914 < baseStart_6305914 := by decide
  rcases family_descends (prefixWord ++ tailWord_6305914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6305941 : List Nat := [1, 3, 2, 1, 1, 1, 3, 1, 5, 1, 4]
def baseStart_6305941 : Nat := 118140960795 + 6305941 * 2 ^ 59
def prefixEnd_6305941 : Nat := 4983230072969 + 3 ^ 40 * 6305941 * 2
def baseEnd_6305941 : Nat := 3237978711893817710537011

theorem tailTrace_6305941 : CollatzResearch.WordTrace tailWord_6305941 prefixEnd_6305941 3237978711893817710537011 := by
  unfold tailWord_6305941
  simp only [CollatzResearch.WordTrace]
  refine ⟨229996563247660200826029677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153331042165106800550686451 229996563247660200826029677)
  ·
    refine ⟨86248711217872575309761129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 229996563247660200826029677 86248711217872575309761129)
    ·
      refine ⟨64686533413404431482320847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86248711217872575309761129 64686533413404431482320847)
      ·
        refine ⟨97029800120106647223481271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64686533413404431482320847 97029800120106647223481271)
        ·
          refine ⟨145544700180159970835221907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97029800120106647223481271 145544700180159970835221907)
          ·
            refine ⟨218317050270239956252832861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 145544700180159970835221907 218317050270239956252832861)
            ·
              refine ⟨81868893851339983594812323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 218317050270239956252832861 81868893851339983594812323)
              ·
                refine ⟨122803340777009975392218485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81868893851339983594812323 122803340777009975392218485)
                ·
                  refine ⟨11512813197844685193020483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 122803340777009975392218485 11512813197844685193020483)
                  ·
                    refine ⟨17269219796767027789530725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11512813197844685193020483 17269219796767027789530725)
                    ·
                      refine ⟨3237978711893817710537011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17269219796767027789530725 3237978711893817710537011)
                      ·
                        rfl

theorem cell23_6305941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 1, 5, 1, 4].length) (baseStart_6305941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6305941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6305941 prefixEnd_6305941 := by exact prefixLift 6305941
  have htrace : WordTrace (prefixWord ++ tailWord_6305941) baseStart_6305941 baseEnd_6305941 := by
    simpa [prefixWord, tailWord_6305941, baseEnd_6305941] using wordTrace_append hprefix tailTrace_6305941
  have hstable : (prefixWord ++ tailWord_6305941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6305941).length < 2 ^ (prefixWord ++ tailWord_6305941).sum := by decide
  have hdescent : baseEnd_6305941 < baseStart_6305941 := by decide
  rcases family_descends (prefixWord ++ tailWord_6305941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6305962 : List Nat := [3, 1, 5, 1, 2, 1, 1, 1, 1, 5, 2]
def baseStart_6305962 : Nat := 118140960795 + 6305962 * 2 ^ 59
def prefixEnd_6305962 : Nat := 4983230072969 + 3 ^ 40 * 6305962 * 2
def baseEnd_6305962 : Nat := 3237989494987562128374415

theorem tailTrace_6305962 : CollatzResearch.WordTrace tailWord_6305962 prefixEnd_6305962 3237989494987562128374415 := by
  unfold tailWord_6305962
  simp only [CollatzResearch.WordTrace]
  refine ⟨57499332295146030353136035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153331552787056080941696093 57499332295146030353136035)
  ·
    refine ⟨86248998442719045529704053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57499332295146030353136035 86248998442719045529704053)
    ·
      refine ⟨8085843604004910518409755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 86248998442719045529704053 8085843604004910518409755)
      ·
        refine ⟨12128765406007365777614633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8085843604004910518409755 12128765406007365777614633)
        ·
          refine ⟨9096574054505524333210975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12128765406007365777614633 9096574054505524333210975)
          ·
            refine ⟨13644861081758286499816463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9096574054505524333210975 13644861081758286499816463)
            ·
              refine ⟨20467291622637429749724695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13644861081758286499816463 20467291622637429749724695)
              ·
                refine ⟨30700937433956144624587043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20467291622637429749724695 30700937433956144624587043)
                ·
                  refine ⟨46051406150934216936880565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30700937433956144624587043 46051406150934216936880565)
                  ·
                    refine ⟨4317319326650082837832553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 46051406150934216936880565 4317319326650082837832553)
                    ·
                      refine ⟨3237989494987562128374415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4317319326650082837832553 3237989494987562128374415)
                      ·
                        rfl

theorem cell23_6305962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 1, 1, 1, 5, 2].length) (baseStart_6305962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6305962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6305962 prefixEnd_6305962 := by exact prefixLift 6305962
  have htrace : WordTrace (prefixWord ++ tailWord_6305962) baseStart_6305962 baseEnd_6305962 := by
    simpa [prefixWord, tailWord_6305962, baseEnd_6305962] using wordTrace_append hprefix tailTrace_6305962
  have hstable : (prefixWord ++ tailWord_6305962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6305962).length < 2 ^ (prefixWord ++ tailWord_6305962).sum := by decide
  have hdescent : baseEnd_6305962 < baseStart_6305962 := by decide
  rcases family_descends (prefixWord ++ tailWord_6305962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6305969 : List Nat := [1, 2, 2, 5, 2, 1, 2, 3, 1, 1, 3]
def baseStart_6305969 : Nat := 118140960795 + 6305969 * 2 ^ 59
def prefixEnd_6305969 : Nat := 4983230072969 + 3 ^ 40 * 6305969 * 2
def baseEnd_6305969 : Nat := 3237993089352143600986883

theorem tailTrace_6305969 : CollatzResearch.WordTrace tailWord_6305969 prefixEnd_6305969 3237993089352143600986883 := by
  unfold tailWord_6305969
  simp only [CollatzResearch.WordTrace]
  refine ⟨229997584491558761608048961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153331722994372507738699307 229997584491558761608048961)
  ·
    refine ⟨172498188368669071206036721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 229997584491558761608048961 172498188368669071206036721)
    ·
      refine ⟨129373641276501803404527541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 172498188368669071206036721 129373641276501803404527541)
      ·
        refine ⟨12128778869672044069174457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 129373641276501803404527541 12128778869672044069174457)
        ·
          refine ⟨9096584152254033051880843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12128778869672044069174457 9096584152254033051880843)
          ·
            refine ⟨13644876228381049577821265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9096584152254033051880843 13644876228381049577821265)
            ·
              refine ⟨10233657171285787183365949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13644876228381049577821265 10233657171285787183365949)
              ·
                refine ⟨3837621439232170193762231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10233657171285787183365949 3837621439232170193762231)
                ·
                  refine ⟨5756432158848255290643347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3837621439232170193762231 5756432158848255290643347)
                  ·
                    refine ⟨8634648238272382935965021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5756432158848255290643347 8634648238272382935965021)
                    ·
                      refine ⟨3237993089352143600986883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8634648238272382935965021 3237993089352143600986883)
                      ·
                        rfl

theorem cell23_6305969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 2, 3, 1, 1, 3].length) (baseStart_6305969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6305969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6305969 prefixEnd_6305969 := by exact prefixLift 6305969
  have htrace : WordTrace (prefixWord ++ tailWord_6305969) baseStart_6305969 baseEnd_6305969 := by
    simpa [prefixWord, tailWord_6305969, baseEnd_6305969] using wordTrace_append hprefix tailTrace_6305969
  have hstable : (prefixWord ++ tailWord_6305969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6305969).length < 2 ^ (prefixWord ++ tailWord_6305969).sum := by decide
  have hdescent : baseEnd_6305969 < baseStart_6305969 := by decide
  rcases family_descends (prefixWord ++ tailWord_6305969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6305975 : List Nat := [1, 1, 3, 1, 4, 2, 4, 1, 1, 1, 4]
def baseStart_6305975 : Nat := 118140960795 + 6305975 * 2 ^ 59
def prefixEnd_6305975 : Nat := 4983230072969 + 3 ^ 40 * 6305975 * 2
def baseEnd_6305975 : Nat := 3237996170236070577511855

theorem tailTrace_6305975 : CollatzResearch.WordTrace tailWord_6305975 prefixEnd_6305975 3237996170236070577511855 := by
  unfold tailWord_6305975
  simp only [CollatzResearch.WordTrace]
  refine ⟨229997803329537024632767379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153331868886358016421844919 229997803329537024632767379)
  ·
    refine ⟨344996704994305536949151069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229997803329537024632767379 344996704994305536949151069)
    ·
      refine ⟨129373764372864576355931651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 344996704994305536949151069 129373764372864576355931651)
      ·
        refine ⟨194060646559296864533897477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129373764372864576355931651 194060646559296864533897477)
        ·
          refine ⟨36386371229868162100105777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 194060646559296864533897477 36386371229868162100105777)
          ·
            refine ⟨27289778422401121575079333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36386371229868162100105777 27289778422401121575079333)
            ·
              refine ⟨5116833454200210295327375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27289778422401121575079333 5116833454200210295327375)
              ·
                refine ⟨7675250181300315442991063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5116833454200210295327375 7675250181300315442991063)
                ·
                  refine ⟨11512875271950473164486595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7675250181300315442991063 11512875271950473164486595)
                  ·
                    refine ⟨17269312907925709746729893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11512875271950473164486595 17269312907925709746729893)
                    ·
                      refine ⟨3237996170236070577511855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17269312907925709746729893 3237996170236070577511855)
                      ·
                        rfl

theorem cell23_6305975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 4, 1, 1, 1, 4].length) (baseStart_6305975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6305975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6305975 prefixEnd_6305975 := by exact prefixLift 6305975
  have htrace : WordTrace (prefixWord ++ tailWord_6305975) baseStart_6305975 baseEnd_6305975 := by
    simpa [prefixWord, tailWord_6305975, baseEnd_6305975] using wordTrace_append hprefix tailTrace_6305975
  have hstable : (prefixWord ++ tailWord_6305975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6305975).length < 2 ^ (prefixWord ++ tailWord_6305975).sum := by decide
  have hdescent : baseEnd_6305975 < baseStart_6305975 := by decide
  rcases family_descends (prefixWord ++ tailWord_6305975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6305986 : List Nat := [3, 5, 1, 1, 1, 1, 2, 4, 1, 1, 3]
def baseStart_6305986 : Nat := 118140960795 + 6305986 * 2 ^ 59
def prefixEnd_6305986 : Nat := 4983230072969 + 3 ^ 40 * 6305986 * 2
def baseEnd_6305986 : Nat := 3238001818523270034474305

theorem tailTrace_6305986 : CollatzResearch.WordTrace tailWord_6305986 prefixEnd_6305986 3238001818523270034474305 := by
  unfold tailWord_6305986
  simp only [CollatzResearch.WordTrace]
  refine ⟨57499551133124293377854453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153332136354998115674278541 57499551133124293377854453)
  ·
    refine ⟨5390582918730402504173855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 57499551133124293377854453 5390582918730402504173855)
    ·
      refine ⟨8085874378095603756260783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5390582918730402504173855 8085874378095603756260783)
      ·
        refine ⟨12128811567143405634391175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8085874378095603756260783 12128811567143405634391175)
        ·
          refine ⟨18193217350715108451586763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12128811567143405634391175 18193217350715108451586763)
          ·
            refine ⟨27289826026072662677380145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18193217350715108451586763 27289826026072662677380145)
            ·
              refine ⟨20467369519554497008035109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27289826026072662677380145 20467369519554497008035109)
              ·
                refine ⟨3837631784916468189006583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20467369519554497008035109 3837631784916468189006583)
                ·
                  refine ⟨5756447677374702283509875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3837631784916468189006583 5756447677374702283509875)
                  ·
                    refine ⟨8634671516062053425264813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5756447677374702283509875 8634671516062053425264813)
                    ·
                      refine ⟨3238001818523270034474305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8634671516062053425264813 3238001818523270034474305)
                      ·
                        rfl

theorem cell23_6305986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 2, 4, 1, 1, 3].length) (baseStart_6305986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6305986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6305986 prefixEnd_6305986 := by exact prefixLift 6305986
  have htrace : WordTrace (prefixWord ++ tailWord_6305986) baseStart_6305986 baseEnd_6305986 := by
    simpa [prefixWord, tailWord_6305986, baseEnd_6305986] using wordTrace_append hprefix tailTrace_6305986
  have hstable : (prefixWord ++ tailWord_6305986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6305986).length < 2 ^ (prefixWord ++ tailWord_6305986).sum := by decide
  have hdescent : baseEnd_6305986 < baseStart_6305986 := by decide
  rcases family_descends (prefixWord ++ tailWord_6305986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6305991 : List Nat := [1, 1, 4, 1, 1, 1, 1, 1, 2, 7, 3]
def baseStart_6305991 : Nat := 118140960795 + 6305991 * 2 ^ 59
def prefixEnd_6305991 : Nat := 4983230072969 + 3 ^ 40 * 6305991 * 2
def baseEnd_6305991 : Nat := 3238004385926542514911781

theorem tailTrace_6305991 : CollatzResearch.WordTrace tailWord_6305991 prefixEnd_6305991 3238004385926542514911781 := by
  unfold tailWord_6305991
  simp only [CollatzResearch.WordTrace]
  refine ⟨229998386897479059365349827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153332257931652706243566551 229998386897479059365349827)
  ·
    refine ⟨344997580346218589048024741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229998386897479059365349827 344997580346218589048024741)
    ·
      refine ⟨64687046314915985446504639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 344997580346218589048024741 64687046314915985446504639)
      ·
        refine ⟨97030569472373978169756959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64687046314915985446504639 97030569472373978169756959)
        ·
          refine ⟨145545854208560967254635439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97030569472373978169756959 145545854208560967254635439)
          ·
            refine ⟨218318781312841450881953159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 145545854208560967254635439 218318781312841450881953159)
            ·
              refine ⟨327478171969262176322929739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 218318781312841450881953159 327478171969262176322929739)
              ·
                refine ⟨491217257953893264484394609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 327478171969262176322929739 491217257953893264484394609)
                ·
                  refine ⟨368412943465419948363295957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 491217257953893264484394609 368412943465419948363295957)
                  ·
                    refine ⟨8634678362470780039764749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 368412943465419948363295957 8634678362470780039764749)
                    ·
                      refine ⟨3238004385926542514911781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8634678362470780039764749 3238004385926542514911781)
                      ·
                        rfl

theorem cell23_6305991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 1, 2, 7, 3].length) (baseStart_6305991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6305991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6305991 prefixEnd_6305991 := by exact prefixLift 6305991
  have htrace : WordTrace (prefixWord ++ tailWord_6305991) baseStart_6305991 baseEnd_6305991 := by
    simpa [prefixWord, tailWord_6305991, baseEnd_6305991] using wordTrace_append hprefix tailTrace_6305991
  have hstable : (prefixWord ++ tailWord_6305991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6305991).length < 2 ^ (prefixWord ++ tailWord_6305991).sum := by decide
  have hdescent : baseEnd_6305991 < baseStart_6305991 := by decide
  rcases family_descends (prefixWord ++ tailWord_6305991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6306002 : List Nat := [3, 2, 2, 2, 1, 3, 3, 1, 2, 4]
def baseStart_6306002 : Nat := 118140960795 + 6306002 * 2 ^ 59
def prefixEnd_6306002 : Nat := 4983230072969 + 3 ^ 40 * 6306002 * 2
def baseEnd_6306002 : Nat := 1079336678071247323958077

theorem tailTrace_6306002 : CollatzResearch.WordTrace tailWord_6306002 prefixEnd_6306002 1079336678071247323958077 := by
  unfold tailWord_6306002
  simp only [CollatzResearch.WordTrace]
  refine ⟨57499697025109802061000065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153332525400292805496000173 57499697025109802061000065)
  ·
    refine ⟨43124772768832351545750049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57499697025109802061000065 43124772768832351545750049)
    ·
      refine ⟨32343579576624263659312537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43124772768832351545750049 32343579576624263659312537)
      ·
        refine ⟨24257684682468197744484403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32343579576624263659312537 24257684682468197744484403)
        ·
          refine ⟨36386527023702296616726605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24257684682468197744484403 36386527023702296616726605)
          ·
            refine ⟨13644947633888361231272477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36386527023702296616726605 13644947633888361231272477)
            ·
              refine ⟨5116855362708135461727179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13644947633888361231272477 5116855362708135461727179)
              ·
                refine ⟨7675283044062203192590769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5116855362708135461727179 7675283044062203192590769)
                ·
                  refine ⟨5756462283046652394443077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7675283044062203192590769 5756462283046652394443077)
                  ·
                    refine ⟨1079336678071247323958077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5756462283046652394443077 1079336678071247323958077)
                    ·
                      rfl

theorem cell23_6306002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 3, 1, 2, 4].length) (baseStart_6306002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6306002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6306002 prefixEnd_6306002 := by exact prefixLift 6306002
  have htrace : WordTrace (prefixWord ++ tailWord_6306002) baseStart_6306002 baseEnd_6306002 := by
    simpa [prefixWord, tailWord_6306002, baseEnd_6306002] using wordTrace_append hprefix tailTrace_6306002
  have hstable : (prefixWord ++ tailWord_6306002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6306002).length < 2 ^ (prefixWord ++ tailWord_6306002).sum := by decide
  have hdescent : baseEnd_6306002 < baseStart_6306002 := by decide
  rcases family_descends (prefixWord ++ tailWord_6306002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6306035 : List Nat := [1, 1, 1, 2, 2, 4, 1, 5, 1, 3, 2]
def baseStart_6306035 : Nat := 118140960795 + 6306035 * 2 ^ 59
def prefixEnd_6306035 : Nat := 4983230072969 + 3 ^ 40 * 6306035 * 2
def baseEnd_6306035 : Nat := 3238026979075340342761579

theorem tailTrace_6306035 : CollatzResearch.WordTrace tailWord_6306035 prefixEnd_6306035 3238026979075340342761579 := by
  unfold tailWord_6306035
  simp only [CollatzResearch.WordTrace]
  refine ⟨229999991709319654879951559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153333327806213103253301039 229999991709319654879951559)
  ·
    refine ⟨344999987563979482319927339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229999991709319654879951559 344999987563979482319927339)
    ·
      refine ⟨517499981345969223479891009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 344999987563979482319927339 517499981345969223479891009)
      ·
        refine ⟨388124986009476917609918257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 517499981345969223479891009 388124986009476917609918257)
        ·
          refine ⟨291093739507107688207438693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 388124986009476917609918257 291093739507107688207438693)
          ·
            refine ⟨54580076157582691538894755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 291093739507107688207438693 54580076157582691538894755)
            ·
              refine ⟨81870114236374037308342133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54580076157582691538894755 81870114236374037308342133)
              ·
                refine ⟨7675323209660065997657075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 81870114236374037308342133 7675323209660065997657075)
                ·
                  refine ⟨11512984814490098996485613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7675323209660065997657075 11512984814490098996485613)
                  ·
                    refine ⟨4317369305433787123682105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11512984814490098996485613 4317369305433787123682105)
                    ·
                      refine ⟨3238026979075340342761579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4317369305433787123682105 3238026979075340342761579)
                      ·
                        rfl

theorem cell23_6306035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 5, 1, 3, 2].length) (baseStart_6306035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6306035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6306035 prefixEnd_6306035 := by exact prefixLift 6306035
  have htrace : WordTrace (prefixWord ++ tailWord_6306035) baseStart_6306035 baseEnd_6306035 := by
    simpa [prefixWord, tailWord_6306035, baseEnd_6306035] using wordTrace_append hprefix tailTrace_6306035
  have hstable : (prefixWord ++ tailWord_6306035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6306035).length < 2 ^ (prefixWord ++ tailWord_6306035).sum := by decide
  have hdescent : baseEnd_6306035 < baseStart_6306035 := by decide
  rcases family_descends (prefixWord ++ tailWord_6306035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6306041 : List Nat := [1, 2, 1, 3, 1, 1, 2, 4, 2, 6]
def baseStart_6306041 : Nat := 118140960795 + 6306041 * 2 ^ 59
def prefixEnd_6306041 : Nat := 4983230072969 + 3 ^ 40 * 6306041 * 2
def baseEnd_6306041 : Nat := 1079343353319755773095517

theorem tailTrace_6306041 : CollatzResearch.WordTrace tailWord_6306041 prefixEnd_6306041 1079343353319755773095517 := by
  unfold tailWord_6306041
  simp only [CollatzResearch.WordTrace]
  refine ⟨230000210547297917904669977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153333473698198611936446651 230000210547297917904669977)
  ·
    refine ⟨172500157910473438428502483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 230000210547297917904669977 172500157910473438428502483)
    ·
      refine ⟨258750236865710157642753725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172500157910473438428502483 258750236865710157642753725)
      ·
        refine ⟨97031338824641309116032647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 258750236865710157642753725 97031338824641309116032647)
        ·
          refine ⟨145547008236961963674048971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97031338824641309116032647 145547008236961963674048971)
          ·
            refine ⟨218320512355442945511073457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 145547008236961963674048971 218320512355442945511073457)
            ·
              refine ⟨163740384266582209133305093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 218320512355442945511073457 163740384266582209133305093)
              ·
                refine ⟨30701322049984164212494705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 163740384266582209133305093 30701322049984164212494705)
                ·
                  refine ⟨23025991537488123159371029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30701322049984164212494705 23025991537488123159371029)
                  ·
                    refine ⟨1079343353319755773095517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23025991537488123159371029 1079343353319755773095517)
                    ·
                      rfl

theorem cell23_6306041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 4, 2, 6].length) (baseStart_6306041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6306041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6306041 prefixEnd_6306041 := by exact prefixLift 6306041
  have htrace : WordTrace (prefixWord ++ tailWord_6306041) baseStart_6306041 baseEnd_6306041 := by
    simpa [prefixWord, tailWord_6306041, baseEnd_6306041] using wordTrace_append hprefix tailTrace_6306041
  have hstable : (prefixWord ++ tailWord_6306041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6306041).length < 2 ^ (prefixWord ++ tailWord_6306041).sum := by decide
  have hdescent : baseEnd_6306041 < baseStart_6306041 := by decide
  rcases family_descends (prefixWord ++ tailWord_6306041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6306051 : List Nat := [1, 1, 1, 3, 2, 3, 1, 2, 1, 3, 5]
def baseStart_6306051 : Nat := 118140960795 + 6306051 * 2 ^ 59
def prefixEnd_6306051 : Nat := 4983230072969 + 3 ^ 40 * 6306051 * 2
def baseEnd_6306051 : Nat := 3238035194765812280161505

theorem tailTrace_6306051 : CollatzResearch.WordTrace tailWord_6306051 prefixEnd_6306051 3238035194765812280161505 := by
  unfold tailWord_6306051
  simp only [CollatzResearch.WordTrace]
  refine ⟨230000575277261689612534007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153333716851507793075022671 230000575277261689612534007)
  ·
    refine ⟨345000862915892534418801011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230000575277261689612534007 345000862915892534418801011)
    ·
      refine ⟨517501294373838801628201517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 345000862915892534418801011 517501294373838801628201517)
      ·
        refine ⟨194062985390189550610575569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 517501294373838801628201517 194062985390189550610575569)
        ·
          refine ⟨145547239042642162957931677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 194062985390189550610575569 145547239042642162957931677)
          ·
            refine ⟨54580214640990811109224379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 145547239042642162957931677 54580214640990811109224379)
            ·
              refine ⟨81870321961486216663836569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54580214640990811109224379 81870321961486216663836569)
              ·
                refine ⟨61402741471114662497877427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 81870321961486216663836569 61402741471114662497877427)
                ·
                  refine ⟨92104112206671993746816141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61402741471114662497877427 92104112206671993746816141)
                  ·
                    refine ⟨34539042077501997655056053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 92104112206671993746816141 34539042077501997655056053)
                    ·
                      refine ⟨3238035194765812280161505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34539042077501997655056053 3238035194765812280161505)
                      ·
                        rfl

theorem cell23_6306051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 2, 1, 3, 5].length) (baseStart_6306051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6306051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6306051 prefixEnd_6306051 := by exact prefixLift 6306051
  have htrace : WordTrace (prefixWord ++ tailWord_6306051) baseStart_6306051 baseEnd_6306051 := by
    simpa [prefixWord, tailWord_6306051, baseEnd_6306051] using wordTrace_append hprefix tailTrace_6306051
  have hstable : (prefixWord ++ tailWord_6306051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6306051).length < 2 ^ (prefixWord ++ tailWord_6306051).sum := by decide
  have hdescent : baseEnd_6306051 < baseStart_6306051 := by decide
  rcases family_descends (prefixWord ++ tailWord_6306051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6306082 : List Nat := [3, 3, 1, 1, 3, 2, 1, 2, 1, 4, 2]
def baseStart_6306082 : Nat := 118140960795 + 6306082 * 2 ^ 59
def prefixEnd_6306082 : Nat := 4983230072969 + 3 ^ 40 * 6306082 * 2
def baseEnd_6306082 : Nat := 3238051112666101658873863

theorem tailTrace_6306082 : CollatzResearch.WordTrace tailWord_6306082 prefixEnd_6306082 3238051112666101658873863 := by
  unfold tailWord_6306082
  simp only [CollatzResearch.WordTrace]
  refine ⟨57500426485037345476728125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153334470626766254604608333 57500426485037345476728125)
  ·
    refine ⟨21562659931889004553773047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57500426485037345476728125 21562659931889004553773047)
    ·
      refine ⟨32343989897833506830659571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21562659931889004553773047 32343989897833506830659571)
      ·
        refine ⟨48515984846750260245989357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32343989897833506830659571 48515984846750260245989357)
        ·
          refine ⟨18193494317531347592246009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48515984846750260245989357 18193494317531347592246009)
          ·
            refine ⟨13645120738148510694184507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18193494317531347592246009 13645120738148510694184507)
            ·
              refine ⟨20467681107222766041276761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13645120738148510694184507 20467681107222766041276761)
              ·
                refine ⟨15350760830417074530957571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20467681107222766041276761 15350760830417074530957571)
                ·
                  refine ⟨23026141245625611796436357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15350760830417074530957571 23026141245625611796436357)
                  ·
                    refine ⟨4317401483554802211831817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23026141245625611796436357 4317401483554802211831817)
                    ·
                      refine ⟨3238051112666101658873863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4317401483554802211831817 3238051112666101658873863)
                      ·
                        rfl

theorem cell23_6306082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 1, 2, 1, 4, 2].length) (baseStart_6306082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6306082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6306082 prefixEnd_6306082 := by exact prefixLift 6306082
  have htrace : WordTrace (prefixWord ++ tailWord_6306082) baseStart_6306082 baseEnd_6306082 := by
    simpa [prefixWord, tailWord_6306082, baseEnd_6306082] using wordTrace_append hprefix tailTrace_6306082
  have hstable : (prefixWord ++ tailWord_6306082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6306082).length < 2 ^ (prefixWord ++ tailWord_6306082).sum := by decide
  have hdescent : baseEnd_6306082 < baseStart_6306082 := by decide
  rcases family_descends (prefixWord ++ tailWord_6306082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6306131 : List Nat := [1, 1, 1, 2, 1, 1, 4, 1, 1, 10]
def baseStart_6306131 : Nat := 118140960795 + 6306131 * 2 ^ 59
def prefixEnd_6306131 : Nat := 4983230072969 + 3 ^ 40 * 6306131 * 2
def baseEnd_6306131 : Nat := 1079358757739390655720379

theorem tailTrace_6306131 : CollatzResearch.WordTrace tailWord_6306131 prefixEnd_6306131 1079358757739390655720379 := by
  unfold tailWord_6306131
  simp only [CollatzResearch.WordTrace]
  refine ⟨230003493116971863275446247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153335662077981242183630831 230003493116971863275446247)
  ·
    refine ⟨345005239675457794913169371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230003493116971863275446247 345005239675457794913169371)
    ·
      refine ⟨517507859513186692369754057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 345005239675457794913169371 517507859513186692369754057)
      ·
        refine ⟨388130894634890019277315543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 517507859513186692369754057 388130894634890019277315543)
        ·
          refine ⟨582196341952335028915973315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 388130894634890019277315543 582196341952335028915973315)
          ·
            refine ⟨873294512928502543373959973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 582196341952335028915973315 873294512928502543373959973)
            ·
              refine ⟨163742721174094226882617495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 873294512928502543373959973 163742721174094226882617495)
              ·
                refine ⟨245614081761141340323926243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 163742721174094226882617495 245614081761141340323926243)
                ·
                  refine ⟨368421122641712010485889365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 245614081761141340323926243 368421122641712010485889365)
                  ·
                    refine ⟨1079358757739390655720379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 368421122641712010485889365 1079358757739390655720379)
                    ·
                      rfl

theorem cell23_6306131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 1, 1, 10].length) (baseStart_6306131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6306131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6306131 prefixEnd_6306131 := by exact prefixLift 6306131
  have htrace : WordTrace (prefixWord ++ tailWord_6306131) baseStart_6306131 baseEnd_6306131 := by
    simpa [prefixWord, tailWord_6306131, baseEnd_6306131] using wordTrace_append hprefix tailTrace_6306131
  have hstable : (prefixWord ++ tailWord_6306131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6306131).length < 2 ^ (prefixWord ++ tailWord_6306131).sum := by decide
  have hdescent : baseEnd_6306131 < baseStart_6306131 := by decide
  rcases family_descends (prefixWord ++ tailWord_6306131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6306209 : List Nat := [1, 2, 3, 5, 1, 1, 1, 2, 2, 2, 3]
def baseStart_6306209 : Nat := 118140960795 + 6306209 * 2 ^ 59
def prefixEnd_6306209 : Nat := 4983230072969 + 3 ^ 40 * 6306209 * 2
def baseEnd_6306209 : Nat := 3238116324709222661985779

theorem tailTrace_6306209 : CollatzResearch.WordTrace tailWord_6306209 prefixEnd_6306209 3238116324709222661985779 := by
  unfold tailWord_6306209
  simp only [CollatzResearch.WordTrace]
  refine ⟨230006338010689282596785681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153337558673792855064523787 230006338010689282596785681)
  ·
    refine ⟨172504753508016961947589261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 230006338010689282596785681 172504753508016961947589261)
    ·
      refine ⟨64689282565506360730345973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 172504753508016961947589261 64689282565506360730345973)
      ·
        refine ⟨6064620240516221318469935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 64689282565506360730345973 6064620240516221318469935)
        ·
          refine ⟨9096930360774331977704903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6064620240516221318469935 9096930360774331977704903)
          ·
            refine ⟨13645395541161497966557355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9096930360774331977704903 13645395541161497966557355)
            ·
              refine ⟨20468093311742246949836033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13645395541161497966557355 20468093311742246949836033)
              ·
                refine ⟨15351069983806685212377025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20468093311742246949836033 15351069983806685212377025)
                ·
                  refine ⟨11513302487855013909282769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15351069983806685212377025 11513302487855013909282769)
                  ·
                    refine ⟨8634976865891260431962077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11513302487855013909282769 8634976865891260431962077)
                    ·
                      refine ⟨3238116324709222661985779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8634976865891260431962077 3238116324709222661985779)
                      ·
                        rfl

theorem cell23_6306209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 1, 2, 2, 2, 3].length) (baseStart_6306209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6306209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6306209 prefixEnd_6306209 := by exact prefixLift 6306209
  have htrace : WordTrace (prefixWord ++ tailWord_6306209) baseStart_6306209 baseEnd_6306209 := by
    simpa [prefixWord, tailWord_6306209, baseEnd_6306209] using wordTrace_append hprefix tailTrace_6306209
  have hstable : (prefixWord ++ tailWord_6306209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6306209).length < 2 ^ (prefixWord ++ tailWord_6306209).sum := by decide
  have hdescent : baseEnd_6306209 < baseStart_6306209 := by decide
  rcases family_descends (prefixWord ++ tailWord_6306209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6306229 : List Nat := [1, 3, 3, 2, 3, 2, 2, 1, 6]
def baseStart_6306229 : Nat := 118140960795 + 6306229 * 2 ^ 59
def prefixEnd_6306229 : Nat := 4983230072969 + 3 ^ 40 * 6306229 * 2
def baseEnd_6306229 : Nat := 359791843813590287081743

theorem tailTrace_6306229 : CollatzResearch.WordTrace tailWord_6306229 prefixEnd_6306229 359791843813590287081743 := by
  unfold tailWord_6306229
  simp only [CollatzResearch.WordTrace]
  refine ⟨230007067470616826012513741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153338044980411217341675827 230007067470616826012513741)
  ·
    refine ⟨86252650301481309754692653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 230007067470616826012513741 86252650301481309754692653)
    ·
      refine ⟨32344743863055491158009745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86252650301481309754692653 32344743863055491158009745)
      ·
        refine ⟨24258557897291618368507309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32344743863055491158009745 24258557897291618368507309)
        ·
          refine ⟨9096959211484356888190241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24258557897291618368507309 9096959211484356888190241)
          ·
            refine ⟨6822719408613267666142681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9096959211484356888190241 6822719408613267666142681)
            ·
              refine ⟨5117039556459950749607011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6822719408613267666142681 5117039556459950749607011)
              ·
                refine ⟨7675559334689926124410517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5117039556459950749607011 7675559334689926124410517)
                ·
                  refine ⟨359791843813590287081743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7675559334689926124410517 359791843813590287081743)
                  ·
                    rfl

theorem cell23_6306229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 2, 2, 1, 6].length) (baseStart_6306229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6306229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6306229 prefixEnd_6306229 := by exact prefixLift 6306229
  have htrace : WordTrace (prefixWord ++ tailWord_6306229) baseStart_6306229 baseEnd_6306229 := by
    simpa [prefixWord, tailWord_6306229, baseEnd_6306229] using wordTrace_append hprefix tailTrace_6306229
  have hstable : (prefixWord ++ tailWord_6306229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6306229).length < 2 ^ (prefixWord ++ tailWord_6306229).sum := by decide
  have hdescent : baseEnd_6306229 < baseStart_6306229 := by decide
  rcases family_descends (prefixWord ++ tailWord_6306229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6306272 : List Nat := [2, 1, 1, 3, 1, 1, 6, 2, 2, 4]
def baseStart_6306272 : Nat := 118140960795 + 6306272 * 2 ^ 59
def prefixEnd_6306272 : Nat := 4983230072969 + 3 ^ 40 * 6306272 * 2
def baseEnd_6306272 : Nat := 1079382891330151971832663

theorem tailTrace_6306272 : CollatzResearch.WordTrace tailWord_6306272 prefixEnd_6306272 1079382891330151971832663 := by
  unfold tailWord_6306272
  simp only [CollatzResearch.WordTrace]
  refine ⟨115004317904730522178164535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153339090539640696237552713 115004317904730522178164535)
  ·
    refine ⟨172506476857095783267246803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115004317904730522178164535 172506476857095783267246803)
    ·
      refine ⟨258759715285643674900870205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172506476857095783267246803 258759715285643674900870205)
      ·
        refine ⟨97034893232116378087826327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 258759715285643674900870205 97034893232116378087826327)
        ·
          refine ⟨145552339848174567131739491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97034893232116378087826327 145552339848174567131739491)
          ·
            refine ⟨218328509772261850697609237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 145552339848174567131739491 218328509772261850697609237)
            ·
              refine ⟨10234148895574774251450433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 218328509772261850697609237 10234148895574774251450433)
              ·
                refine ⟨7675611671681080688587825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10234148895574774251450433 7675611671681080688587825)
                ·
                  refine ⟨5756708753760810516440869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7675611671681080688587825 5756708753760810516440869)
                  ·
                    refine ⟨1079382891330151971832663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5756708753760810516440869 1079382891330151971832663)
                    ·
                      rfl

theorem cell23_6306272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 6, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 6, 2, 2, 4].length) (baseStart_6306272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6306272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6306272 prefixEnd_6306272 := by exact prefixLift 6306272
  have htrace : WordTrace (prefixWord ++ tailWord_6306272) baseStart_6306272 baseEnd_6306272 := by
    simpa [prefixWord, tailWord_6306272, baseEnd_6306272] using wordTrace_append hprefix tailTrace_6306272
  have hstable : (prefixWord ++ tailWord_6306272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6306272).length < 2 ^ (prefixWord ++ tailWord_6306272).sum := by decide
  have hdescent : baseEnd_6306272 < baseStart_6306272 := by decide
  rcases family_descends (prefixWord ++ tailWord_6306272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6306279 : List Nat := [1, 1, 5, 2, 1, 1, 2, 3, 3, 2, 2]
def baseStart_6306279 : Nat := 118140960795 + 6306279 * 2 ^ 59
def prefixEnd_6306279 : Nat := 4983230072969 + 3 ^ 40 * 6306279 * 2
def baseEnd_6306279 : Nat := 3238152268355037388110457

theorem tailTrace_6306279 : CollatzResearch.WordTrace tailWord_6306279 prefixEnd_6306279 3238152268355037388110457 := by
  unfold tailWord_6306279
  simp only [CollatzResearch.WordTrace]
  refine ⟨230008891120435684551833891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153339260746957123034555927 230008891120435684551833891)
  ·
    refine ⟨345013336680653526827750837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230008891120435684551833891 345013336680653526827750837)
    ·
      refine ⟨32345000313811268140101641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 345013336680653526827750837 32345000313811268140101641)
      ·
        refine ⟨24258750235358451105076231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32345000313811268140101641 24258750235358451105076231)
        ·
          refine ⟨36388125353037676657614347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24258750235358451105076231 36388125353037676657614347)
          ·
            refine ⟨54582188029556514986421521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36388125353037676657614347 54582188029556514986421521)
            ·
              refine ⟨40936641022167386239816141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54582188029556514986421521 40936641022167386239816141)
              ·
                refine ⟨15351240383312769839931053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40936641022167386239816141 15351240383312769839931053)
                ·
                  refine ⟨5756715143742288689974145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15351240383312769839931053 5756715143742288689974145)
                  ·
                    refine ⟨4317536357806716517480609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5756715143742288689974145 4317536357806716517480609)
                    ·
                      refine ⟨3238152268355037388110457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4317536357806716517480609 3238152268355037388110457)
                      ·
                        rfl

theorem cell23_6306279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 3, 3, 2, 2].length) (baseStart_6306279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6306279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6306279 prefixEnd_6306279 := by exact prefixLift 6306279
  have htrace : WordTrace (prefixWord ++ tailWord_6306279) baseStart_6306279 baseEnd_6306279 := by
    simpa [prefixWord, tailWord_6306279, baseEnd_6306279] using wordTrace_append hprefix tailTrace_6306279
  have hstable : (prefixWord ++ tailWord_6306279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6306279).length < 2 ^ (prefixWord ++ tailWord_6306279).sum := by decide
  have hdescent : baseEnd_6306279 < baseStart_6306279 := by decide
  rcases family_descends (prefixWord ++ tailWord_6306279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6306282 : List Nat := [3, 1, 3, 1, 3, 1, 1, 2, 3, 2, 3]
def baseStart_6306282 : Nat := 118140960795 + 6306282 * 2 ^ 59
def prefixEnd_6306282 : Nat := 4983230072969 + 3 ^ 40 * 6306282 * 2
def baseEnd_6306282 : Nat := 3238153808797000876372943

theorem tailTrace_6306282 : CollatzResearch.WordTrace tailWord_6306282 prefixEnd_6306282 3238153808797000876372943 := by
  unfold tailWord_6306282
  simp only [CollatzResearch.WordTrace]
  refine ⟨57502250134856204016048275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153339333692949877376128733 57502250134856204016048275)
  ·
    refine ⟨86253375202284306024072413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57502250134856204016048275 86253375202284306024072413)
    ·
      refine ⟨32345015700856614759027155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86253375202284306024072413 32345015700856614759027155)
      ·
        refine ⟨48517523551284922138540733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32345015700856614759027155 48517523551284922138540733)
        ·
          refine ⟨18194071331731845801952775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48517523551284922138540733 18194071331731845801952775)
          ·
            refine ⟨27291106997597768702929163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18194071331731845801952775 27291106997597768702929163)
            ·
              refine ⟨40936660496396653054393745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27291106997597768702929163 40936660496396653054393745)
              ·
                refine ⟨30702495372297489790795309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40936660496396653054393745 30702495372297489790795309)
                ·
                  refine ⟨11513435764611558671548241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30702495372297489790795309 11513435764611558671548241)
                  ·
                    refine ⟨8635076823458669003661181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11513435764611558671548241 8635076823458669003661181)
                    ·
                      refine ⟨3238153808797000876372943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8635076823458669003661181 3238153808797000876372943)
                      ·
                        rfl

theorem cell23_6306282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 2, 3, 2, 3].length) (baseStart_6306282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6306282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6306282 prefixEnd_6306282 := by exact prefixLift 6306282
  have htrace : WordTrace (prefixWord ++ tailWord_6306282) baseStart_6306282 baseEnd_6306282 := by
    simpa [prefixWord, tailWord_6306282, baseEnd_6306282] using wordTrace_append hprefix tailTrace_6306282
  have hstable : (prefixWord ++ tailWord_6306282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6306282).length < 2 ^ (prefixWord ++ tailWord_6306282).sum := by decide
  have hdescent : baseEnd_6306282 < baseStart_6306282 := by decide
  rcases family_descends (prefixWord ++ tailWord_6306282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6306310 : List Nat := [6, 2, 1, 1, 1, 3, 2, 1, 1, 5]
def baseStart_6306310 : Nat := 118140960795 + 6306310 * 2 ^ 59
def prefixEnd_6306310 : Nat := 4983230072969 + 3 ^ 40 * 6306310 * 2
def baseEnd_6306310 : Nat := 1079389395418442255607605

theorem tailTrace_6306310 : CollatzResearch.WordTrace tailWord_6306310 prefixEnd_6306310 1079389395418442255607605 := by
  unfold tailWord_6306310
  simp only [CollatzResearch.WordTrace]
  refine ⟨7187813180728855526444137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 153340014522215584564141589 7187813180728855526444137)
  ·
    refine ⟨5390859885546641644833103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7187813180728855526444137 5390859885546641644833103)
    ·
      refine ⟨8086289828319962467249655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5390859885546641644833103 8086289828319962467249655)
      ·
        refine ⟨12129434742479943700874483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8086289828319962467249655 12129434742479943700874483)
        ·
          refine ⟨18194152113719915551311725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12129434742479943700874483 18194152113719915551311725)
          ·
            refine ⟨6822807042644968331741897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18194152113719915551311725 6822807042644968331741897)
            ·
              refine ⟨5117105281983726248806423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6822807042644968331741897 5117105281983726248806423)
              ·
                refine ⟨7675657922975589373209635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5117105281983726248806423 7675657922975589373209635)
                ·
                  refine ⟨11513486884463384059814453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7675657922975589373209635 11513486884463384059814453)
                  ·
                    refine ⟨1079389395418442255607605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11513486884463384059814453 1079389395418442255607605)
                    ·
                      rfl

theorem cell23_6306310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 3, 2, 1, 1, 5].length) (baseStart_6306310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6306310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6306310 prefixEnd_6306310 := by exact prefixLift 6306310
  have htrace : WordTrace (prefixWord ++ tailWord_6306310) baseStart_6306310 baseEnd_6306310 := by
    simpa [prefixWord, tailWord_6306310, baseEnd_6306310] using wordTrace_append hprefix tailTrace_6306310
  have hstable : (prefixWord ++ tailWord_6306310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6306310).length < 2 ^ (prefixWord ++ tailWord_6306310).sum := by decide
  have hdescent : baseEnd_6306310 < baseStart_6306310 := by decide
  rcases family_descends (prefixWord ++ tailWord_6306310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6306312 : List Nat := [2, 1, 3, 2, 1, 1, 1, 4, 4, 1, 3]
def baseStart_6306312 : Nat := 118140960795 + 6306312 * 2 ^ 59
def prefixEnd_6306312 : Nat := 4983230072969 + 3 ^ 40 * 6306312 * 2
def baseEnd_6306312 : Nat := 3238169213216635758997805

theorem tailTrace_6306312 : CollatzResearch.WordTrace tailWord_6306312 prefixEnd_6306312 3238169213216635758997805 := by
  unfold tailWord_6306312
  simp only [CollatzResearch.WordTrace]
  refine ⟨115005047364658065593892595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153340063152877420791856793 115005047364658065593892595)
  ·
    refine ⟨172507571046987098390838893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115005047364658065593892595 172507571046987098390838893)
    ·
      refine ⟨64690339142620161896564585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 172507571046987098390838893 64690339142620161896564585)
      ·
        refine ⟨48517754356965121422423439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64690339142620161896564585 48517754356965121422423439)
        ·
          refine ⟨72776631535447682133635159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48517754356965121422423439 72776631535447682133635159)
          ·
            refine ⟨109164947303171523200452739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72776631535447682133635159 109164947303171523200452739)
            ·
              refine ⟨163747420954757284800679109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109164947303171523200452739 163747420954757284800679109)
              ·
                refine ⟨30702641429016990900127333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 163747420954757284800679109 30702641429016990900127333)
                ·
                  refine ⟨5756745267940685793773875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30702641429016990900127333 5756745267940685793773875)
                  ·
                    refine ⟨8635117901911028690660813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5756745267940685793773875 8635117901911028690660813)
                    ·
                      refine ⟨3238169213216635758997805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8635117901911028690660813 3238169213216635758997805)
                      ·
                        rfl

theorem cell23_6306312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 4, 4, 1, 3].length) (baseStart_6306312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6306312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6306312 prefixEnd_6306312 := by exact prefixLift 6306312
  have htrace : WordTrace (prefixWord ++ tailWord_6306312) baseStart_6306312 baseEnd_6306312 := by
    simpa [prefixWord, tailWord_6306312, baseEnd_6306312] using wordTrace_append hprefix tailTrace_6306312
  have hstable : (prefixWord ++ tailWord_6306312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6306312).length < 2 ^ (prefixWord ++ tailWord_6306312).sum := by decide
  have hdescent : baseEnd_6306312 < baseStart_6306312 := by decide
  rcases family_descends (prefixWord ++ tailWord_6306312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6306316 : List Nat := [2, 2, 1, 2, 4, 3, 2, 1, 1, 2, 3]
def baseStart_6306316 : Nat := 118140960795 + 6306316 * 2 ^ 59
def prefixEnd_6306316 : Nat := 4983230072969 + 3 ^ 40 * 6306316 * 2
def baseEnd_6306316 : Nat := 3238171267139253743347787

theorem tailTrace_6306316 : CollatzResearch.WordTrace tailWord_6306316 prefixEnd_6306316 3238171267139253743347787 := by
  unfold tailWord_6306316
  simp only [CollatzResearch.WordTrace]
  refine ⟨115005120310650819935465401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153340160414201093247287201 115005120310650819935465401)
  ·
    refine ⟨86253840232988114951599051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115005120310650819935465401 86253840232988114951599051)
    ·
      refine ⟨129380760349482172427398577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86253840232988114951599051 129380760349482172427398577)
      ·
        refine ⟨97035570262111629320548933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129380760349482172427398577 97035570262111629320548933)
        ·
          refine ⟨18194169424145930497602925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 97035570262111629320548933 18194169424145930497602925)
          ·
            refine ⟨6822813534054723936601097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18194169424145930497602925 6822813534054723936601097)
            ·
              refine ⟨5117110150541042952450823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6822813534054723936601097 5117110150541042952450823)
              ·
                refine ⟨7675665225811564428676235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5117110150541042952450823 7675665225811564428676235)
                ·
                  refine ⟨11513497838717346643014353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7675665225811564428676235 11513497838717346643014353)
                  ·
                    refine ⟨8635123379038009982260765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11513497838717346643014353 8635123379038009982260765)
                    ·
                      refine ⟨3238171267139253743347787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8635123379038009982260765 3238171267139253743347787)
                      ·
                        rfl

theorem cell23_6306316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 3, 2, 1, 1, 2, 3].length) (baseStart_6306316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6306316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6306316 prefixEnd_6306316 := by exact prefixLift 6306316
  have htrace : WordTrace (prefixWord ++ tailWord_6306316) baseStart_6306316 baseEnd_6306316 := by
    simpa [prefixWord, tailWord_6306316, baseEnd_6306316] using wordTrace_append hprefix tailTrace_6306316
  have hstable : (prefixWord ++ tailWord_6306316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6306316).length < 2 ^ (prefixWord ++ tailWord_6306316).sum := by decide
  have hdescent : baseEnd_6306316 < baseStart_6306316 := by decide
  rcases family_descends (prefixWord ++ tailWord_6306316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6306343 : List Nat := [1, 1, 7, 2, 2, 1, 1, 1, 1, 2, 4]
def baseStart_6306343 : Nat := 118140960795 + 6306343 * 2 ^ 59
def prefixEnd_6306343 : Nat := 4983230072969 + 3 ^ 40 * 6306343 * 2
def baseEnd_6306343 : Nat := 3238185131116925137710163

theorem tailTrace_6306343 : CollatzResearch.WordTrace tailWord_6306343 prefixEnd_6306343 3238185131116925137710163 := by
  unfold tailWord_6306343
  simp only [CollatzResearch.WordTrace]
  refine ⟨230011225392203823482163683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153340816928135882321442455 230011225392203823482163683)
  ·
    refine ⟨345016838088305735223245525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230011225392203823482163683 345016838088305735223245525)
    ·
      refine ⟨8086332142694665669294817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 345016838088305735223245525 8086332142694665669294817)
      ·
        refine ⟨6064749107020999251971113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8086332142694665669294817 6064749107020999251971113)
        ·
          refine ⟨4548561830265749438978335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6064749107020999251971113 4548561830265749438978335)
          ·
            refine ⟨6822842745398624158467503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4548561830265749438978335 6822842745398624158467503)
            ·
              refine ⟨10234264118097936237701255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6822842745398624158467503 10234264118097936237701255)
              ·
                refine ⟨15351396177146904356551883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10234264118097936237701255 15351396177146904356551883)
                ·
                  refine ⟨23027094265720356534827825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15351396177146904356551883 23027094265720356534827825)
                  ·
                    refine ⟨17270320699290267401120869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23027094265720356534827825 17270320699290267401120869)
                    ·
                      refine ⟨3238185131116925137710163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17270320699290267401120869 3238185131116925137710163)
                      ·
                        rfl

theorem cell23_6306343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 2, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 2, 1, 1, 1, 1, 2, 4].length) (baseStart_6306343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6306343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6306343 prefixEnd_6306343 := by exact prefixLift 6306343
  have htrace : WordTrace (prefixWord ++ tailWord_6306343) baseStart_6306343 baseEnd_6306343 := by
    simpa [prefixWord, tailWord_6306343, baseEnd_6306343] using wordTrace_append hprefix tailTrace_6306343
  have hstable : (prefixWord ++ tailWord_6306343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6306343).length < 2 ^ (prefixWord ++ tailWord_6306343).sum := by decide
  have hdescent : baseEnd_6306343 < baseStart_6306343 := by decide
  rcases family_descends (prefixWord ++ tailWord_6306343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6306355 : List Nat := [1, 1, 1, 2, 4, 2, 2, 2, 2, 1, 5]
def baseStart_6306355 : Nat := 118140960795 + 6306355 * 2 ^ 59
def prefixEnd_6306355 : Nat := 4983230072969 + 3 ^ 40 * 6306355 * 2
def baseEnd_6306355 : Nat := 3238191292884779090760107

theorem tailTrace_6306355 : CollatzResearch.WordTrace tailWord_6306355 prefixEnd_6306355 3238191292884779090760107 := by
  unfold tailWord_6306355
  simp only [CollatzResearch.WordTrace]
  refine ⟨230011663068160349531600519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153341108712106899687733679 230011663068160349531600519)
  ·
    refine ⟨345017494602240524297400779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230011663068160349531600519 345017494602240524297400779)
    ·
      refine ⟨517526241903360786446101169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 345017494602240524297400779 517526241903360786446101169)
      ·
        refine ⟨388144681427520589834575877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 517526241903360786446101169 388144681427520589834575877)
        ·
          refine ⟨72777127767660110593982977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 388144681427520589834575877 72777127767660110593982977)
          ·
            refine ⟨54582845825745082945487233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72777127767660110593982977 54582845825745082945487233)
            ·
              refine ⟨40937134369308812209115425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54582845825745082945487233 40937134369308812209115425)
              ·
                refine ⟨30702850776981609156836569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40937134369308812209115425 30702850776981609156836569)
                ·
                  refine ⟨23027138082736206867627427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30702850776981609156836569 23027138082736206867627427)
                  ·
                    refine ⟨34540707124104310301441141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23027138082736206867627427 34540707124104310301441141)
                    ·
                      refine ⟨3238191292884779090760107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34540707124104310301441141 3238191292884779090760107)
                      ·
                        rfl

theorem cell23_6306355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 2, 2, 1, 5].length) (baseStart_6306355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6306355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6306355 prefixEnd_6306355 := by exact prefixLift 6306355
  have htrace : WordTrace (prefixWord ++ tailWord_6306355) baseStart_6306355 baseEnd_6306355 := by
    simpa [prefixWord, tailWord_6306355, baseEnd_6306355] using wordTrace_append hprefix tailTrace_6306355
  have hstable : (prefixWord ++ tailWord_6306355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6306355).length < 2 ^ (prefixWord ++ tailWord_6306355).sum := by decide
  have hdescent : baseEnd_6306355 < baseStart_6306355 := by decide
  rcases family_descends (prefixWord ++ tailWord_6306355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6306386 : List Nat := [3, 2, 2, 1, 2, 1, 2, 4, 2, 2, 2]
def baseStart_6306386 : Nat := 118140960795 + 6306386 * 2 ^ 59
def prefixEnd_6306386 : Nat := 4983230072969 + 3 ^ 40 * 6306386 * 2
def baseEnd_6306386 : Nat := 3238207210785068469472465

theorem tailTrace_6306386 : CollatzResearch.WordTrace tailWord_6306386 prefixEnd_6306386 3238207210785068469472465 := by
  unfold tailWord_6306386
  simp only [CollatzResearch.WordTrace]
  refine ⟨57503198432762010456494753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153341862487365361217319341 57503198432762010456494753)
  ·
    refine ⟨43127398824571507842371065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57503198432762010456494753 43127398824571507842371065)
    ·
      refine ⟨32345549118428630881778299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43127398824571507842371065 32345549118428630881778299)
      ·
        refine ⟨48518323677642946322667449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32345549118428630881778299 48518323677642946322667449)
        ·
          refine ⟨36388742758232209742000587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48518323677642946322667449 36388742758232209742000587)
          ·
            refine ⟨54583114137348314613000881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36388742758232209742000587 54583114137348314613000881)
            ·
              refine ⟨40937335603011235959750661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54583114137348314613000881 40937335603011235959750661)
              ·
                refine ⟨7675750425564606742453249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40937335603011235959750661 7675750425564606742453249)
                ·
                  refine ⟨5756812819173455056839937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7675750425564606742453249 5756812819173455056839937)
                  ·
                    refine ⟨4317609614380091292629953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5756812819173455056839937 4317609614380091292629953)
                    ·
                      refine ⟨3238207210785068469472465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4317609614380091292629953 3238207210785068469472465)
                      ·
                        rfl

theorem cell23_6306386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 4, 2, 2, 2].length) (baseStart_6306386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6306386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6306386 prefixEnd_6306386 := by exact prefixLift 6306386
  have htrace : WordTrace (prefixWord ++ tailWord_6306386) baseStart_6306386 baseEnd_6306386 := by
    simpa [prefixWord, tailWord_6306386, baseEnd_6306386] using wordTrace_append hprefix tailTrace_6306386
  have hstable : (prefixWord ++ tailWord_6306386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6306386).length < 2 ^ (prefixWord ++ tailWord_6306386).sum := by decide
  have hdescent : baseEnd_6306386 < baseStart_6306386 := by decide
  rcases family_descends (prefixWord ++ tailWord_6306386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6306392 : List Nat := [2, 1, 2, 2, 1, 2, 2, 6, 5]
def baseStart_6306392 : Nat := 118140960795 + 6306392 * 2 ^ 59
def prefixEnd_6306392 : Nat := 4983230072969 + 3 ^ 40 * 6306392 * 2
def baseEnd_6306392 : Nat := 359801143518777271777493

theorem tailTrace_6306392 : CollatzResearch.WordTrace tailWord_6306392 prefixEnd_6306392 359801143518777271777493 := by
  unfold tailWord_6306392
  simp only [CollatzResearch.WordTrace]
  refine ⟨115006506284513152425348715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153342008379350869900464953 115006506284513152425348715)
  ·
    refine ⟨172509759426769728638023073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115006506284513152425348715 172509759426769728638023073)
    ·
      refine ⟨129382319570077296478517305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 172509759426769728638023073 129382319570077296478517305)
      ·
        refine ⟨97036739677557972358887979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129382319570077296478517305 97036739677557972358887979)
        ·
          refine ⟨145555109516336958538331969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97036739677557972358887979 145555109516336958538331969)
          ·
            refine ⟨109166332137252718903748977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 145555109516336958538331969 109166332137252718903748977)
            ·
              refine ⟨81874749102939539177811733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 109166332137252718903748977 81874749102939539177811733)
              ·
                refine ⟨3837878864200290898959925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 81874749102939539177811733 3837878864200290898959925)
                ·
                  refine ⟨359801143518777271777493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3837878864200290898959925 359801143518777271777493)
                  ·
                    rfl

theorem cell23_6306392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 6, 5].length) (baseStart_6306392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6306392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6306392 prefixEnd_6306392 := by exact prefixLift 6306392
  have htrace : WordTrace (prefixWord ++ tailWord_6306392) baseStart_6306392 baseEnd_6306392 := by
    simpa [prefixWord, tailWord_6306392, baseEnd_6306392] using wordTrace_append hprefix tailTrace_6306392
  have hstable : (prefixWord ++ tailWord_6306392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6306392).length < 2 ^ (prefixWord ++ tailWord_6306392).sum := by decide
  have hdescent : baseEnd_6306392 < baseStart_6306392 := by decide
  rcases family_descends (prefixWord ++ tailWord_6306392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6306479 : List Nat := [1, 1, 2, 1, 2, 5, 3, 1, 2, 2, 3]
def baseStart_6306479 : Nat := 118140960795 + 6306479 * 2 ^ 59
def prefixEnd_6306479 : Nat := 4983230072969 + 3 ^ 40 * 6306479 * 2
def baseEnd_6306479 : Nat := 3238254964485936605609537

theorem tailTrace_6306479 : CollatzResearch.WordTrace tailWord_6306479 prefixEnd_6306479 3238254964485936605609537 := by
  unfold tailWord_6306479
  simp only [CollatzResearch.WordTrace]
  refine ⟨230016185719711118709114491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153344123813140745806076327 230016185719711118709114491)
  ·
    refine ⟨345024278579566678063671737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230016185719711118709114491 345024278579566678063671737)
    ·
      refine ⟨258768208934675008547753803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 345024278579566678063671737 258768208934675008547753803)
      ·
        refine ⟨388152313402012512821630705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 258768208934675008547753803 388152313402012512821630705)
        ·
          refine ⟨291114235051509384616223029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 388152313402012512821630705 291114235051509384616223029)
          ·
            refine ⟨27291959536079004807770909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 291114235051509384616223029 27291959536079004807770909)
            ·
              refine ⟨10234484826029626802914091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27291959536079004807770909 10234484826029626802914091)
              ·
                refine ⟨15351727239044440204371137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10234484826029626802914091 15351727239044440204371137)
                ·
                  refine ⟨11513795429283330153278353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15351727239044440204371137 11513795429283330153278353)
                  ·
                    refine ⟨8635346571962497614958765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11513795429283330153278353 8635346571962497614958765)
                    ·
                      refine ⟨3238254964485936605609537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8635346571962497614958765 3238254964485936605609537)
                      ·
                        rfl

theorem cell23_6306479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 3, 1, 2, 2, 3].length) (baseStart_6306479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6306479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6306479 prefixEnd_6306479 := by exact prefixLift 6306479
  have htrace : WordTrace (prefixWord ++ tailWord_6306479) baseStart_6306479 baseEnd_6306479 := by
    simpa [prefixWord, tailWord_6306479, baseEnd_6306479] using wordTrace_append hprefix tailTrace_6306479
  have hstable : (prefixWord ++ tailWord_6306479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6306479).length < 2 ^ (prefixWord ++ tailWord_6306479).sum := by decide
  have hdescent : baseEnd_6306479 < baseStart_6306479 := by decide
  rcases family_descends (prefixWord ++ tailWord_6306479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6306519 : List Nat := [1, 1, 3, 2, 1, 4, 1, 2, 1, 5, 2]
def baseStart_6306519 : Nat := 118140960795 + 6306519 * 2 ^ 59
def prefixEnd_6306519 : Nat := 4983230072969 + 3 ^ 40 * 6306519 * 2
def baseEnd_6306519 : Nat := 3238275503712116449109353

theorem tailTrace_6306519 : CollatzResearch.WordTrace tailWord_6306519 prefixEnd_6306519 3238275503712116449109353 := by
  unfold tailWord_6306519
  simp only [CollatzResearch.WordTrace]
  refine ⟨230017644639566205540570611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153345096426377470360380407 230017644639566205540570611)
  ·
    refine ⟨345026466959349308310855917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230017644639566205540570611 345026466959349308310855917)
    ·
      refine ⟨129384925109755990616570969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 345026466959349308310855917 129384925109755990616570969)
      ·
        refine ⟨97038693832316992962428227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129384925109755990616570969 97038693832316992962428227)
        ·
          refine ⟨145558040748475489443642341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97038693832316992962428227 145558040748475489443642341)
          ·
            refine ⟨27292132640339154270682939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 145558040748475489443642341 27292132640339154270682939)
            ·
              refine ⟨40938198960508731406024409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27292132640339154270682939 40938198960508731406024409)
              ·
                refine ⟨30703649220381548554518307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40938198960508731406024409 30703649220381548554518307)
                ·
                  refine ⟨46055473830572322831777461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30703649220381548554518307 46055473830572322831777461)
                  ·
                    refine ⟨4317700671616155265479137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 46055473830572322831777461 4317700671616155265479137)
                    ·
                      refine ⟨3238275503712116449109353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4317700671616155265479137 3238275503712116449109353)
                      ·
                        rfl

theorem cell23_6306519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 2, 1, 5, 2].length) (baseStart_6306519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6306519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6306519 prefixEnd_6306519 := by exact prefixLift 6306519
  have htrace : WordTrace (prefixWord ++ tailWord_6306519) baseStart_6306519 baseEnd_6306519 := by
    simpa [prefixWord, tailWord_6306519, baseEnd_6306519] using wordTrace_append hprefix tailTrace_6306519
  have hstable : (prefixWord ++ tailWord_6306519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6306519).length < 2 ^ (prefixWord ++ tailWord_6306519).sum := by decide
  have hdescent : baseEnd_6306519 < baseStart_6306519 := by decide
  rcases family_descends (prefixWord ++ tailWord_6306519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6306529 : List Nat := [1, 2, 3, 1, 4, 1, 1, 4, 1, 5]
def baseStart_6306529 : Nat := 118140960795 + 6306529 * 2 ^ 59
def prefixEnd_6306529 : Nat := 4983230072969 + 3 ^ 40 * 6306529 * 2
def baseEnd_6306529 : Nat := 1079426879506220469994769

theorem tailTrace_6306529 : CollatzResearch.WordTrace tailWord_6306529 prefixEnd_6306529 1079426879506220469994769 := by
  unfold tailWord_6306529
  simp only [CollatzResearch.WordTrace]
  refine ⟨230018009369529977248434641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153345339579686651498956427 230018009369529977248434641)
  ·
    refine ⟨172513507027147482936325981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 230018009369529977248434641 172513507027147482936325981)
    ·
      refine ⟨64692565135180306101122243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 172513507027147482936325981 64692565135180306101122243)
      ·
        refine ⟨97038847702770459151683365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64692565135180306101122243 97038847702770459151683365)
        ·
          refine ⟨18194783944269461090940631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 97038847702770459151683365 18194783944269461090940631)
          ·
            refine ⟨27292175916404191636410947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18194783944269461090940631 27292175916404191636410947)
            ·
              refine ⟨40938263874606287454616421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27292175916404191636410947 40938263874606287454616421)
              ·
                refine ⟨7675924476488678897740579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40938263874606287454616421 7675924476488678897740579)
                ·
                  refine ⟨11513886714733018346610869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7675924476488678897740579 11513886714733018346610869)
                  ·
                    refine ⟨1079426879506220469994769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11513886714733018346610869 1079426879506220469994769)
                    ·
                      rfl

theorem cell23_6306529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 4, 1, 5].length) (baseStart_6306529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6306529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6306529 prefixEnd_6306529 := by exact prefixLift 6306529
  have htrace : WordTrace (prefixWord ++ tailWord_6306529) baseStart_6306529 baseEnd_6306529 := by
    simpa [prefixWord, tailWord_6306529, baseEnd_6306529] using wordTrace_append hprefix tailTrace_6306529
  have hstable : (prefixWord ++ tailWord_6306529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6306529).length < 2 ^ (prefixWord ++ tailWord_6306529).sum := by decide
  have hdescent : baseEnd_6306529 < baseStart_6306529 := by decide
  rcases family_descends (prefixWord ++ tailWord_6306529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6306543 : List Nat := [1, 1, 2, 1, 5, 2, 3, 3, 1, 1, 3]
def baseStart_6306543 : Nat := 118140960795 + 6306543 * 2 ^ 59
def prefixEnd_6306543 : Nat := 4983230072969 + 3 ^ 40 * 6306543 * 2
def baseEnd_6306543 : Nat := 3238287827247824355209243

theorem tailTrace_6306543 : CollatzResearch.WordTrace tailWord_6306543 prefixEnd_6306543 3238287827247824355209243 := by
  unfold tailWord_6306543
  simp only [CollatzResearch.WordTrace]
  refine ⟨230018519991479257639444283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153345679994319505092962855 230018519991479257639444283)
  ·
    refine ⟨345027779987218886459166425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230018519991479257639444283 345027779987218886459166425)
    ·
      refine ⟨258770834990414164844374819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 345027779987218886459166425 258770834990414164844374819)
      ·
        refine ⟨388156252485621247266562229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 258770834990414164844374819 388156252485621247266562229)
        ·
          refine ⟨36389648670526991931240209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 388156252485621247266562229 36389648670526991931240209)
          ·
            refine ⟨27292236502895243948430157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36389648670526991931240209 27292236502895243948430157)
            ·
              refine ⟨10234588688585716480661309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27292236502895243948430157 10234588688585716480661309)
              ·
                refine ⟨3837970758219643680247991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10234588688585716480661309 3837970758219643680247991)
                ·
                  refine ⟨5756956137329465520371987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3837970758219643680247991 5756956137329465520371987)
                  ·
                    refine ⟨8635434205994198280557981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5756956137329465520371987 8635434205994198280557981)
                    ·
                      refine ⟨3238287827247824355209243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8635434205994198280557981 3238287827247824355209243)
                      ·
                        rfl

theorem cell23_6306543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 3, 3, 1, 1, 3].length) (baseStart_6306543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6306543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6306543 prefixEnd_6306543 := by exact prefixLift 6306543
  have htrace : WordTrace (prefixWord ++ tailWord_6306543) baseStart_6306543 baseEnd_6306543 := by
    simpa [prefixWord, tailWord_6306543, baseEnd_6306543] using wordTrace_append hprefix tailTrace_6306543
  have hstable : (prefixWord ++ tailWord_6306543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6306543).length < 2 ^ (prefixWord ++ tailWord_6306543).sum := by decide
  have hdescent : baseEnd_6306543 < baseStart_6306543 := by decide
  rcases family_descends (prefixWord ++ tailWord_6306543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6306559 : List Nat := [1, 1, 2, 2, 1, 3, 1, 6, 2, 4]
def baseStart_6306559 : Nat := 118140960795 + 6306559 * 2 ^ 59
def prefixEnd_6306559 : Nat := 4983230072969 + 3 ^ 40 * 6306559 * 2
def baseEnd_6306559 : Nat := 1079432014312765430869723

theorem tailTrace_6306559 : CollatzResearch.WordTrace tailWord_6306559 prefixEnd_6306559 1079432014312765430869723 := by
  unfold tailWord_6306559
  simp only [CollatzResearch.WordTrace]
  refine ⟨230019103559421292372026731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153346069039614194914684487 230019103559421292372026731)
  ·
    refine ⟨345028655339131938558040097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230019103559421292372026731 345028655339131938558040097)
    ·
      refine ⟨258771491504348953918530073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 345028655339131938558040097 258771491504348953918530073)
      ·
        refine ⟨194078618628261715438897555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 258771491504348953918530073 194078618628261715438897555)
        ·
          refine ⟨291117927942392573158346333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 194078618628261715438897555 291117927942392573158346333)
          ·
            refine ⟨109169222978397214934379875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 291117927942392573158346333 109169222978397214934379875)
            ·
              refine ⟨163753834467595822401569813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109169222978397214934379875 163753834467595822401569813)
              ·
                refine ⟨7675960990668554175073585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 163753834467595822401569813 7675960990668554175073585)
                ·
                  refine ⟨5756970743001415631305189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7675960990668554175073585 5756970743001415631305189)
                  ·
                    refine ⟨1079432014312765430869723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5756970743001415631305189 1079432014312765430869723)
                    ·
                      rfl

theorem cell23_6306559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 6, 2, 4].length) (baseStart_6306559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6306559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6306559 prefixEnd_6306559 := by exact prefixLift 6306559
  have htrace : WordTrace (prefixWord ++ tailWord_6306559) baseStart_6306559 baseEnd_6306559 := by
    simpa [prefixWord, tailWord_6306559, baseEnd_6306559] using wordTrace_append hprefix tailTrace_6306559
  have hstable : (prefixWord ++ tailWord_6306559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6306559).length < 2 ^ (prefixWord ++ tailWord_6306559).sum := by decide
  have hdescent : baseEnd_6306559 < baseStart_6306559 := by decide
  rcases family_descends (prefixWord ++ tailWord_6306559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6306583 : List Nat := [1, 1, 3, 4, 3, 2, 1, 2, 1, 1, 4]
def baseStart_6306583 : Nat := 118140960795 + 6306583 * 2 ^ 59
def prefixEnd_6306583 : Nat := 4983230072969 + 3 ^ 40 * 6306583 * 2
def baseEnd_6306583 : Nat := 3238308366474004198709059

theorem tailTrace_6306583 : CollatzResearch.WordTrace tailWord_6306583 prefixEnd_6306583 3238308366474004198709059 := by
  unfold tailWord_6306583
  simp only [CollatzResearch.WordTrace]
  refine ⟨230019978911334344470900403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153346652607556229647266935 230019978911334344470900403)
  ·
    refine ⟨345029968367001516706350605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230019978911334344470900403 345029968367001516706350605)
    ·
      refine ⟨129386238137625568764881477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 345029968367001516706350605 129386238137625568764881477)
      ·
        refine ⟨24259919650804794143415277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 129386238137625568764881477 24259919650804794143415277)
        ·
          refine ⟨9097469869051797803780729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24259919650804794143415277 9097469869051797803780729)
          ·
            refine ⟨6823102401788848352835547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9097469869051797803780729 6823102401788848352835547)
            ·
              refine ⟨10234653602683272529253321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6823102401788848352835547 10234653602683272529253321)
              ·
                refine ⟨7675990202012454396939991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10234653602683272529253321 7675990202012454396939991)
                ·
                  refine ⟨11513985303018681595409987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7675990202012454396939991 11513985303018681595409987)
                  ·
                    refine ⟨17270977954528022393114981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11513985303018681595409987 17270977954528022393114981)
                    ·
                      refine ⟨3238308366474004198709059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17270977954528022393114981 3238308366474004198709059)
                      ·
                        rfl

theorem cell23_6306583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 2, 1, 2, 1, 1, 4].length) (baseStart_6306583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6306583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6306583 prefixEnd_6306583 := by exact prefixLift 6306583
  have htrace : WordTrace (prefixWord ++ tailWord_6306583) baseStart_6306583 baseEnd_6306583 := by
    simpa [prefixWord, tailWord_6306583, baseEnd_6306583] using wordTrace_append hprefix tailTrace_6306583
  have hstable : (prefixWord ++ tailWord_6306583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6306583).length < 2 ^ (prefixWord ++ tailWord_6306583).sum := by decide
  have hdescent : baseEnd_6306583 < baseStart_6306583 := by decide
  rcases family_descends (prefixWord ++ tailWord_6306583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6306596 : List Nat := [2, 3, 1, 3, 3, 1, 1, 2, 1, 2, 4]
def baseStart_6306596 : Nat := 118140960795 + 6306596 * 2 ^ 59
def prefixEnd_6306596 : Nat := 4983230072969 + 3 ^ 40 * 6306596 * 2
def baseEnd_6306596 : Nat := 3238315041722512647846499

theorem tailTrace_6306596 : CollatzResearch.WordTrace tailWord_6306596 prefixEnd_6306596 3238315041722512647846499 := by
  unfold tailWord_6306596
  simp only [CollatzResearch.WordTrace]
  refine ⟨115010226530143623845561821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153346968706858165127415761 115010226530143623845561821)
  ·
    refine ⟨43128834948803858942085683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115010226530143623845561821 43128834948803858942085683)
    ·
      refine ⟨64693252423205788413128525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43128834948803858942085683 64693252423205788413128525)
      ·
        refine ⟨24259969658702170654923197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64693252423205788413128525 24259969658702170654923197)
        ·
          refine ⟨9097488622013313995596199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24259969658702170654923197 9097488622013313995596199)
          ·
            refine ⟨13646232933019970993394299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9097488622013313995596199 13646232933019970993394299)
            ·
              refine ⟨20469349399529956490091449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13646232933019970993394299 20469349399529956490091449)
              ·
                refine ⟨15352012049647467367568587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20469349399529956490091449 15352012049647467367568587)
                ·
                  refine ⟨23028018074471201051352881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15352012049647467367568587 23028018074471201051352881)
                  ·
                    refine ⟨17271013555853400788514661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23028018074471201051352881 17271013555853400788514661)
                    ·
                      refine ⟨3238315041722512647846499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17271013555853400788514661 3238315041722512647846499)
                      ·
                        rfl

theorem cell23_6306596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 1, 2, 1, 2, 4].length) (baseStart_6306596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6306596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6306596 prefixEnd_6306596 := by exact prefixLift 6306596
  have htrace : WordTrace (prefixWord ++ tailWord_6306596) baseStart_6306596 baseEnd_6306596 := by
    simpa [prefixWord, tailWord_6306596, baseEnd_6306596] using wordTrace_append hprefix tailTrace_6306596
  have hstable : (prefixWord ++ tailWord_6306596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6306596).length < 2 ^ (prefixWord ++ tailWord_6306596).sum := by decide
  have hdescent : baseEnd_6306596 < baseStart_6306596 := by decide
  rcases family_descends (prefixWord ++ tailWord_6306596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6306600 : List Nat := [2, 1, 5, 1, 1, 1, 2, 5, 1, 2, 2]
def baseStart_6306600 : Nat := 118140960795 + 6306600 * 2 ^ 59
def prefixEnd_6306600 : Nat := 4983230072969 + 3 ^ 40 * 6306600 * 2
def baseEnd_6306600 : Nat := 3238317095645130632196481

theorem tailTrace_6306600 : CollatzResearch.WordTrace tailWord_6306600 prefixEnd_6306600 3238317095645130632196481 := by
  unfold tailWord_6306600
  simp only [CollatzResearch.WordTrace]
  refine ⟨115010299476136378187134627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153347065968181837582846169 115010299476136378187134627)
  ·
    refine ⟨172515449214204567280701941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115010299476136378187134627 172515449214204567280701941)
    ·
      refine ⟨16173323363831678182565807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 172515449214204567280701941 16173323363831678182565807)
      ·
        refine ⟨24259985045747517273848711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16173323363831678182565807 24259985045747517273848711)
        ·
          refine ⟨36389977568621275910773067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24259985045747517273848711 36389977568621275910773067)
          ·
            refine ⟨54584966352931913866159601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36389977568621275910773067 54584966352931913866159601)
            ·
              refine ⟨40938724764698935399619701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54584966352931913866159601 40938724764698935399619701)
              ·
                refine ⟨3838005446690525193714347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 40938724764698935399619701 3838005446690525193714347)
                ·
                  refine ⟨5757008170035787790571521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3838005446690525193714347 5757008170035787790571521)
                  ·
                    refine ⟨4317756127526840842928641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5757008170035787790571521 4317756127526840842928641)
                    ·
                      refine ⟨3238317095645130632196481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4317756127526840842928641 3238317095645130632196481)
                      ·
                        rfl

theorem cell23_6306600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 5, 1, 2, 2].length) (baseStart_6306600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6306600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6306600 prefixEnd_6306600 := by exact prefixLift 6306600
  have htrace : WordTrace (prefixWord ++ tailWord_6306600) baseStart_6306600 baseEnd_6306600 := by
    simpa [prefixWord, tailWord_6306600, baseEnd_6306600] using wordTrace_append hprefix tailTrace_6306600
  have hstable : (prefixWord ++ tailWord_6306600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6306600).length < 2 ^ (prefixWord ++ tailWord_6306600).sum := by decide
  have hdescent : baseEnd_6306600 < baseStart_6306600 := by decide
  rcases family_descends (prefixWord ++ tailWord_6306600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6306630 : List Nat := [6, 1, 1, 2, 2, 1, 2, 1, 1, 2, 4]
def baseStart_6306630 : Nat := 118140960795 + 6306630 * 2 ^ 59
def prefixEnd_6306630 : Nat := 4983230072969 + 3 ^ 40 * 6306630 * 2
def baseEnd_6306630 : Nat := 3238332500064765514821343

theorem tailTrace_6306630 : CollatzResearch.WordTrace tailWord_6306630 prefixEnd_6306630 3238332500064765514821343 := by
  unfold tailWord_6306630
  simp only [CollatzResearch.WordTrace]
  refine ⟨7188177910692627234308167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 153347795428109380998574229 7188177910692627234308167)
  ·
    refine ⟨10782266866038940851462251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7188177910692627234308167 10782266866038940851462251)
    ·
      refine ⟨16173400299058411277193377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10782266866038940851462251 16173400299058411277193377)
      ·
        refine ⟨12130050224293808457895033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16173400299058411277193377 12130050224293808457895033)
        ·
          refine ⟨9097537668220356343421275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12130050224293808457895033 9097537668220356343421275)
          ·
            refine ⟨13646306502330534515131913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9097537668220356343421275 13646306502330534515131913)
            ·
              refine ⟨10234729876747900886348935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13646306502330534515131913 10234729876747900886348935)
              ·
                refine ⟨15352094815121851329523403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10234729876747900886348935 15352094815121851329523403)
                ·
                  refine ⟨23028142222682776994285105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15352094815121851329523403 23028142222682776994285105)
                  ·
                    refine ⟨17271106667012082745713829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23028142222682776994285105 17271106667012082745713829)
                    ·
                      refine ⟨3238332500064765514821343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17271106667012082745713829 3238332500064765514821343)
                      ·
                        rfl

theorem cell23_6306630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 2, 1, 1, 2, 4].length) (baseStart_6306630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6306630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6306630 prefixEnd_6306630 := by exact prefixLift 6306630
  have htrace : WordTrace (prefixWord ++ tailWord_6306630) baseStart_6306630 baseEnd_6306630 := by
    simpa [prefixWord, tailWord_6306630, baseEnd_6306630] using wordTrace_append hprefix tailTrace_6306630
  have hstable : (prefixWord ++ tailWord_6306630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6306630).length < 2 ^ (prefixWord ++ tailWord_6306630).sum := by decide
  have hdescent : baseEnd_6306630 < baseStart_6306630 := by decide
  rcases family_descends (prefixWord ++ tailWord_6306630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6306656 : List Nat := [2, 1, 1, 3, 3, 1, 1, 4, 1, 4, 2]
def baseStart_6306656 : Nat := 118140960795 + 6306656 * 2 ^ 59
def prefixEnd_6306656 : Nat := 4983230072969 + 3 ^ 40 * 6306656 * 2
def baseEnd_6306656 : Nat := 3238345850561782413096223

theorem tailTrace_6306656 : CollatzResearch.WordTrace tailWord_6306656 prefixEnd_6306656 3238345850561782413096223 := by
  unfold tailWord_6306656
  simp only [CollatzResearch.WordTrace]
  refine ⟨115011320720034938969153911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153348427626713251958871881 115011320720034938969153911)
  ·
    refine ⟨172516981080052408453730867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115011320720034938969153911 172516981080052408453730867)
    ·
      refine ⟨258775471620078612680596301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172516981080052408453730867 258775471620078612680596301)
      ·
        refine ⟨97040801857529479755223613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 258775471620078612680596301 97040801857529479755223613)
        ·
          refine ⟨36390300696573554908208855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 97040801857529479755223613 36390300696573554908208855)
          ·
            refine ⟨54585451044860332362313283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36390300696573554908208855 54585451044860332362313283)
            ·
              refine ⟨81878176567290498543469925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54585451044860332362313283 81878176567290498543469925)
              ·
                refine ⟨15352158106366968476900611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 81878176567290498543469925 15352158106366968476900611)
                ·
                  refine ⟨23028237159550452715350917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15352158106366968476900611 23028237159550452715350917)
                  ·
                    refine ⟨4317794467415709884128297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23028237159550452715350917 4317794467415709884128297)
                    ·
                      refine ⟨3238345850561782413096223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4317794467415709884128297 3238345850561782413096223)
                      ·
                        rfl

theorem cell23_6306656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 4, 1, 4, 2].length) (baseStart_6306656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6306656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6306656 prefixEnd_6306656 := by exact prefixLift 6306656
  have htrace : WordTrace (prefixWord ++ tailWord_6306656) baseStart_6306656 baseEnd_6306656 := by
    simpa [prefixWord, tailWord_6306656, baseEnd_6306656] using wordTrace_append hprefix tailTrace_6306656
  have hstable : (prefixWord ++ tailWord_6306656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6306656).length < 2 ^ (prefixWord ++ tailWord_6306656).sum := by decide
  have hdescent : baseEnd_6306656 < baseStart_6306656 := by decide
  rcases family_descends (prefixWord ++ tailWord_6306656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6306660 : List Nat := [2, 3, 1, 1, 4, 1, 4, 1, 1, 3, 2]
def baseStart_6306660 : Nat := 118140960795 + 6306660 * 2 ^ 59
def prefixEnd_6306660 : Nat := 4983230072969 + 3 ^ 40 * 6306660 * 2
def baseEnd_6306660 : Nat := 3238347904484400397446205

theorem tailTrace_6306660 : CollatzResearch.WordTrace tailWord_6306660 prefixEnd_6306660 3238347904484400397446205 := by
  unfold tailWord_6306660
  simp only [CollatzResearch.WordTrace]
  refine ⟨115011393666027693310726717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153348524888036924414302289 115011393666027693310726717)
  ·
    refine ⟨43129272624760384991522519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115011393666027693310726717 43129272624760384991522519)
    ·
      refine ⟨64693908937140577487283779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43129272624760384991522519 64693908937140577487283779)
      ·
        refine ⟨97040863405710866230925669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64693908937140577487283779 97040863405710866230925669)
        ·
          refine ⟨18195161888570787418298563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 97040863405710866230925669 18195161888570787418298563)
          ·
            refine ⟨27292742832856181127447845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18195161888570787418298563 27292742832856181127447845)
            ·
              refine ⟨5117389281160533961396471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27292742832856181127447845 5117389281160533961396471)
              ·
                refine ⟨7676083921740800942094707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5117389281160533961396471 7676083921740800942094707)
                ·
                  refine ⟨11514125882611201413142061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7676083921740800942094707 11514125882611201413142061)
                  ·
                    refine ⟨4317797205979200529928273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11514125882611201413142061 4317797205979200529928273)
                    ·
                      refine ⟨3238347904484400397446205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4317797205979200529928273 3238347904484400397446205)
                      ·
                        rfl

theorem cell23_6306660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 4, 1, 1, 3, 2].length) (baseStart_6306660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6306660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6306660 prefixEnd_6306660 := by exact prefixLift 6306660
  have htrace : WordTrace (prefixWord ++ tailWord_6306660) baseStart_6306660 baseEnd_6306660 := by
    simpa [prefixWord, tailWord_6306660, baseEnd_6306660] using wordTrace_append hprefix tailTrace_6306660
  have hstable : (prefixWord ++ tailWord_6306660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6306660).length < 2 ^ (prefixWord ++ tailWord_6306660).sum := by decide
  have hdescent : baseEnd_6306660 < baseStart_6306660 := by decide
  rcases family_descends (prefixWord ++ tailWord_6306660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6306673 : List Nat := [1, 2, 2, 2, 1, 5, 1, 1, 4, 2, 2]
def baseStart_6306673 : Nat := 118140960795 + 6306673 * 2 ^ 59
def prefixEnd_6306673 : Nat := 4983230072969 + 3 ^ 40 * 6306673 * 2
def baseEnd_6306673 : Nat := 3238354579732908846583645

theorem tailTrace_6306673 : CollatzResearch.WordTrace tailWord_6306673 prefixEnd_6306673 3238354579732908846583645 := by
  unfold tailWord_6306673
  simp only [CollatzResearch.WordTrace]
  refine ⟨230023261481008289841676673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153348840987338859894451115 230023261481008289841676673)
  ·
    refine ⟨172517446110756217381257505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 230023261481008289841676673 172517446110756217381257505)
    ·
      refine ⟨129388084583067163035943129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 172517446110756217381257505 129388084583067163035943129)
      ·
        refine ⟨97041063437300372276957347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129388084583067163035943129 97041063437300372276957347)
        ·
          refine ⟨145561595155950558415436021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97041063437300372276957347 145561595155950558415436021)
          ·
            refine ⟨13646399545870364851447127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 145561595155950558415436021 13646399545870364851447127)
            ·
              refine ⟨20469599318805547277170691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13646399545870364851447127 20469599318805547277170691)
              ·
                refine ⟨30704398978208320915756037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20469599318805547277170691 30704398978208320915756037)
                ·
                  refine ⟨5757074808414060171704257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30704398978208320915756037 5757074808414060171704257)
                  ·
                    refine ⟨4317806106310545128778193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5757074808414060171704257 4317806106310545128778193)
                    ·
                      refine ⟨3238354579732908846583645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4317806106310545128778193 3238354579732908846583645)
                      ·
                        rfl

theorem cell23_6306673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 1, 1, 4, 2, 2].length) (baseStart_6306673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6306673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6306673 prefixEnd_6306673 := by exact prefixLift 6306673
  have htrace : WordTrace (prefixWord ++ tailWord_6306673) baseStart_6306673 baseEnd_6306673 := by
    simpa [prefixWord, tailWord_6306673, baseEnd_6306673] using wordTrace_append hprefix tailTrace_6306673
  have hstable : (prefixWord ++ tailWord_6306673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6306673).length < 2 ^ (prefixWord ++ tailWord_6306673).sum := by decide
  have hdescent : baseEnd_6306673 < baseStart_6306673 := by decide
  rcases family_descends (prefixWord ++ tailWord_6306673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6306709 : List Nat := [1, 3, 2, 1, 1, 4, 2, 1, 1, 7]
def baseStart_6306709 : Nat := 118140960795 + 6306709 * 2 ^ 59
def prefixEnd_6306709 : Nat := 4983230072969 + 3 ^ 40 * 6306709 * 2
def baseEnd_6306709 : Nat := 1079457688345490235244493

theorem tailTrace_6306709 : CollatzResearch.WordTrace tailWord_6306709 prefixEnd_6306709 1079457688345490235244493 := by
  unfold tailWord_6306709
  simp only [CollatzResearch.WordTrace]
  refine ⟨230024574508877867989987181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153349716339251911993324787 230024574508877867989987181)
  ·
    refine ⟨86259215440829200496245193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 230024574508877867989987181 86259215440829200496245193)
    ·
      refine ⟨64694411580621900372183895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86259215440829200496245193 64694411580621900372183895)
      ·
        refine ⟨97041617370932850558275843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64694411580621900372183895 97041617370932850558275843)
        ·
          refine ⟨145562426056399275837413765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97041617370932850558275843 145562426056399275837413765)
          ·
            refine ⟨27292954885574864219515081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 145562426056399275837413765 27292954885574864219515081)
            ·
              refine ⟨20469716164181148164636311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27292954885574864219515081 20469716164181148164636311)
              ·
                refine ⟨30704574246271722246954467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20469716164181148164636311 30704574246271722246954467)
                ·
                  refine ⟨46056861369407583370431701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30704574246271722246954467 46056861369407583370431701)
                  ·
                    refine ⟨1079457688345490235244493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 46056861369407583370431701 1079457688345490235244493)
                    ·
                      rfl

theorem cell23_6306709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 2, 1, 1, 7].length) (baseStart_6306709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6306709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6306709 prefixEnd_6306709 := by exact prefixLift 6306709
  have htrace : WordTrace (prefixWord ++ tailWord_6306709) baseStart_6306709 baseEnd_6306709 := by
    simpa [prefixWord, tailWord_6306709, baseEnd_6306709] using wordTrace_append hprefix tailTrace_6306709
  have hstable : (prefixWord ++ tailWord_6306709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6306709).length < 2 ^ (prefixWord ++ tailWord_6306709).sum := by decide
  have hdescent : baseEnd_6306709 < baseStart_6306709 := by decide
  rcases family_descends (prefixWord ++ tailWord_6306709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6306710 : List Nat := [5, 3, 1, 1, 1, 2, 1, 1, 2, 1, 5]
def baseStart_6306710 : Nat := 118140960795 + 6306710 * 2 ^ 59
def prefixEnd_6306710 : Nat := 4983230072969 + 3 ^ 40 * 6306710 * 2
def baseEnd_6306710 : Nat := 3238373578517125201820975

theorem tailTrace_6306710 : CollatzResearch.WordTrace tailWord_6306710 prefixEnd_6306710 3238373578517125201820975 := by
  unfold tailWord_6306710
  simp only [CollatzResearch.WordTrace]
  refine ⟨14376538186367140322548349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 153349740654582830107182389 14376538186367140322548349)
  ·
    refine ⟨5391201819887677620955631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14376538186367140322548349 5391201819887677620955631)
    ·
      refine ⟨8086802729831516431433447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5391201819887677620955631 8086802729831516431433447)
      ·
        refine ⟨12130204094747274647150171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8086802729831516431433447 12130204094747274647150171)
        ·
          refine ⟨18195306142120911970725257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12130204094747274647150171 18195306142120911970725257)
          ·
            refine ⟨13646479606590683978043943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18195306142120911970725257 13646479606590683978043943)
            ·
              refine ⟨20469719409886025967065915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13646479606590683978043943 20469719409886025967065915)
              ·
                refine ⟨30704579114829038950598873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20469719409886025967065915 30704579114829038950598873)
                ·
                  refine ⟨23028434336121779212949155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30704579114829038950598873 23028434336121779212949155)
                  ·
                    refine ⟨34542651504182668819423733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23028434336121779212949155 34542651504182668819423733)
                    ·
                      refine ⟨3238373578517125201820975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34542651504182668819423733 3238373578517125201820975)
                      ·
                        rfl

theorem cell23_6306710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 1, 1, 2, 1, 5].length) (baseStart_6306710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6306710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6306710 prefixEnd_6306710 := by exact prefixLift 6306710
  have htrace : WordTrace (prefixWord ++ tailWord_6306710) baseStart_6306710 baseEnd_6306710 := by
    simpa [prefixWord, tailWord_6306710, baseEnd_6306710] using wordTrace_append hprefix tailTrace_6306710
  have hstable : (prefixWord ++ tailWord_6306710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6306710).length < 2 ^ (prefixWord ++ tailWord_6306710).sum := by decide
  have hdescent : baseEnd_6306710 < baseStart_6306710 := by decide
  rcases family_descends (prefixWord ++ tailWord_6306710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6306746 : List Nat := [3, 1, 1, 1, 2, 1, 4, 1, 1, 6, 2]
def baseStart_6306746 : Nat := 118140960795 + 6306746 * 2 ^ 59
def prefixEnd_6306746 : Nat := 4983230072969 + 3 ^ 40 * 6306746 * 2
def baseEnd_6306746 : Nat := 3238392063820687060970809

theorem tailTrace_6306746 : CollatzResearch.WordTrace tailWord_6306746 prefixEnd_6306746 3238392063820687060970809 := by
  unfold tailWord_6306746
  simp only [CollatzResearch.WordTrace]
  refine ⟨57506481002435955827271023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153350616006495882206056061 57506481002435955827271023)
  ·
    refine ⟨86259721503653933740906535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57506481002435955827271023 86259721503653933740906535)
    ·
      refine ⟨129389582255480900611359803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86259721503653933740906535 129389582255480900611359803)
      ·
        refine ⟨194084373383221350917039705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129389582255480900611359803 194084373383221350917039705)
        ·
          refine ⟨145563280037416013187779779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 194084373383221350917039705 145563280037416013187779779)
          ·
            refine ⟨218344920056124019781669669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 145563280037416013187779779 218344920056124019781669669)
            ·
              refine ⟨40939672510523253709063063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 218344920056124019781669669 40939672510523253709063063)
              ·
                refine ⟨61409508765784880563594595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40939672510523253709063063 61409508765784880563594595)
                ·
                  refine ⟨92114263148677320845391893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61409508765784880563594595 92114263148677320845391893)
                  ·
                    refine ⟨4317856085094249414627745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 92114263148677320845391893 4317856085094249414627745)
                    ·
                      refine ⟨3238392063820687060970809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4317856085094249414627745 3238392063820687060970809)
                      ·
                        rfl

theorem cell23_6306746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 1, 1, 6, 2].length) (baseStart_6306746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6306746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6306746 prefixEnd_6306746 := by exact prefixLift 6306746
  have htrace : WordTrace (prefixWord ++ tailWord_6306746) baseStart_6306746 baseEnd_6306746 := by
    simpa [prefixWord, tailWord_6306746, baseEnd_6306746] using wordTrace_append hprefix tailTrace_6306746
  have hstable : (prefixWord ++ tailWord_6306746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6306746).length < 2 ^ (prefixWord ++ tailWord_6306746).sum := by decide
  have hdescent : baseEnd_6306746 < baseStart_6306746 := by decide
  rcases family_descends (prefixWord ++ tailWord_6306746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6306759 : List Nat := [1, 1, 4, 1, 1, 2, 2, 1, 2, 4, 4]
def baseStart_6306759 : Nat := 118140960795 + 6306759 * 2 ^ 59
def prefixEnd_6306759 : Nat := 4983230072969 + 3 ^ 40 * 6306759 * 2
def baseEnd_6306759 : Nat := 3238398739069195510108249

theorem tailTrace_6306759 : CollatzResearch.WordTrace tailWord_6306759 prefixEnd_6306759 3238398739069195510108249 := by
  unfold tailWord_6306759
  simp only [CollatzResearch.WordTrace]
  refine ⟨230026398158696726529307331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153350932105797817686204887 230026398158696726529307331)
  ·
    refine ⟨345039597238045089793960997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230026398158696726529307331 345039597238045089793960997)
    ·
      refine ⟨64694924482133454336367687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 345039597238045089793960997 64694924482133454336367687)
      ·
        refine ⟨97042386723200181504551531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64694924482133454336367687 97042386723200181504551531)
        ·
          refine ⟨145563580084800272256827297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97042386723200181504551531 145563580084800272256827297)
          ·
            refine ⟨109172685063600204192620473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 145563580084800272256827297 109172685063600204192620473)
            ·
              refine ⟨81879513797700153144465355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 109172685063600204192620473 81879513797700153144465355)
              ·
                refine ⟨122819270696550229716698033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81879513797700153144465355 122819270696550229716698033)
                ·
                  refine ⟨92114453022412672287523525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 122819270696550229716698033 92114453022412672287523525)
                  ·
                    refine ⟨17271459941702376053910661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 92114453022412672287523525 17271459941702376053910661)
                    ·
                      refine ⟨3238398739069195510108249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17271459941702376053910661 3238398739069195510108249)
                      ·
                        rfl

theorem cell23_6306759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 1, 2, 4, 4].length) (baseStart_6306759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6306759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6306759 prefixEnd_6306759 := by exact prefixLift 6306759
  have htrace : WordTrace (prefixWord ++ tailWord_6306759) baseStart_6306759 baseEnd_6306759 := by
    simpa [prefixWord, tailWord_6306759, baseEnd_6306759] using wordTrace_append hprefix tailTrace_6306759
  have hstable : (prefixWord ++ tailWord_6306759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6306759).length < 2 ^ (prefixWord ++ tailWord_6306759).sum := by decide
  have hdescent : baseEnd_6306759 < baseStart_6306759 := by decide
  rcases family_descends (prefixWord ++ tailWord_6306759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6306809 : List Nat := [1, 2, 1, 3, 1, 3, 1, 1, 2, 1, 7]
def baseStart_6306809 : Nat := 118140960795 + 6306809 * 2 ^ 59
def prefixEnd_6306809 : Nat := 4983230072969 + 3 ^ 40 * 6306809 * 2
def baseEnd_6306809 : Nat := 3238424413101920314483019

theorem tailTrace_6306809 : CollatzResearch.WordTrace tailWord_6306809 prefixEnd_6306809 3238424413101920314483019 := by
  unfold tailWord_6306809
  simp only [CollatzResearch.WordTrace]
  refine ⟨230028221808515585068627481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153352147872343723379084987 230028221808515585068627481)
  ·
    refine ⟨172521166356386688801470611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 230028221808515585068627481 172521166356386688801470611)
    ·
      refine ⟨258781749534580033202205917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172521166356386688801470611 258781749534580033202205917)
      ·
        refine ⟨97043156075467512450827219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 258781749534580033202205917 97043156075467512450827219)
        ·
          refine ⟨145564734113201268676240829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97043156075467512450827219 145564734113201268676240829)
          ·
            refine ⟨54586775292450475753590311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 145564734113201268676240829 54586775292450475753590311)
            ·
              refine ⟨81880162938675713630385467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54586775292450475753590311 81880162938675713630385467)
              ·
                refine ⟨122820244408013570445578201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81880162938675713630385467 122820244408013570445578201)
                ·
                  refine ⟨92115183306010177834183651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 122820244408013570445578201 92115183306010177834183651)
                  ·
                    refine ⟨138172774959015266751275477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 92115183306010177834183651 138172774959015266751275477)
                    ·
                      refine ⟨3238424413101920314483019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 138172774959015266751275477 3238424413101920314483019)
                      ·
                        rfl

theorem cell23_6306809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 1, 2, 1, 7].length) (baseStart_6306809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6306809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6306809 prefixEnd_6306809 := by exact prefixLift 6306809
  have htrace : WordTrace (prefixWord ++ tailWord_6306809) baseStart_6306809 baseEnd_6306809 := by
    simpa [prefixWord, tailWord_6306809, baseEnd_6306809] using wordTrace_append hprefix tailTrace_6306809
  have hstable : (prefixWord ++ tailWord_6306809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6306809).length < 2 ^ (prefixWord ++ tailWord_6306809).sum := by decide
  have hdescent : baseEnd_6306809 < baseStart_6306809 := by decide
  rcases family_descends (prefixWord ++ tailWord_6306809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6306823 : List Nat := [1, 1, 4, 3, 1, 1, 3, 1, 1, 5, 2]
def baseStart_6306823 : Nat := 118140960795 + 6306823 * 2 ^ 59
def prefixEnd_6306823 : Nat := 4983230072969 + 3 ^ 40 * 6306823 * 2
def baseEnd_6306823 : Nat := 3238431601831083259707955

theorem tailTrace_6306823 : CollatzResearch.WordTrace tailWord_6306823 prefixEnd_6306823 3238431601831083259707955 := by
  unfold tailWord_6306823
  simp only [CollatzResearch.WordTrace]
  refine ⟨230028732430464865459637123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153352488286976576973091415 230028732430464865459637123)
  ·
    refine ⟨345043098645697298189455685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230028732430464865459637123 345043098645697298189455685)
    ·
      refine ⟨64695580996068243410522941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 345043098645697298189455685 64695580996068243410522941)
      ·
        refine ⟨24260842873525591278946103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64695580996068243410522941 24260842873525591278946103)
        ·
          refine ⟨36391264310288386918419155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24260842873525591278946103 36391264310288386918419155)
          ·
            refine ⟨54586896465432580377628733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36391264310288386918419155 54586896465432580377628733)
            ·
              refine ⟨20470086174537217641610775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54586896465432580377628733 20470086174537217641610775)
              ·
                refine ⟨30705129261805826462416163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20470086174537217641610775 30705129261805826462416163)
                ·
                  refine ⟨46057693892708739693624245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30705129261805826462416163 46057693892708739693624245)
                  ·
                    refine ⟨4317908802441444346277273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 46057693892708739693624245 4317908802441444346277273)
                    ·
                      refine ⟨3238431601831083259707955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4317908802441444346277273 3238431601831083259707955)
                      ·
                        rfl

theorem cell23_6306823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 3, 1, 1, 5, 2].length) (baseStart_6306823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6306823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6306823 prefixEnd_6306823 := by exact prefixLift 6306823
  have htrace : WordTrace (prefixWord ++ tailWord_6306823) baseStart_6306823 baseEnd_6306823 := by
    simpa [prefixWord, tailWord_6306823, baseEnd_6306823] using wordTrace_append hprefix tailTrace_6306823
  have hstable : (prefixWord ++ tailWord_6306823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6306823).length < 2 ^ (prefixWord ++ tailWord_6306823).sum := by decide
  have hdescent : baseEnd_6306823 < baseStart_6306823 := by decide
  rcases family_descends (prefixWord ++ tailWord_6306823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6306859 : List Nat := [1, 1, 1, 1, 2, 1, 6, 10]
def baseStart_6306859 : Nat := 118140960795 + 6306859 * 2 ^ 59
def prefixEnd_6306859 : Nat := 4983230072969 + 3 ^ 40 * 6306859 * 2
def baseEnd_6306859 : Nat := 119942595819801671068807

theorem tailTrace_6306859 : CollatzResearch.WordTrace tailWord_6306859 prefixEnd_6306859 119942595819801671068807 := by
  unfold tailWord_6306859
  simp only [CollatzResearch.WordTrace]
  refine ⟨230030045458334443607947631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153353363638889629071965087 230030045458334443607947631)
  ·
    refine ⟨345045068187501665411921447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230030045458334443607947631 345045068187501665411921447)
    ·
      refine ⟨517567602281252498117882171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 345045068187501665411921447 517567602281252498117882171)
      ·
        refine ⟨776351403421878747176823257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 517567602281252498117882171 776351403421878747176823257)
        ·
          refine ⟨582263552566409060382617443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 776351403421878747176823257 582263552566409060382617443)
          ·
            refine ⟨873395328849613590573926165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 582263552566409060382617443 873395328849613590573926165)
            ·
              refine ⟨40940406039825637058152789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 873395328849613590573926165 40940406039825637058152789)
              ·
                refine ⟨119942595819801671068807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 40940406039825637058152789 119942595819801671068807)
                ·
                  rfl

theorem cell23_6306859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 10].length) (baseStart_6306859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6306859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6306859 prefixEnd_6306859 := by exact prefixLift 6306859
  have htrace : WordTrace (prefixWord ++ tailWord_6306859) baseStart_6306859 baseEnd_6306859 := by
    simpa [prefixWord, tailWord_6306859, baseEnd_6306859] using wordTrace_append hprefix tailTrace_6306859
  have hstable : (prefixWord ++ tailWord_6306859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6306859).length < 2 ^ (prefixWord ++ tailWord_6306859).sum := by decide
  have hdescent : baseEnd_6306859 < baseStart_6306859 := by decide
  rcases family_descends (prefixWord ++ tailWord_6306859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6306866 : List Nat := [3, 2, 1, 1, 2, 2, 3, 1, 1, 1, 6]
def baseStart_6306866 : Nat := 118140960795 + 6306866 * 2 ^ 59
def prefixEnd_6306866 : Nat := 4983230072969 + 3 ^ 40 * 6306866 * 2
def baseEnd_6306866 : Nat := 3238453681499226591470257

theorem tailTrace_6306866 : CollatzResearch.WordTrace tailWord_6306866 prefixEnd_6306866 3238453681499226591470257 := by
  unfold tailWord_6306866
  simp only [CollatzResearch.WordTrace]
  refine ⟨57507575192327270950863113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153353533846206055868968301 57507575192327270950863113)
  ·
    refine ⟨43130681394245453213147335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57507575192327270950863113 43130681394245453213147335)
    ·
      refine ⟨64696022091368179819721003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43130681394245453213147335 64696022091368179819721003)
      ·
        refine ⟨97044033137052269729581505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64696022091368179819721003 97044033137052269729581505)
        ·
          refine ⟨72783024852789202297186129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97044033137052269729581505 72783024852789202297186129)
          ·
            refine ⟨54587268639591901722889597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72783024852789202297186129 54587268639591901722889597)
            ·
              refine ⟨20470225739846963146083599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54587268639591901722889597 20470225739846963146083599)
              ·
                refine ⟨30705338609770444719125399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20470225739846963146083599 30705338609770444719125399)
                ·
                  refine ⟨46058007914655667078688099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30705338609770444719125399 46058007914655667078688099)
                  ·
                    refine ⟨69087011871983500618032149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 46058007914655667078688099 69087011871983500618032149)
                    ·
                      refine ⟨3238453681499226591470257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 69087011871983500618032149 3238453681499226591470257)
                      ·
                        rfl

theorem cell23_6306866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 3, 1, 1, 1, 6].length) (baseStart_6306866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6306866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6306866 prefixEnd_6306866 := by exact prefixLift 6306866
  have htrace : WordTrace (prefixWord ++ tailWord_6306866) baseStart_6306866 baseEnd_6306866 := by
    simpa [prefixWord, tailWord_6306866, baseEnd_6306866] using wordTrace_append hprefix tailTrace_6306866
  have hstable : (prefixWord ++ tailWord_6306866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6306866).length < 2 ^ (prefixWord ++ tailWord_6306866).sum := by decide
  have hdescent : baseEnd_6306866 < baseStart_6306866 := by decide
  rcases family_descends (prefixWord ++ tailWord_6306866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6306870 : List Nat := [5, 1, 2, 1, 1, 2, 1, 4, 1, 1, 4]
def baseStart_6306870 : Nat := 118140960795 + 6306870 * 2 ^ 59
def prefixEnd_6306870 : Nat := 4983230072969 + 3 ^ 40 * 6306870 * 2
def baseEnd_6306870 : Nat := 3238455735421844575820239

theorem tailTrace_6306870 : CollatzResearch.WordTrace tailWord_6306870 prefixEnd_6306870 3238455735421844575820239 := by
  unfold tailWord_6306870
  simp only [CollatzResearch.WordTrace]
  refine ⟨14376902916330912030412379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 153353631107529728324398709 14376902916330912030412379)
  ·
    refine ⟨21565354374496368045618569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14376902916330912030412379 21565354374496368045618569)
    ·
      refine ⟨16174015780872276034213927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21565354374496368045618569 16174015780872276034213927)
      ·
        refine ⟨24261023671308414051320891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16174015780872276034213927 24261023671308414051320891)
        ·
          refine ⟨36391535506962621076981337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24261023671308414051320891 36391535506962621076981337)
          ·
            refine ⟨27293651630221965807736003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36391535506962621076981337 27293651630221965807736003)
            ·
              refine ⟨40940477445332948711604005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27293651630221965807736003 40940477445332948711604005)
              ·
                refine ⟨7676339520999927883425751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40940477445332948711604005 7676339520999927883425751)
                ·
                  refine ⟨11514509281499891825138627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7676339520999927883425751 11514509281499891825138627)
                  ·
                    refine ⟨17271763922249837737707941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11514509281499891825138627 17271763922249837737707941)
                    ·
                      refine ⟨3238455735421844575820239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17271763922249837737707941 3238455735421844575820239)
                      ·
                        rfl

theorem cell23_6306870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 4, 1, 1, 4].length) (baseStart_6306870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6306870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6306870 prefixEnd_6306870 := by exact prefixLift 6306870
  have htrace : WordTrace (prefixWord ++ tailWord_6306870) baseStart_6306870 baseEnd_6306870 := by
    simpa [prefixWord, tailWord_6306870, baseEnd_6306870] using wordTrace_append hprefix tailTrace_6306870
  have hstable : (prefixWord ++ tailWord_6306870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6306870).length < 2 ^ (prefixWord ++ tailWord_6306870).sum := by decide
  have hdescent : baseEnd_6306870 < baseStart_6306870 := by decide
  rcases family_descends (prefixWord ++ tailWord_6306870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6306876 : List Nat := [2, 2, 2, 2, 2, 3, 1, 9]
def baseStart_6306876 : Nat := 118140960795 + 6306876 * 2 ^ 59
def prefixEnd_6306876 : Nat := 4983230072969 + 3 ^ 40 * 6306876 * 2
def baseEnd_6306876 : Nat := 119942919122435983420193

theorem tailTrace_6306876 : CollatzResearch.WordTrace tailWord_6306876 prefixEnd_6306876 119942919122435983420193 := by
  unfold tailWord_6306876
  simp only [CollatzResearch.WordTrace]
  refine ⟨115015332749636427755658241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153353776999515237007544321 115015332749636427755658241)
  ·
    refine ⟨86261499562227320816743681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115015332749636427755658241 86261499562227320816743681)
    ·
      refine ⟨64696124671670490612557761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86261499562227320816743681 64696124671670490612557761)
      ·
        refine ⟨48522093503752867959418321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64696124671670490612557761 48522093503752867959418321)
        ·
          refine ⟨36391570127814650969563741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48522093503752867959418321 36391570127814650969563741)
          ·
            refine ⟨13646838797930494113586403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36391570127814650969563741 13646838797930494113586403)
            ·
              refine ⟨20470258196895741170379605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13646838797930494113586403 20470258196895741170379605)
              ·
                refine ⟨119942919122435983420193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 20470258196895741170379605 119942919122435983420193)
                ·
                  rfl

theorem cell23_6306876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 1, 9].length) (baseStart_6306876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6306876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6306876 prefixEnd_6306876 := by exact prefixLift 6306876
  have htrace : WordTrace (prefixWord ++ tailWord_6306876) baseStart_6306876 baseEnd_6306876 := by
    simpa [prefixWord, tailWord_6306876, baseEnd_6306876] using wordTrace_append hprefix tailTrace_6306876
  have hstable : (prefixWord ++ tailWord_6306876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6306876).length < 2 ^ (prefixWord ++ tailWord_6306876).sum := by decide
  have hdescent : baseEnd_6306876 < baseStart_6306876 := by decide
  rcases family_descends (prefixWord ++ tailWord_6306876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6306881 : List Nat := [1, 2, 5, 1, 4, 1, 1, 3, 1, 1, 3]
def baseStart_6306881 : Nat := 118140960795 + 6306881 * 2 ^ 59
def prefixEnd_6306881 : Nat := 4983230072969 + 3 ^ 40 * 6306881 * 2
def baseEnd_6306881 : Nat := 3238461383709044032782689

theorem tailTrace_6306881 : CollatzResearch.WordTrace tailWord_6306881 prefixEnd_6306881 3238461383709044032782689 := by
  unfold tailWord_6306881
  simp only [CollatzResearch.WordTrace]
  refine ⟨230030847864254741365248497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153353898576169827576832331 230030847864254741365248497)
  ·
    refine ⟨172523135898191056023936373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 230030847864254741365248497 172523135898191056023936373)
    ·
      refine ⟨16174043990455411502244035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 172523135898191056023936373 16174043990455411502244035)
      ·
        refine ⟨24261065985683117253366053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16174043990455411502244035 24261065985683117253366053)
        ·
          refine ⟨4548949872315584485006135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24261065985683117253366053 4548949872315584485006135)
          ·
            refine ⟨6823424808473376727509203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4548949872315584485006135 6823424808473376727509203)
            ·
              refine ⟨10235137212710065091263805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6823424808473376727509203 10235137212710065091263805)
              ·
                refine ⟨3838176454766274409223927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10235137212710065091263805 3838176454766274409223927)
                ·
                  refine ⟨5757264682149411613835891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3838176454766274409223927 5757264682149411613835891)
                  ·
                    refine ⟨8635897023224117420753837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5757264682149411613835891 8635897023224117420753837)
                    ·
                      refine ⟨3238461383709044032782689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8635897023224117420753837 3238461383709044032782689)
                      ·
                        rfl

theorem cell23_6306881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 4, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 4, 1, 1, 3, 1, 1, 3].length) (baseStart_6306881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6306881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6306881 prefixEnd_6306881 := by exact prefixLift 6306881
  have htrace : WordTrace (prefixWord ++ tailWord_6306881) baseStart_6306881 baseEnd_6306881 := by
    simpa [prefixWord, tailWord_6306881, baseEnd_6306881] using wordTrace_append hprefix tailTrace_6306881
  have hstable : (prefixWord ++ tailWord_6306881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6306881).length < 2 ^ (prefixWord ++ tailWord_6306881).sum := by decide
  have hdescent : baseEnd_6306881 < baseStart_6306881 := by decide
  rcases family_descends (prefixWord ++ tailWord_6306881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6306893 : List Nat := [1, 6, 1, 1, 1, 4, 9]
def baseStart_6306893 : Nat := 118140960795 + 6306893 * 2 ^ 59
def prefixEnd_6306893 : Nat := 4983230072969 + 3 ^ 40 * 6306893 * 2
def baseEnd_6306893 : Nat := 39981080808356765257193

theorem tailTrace_6306893 : CollatzResearch.WordTrace tailWord_6306893 prefixEnd_6306893 39981080808356765257193 := by
  unfold tailWord_6306893
  simp only [CollatzResearch.WordTrace]
  refine ⟨230031285540211267414685333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153354190360140844943123555 230031285540211267414685333)
  ·
    refine ⟨10782716509697403160063375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 230031285540211267414685333 10782716509697403160063375)
    ·
      refine ⟨16174074764546104740095063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10782716509697403160063375 16174074764546104740095063)
      ·
        refine ⟨24261112146819157110142595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16174074764546104740095063 24261112146819157110142595)
        ·
          refine ⟨36391668220228735665213893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24261112146819157110142595 36391668220228735665213893)
          ·
            refine ⟨6823437791292887937227605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36391668220228735665213893 6823437791292887937227605)
            ·
              refine ⟨39981080808356765257193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6823437791292887937227605 39981080808356765257193)
              ·
                rfl

theorem cell23_6306893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 4, 9].length) (baseStart_6306893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6306893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6306893 prefixEnd_6306893 := by exact prefixLift 6306893
  have htrace : WordTrace (prefixWord ++ tailWord_6306893) baseStart_6306893 baseEnd_6306893 := by
    simpa [prefixWord, tailWord_6306893, baseEnd_6306893] using wordTrace_append hprefix tailTrace_6306893
  have hstable : (prefixWord ++ tailWord_6306893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6306893).length < 2 ^ (prefixWord ++ tailWord_6306893).sum := by decide
  have hdescent : baseEnd_6306893 < baseStart_6306893 := by decide
  rcases family_descends (prefixWord ++ tailWord_6306893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6306904 : List Nat := [2, 1, 2, 2, 1, 3, 5, 2, 1, 2, 2]
def baseStart_6306904 : Nat := 118140960795 + 6306904 * 2 ^ 59
def prefixEnd_6306904 : Nat := 4983230072969 + 3 ^ 40 * 6306904 * 2
def baseEnd_6306904 : Nat := 3238473193764097442795083

theorem tailTrace_6306904 : CollatzResearch.WordTrace tailWord_6306904 prefixEnd_6306904 3238473193764097442795083 := by
  unfold tailWord_6306904
  simp only [CollatzResearch.WordTrace]
  refine ⟨115015843371585708146667883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153354457828780944195557177 115015843371585708146667883)
  ·
    refine ⟨172523765057378562220001825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115015843371585708146667883 172523765057378562220001825)
    ·
      refine ⟨129392823793033921665001369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 172523765057378562220001825 129392823793033921665001369)
      ·
        refine ⟨97044617844775441248751027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129392823793033921665001369 97044617844775441248751027)
        ·
          refine ⟨145566926767163161873126541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97044617844775441248751027 145566926767163161873126541)
          ·
            refine ⟨54587597537686185702422453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 145566926767163161873126541 54587597537686185702422453)
            ·
              refine ⟨5117587269158079909602105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 54587597537686185702422453 5117587269158079909602105)
              ·
                refine ⟨3838190451868559932201579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5117587269158079909602105 3838190451868559932201579)
                ·
                  refine ⟨5757285677802839898302369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3838190451868559932201579 5757285677802839898302369)
                  ·
                    refine ⟨4317964258352129923726777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5757285677802839898302369 4317964258352129923726777)
                    ·
                      refine ⟨3238473193764097442795083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4317964258352129923726777 3238473193764097442795083)
                      ·
                        rfl

theorem cell23_6306904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 5, 2, 1, 2, 2].length) (baseStart_6306904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6306904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6306904 prefixEnd_6306904 := by exact prefixLift 6306904
  have htrace : WordTrace (prefixWord ++ tailWord_6306904) baseStart_6306904 baseEnd_6306904 := by
    simpa [prefixWord, tailWord_6306904, baseEnd_6306904] using wordTrace_append hprefix tailTrace_6306904
  have hstable : (prefixWord ++ tailWord_6306904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6306904).length < 2 ^ (prefixWord ++ tailWord_6306904).sum := by decide
  have hdescent : baseEnd_6306904 < baseStart_6306904 := by decide
  rcases family_descends (prefixWord ++ tailWord_6306904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6306910 : List Nat := [4, 4, 1, 1, 1, 1, 1, 10]
def baseStart_6306910 : Nat := 118140960795 + 6306910 * 2 ^ 59
def prefixEnd_6306910 : Nat := 4983230072969 + 3 ^ 40 * 6306910 * 2
def baseEnd_6306910 : Nat := 119943565727704608122965

theorem tailTrace_6306910 : CollatzResearch.WordTrace tailWord_6306910 prefixEnd_6306910 119943565727704608122965 := by
  unfold tailWord_6306910
  simp only [CollatzResearch.WordTrace]
  refine ⟨28753988197643709914756773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 153354603720766452878702789 28753988197643709914756773)
  ·
    refine ⟨5391372787058195609016895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28753988197643709914756773 5391372787058195609016895)
    ·
      refine ⟨8087059180587293413525343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5391372787058195609016895 8087059180587293413525343)
      ·
        refine ⟨12130588770880940120288015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8087059180587293413525343 12130588770880940120288015)
        ·
          refine ⟨18195883156321410180432023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12130588770880940120288015 18195883156321410180432023)
          ·
            refine ⟨27293824734482115270648035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18195883156321410180432023 27293824734482115270648035)
            ·
              refine ⟨40940737101723172905972053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27293824734482115270648035 40940737101723172905972053)
              ·
                refine ⟨119943565727704608122965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 40940737101723172905972053 119943565727704608122965)
                ·
                  rfl

theorem cell23_6306910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 10].length) (baseStart_6306910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6306910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6306910 prefixEnd_6306910 := by exact prefixLift 6306910
  have htrace : WordTrace (prefixWord ++ tailWord_6306910) baseStart_6306910 baseEnd_6306910 := by
    simpa [prefixWord, tailWord_6306910, baseEnd_6306910] using wordTrace_append hprefix tailTrace_6306910
  have hstable : (prefixWord ++ tailWord_6306910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6306910).length < 2 ^ (prefixWord ++ tailWord_6306910).sum := by decide
  have hdescent : baseEnd_6306910 < baseStart_6306910 := by decide
  rcases family_descends (prefixWord ++ tailWord_6306910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6306914 : List Nat := [3, 3, 2, 2, 1, 3, 2, 1, 2, 4]
def baseStart_6306914 : Nat := 118140960795 + 6306914 * 2 ^ 59
def prefixEnd_6306914 : Nat := 4983230072969 + 3 ^ 40 * 6306914 * 2
def baseEnd_6306914 : Nat := 1079492776190214134556679

theorem tailTrace_6306914 : CollatzResearch.WordTrace tailWord_6306914 prefixEnd_6306914 1079492776190214134556679 := by
  unfold tailWord_6306914
  simp only [CollatzResearch.WordTrace]
  refine ⟨57508012868283797000299949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153354700982090125334133197 57508012868283797000299949)
  ·
    refine ⟨21565504825606423875112481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57508012868283797000299949 21565504825606423875112481)
    ·
      refine ⟨16174128619204817906334361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21565504825606423875112481 16174128619204817906334361)
      ·
        refine ⟨12130596464403613429750771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16174128619204817906334361 12130596464403613429750771)
        ·
          refine ⟨18195894696605420144626157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12130596464403613429750771 18195894696605420144626157)
          ·
            refine ⟨6823460511227032554234809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18195894696605420144626157 6823460511227032554234809)
            ·
              refine ⟨5117595383420274415676107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6823460511227032554234809 5117595383420274415676107)
              ·
                refine ⟨7676393075130411623514161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5117595383420274415676107 7676393075130411623514161)
                ·
                  refine ⟨5757294806347808717635621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7676393075130411623514161 5757294806347808717635621)
                  ·
                    refine ⟨1079492776190214134556679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5757294806347808717635621 1079492776190214134556679)
                    ·
                      rfl

theorem cell23_6306914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 3, 2, 1, 2, 4].length) (baseStart_6306914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6306914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6306914 prefixEnd_6306914 := by exact prefixLift 6306914
  have htrace : WordTrace (prefixWord ++ tailWord_6306914) baseStart_6306914 baseEnd_6306914 := by
    simpa [prefixWord, tailWord_6306914, baseEnd_6306914] using wordTrace_append hprefix tailTrace_6306914
  have hstable : (prefixWord ++ tailWord_6306914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6306914).length < 2 ^ (prefixWord ++ tailWord_6306914).sum := by decide
  have hdescent : baseEnd_6306914 < baseStart_6306914 := by decide
  rcases family_descends (prefixWord ++ tailWord_6306914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6306930 : List Nat := [3, 2, 1, 2, 2, 1, 3, 1, 3, 3, 2]
def baseStart_6306930 : Nat := 118140960795 + 6306930 * 2 ^ 59
def prefixEnd_6306930 : Nat := 4983230072969 + 3 ^ 40 * 6306930 * 2
def baseEnd_6306930 : Nat := 3238486544261114341069963

theorem tailTrace_6306930 : CollatzResearch.WordTrace tailWord_6306930 prefixEnd_6306930 3238486544261114341069963 := by
  unfold tailWord_6306930
  simp only [CollatzResearch.WordTrace]
  refine ⟨57508158760269305683445561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153355090027384815155854829 57508158760269305683445561)
  ·
    refine ⟨43131119070201979262584171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57508158760269305683445561 43131119070201979262584171)
    ·
      refine ⟨64696678605302968893876257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43131119070201979262584171 64696678605302968893876257)
      ·
        refine ⟨48522508953977226670407193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64696678605302968893876257 48522508953977226670407193)
        ·
          refine ⟨36391881715482920002805395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48522508953977226670407193 36391881715482920002805395)
          ·
            refine ⟨54587822573224380004208093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36391881715482920002805395 54587822573224380004208093)
            ·
              refine ⟨20470433464959142501578035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54587822573224380004208093 20470433464959142501578035)
              ·
                refine ⟨30705650197438713752367053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20470433464959142501578035 30705650197438713752367053)
                ·
                  refine ⟨11514618824039517657137645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30705650197438713752367053 11514618824039517657137645)
                  ·
                    refine ⟨4317982059014819121426617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11514618824039517657137645 4317982059014819121426617)
                    ·
                      refine ⟨3238486544261114341069963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4317982059014819121426617 3238486544261114341069963)
                      ·
                        rfl

theorem cell23_6306930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 3, 1, 3, 3, 2].length) (baseStart_6306930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6306930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6306930 prefixEnd_6306930 := by exact prefixLift 6306930
  have htrace : WordTrace (prefixWord ++ tailWord_6306930) baseStart_6306930 baseEnd_6306930 := by
    simpa [prefixWord, tailWord_6306930, baseEnd_6306930] using wordTrace_append hprefix tailTrace_6306930
  have hstable : (prefixWord ++ tailWord_6306930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6306930).length < 2 ^ (prefixWord ++ tailWord_6306930).sum := by decide
  have hdescent : baseEnd_6306930 < baseStart_6306930 := by decide
  rcases family_descends (prefixWord ++ tailWord_6306930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6306947 : List Nat := [1, 1, 1, 3, 3, 2, 5, 1, 1, 3, 2]
def baseStart_6306947 : Nat := 118140960795 + 6306947 * 2 ^ 59
def prefixEnd_6306947 : Nat := 4983230072969 + 3 ^ 40 * 6306947 * 2
def baseEnd_6306947 : Nat := 3238495273432240774557385

theorem tailTrace_6306947 : CollatzResearch.WordTrace tailWord_6306947 prefixEnd_6306947 3238495273432240774557385 := by
  unfold tailWord_6306947
  simp only [CollatzResearch.WordTrace]
  refine ⟨230033255082015634637151095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153355503388010423091434063 230033255082015634637151095)
  ·
    refine ⟨345049882623023451955726643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230033255082015634637151095 345049882623023451955726643)
    ·
      refine ⟨517574823934535177933589965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 345049882623023451955726643 517574823934535177933589965)
      ·
        refine ⟨194090558975450691725096237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 517574823934535177933589965 194090558975450691725096237)
        ·
          refine ⟨72783959615794009396911089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 194090558975450691725096237 72783959615794009396911089)
          ·
            refine ⟨54587969711845507047683317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72783959615794009396911089 54587969711845507047683317)
            ·
              refine ⟨5117622160485516285720311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 54587969711845507047683317 5117622160485516285720311)
              ·
                refine ⟨7676433240728274428580467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5117622160485516285720311 7676433240728274428580467)
                ·
                  refine ⟨11514649861092411642870701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7676433240728274428580467 11514649861092411642870701)
                  ·
                    refine ⟨4317993697909654366076513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11514649861092411642870701 4317993697909654366076513)
                    ·
                      refine ⟨3238495273432240774557385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4317993697909654366076513 3238495273432240774557385)
                      ·
                        rfl

theorem cell23_6306947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 5, 1, 1, 3, 2].length) (baseStart_6306947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6306947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6306947 prefixEnd_6306947 := by exact prefixLift 6306947
  have htrace : WordTrace (prefixWord ++ tailWord_6306947) baseStart_6306947 baseEnd_6306947 := by
    simpa [prefixWord, tailWord_6306947, baseEnd_6306947] using wordTrace_append hprefix tailTrace_6306947
  have hstable : (prefixWord ++ tailWord_6306947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6306947).length < 2 ^ (prefixWord ++ tailWord_6306947).sum := by decide
  have hdescent : baseEnd_6306947 < baseStart_6306947 := by decide
  rcases family_descends (prefixWord ++ tailWord_6306947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6306956 : List Nat := [2, 2, 1, 2, 1, 1, 1, 2, 3, 4, 4]
def baseStart_6306956 : Nat := 118140960795 + 6306956 * 2 ^ 59
def prefixEnd_6306956 : Nat := 4983230072969 + 3 ^ 40 * 6306956 * 2
def baseEnd_6306956 : Nat := 3238499894758131239344843

theorem tailTrace_6306956 : CollatzResearch.WordTrace tailWord_6306956 prefixEnd_6306956 3238499894758131239344843 := by
  unfold tailWord_6306956
  simp only [CollatzResearch.WordTrace]
  refine ⟨115016791669491514587114361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153355722225988686116152481 115016791669491514587114361)
  ·
    refine ⟨86262593752118635940335771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115016791669491514587114361 86262593752118635940335771)
    ·
      refine ⟨129393890628177953910503657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86262593752118635940335771 129393890628177953910503657)
      ·
        refine ⟨97045417971133465432877743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129393890628177953910503657 97045417971133465432877743)
        ·
          refine ⟨145568126956700198149316615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97045417971133465432877743 145568126956700198149316615)
          ·
            refine ⟨218352190435050297223974923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 145568126956700198149316615 218352190435050297223974923)
            ·
              refine ⟨327528285652575445835962385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 218352190435050297223974923 327528285652575445835962385)
              ·
                refine ⟨245646214239431584376971789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 327528285652575445835962385 245646214239431584376971789)
                ·
                  refine ⟨92117330339786844141364421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 245646214239431584376971789 92117330339786844141364421)
                  ·
                    refine ⟨17271999438710033276505829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 92117330339786844141364421 17271999438710033276505829)
                    ·
                      refine ⟨3238499894758131239344843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17271999438710033276505829 3238499894758131239344843)
                      ·
                        rfl

theorem cell23_6306956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 3, 4, 4].length) (baseStart_6306956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6306956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6306956 prefixEnd_6306956 := by exact prefixLift 6306956
  have htrace : WordTrace (prefixWord ++ tailWord_6306956) baseStart_6306956 baseEnd_6306956 := by
    simpa [prefixWord, tailWord_6306956, baseEnd_6306956] using wordTrace_append hprefix tailTrace_6306956
  have hstable : (prefixWord ++ tailWord_6306956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6306956).length < 2 ^ (prefixWord ++ tailWord_6306956).sum := by decide
  have hdescent : baseEnd_6306956 < baseStart_6306956 := by decide
  rcases family_descends (prefixWord ++ tailWord_6306956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6306973 : List Nat := [1, 4, 2, 1, 1, 2, 3, 1, 2, 2, 4]
def baseStart_6306973 : Nat := 118140960795 + 6306973 * 2 ^ 59
def prefixEnd_6306973 : Nat := 4983230072969 + 3 ^ 40 * 6306973 * 2
def baseEnd_6306973 : Nat := 3238508623929257672832265

theorem tailTrace_6306973 : CollatzResearch.WordTrace tailWord_6306973 prefixEnd_6306973 3238508623929257672832265 := by
  unfold tailWord_6306973
  simp only [CollatzResearch.WordTrace]
  refine ⟨230034203379921441077597573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153356135586614294051731715 230034203379921441077597573)
  ·
    refine ⟨43131413133735270202049545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 230034203379921441077597573 43131413133735270202049545)
    ·
      refine ⟨32348559850301452651537159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43131413133735270202049545 32348559850301452651537159)
      ·
        refine ⟨48522839775452178977305739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32348559850301452651537159 48522839775452178977305739)
        ·
          refine ⟨72784259663178268465958609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48522839775452178977305739 72784259663178268465958609)
          ·
            refine ⟨54588194747383701349468957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72784259663178268465958609 54588194747383701349468957)
            ·
              refine ⟨20470573030268888006050859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54588194747383701349468957 20470573030268888006050859)
              ·
                refine ⟨30705859545403332009076289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20470573030268888006050859 30705859545403332009076289)
                ·
                  refine ⟨23029394659052499006807217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30705859545403332009076289 23029394659052499006807217)
                  ·
                    refine ⟨17272045994289374255105413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23029394659052499006807217 17272045994289374255105413)
                    ·
                      refine ⟨3238508623929257672832265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17272045994289374255105413 3238508623929257672832265)
                      ·
                        rfl

theorem cell23_6306973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 3, 1, 2, 2, 4].length) (baseStart_6306973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6306973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6306973 prefixEnd_6306973 := by exact prefixLift 6306973
  have htrace : WordTrace (prefixWord ++ tailWord_6306973) baseStart_6306973 baseEnd_6306973 := by
    simpa [prefixWord, tailWord_6306973, baseEnd_6306973] using wordTrace_append hprefix tailTrace_6306973
  have hstable : (prefixWord ++ tailWord_6306973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6306973).length < 2 ^ (prefixWord ++ tailWord_6306973).sum := by decide
  have hdescent : baseEnd_6306973 < baseStart_6306973 := by decide
  rcases family_descends (prefixWord ++ tailWord_6306973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6306977 : List Nat := [1, 2, 3, 3, 1, 1, 1, 5, 2, 2, 2]
def baseStart_6306977 : Nat := 118140960795 + 6306977 * 2 ^ 59
def prefixEnd_6306977 : Nat := 4983230072969 + 3 ^ 40 * 6306977 * 2
def baseEnd_6306977 : Nat := 3238510677851875657182247

theorem tailTrace_6306977 : CollatzResearch.WordTrace tailWord_6306977 prefixEnd_6306977 3238510677851875657182247 := by
  unfold tailWord_6306977
  simp only [CollatzResearch.WordTrace]
  refine ⟨230034349271906949760743185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153356232847937966507162123 230034349271906949760743185)
  ·
    refine ⟨172525761953930212320557389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 230034349271906949760743185 172525761953930212320557389)
    ·
      refine ⟨64697160732723829620209021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 172525761953930212320557389 64697160732723829620209021)
      ·
        refine ⟨24261435274771436107578383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64697160732723829620209021 24261435274771436107578383)
        ·
          refine ⟨36392152912157154161367575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24261435274771436107578383 36392152912157154161367575)
          ·
            refine ⟨54588229368235731242051363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36392152912157154161367575 54588229368235731242051363)
            ·
              refine ⟨81882344052353596863077045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54588229368235731242051363 81882344052353596863077045)
              ·
                refine ⟨7676469754908149705913473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 81882344052353596863077045 7676469754908149705913473)
                ·
                  refine ⟨5757352316181112279435105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7676469754908149705913473 5757352316181112279435105)
                  ·
                    refine ⟨4318014237135834209576329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5757352316181112279435105 4318014237135834209576329)
                    ·
                      refine ⟨3238510677851875657182247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4318014237135834209576329 3238510677851875657182247)
                      ·
                        rfl

theorem cell23_6306977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 5, 2, 2, 2].length) (baseStart_6306977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6306977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6306977 prefixEnd_6306977 := by exact prefixLift 6306977
  have htrace : WordTrace (prefixWord ++ tailWord_6306977) baseStart_6306977 baseEnd_6306977 := by
    simpa [prefixWord, tailWord_6306977, baseEnd_6306977] using wordTrace_append hprefix tailTrace_6306977
  have hstable : (prefixWord ++ tailWord_6306977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6306977).length < 2 ^ (prefixWord ++ tailWord_6306977).sum := by decide
  have hdescent : baseEnd_6306977 < baseStart_6306977 := by decide
  rcases family_descends (prefixWord ++ tailWord_6306977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6306983 : List Nat := [1, 1, 6, 2, 1, 1, 1, 1, 9]
def baseStart_6306983 : Nat := 118140960795 + 6306983 * 2 ^ 59
def prefixEnd_6306983 : Nat := 4983230072969 + 3 ^ 40 * 6306983 * 2
def baseEnd_6306983 : Nat := 359834862081755848189691

theorem tailTrace_6306983 : CollatzResearch.WordTrace tailWord_6306983 prefixEnd_6306983 359834862081755848189691 := by
  unfold tailWord_6306983
  simp only [CollatzResearch.WordTrace]
  refine ⟨230034568109885212785461603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153356378739923475190307735 230034568109885212785461603)
  ·
    refine ⟨345051852164827819178192405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230034568109885212785461603 345051852164827819178192405)
    ·
      refine ⟨16174305570226304023977769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 345051852164827819178192405 16174305570226304023977769)
      ·
        refine ⟨12130729177669728017983327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16174305570226304023977769 12130729177669728017983327)
        ·
          refine ⟨18196093766504592026974991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12130729177669728017983327 18196093766504592026974991)
          ·
            refine ⟨27294140649756888040462487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18196093766504592026974991 27294140649756888040462487)
            ·
              refine ⟨40941210974635332060693731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27294140649756888040462487 40941210974635332060693731)
              ·
                refine ⟨61411816461952998091040597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40941210974635332060693731 61411816461952998091040597)
                ·
                  refine ⟨359834862081755848189691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 61411816461952998091040597 359834862081755848189691)
                  ·
                    rfl

theorem cell23_6306983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 1, 9].length) (baseStart_6306983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6306983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6306983 prefixEnd_6306983 := by exact prefixLift 6306983
  have htrace : WordTrace (prefixWord ++ tailWord_6306983) baseStart_6306983 baseEnd_6306983 := by
    simpa [prefixWord, tailWord_6306983, baseEnd_6306983] using wordTrace_append hprefix tailTrace_6306983
  have hstable : (prefixWord ++ tailWord_6306983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6306983).length < 2 ^ (prefixWord ++ tailWord_6306983).sum := by decide
  have hdescent : baseEnd_6306983 < baseStart_6306983 := by decide
  rcases family_descends (prefixWord ++ tailWord_6306983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6307003 : List Nat := [1, 1, 1, 1, 1, 2, 4, 2, 1, 7, 2]
def baseStart_6307003 : Nat := 118140960795 + 6307003 * 2 ^ 59
def prefixEnd_6307003 : Nat := 4983230072969 + 3 ^ 40 * 6307003 * 2
def baseEnd_6307003 : Nat := 3238524028348892555457127

theorem tailTrace_6307003 : CollatzResearch.WordTrace tailWord_6307003 prefixEnd_6307003 3238524028348892555457127 := by
  unfold tailWord_6307003
  simp only [CollatzResearch.WordTrace]
  refine ⟨230035297569812756201189663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153356865046541837467459775 230035297569812756201189663)
  ·
    refine ⟨345052946354719134301784495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230035297569812756201189663 345052946354719134301784495)
    ·
      refine ⟨517579419532078701452676743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 345052946354719134301784495 517579419532078701452676743)
      ·
        refine ⟨776369129298118052179015115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 517579419532078701452676743 776369129298118052179015115)
        ·
          refine ⟨1164553693947177078268522673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 776369129298118052179015115 1164553693947177078268522673)
          ·
            refine ⟨873415270460382808701392005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1164553693947177078268522673 873415270460382808701392005)
            ·
              refine ⟨163765363211321776631511001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 873415270460382808701392005 163765363211321776631511001)
              ·
                refine ⟨122824022408491332473633251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 163765363211321776631511001 122824022408491332473633251)
                ·
                  refine ⟨184236033612736998710449877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 122824022408491332473633251 184236033612736998710449877)
                  ·
                    refine ⟨4318032037798523407276169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 184236033612736998710449877 4318032037798523407276169)
                    ·
                      refine ⟨3238524028348892555457127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4318032037798523407276169 3238524028348892555457127)
                      ·
                        rfl

theorem cell23_6307003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 2, 1, 7, 2].length) (baseStart_6307003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6307003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6307003 prefixEnd_6307003 := by exact prefixLift 6307003
  have htrace : WordTrace (prefixWord ++ tailWord_6307003) baseStart_6307003 baseEnd_6307003 := by
    simpa [prefixWord, tailWord_6307003, baseEnd_6307003] using wordTrace_append hprefix tailTrace_6307003
  have hstable : (prefixWord ++ tailWord_6307003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6307003).length < 2 ^ (prefixWord ++ tailWord_6307003).sum := by decide
  have hdescent : baseEnd_6307003 < baseStart_6307003 := by decide
  rcases family_descends (prefixWord ++ tailWord_6307003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6307028 : List Nat := [2, 4, 1, 4, 1, 1, 3, 1, 2, 2, 2]
def baseStart_6307028 : Nat := 118140960795 + 6307028 * 2 ^ 59
def prefixEnd_6307028 : Nat := 4983230072969 + 3 ^ 40 * 6307028 * 2
def baseEnd_6307028 : Nat := 3238536865365254957644513

theorem tailTrace_6307028 : CollatzResearch.WordTrace tailWord_6307028 prefixEnd_6307028 3238536865365254957644513 := by
  unfold tailWord_6307028
  simp only [CollatzResearch.WordTrace]
  refine ⟨115018104697361092735424869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153357472929814790313899825 115018104697361092735424869)
  ·
    refine ⟨21565894630755204887892163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 115018104697361092735424869 21565894630755204887892163)
    ·
      refine ⟨32348841946132807331838245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21565894630755204887892163 32348841946132807331838245)
      ·
        refine ⟨6065407864899901374719671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32348841946132807331838245 6065407864899901374719671)
        ·
          refine ⟨9098111797349852062079507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6065407864899901374719671 9098111797349852062079507)
          ·
            refine ⟨13647167696024778093119261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9098111797349852062079507 13647167696024778093119261)
            ·
              refine ⟨5117687886009291784919723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13647167696024778093119261 5117687886009291784919723)
              ·
                refine ⟨7676531829013937677379585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5117687886009291784919723 7676531829013937677379585)
                ·
                  refine ⟨5757398871760453258034689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7676531829013937677379585 5757398871760453258034689)
                  ·
                    refine ⟨4318049153820339943526017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5757398871760453258034689 4318049153820339943526017)
                    ·
                      refine ⟨3238536865365254957644513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4318049153820339943526017 3238536865365254957644513)
                      ·
                        rfl

theorem cell23_6307028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 3, 1, 2, 2, 2].length) (baseStart_6307028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6307028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6307028 prefixEnd_6307028 := by exact prefixLift 6307028
  have htrace : WordTrace (prefixWord ++ tailWord_6307028) baseStart_6307028 baseEnd_6307028 := by
    simpa [prefixWord, tailWord_6307028, baseEnd_6307028] using wordTrace_append hprefix tailTrace_6307028
  have hstable : (prefixWord ++ tailWord_6307028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6307028).length < 2 ^ (prefixWord ++ tailWord_6307028).sum := by decide
  have hdescent : baseEnd_6307028 < baseStart_6307028 := by decide
  rcases family_descends (prefixWord ++ tailWord_6307028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6307073 : List Nat := [1, 2, 4, 1, 1, 3, 2, 1, 8]
def baseStart_6307073 : Nat := 118140960795 + 6307073 * 2 ^ 59
def prefixEnd_6307073 : Nat := 4983230072969 + 3 ^ 40 * 6307073 * 2
def baseEnd_6307073 : Nat := 359839996888300809064645

theorem tailTrace_6307073 : CollatzResearch.WordTrace tailWord_6307073 prefixEnd_6307073 359839996888300809064645 := by
  unfold tailWord_6307073
  simp only [CollatzResearch.WordTrace]
  refine ⟨230037850679559158156237873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153358567119706105437491915 230037850679559158156237873)
  ·
    refine ⟨172528388009669368617178405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 230037850679559158156237873 172528388009669368617178405)
    ·
      refine ⟨32349072751813006615720951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 172528388009669368617178405 32349072751813006615720951)
      ·
        refine ⟨48523609127719509923581427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32349072751813006615720951 48523609127719509923581427)
        ·
          refine ⟨72785413691579264885372141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48523609127719509923581427 72785413691579264885372141)
          ·
            refine ⟨27294530134342224332014553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72785413691579264885372141 27294530134342224332014553)
            ·
              refine ⟨20470897600756668249010915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27294530134342224332014553 20470897600756668249010915)
              ·
                refine ⟨30706346401135002373516373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20470897600756668249010915 30706346401135002373516373)
                ·
                  refine ⟨359839996888300809064645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 30706346401135002373516373 359839996888300809064645)
                  ·
                    rfl

theorem cell23_6307073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 2, 1, 8].length) (baseStart_6307073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6307073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6307073 prefixEnd_6307073 := by exact prefixLift 6307073
  have htrace : WordTrace (prefixWord ++ tailWord_6307073) baseStart_6307073 baseEnd_6307073 := by
    simpa [prefixWord, tailWord_6307073, baseEnd_6307073] using wordTrace_append hprefix tailTrace_6307073
  have hstable : (prefixWord ++ tailWord_6307073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6307073).length < 2 ^ (prefixWord ++ tailWord_6307073).sum := by decide
  have hdescent : baseEnd_6307073 < baseStart_6307073 := by decide
  rcases family_descends (prefixWord ++ tailWord_6307073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6307150 : List Nat := [4, 1, 1, 1, 1, 1, 6, 1, 1, 6]
def baseStart_6307150 : Nat := 118140960795 + 6307150 * 2 ^ 59
def prefixEnd_6307150 : Nat := 4983230072969 + 3 ^ 40 * 6307150 * 2
def baseEnd_6307150 : Nat := 1079533170001701160106317

theorem tailTrace_6307150 : CollatzResearch.WordTrace tailWord_6307150 prefixEnd_6307150 1079533170001701160106317 := by
  unfold tailWord_6307150
  simp only [CollatzResearch.WordTrace]
  refine ⟨28755082387535025038348863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 153360439400186800204527269 28755082387535025038348863)
  ·
    refine ⟨43132623581302537557523295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28755082387535025038348863 43132623581302537557523295)
    ·
      refine ⟨64698935371953806336284943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43132623581302537557523295 64698935371953806336284943)
      ·
        refine ⟨97048403057930709504427415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64698935371953806336284943 97048403057930709504427415)
        ·
          refine ⟨145572604586896064256641123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97048403057930709504427415 145572604586896064256641123)
          ·
            refine ⟨218358906880344096384961685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 145572604586896064256641123 218358906880344096384961685)
            ·
              refine ⟨10235573760016129518045079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 218358906880344096384961685 10235573760016129518045079)
              ·
                refine ⟨15353360640024194277067619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10235573760016129518045079 15353360640024194277067619)
                ·
                  refine ⟨23030040960036291415601429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15353360640024194277067619 23030040960036291415601429)
                  ·
                    refine ⟨1079533170001701160106317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23030040960036291415601429 1079533170001701160106317)
                    ·
                      rfl

theorem cell23_6307150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 6, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 6, 1, 1, 6].length) (baseStart_6307150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6307150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6307150 prefixEnd_6307150 := by exact prefixLift 6307150
  have htrace : WordTrace (prefixWord ++ tailWord_6307150) baseStart_6307150 baseEnd_6307150 := by
    simpa [prefixWord, tailWord_6307150, baseEnd_6307150] using wordTrace_append hprefix tailTrace_6307150
  have hstable : (prefixWord ++ tailWord_6307150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6307150).length < 2 ^ (prefixWord ++ tailWord_6307150).sum := by decide
  have hdescent : baseEnd_6307150 < baseStart_6307150 := by decide
  rcases family_descends (prefixWord ++ tailWord_6307150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6307160 : List Nat := [2, 1, 2, 2, 1, 1, 3, 3, 3, 2, 3]
def baseStart_6307160 : Nat := 118140960795 + 6307160 * 2 ^ 59
def prefixEnd_6307160 : Nat := 4983230072969 + 3 ^ 40 * 6307160 * 2
def baseEnd_6307160 : Nat := 3238604644811648441193905

theorem tailTrace_6307160 : CollatzResearch.WordTrace tailWord_6307160 prefixEnd_6307160 3238604644811648441193905 := by
  unfold tailWord_6307160
  simp only [CollatzResearch.WordTrace]
  refine ⟨115020511915121986007327467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153360682553495981343103289 115020511915121986007327467)
  ·
    refine ⟨172530767872682979010991201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115020511915121986007327467 172530767872682979010991201)
    ·
      refine ⟨129398075904512234258243401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 172530767872682979010991201 129398075904512234258243401)
      ·
        refine ⟨97048556928384175693682551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129398075904512234258243401 97048556928384175693682551)
        ·
          refine ⟨145572835392576263540523827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97048556928384175693682551 145572835392576263540523827)
          ·
            refine ⟨218359253088864395310785741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 145572835392576263540523827 218359253088864395310785741)
            ·
              refine ⟨81884719908324148241544653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 218359253088864395310785741 81884719908324148241544653)
              ·
                refine ⟨30706769965621555590579245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 81884719908324148241544653 30706769965621555590579245)
                ·
                  refine ⟨11515038737108083346467217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30706769965621555590579245 11515038737108083346467217)
                  ·
                    refine ⟨8636279052831062509850413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11515038737108083346467217 8636279052831062509850413)
                    ·
                      refine ⟨3238604644811648441193905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8636279052831062509850413 3238604644811648441193905)
                      ·
                        rfl

theorem cell23_6307160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 3, 3, 2, 3].length) (baseStart_6307160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6307160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6307160 prefixEnd_6307160 := by exact prefixLift 6307160
  have htrace : WordTrace (prefixWord ++ tailWord_6307160) baseStart_6307160 baseEnd_6307160 := by
    simpa [prefixWord, tailWord_6307160, baseEnd_6307160] using wordTrace_append hprefix tailTrace_6307160
  have hstable : (prefixWord ++ tailWord_6307160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6307160).length < 2 ^ (prefixWord ++ tailWord_6307160).sum := by decide
  have hdescent : baseEnd_6307160 < baseStart_6307160 := by decide
  rcases family_descends (prefixWord ++ tailWord_6307160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6307193 : List Nat := [1, 2, 1, 3, 2, 1, 2, 1, 1, 9]
def baseStart_6307193 : Nat := 118140960795 + 6307193 * 2 ^ 59
def prefixEnd_6307193 : Nat := 4983230072969 + 3 ^ 40 * 6307193 * 2
def baseEnd_6307193 : Nat := 1079540529891082270693751

theorem tailTrace_6307193 : CollatzResearch.WordTrace tailWord_6307193 prefixEnd_6307193 1079540529891082270693751 := by
  unfold tailWord_6307193
  simp only [CollatzResearch.WordTrace]
  refine ⟨230042227439124418650606233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153361484959416279100404155 230042227439124418650606233)
  ·
    refine ⟨172531670579343313987954675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 230042227439124418650606233 172531670579343313987954675)
    ·
      refine ⟨258797505869014970981932013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172531670579343313987954675 258797505869014970981932013)
      ·
        refine ⟨97049064700880614118224505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 258797505869014970981932013 97049064700880614118224505)
        ·
          refine ⟨72786798525660460588668379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97049064700880614118224505 72786798525660460588668379)
          ·
            refine ⟨109180197788490690883002569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72786798525660460588668379 109180197788490690883002569)
            ·
              refine ⟨81885148341368018162251927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 109180197788490690883002569 81885148341368018162251927)
              ·
                refine ⟨122827722512052027243377891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81885148341368018162251927 122827722512052027243377891)
                ·
                  refine ⟨184241583768078040865066837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 122827722512052027243377891 184241583768078040865066837)
                  ·
                    refine ⟨1079540529891082270693751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 184241583768078040865066837 1079540529891082270693751)
                    ·
                      rfl

theorem cell23_6307193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 1, 1, 9].length) (baseStart_6307193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6307193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6307193 prefixEnd_6307193 := by exact prefixLift 6307193
  have htrace : WordTrace (prefixWord ++ tailWord_6307193) baseStart_6307193 baseEnd_6307193 := by
    simpa [prefixWord, tailWord_6307193, baseEnd_6307193] using wordTrace_append hprefix tailTrace_6307193
  have hstable : (prefixWord ++ tailWord_6307193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6307193).length < 2 ^ (prefixWord ++ tailWord_6307193).sum := by decide
  have hdescent : baseEnd_6307193 < baseStart_6307193 := by decide
  rcases family_descends (prefixWord ++ tailWord_6307193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6307201 : List Nat := [1, 2, 4, 3, 2, 1, 3, 1, 2, 4]
def baseStart_6307201 : Nat := 118140960795 + 6307201 * 2 ^ 59
def prefixEnd_6307201 : Nat := 4983230072969 + 3 ^ 40 * 6307201 * 2
def baseEnd_6307201 : Nat := 1079541899172827593593739

theorem tailTrace_6307201 : CollatzResearch.WordTrace tailWord_6307201 prefixEnd_6307201 1079541899172827593593739 := by
  unfold tailWord_6307201
  simp only [CollatzResearch.WordTrace]
  refine ⟨230042519223095436016897457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153361679482063624011264971 230042519223095436016897457)
  ·
    refine ⟨172531889417321577012673093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 230042519223095436016897457 172531889417321577012673093)
    ·
      refine ⟨32349729265747795689876205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 172531889417321577012673093 32349729265747795689876205)
      ·
        refine ⟨12131148474655423383703577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32349729265747795689876205 12131148474655423383703577)
        ·
          refine ⟨9098361355991567537777683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12131148474655423383703577 9098361355991567537777683)
          ·
            refine ⟨13647542033987351306666525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9098361355991567537777683 13647542033987351306666525)
            ·
              refine ⟨5117828262745256739999947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13647542033987351306666525 5117828262745256739999947)
              ·
                refine ⟨7676742394117885109999921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5117828262745256739999947 7676742394117885109999921)
                ·
                  refine ⟨5757556795588413832499941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7676742394117885109999921 5757556795588413832499941)
                  ·
                    refine ⟨1079541899172827593593739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5757556795588413832499941 1079541899172827593593739)
                    ·
                      rfl

theorem cell23_6307201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 3, 1, 2, 4].length) (baseStart_6307201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6307201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6307201 prefixEnd_6307201 := by exact prefixLift 6307201
  have htrace : WordTrace (prefixWord ++ tailWord_6307201) baseStart_6307201 baseEnd_6307201 := by
    simpa [prefixWord, tailWord_6307201, baseEnd_6307201] using wordTrace_append hprefix tailTrace_6307201
  have hstable : (prefixWord ++ tailWord_6307201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6307201).length < 2 ^ (prefixWord ++ tailWord_6307201).sum := by decide
  have hdescent : baseEnd_6307201 < baseStart_6307201 := by decide
  rcases family_descends (prefixWord ++ tailWord_6307201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6307207 : List Nat := [1, 1, 4, 2, 2, 2, 3, 1, 1, 3, 3]
def baseStart_6307207 : Nat := 118140960795 + 6307207 * 2 ^ 59
def prefixEnd_6307207 : Nat := 4983230072969 + 3 ^ 40 * 6307207 * 2
def baseEnd_6307207 : Nat := 3238628778402409757306189

theorem tailTrace_6307207 : CollatzResearch.WordTrace tailWord_6307207 prefixEnd_6307207 3238628778402409757306189 := by
  unfold tailWord_6307207
  simp only [CollatzResearch.WordTrace]
  refine ⟨230042738061073699041615875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153361825374049132694410583 230042738061073699041615875)
  ·
    refine ⟨345064107091610548562423813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230042738061073699041615875 345064107091610548562423813)
    ·
      refine ⟨64699520079676977855454465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 345064107091610548562423813 64699520079676977855454465)
      ·
        refine ⟨48524640059757733391590849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64699520079676977855454465 48524640059757733391590849)
        ·
          refine ⟨36393480044818300043693137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48524640059757733391590849 36393480044818300043693137)
          ·
            refine ⟨27295110033613725032769853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36393480044818300043693137 27295110033613725032769853)
            ·
              refine ⟨10235666262605146887288695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27295110033613725032769853 10235666262605146887288695)
              ·
                refine ⟨15353499393907720330933043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10235666262605146887288695 15353499393907720330933043)
                ·
                  refine ⟨23030249090861580496399565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15353499393907720330933043 23030249090861580496399565)
                  ·
                    refine ⟨8636343409073092686149837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23030249090861580496399565 8636343409073092686149837)
                    ·
                      refine ⟨3238628778402409757306189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8636343409073092686149837 3238628778402409757306189)
                      ·
                        rfl

theorem cell23_6307207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 3, 1, 1, 3, 3].length) (baseStart_6307207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6307207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6307207 prefixEnd_6307207 := by exact prefixLift 6307207
  have htrace : WordTrace (prefixWord ++ tailWord_6307207) baseStart_6307207 baseEnd_6307207 := by
    simpa [prefixWord, tailWord_6307207, baseEnd_6307207] using wordTrace_append hprefix tailTrace_6307207
  have hstable : (prefixWord ++ tailWord_6307207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6307207).length < 2 ^ (prefixWord ++ tailWord_6307207).sum := by decide
  have hdescent : baseEnd_6307207 < baseStart_6307207 := by decide
  rcases family_descends (prefixWord ++ tailWord_6307207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6307214 : List Nat := [4, 1, 1, 4, 2, 2, 2, 7]
def baseStart_6307214 : Nat := 118140960795 + 6307214 * 2 ^ 59
def prefixEnd_6307214 : Nat := 4983230072969 + 3 ^ 40 * 6307214 * 2
def baseEnd_6307214 : Nat := 119949347139518193700691

theorem tailTrace_6307214 : CollatzResearch.WordTrace tailWord_6307214 prefixEnd_6307214 119949347139518193700691 := by
  unfold tailWord_6307214
  simp only [CollatzResearch.WordTrace]
  refine ⟨28755374171506042404640087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 153361995581365559491413797 28755374171506042404640087)
  ·
    refine ⟨43133061257259063606960131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28755374171506042404640087 43133061257259063606960131)
    ·
      refine ⟨64699591885888595410440197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43133061257259063606960131 64699591885888595410440197)
      ·
        refine ⟨12131173478604111639457537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 64699591885888595410440197 12131173478604111639457537)
        ·
          refine ⟨9098380108953083729593153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12131173478604111639457537 9098380108953083729593153)
          ·
            refine ⟨6823785081714812797194865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9098380108953083729593153 6823785081714812797194865)
            ·
              refine ⟨5117838811286109597896149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6823785081714812797194865 5117838811286109597896149)
              ·
                refine ⟨119949347139518193700691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5117838811286109597896149 119949347139518193700691)
                ·
                  rfl

theorem cell23_6307214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 2, 2, 7].length) (baseStart_6307214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6307214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6307214 prefixEnd_6307214 := by exact prefixLift 6307214
  have htrace : WordTrace (prefixWord ++ tailWord_6307214) baseStart_6307214 baseEnd_6307214 := by
    simpa [prefixWord, tailWord_6307214, baseEnd_6307214] using wordTrace_append hprefix tailTrace_6307214
  have hstable : (prefixWord ++ tailWord_6307214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6307214).length < 2 ^ (prefixWord ++ tailWord_6307214).sum := by decide
  have hdescent : baseEnd_6307214 < baseStart_6307214 := by decide
  rcases family_descends (prefixWord ++ tailWord_6307214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6307268 : List Nat := [2, 3, 3, 2, 1, 3, 1, 2, 1, 3, 2]
def baseStart_6307268 : Nat := 118140960795 + 6307268 * 2 ^ 59
def prefixEnd_6307268 : Nat := 4983230072969 + 3 ^ 40 * 6307268 * 2
def baseEnd_6307268 : Nat := 3238660100722334018643409

theorem tailTrace_6307268 : CollatzResearch.WordTrace tailWord_6307268 prefixEnd_6307268 3238660100722334018643409 := by
  unfold tailWord_6307268
  simp only [CollatzResearch.WordTrace]
  refine ⟨115022481456926353229793229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153363308609235137639724305 115022481456926353229793229)
  ·
    refine ⟨43133430546347382461172461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115022481456926353229793229 43133430546347382461172461)
    ·
      refine ⟨16175036454880268422939673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43133430546347382461172461 16175036454880268422939673)
      ·
        refine ⟨12131277341160201317204755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16175036454880268422939673 12131277341160201317204755)
        ·
          refine ⟨18196916011740301975807133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12131277341160201317204755 18196916011740301975807133)
          ·
            refine ⟨6823843504402613240927675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18196916011740301975807133 6823843504402613240927675)
            ·
              refine ⟨10235765256603919861391513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6823843504402613240927675 10235765256603919861391513)
              ·
                refine ⟨7676823942452939896043635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10235765256603919861391513 7676823942452939896043635)
                ·
                  refine ⟨11515235913679409844065453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7676823942452939896043635 11515235913679409844065453)
                  ·
                    refine ⟨4318213467629778691524545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11515235913679409844065453 4318213467629778691524545)
                    ·
                      refine ⟨3238660100722334018643409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4318213467629778691524545 3238660100722334018643409)
                      ·
                        rfl

theorem cell23_6307268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 3, 1, 2, 1, 3, 2].length) (baseStart_6307268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6307268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6307268 prefixEnd_6307268 := by exact prefixLift 6307268
  have htrace : WordTrace (prefixWord ++ tailWord_6307268) baseStart_6307268 baseEnd_6307268 := by
    simpa [prefixWord, tailWord_6307268, baseEnd_6307268] using wordTrace_append hprefix tailTrace_6307268
  have hstable : (prefixWord ++ tailWord_6307268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6307268).length < 2 ^ (prefixWord ++ tailWord_6307268).sum := by decide
  have hdescent : baseEnd_6307268 < baseStart_6307268 := by decide
  rcases family_descends (prefixWord ++ tailWord_6307268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6307280 : List Nat := [2, 1, 1, 1, 1, 2, 2, 4, 1, 5, 3]
def baseStart_6307280 : Nat := 118140960795 + 6307280 * 2 ^ 59
def prefixEnd_6307280 : Nat := 4983230072969 + 3 ^ 40 * 6307280 * 2
def baseEnd_6307280 : Nat := 3238666262490187971693353

theorem tailTrace_6307280 : CollatzResearch.WordTrace tailWord_6307280 prefixEnd_6307280 3238666262490187971693353 := by
  unfold tailWord_6307280
  simp only [CollatzResearch.WordTrace]
  refine ⟨115022700294904616254511647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153363600393206155006015529 115022700294904616254511647)
  ·
    refine ⟨172534050442356924381767471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115022700294904616254511647 172534050442356924381767471)
    ·
      refine ⟨258801075663535386572651207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172534050442356924381767471 258801075663535386572651207)
      ·
        refine ⟨388201613495303079858976811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 258801075663535386572651207 388201613495303079858976811)
        ·
          refine ⟨582302420242954619788465217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 388201613495303079858976811 582302420242954619788465217)
          ·
            refine ⟨436726815182215964841348913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 582302420242954619788465217 436726815182215964841348913)
            ·
              refine ⟨327545111386661973631011685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 436726815182215964841348913 327545111386661973631011685)
              ·
                refine ⟨61414708384999120055814691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 327545111386661973631011685 61414708384999120055814691)
                ·
                  refine ⟨92122062577498680083722037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61414708384999120055814691 92122062577498680083722037)
                  ·
                    refine ⟨8636443366640501257848941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 92122062577498680083722037 8636443366640501257848941)
                    ·
                      refine ⟨3238666262490187971693353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8636443366640501257848941 3238666262490187971693353)
                      ·
                        rfl

theorem cell23_6307280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 4, 1, 5, 3].length) (baseStart_6307280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6307280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6307280 prefixEnd_6307280 := by exact prefixLift 6307280
  have htrace : WordTrace (prefixWord ++ tailWord_6307280) baseStart_6307280 baseEnd_6307280 := by
    simpa [prefixWord, tailWord_6307280, baseEnd_6307280] using wordTrace_append hprefix tailTrace_6307280
  have hstable : (prefixWord ++ tailWord_6307280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6307280).length < 2 ^ (prefixWord ++ tailWord_6307280).sum := by decide
  have hdescent : baseEnd_6307280 < baseStart_6307280 := by decide
  rcases family_descends (prefixWord ++ tailWord_6307280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6307314 : List Nat := [3, 2, 1, 4, 1, 2, 1, 1, 2, 3, 3]
def baseStart_6307314 : Nat := 118140960795 + 6307314 * 2 ^ 59
def prefixEnd_6307314 : Nat := 4983230072969 + 3 ^ 40 * 6307314 * 2
def baseEnd_6307314 : Nat := 3238683720832440838668197

theorem tailTrace_6307314 : CollatzResearch.WordTrace tailWord_6307314 prefixEnd_6307314 3238683720832440838668197 := by
  unfold tailWord_6307314
  simp only [CollatzResearch.WordTrace]
  refine ⟨57511660167921514078940249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153364427114457370877173997 57511660167921514078940249)
  ·
    refine ⟨43133745125941135559205187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57511660167921514078940249 43133745125941135559205187)
    ·
      refine ⟨64700617688911703338807781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43133745125941135559205187 64700617688911703338807781)
      ·
        refine ⟨12131365816670944376026459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 64700617688911703338807781 12131365816670944376026459)
        ·
          refine ⟨18197048725006416564039689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12131365816670944376026459 18197048725006416564039689)
          ·
            refine ⟨13647786543754812423029767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18197048725006416564039689 13647786543754812423029767)
            ·
              refine ⟨20471679815632218634544651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13647786543754812423029767 20471679815632218634544651)
              ·
                refine ⟨30707519723448327951816977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20471679815632218634544651 30707519723448327951816977)
                ·
                  refine ⟨23030639792586245963862733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30707519723448327951816977 23030639792586245963862733)
                  ·
                    refine ⟨8636489922219842236448525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23030639792586245963862733 8636489922219842236448525)
                    ·
                      refine ⟨3238683720832440838668197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8636489922219842236448525 3238683720832440838668197)
                      ·
                        rfl

theorem cell23_6307314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 1, 1, 2, 3, 3].length) (baseStart_6307314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6307314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6307314 prefixEnd_6307314 := by exact prefixLift 6307314
  have htrace : WordTrace (prefixWord ++ tailWord_6307314) baseStart_6307314 baseEnd_6307314 := by
    simpa [prefixWord, tailWord_6307314, baseEnd_6307314] using wordTrace_append hprefix tailTrace_6307314
  have hstable : (prefixWord ++ tailWord_6307314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6307314).length < 2 ^ (prefixWord ++ tailWord_6307314).sum := by decide
  have hdescent : baseEnd_6307314 < baseStart_6307314 := by decide
  rcases family_descends (prefixWord ++ tailWord_6307314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6307337 : List Nat := [1, 2, 1, 1, 3, 1, 3, 2, 1, 6, 2]
def baseStart_6307337 : Nat := 118140960795 + 6307337 * 2 ^ 59
def prefixEnd_6307337 : Nat := 4983230072969 + 3 ^ 40 * 6307337 * 2
def baseEnd_6307337 : Nat := 3238695530887494248680591

theorem tailTrace_6307337 : CollatzResearch.WordTrace tailWord_6307337 prefixEnd_6307337 3238695530887494248680591 := by
  unfold tailWord_6307337
  simp only [CollatzResearch.WordTrace]
  refine ⟨230047479550602731243848265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153364986367068487495898843 230047479550602731243848265)
  ·
    refine ⟨172535609662952048432886199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 230047479550602731243848265 172535609662952048432886199)
    ·
      refine ⟨258803414494428072649329299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172535609662952048432886199 258803414494428072649329299)
      ·
        refine ⟨388205121741642108973993949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 258803414494428072649329299 388205121741642108973993949)
        ·
          refine ⟨145576920653115790865247731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 388205121741642108973993949 145576920653115790865247731)
          ·
            refine ⟨218365380979673686297871597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 145576920653115790865247731 218365380979673686297871597)
            ·
              refine ⟨81887017867377632361701849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 218365380979673686297871597 81887017867377632361701849)
              ·
                refine ⟨61415263400533224271276387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 81887017867377632361701849 61415263400533224271276387)
                ·
                  refine ⟨92122895100799836406914581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61415263400533224271276387 92122895100799836406914581)
                  ·
                    refine ⟨4318260707849992331574121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 92122895100799836406914581 4318260707849992331574121)
                    ·
                      refine ⟨3238695530887494248680591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4318260707849992331574121 3238695530887494248680591)
                      ·
                        rfl

theorem cell23_6307337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 2, 1, 6, 2].length) (baseStart_6307337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6307337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6307337 prefixEnd_6307337 := by exact prefixLift 6307337
  have htrace : WordTrace (prefixWord ++ tailWord_6307337) baseStart_6307337 baseEnd_6307337 := by
    simpa [prefixWord, tailWord_6307337, baseEnd_6307337] using wordTrace_append hprefix tailTrace_6307337
  have hstable : (prefixWord ++ tailWord_6307337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6307337).length < 2 ^ (prefixWord ++ tailWord_6307337).sum := by decide
  have hdescent : baseEnd_6307337 < baseStart_6307337 := by decide
  rcases family_descends (prefixWord ++ tailWord_6307337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6307374 : List Nat := [4, 1, 3, 1, 2, 1, 1, 2, 1, 4, 3]
def baseStart_6307374 : Nat := 118140960795 + 6307374 * 2 ^ 59
def prefixEnd_6307374 : Nat := 4983230072969 + 3 ^ 40 * 6307374 * 2
def baseEnd_6307374 : Nat := 3238714529671710603917921

theorem tailTrace_6307374 : CollatzResearch.WordTrace tailWord_6307374 prefixEnd_6307374 3238714529671710603917921 := by
  unfold tailWord_6307374
  simp only [CollatzResearch.WordTrace]
  refine ⟨28756103631433585820368147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 153365886034312457708630117 28756103631433585820368147)
  ·
    refine ⟨43134155447150378730552221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28756103631433585820368147 43134155447150378730552221)
    ·
      refine ⟨16175308292681392023957083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43134155447150378730552221 16175308292681392023957083)
      ·
        refine ⟨24262962439022088035935625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16175308292681392023957083 24262962439022088035935625)
        ·
          refine ⟨18197221829266566026951719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24262962439022088035935625 18197221829266566026951719)
          ·
            refine ⟨27295832743899849040427579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18197221829266566026951719 27295832743899849040427579)
            ·
              refine ⟨40943749115849773560641369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27295832743899849040427579 40943749115849773560641369)
              ·
                refine ⟨30707811836887330170481027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40943749115849773560641369 30707811836887330170481027)
                ·
                  refine ⟨46061717755330995255721541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30707811836887330170481027 46061717755330995255721541)
                  ·
                    refine ⟨8636572079124561610447789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 46061717755330995255721541 8636572079124561610447789)
                    ·
                      refine ⟨3238714529671710603917921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8636572079124561610447789 3238714529671710603917921)
                      ·
                        rfl

theorem cell23_6307374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 2, 1, 4, 3].length) (baseStart_6307374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6307374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6307374 prefixEnd_6307374 := by exact prefixLift 6307374
  have htrace : WordTrace (prefixWord ++ tailWord_6307374) baseStart_6307374 baseEnd_6307374 := by
    simpa [prefixWord, tailWord_6307374, baseEnd_6307374] using wordTrace_append hprefix tailTrace_6307374
  have hstable : (prefixWord ++ tailWord_6307374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6307374).length < 2 ^ (prefixWord ++ tailWord_6307374).sum := by decide
  have hdescent : baseEnd_6307374 < baseStart_6307374 := by decide
  rcases family_descends (prefixWord ++ tailWord_6307374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6307461 : List Nat := [1, 3, 1, 1, 4, 1, 5, 1, 1, 1, 4]
def baseStart_6307461 : Nat := 118140960795 + 6307461 * 2 ^ 59
def prefixEnd_6307461 : Nat := 4983230072969 + 3 ^ 40 * 6307461 * 2
def baseEnd_6307461 : Nat := 3238759202488651763530021

theorem tailTrace_6307461 : CollatzResearch.WordTrace tailWord_6307461 prefixEnd_6307461 3238759202488651763530021 := by
  unfold tailWord_6307461
  simp only [CollatzResearch.WordTrace]
  refine ⟨230052002202153500421362237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153368001468102333614241491 230052002202153500421362237)
  ·
    refine ⟨86269500825807562658010839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 230052002202153500421362237 86269500825807562658010839)
    ·
      refine ⟨129404251238711343987016259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86269500825807562658010839 129404251238711343987016259)
      ·
        refine ⟨194106376858067015980524389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129404251238711343987016259 194106376858067015980524389)
        ·
          refine ⟨36394945660887565496348323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 194106376858067015980524389 36394945660887565496348323)
          ·
            refine ⟨54592418491331348244522485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36394945660887565496348323 54592418491331348244522485)
            ·
              refine ⟨5118039233562313897923983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 54592418491331348244522485 5118039233562313897923983)
              ·
                refine ⟨7677058850343470846885975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5118039233562313897923983 7677058850343470846885975)
                ·
                  refine ⟨11515588275515206270328963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7677058850343470846885975 11515588275515206270328963)
                  ·
                    refine ⟨17273382413272809405493445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11515588275515206270328963 17273382413272809405493445)
                    ·
                      refine ⟨3238759202488651763530021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17273382413272809405493445 3238759202488651763530021)
                      ·
                        rfl

theorem cell23_6307461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 5, 1, 1, 1, 4].length) (baseStart_6307461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6307461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6307461 prefixEnd_6307461 := by exact prefixLift 6307461
  have htrace : WordTrace (prefixWord ++ tailWord_6307461) baseStart_6307461 baseEnd_6307461 := by
    simpa [prefixWord, tailWord_6307461, baseEnd_6307461] using wordTrace_append hprefix tailTrace_6307461
  have hstable : (prefixWord ++ tailWord_6307461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6307461).length < 2 ^ (prefixWord ++ tailWord_6307461).sum := by decide
  have hdescent : baseEnd_6307461 < baseStart_6307461 := by decide
  rcases family_descends (prefixWord ++ tailWord_6307461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6307507 : List Nat := [1, 1, 1, 2, 3, 3, 2, 1, 2, 2, 5]
def baseStart_6307507 : Nat := 118140960795 + 6307507 * 2 ^ 59
def prefixEnd_6307507 : Nat := 4983230072969 + 3 ^ 40 * 6307507 * 2
def baseEnd_6307507 : Nat := 3238782822598758583554809

theorem tailTrace_6307507 : CollatzResearch.WordTrace tailWord_6307507 prefixEnd_6307507 3238782822598758583554809 := by
  unfold tailWord_6307507
  simp only [CollatzResearch.WordTrace]
  refine ⟨230053679959986850277536775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153369119973324566851691183 230053679959986850277536775)
  ·
    refine ⟨345080519939980275416305163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230053679959986850277536775 345080519939980275416305163)
    ·
      refine ⟨517620779909970413124457745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 345080519939980275416305163 517620779909970413124457745)
      ·
        refine ⟨388215584932477809843343309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 517620779909970413124457745 388215584932477809843343309)
        ·
          refine ⟨145580844349679178691253741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 388215584932477809843343309 145580844349679178691253741)
          ·
            refine ⟨54592816631129692009220153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 145580844349679178691253741 54592816631129692009220153)
            ·
              refine ⟨40944612473347269006915115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54592816631129692009220153 40944612473347269006915115)
              ·
                refine ⟨61416918710020903510372673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40944612473347269006915115 61416918710020903510372673)
                ·
                  refine ⟨46062689032515677632779505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 61416918710020903510372673 46062689032515677632779505)
                  ·
                    refine ⟨34547016774386758224584629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 46062689032515677632779505 34547016774386758224584629)
                    ·
                      refine ⟨3238782822598758583554809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34547016774386758224584629 3238782822598758583554809)
                      ·
                        rfl

theorem cell23_6307507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 1, 2, 2, 5].length) (baseStart_6307507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6307507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6307507 prefixEnd_6307507 := by exact prefixLift 6307507
  have htrace : WordTrace (prefixWord ++ tailWord_6307507) baseStart_6307507 baseEnd_6307507 := by
    simpa [prefixWord, tailWord_6307507, baseEnd_6307507] using wordTrace_append hprefix tailTrace_6307507
  have hstable : (prefixWord ++ tailWord_6307507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6307507).length < 2 ^ (prefixWord ++ tailWord_6307507).sum := by decide
  have hdescent : baseEnd_6307507 < baseStart_6307507 := by decide
  rcases family_descends (prefixWord ++ tailWord_6307507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6307527 : List Nat := [1, 1, 4, 1, 1, 1, 3, 1, 4, 6]
def baseStart_6307527 : Nat := 118140960795 + 6307527 * 2 ^ 59
def prefixEnd_6307527 : Nat := 4983230072969 + 3 ^ 40 * 6307527 * 2
def baseEnd_6307527 : Nat := 1079597697403949501768239

theorem tailTrace_6307527 : CollatzResearch.WordTrace tailWord_6307527 prefixEnd_6307527 1079597697403949501768239 := by
  unfold tailWord_6307527
  simp only [CollatzResearch.WordTrace]
  refine ⟨230054409419914393693264835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153369606279942929128843223 230054409419914393693264835)
  ·
    refine ⟨345081614129871590539897253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230054409419914393693264835 345081614129871590539897253)
    ·
      refine ⟨64702802649350923226230735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 345081614129871590539897253 64702802649350923226230735)
      ·
        refine ⟨97054203974026384839346103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64702802649350923226230735 97054203974026384839346103)
        ·
          refine ⟨145581305961039577259019155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97054203974026384839346103 145581305961039577259019155)
          ·
            refine ⟨218371958941559365888528733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 145581305961039577259019155 218371958941559365888528733)
            ·
              refine ⟨81889484603084762208198275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 218371958941559365888528733 81889484603084762208198275)
              ·
                refine ⟨122834226904627143312297413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81889484603084762208198275 122834226904627143312297413)
                ·
                  refine ⟨23031417544617589371055765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 122834226904627143312297413 23031417544617589371055765)
                  ·
                    refine ⟨1079597697403949501768239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23031417544617589371055765 1079597697403949501768239)
                    ·
                      rfl

theorem cell23_6307527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 1, 4, 6].length) (baseStart_6307527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6307527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6307527 prefixEnd_6307527 := by exact prefixLift 6307527
  have htrace : WordTrace (prefixWord ++ tailWord_6307527) baseStart_6307527 baseEnd_6307527 := by
    simpa [prefixWord, tailWord_6307527, baseEnd_6307527] using wordTrace_append hprefix tailTrace_6307527
  have hstable : (prefixWord ++ tailWord_6307527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6307527).length < 2 ^ (prefixWord ++ tailWord_6307527).sum := by decide
  have hdescent : baseEnd_6307527 < baseStart_6307527 := by decide
  rcases family_descends (prefixWord ++ tailWord_6307527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6307542 : List Nat := [5, 2, 1, 3, 2, 1, 1, 1, 1, 2, 4]
def baseStart_6307542 : Nat := 118140960795 + 6307542 * 2 ^ 59
def prefixEnd_6307542 : Nat := 4983230072969 + 3 ^ 40 * 6307542 * 2
def baseEnd_6307542 : Nat := 3238800794421665946617149

theorem tailTrace_6307542 : CollatzResearch.WordTrace tailWord_6307542 prefixEnd_6307542 3238800794421665946617149 := by
  unfold tailWord_6307542
  simp only [CollatzResearch.WordTrace]
  refine ⟨14378434782178753203441305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 153369971009906700836707253 14378434782178753203441305)
  ·
    refine ⟨10783826086634064902580979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14378434782178753203441305 10783826086634064902580979)
    ·
      refine ⟨16175739129951097353871469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10783826086634064902580979 16175739129951097353871469)
      ·
        refine ⟨6065902173731661507701801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16175739129951097353871469 6065902173731661507701801)
        ·
          refine ⟨4549426630298746130776351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6065902173731661507701801 4549426630298746130776351)
          ·
            refine ⟨6824139945448119196164527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4549426630298746130776351 6824139945448119196164527)
            ·
              refine ⟨10236209918172178794246791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6824139945448119196164527 10236209918172178794246791)
              ·
                refine ⟨15354314877258268191370187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10236209918172178794246791 15354314877258268191370187)
                ·
                  refine ⟨23031472315887402287055281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15354314877258268191370187 23031472315887402287055281)
                  ·
                    refine ⟨17273604236915551715291461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23031472315887402287055281 17273604236915551715291461)
                    ·
                      refine ⟨3238800794421665946617149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17273604236915551715291461 3238800794421665946617149)
                      ·
                        rfl

theorem cell23_6307542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 2, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 2, 1, 1, 1, 1, 2, 4].length) (baseStart_6307542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6307542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6307542 prefixEnd_6307542 := by exact prefixLift 6307542
  have htrace : WordTrace (prefixWord ++ tailWord_6307542) baseStart_6307542 baseEnd_6307542 := by
    simpa [prefixWord, tailWord_6307542, baseEnd_6307542] using wordTrace_append hprefix tailTrace_6307542
  have hstable : (prefixWord ++ tailWord_6307542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6307542).length < 2 ^ (prefixWord ++ tailWord_6307542).sum := by decide
  have hdescent : baseEnd_6307542 < baseStart_6307542 := by decide
  rcases family_descends (prefixWord ++ tailWord_6307542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6307555 : List Nat := [1, 1, 1, 7, 2, 1, 2, 2, 1, 3, 2]
def baseStart_6307555 : Nat := 118140960795 + 6307555 * 2 ^ 59
def prefixEnd_6307555 : Nat := 4983230072969 + 3 ^ 40 * 6307555 * 2
def baseEnd_6307555 : Nat := 3238807469670174395754589

theorem tailTrace_6307555 : CollatzResearch.WordTrace tailWord_6307555 prefixEnd_6307555 3238807469670174395754589 := by
  unfold tailWord_6307555
  simp only [CollatzResearch.WordTrace]
  refine ⟨230055430663812954475284119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153370287109208636316856079 230055430663812954475284119)
  ·
    refine ⟨345083145995719431712926179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230055430663812954475284119 345083145995719431712926179)
    ·
      refine ⟨517624718993579147569389269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 345083145995719431712926179 517624718993579147569389269)
      ·
        refine ⟨12131829351412011271157561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 517624718993579147569389269 12131829351412011271157561)
        ·
          refine ⟨9098872013559008453368171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12131829351412011271157561 9098872013559008453368171)
          ·
            refine ⟨13648308020338512680052257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9098872013559008453368171 13648308020338512680052257)
            ·
              refine ⟨10236231015253884510039193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13648308020338512680052257 10236231015253884510039193)
              ·
                refine ⟨7677173261440413382529395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10236231015253884510039193 7677173261440413382529395)
                ·
                  refine ⟨11515759892160620073794093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7677173261440413382529395 11515759892160620073794093)
                  ·
                    refine ⟨4318409959560232527672785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11515759892160620073794093 4318409959560232527672785)
                    ·
                      refine ⟨3238807469670174395754589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4318409959560232527672785 3238807469670174395754589)
                      ·
                        rfl

theorem cell23_6307555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 2, 2, 1, 3, 2].length) (baseStart_6307555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6307555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6307555 prefixEnd_6307555 := by exact prefixLift 6307555
  have htrace : WordTrace (prefixWord ++ tailWord_6307555) baseStart_6307555 baseEnd_6307555 := by
    simpa [prefixWord, tailWord_6307555, baseEnd_6307555] using wordTrace_append hprefix tailTrace_6307555
  have hstable : (prefixWord ++ tailWord_6307555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6307555).length < 2 ^ (prefixWord ++ tailWord_6307555).sum := by decide
  have hdescent : baseEnd_6307555 < baseStart_6307555 := by decide
  rcases family_descends (prefixWord ++ tailWord_6307555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6307572 : List Nat := [2, 6, 1, 1, 1, 1, 2, 3, 1, 3, 2]
def baseStart_6307572 : Nat := 118140960795 + 6307572 * 2 ^ 59
def prefixEnd_6307572 : Nat := 4983230072969 + 3 ^ 40 * 6307572 * 2
def baseEnd_6307572 : Nat := 3238816198841300829242011

theorem tailTrace_6307572 : CollatzResearch.WordTrace tailWord_6307572 prefixEnd_6307572 3238816198841300829242011 := by
  unfold tailWord_6307572
  simp only [CollatzResearch.WordTrace]
  refine ⟨115028025352375683189326485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153370700469834244252435313 115028025352375683189326485)
  ·
    refine ⟨5391938688392610149499679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 115028025352375683189326485 5391938688392610149499679)
    ·
      refine ⟨8087908032588915224249519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5391938688392610149499679 8087908032588915224249519)
      ·
        refine ⟨12131862048883372836374279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8087908032588915224249519 12131862048883372836374279)
        ·
          refine ⟨18197793073325059254561419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12131862048883372836374279 18197793073325059254561419)
          ·
            refine ⟨27296689609987588881842129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18197793073325059254561419 27296689609987588881842129)
            ·
              refine ⟨20472517207490691661381597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27296689609987588881842129 20472517207490691661381597)
              ·
                refine ⟨7677193952809009373018099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20472517207490691661381597 7677193952809009373018099)
                ·
                  refine ⟨11515790929213514059527149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7677193952809009373018099 11515790929213514059527149)
                  ·
                    refine ⟨4318421598455067772322681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11515790929213514059527149 4318421598455067772322681)
                    ·
                      refine ⟨3238816198841300829242011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4318421598455067772322681 3238816198841300829242011)
                      ·
                        rfl

theorem cell23_6307572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 2, 3, 1, 3, 2].length) (baseStart_6307572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6307572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6307572 prefixEnd_6307572 := by exact prefixLift 6307572
  have htrace : WordTrace (prefixWord ++ tailWord_6307572) baseStart_6307572 baseEnd_6307572 := by
    simpa [prefixWord, tailWord_6307572, baseEnd_6307572] using wordTrace_append hprefix tailTrace_6307572
  have hstable : (prefixWord ++ tailWord_6307572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6307572).length < 2 ^ (prefixWord ++ tailWord_6307572).sum := by decide
  have hdescent : baseEnd_6307572 < baseStart_6307572 := by decide
  rcases family_descends (prefixWord ++ tailWord_6307572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6307577 : List Nat := [1, 2, 1, 3, 1, 1, 1, 1, 2, 4, 6]
def baseStart_6307577 : Nat := 118140960795 + 6307577 * 2 ^ 59
def prefixEnd_6307577 : Nat := 4983230072969 + 3 ^ 40 * 6307577 * 2
def baseEnd_6307577 : Nat := 3238818766244573309679487

theorem tailTrace_6307577 : CollatzResearch.WordTrace tailWord_6307577 prefixEnd_6307577 3238818766244573309679487 := by
  unfold tailWord_6307577
  simp only [CollatzResearch.WordTrace]
  refine ⟨230056233069733252232584985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153370822046488834821723323 230056233069733252232584985)
  ·
    refine ⟨172542174802299939174438739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 230056233069733252232584985 172542174802299939174438739)
    ·
      refine ⟨258813262203449908761658109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172542174802299939174438739 258813262203449908761658109)
      ·
        refine ⟨97054973326293715785621791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 258813262203449908761658109 97054973326293715785621791)
        ·
          refine ⟨145582459989440573678432687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97054973326293715785621791 145582459989440573678432687)
          ·
            refine ⟨218373689984160860517649031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 145582459989440573678432687 218373689984160860517649031)
            ·
              refine ⟨327560534976241290776473547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 218373689984160860517649031 327560534976241290776473547)
              ·
                refine ⟨491340802464361936164710321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 327560534976241290776473547 491340802464361936164710321)
                ·
                  refine ⟨368505601848271452123532741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 491340802464361936164710321 368505601848271452123532741)
                  ·
                    refine ⟨69094800346550897273162389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 368505601848271452123532741 69094800346550897273162389)
                    ·
                      refine ⟨3238818766244573309679487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 69094800346550897273162389 3238818766244573309679487)
                      ·
                        rfl

theorem cell23_6307577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 1, 2, 4, 6].length) (baseStart_6307577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6307577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6307577 prefixEnd_6307577 := by exact prefixLift 6307577
  have htrace : WordTrace (prefixWord ++ tailWord_6307577) baseStart_6307577 baseEnd_6307577 := by
    simpa [prefixWord, tailWord_6307577, baseEnd_6307577] using wordTrace_append hprefix tailTrace_6307577
  have hstable : (prefixWord ++ tailWord_6307577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6307577).length < 2 ^ (prefixWord ++ tailWord_6307577).sum := by decide
  have hdescent : baseEnd_6307577 < baseStart_6307577 := by decide
  rcases family_descends (prefixWord ++ tailWord_6307577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6307602 : List Nat := [3, 2, 4, 1, 1, 2, 1, 3, 2, 2, 2]
def baseStart_6307602 : Nat := 118140960795 + 6307602 * 2 ^ 59
def prefixEnd_6307602 : Nat := 4983230072969 + 3 ^ 40 * 6307602 * 2
def baseEnd_6307602 : Nat := 3238831603260935711866873

theorem tailTrace_6307602 : CollatzResearch.WordTrace tailWord_6307602 prefixEnd_6307602 3238831603260935711866873 := by
  unfold tailWord_6307602
  simp only [CollatzResearch.WordTrace]
  refine ⟨57514286223660670375561265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153371429929761787668163373 57514286223660670375561265)
  ·
    refine ⟨43135714667745502781670949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57514286223660670375561265 43135714667745502781670949)
    ·
      refine ⟨8087946500202281771563303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43135714667745502781670949 8087946500202281771563303)
      ·
        refine ⟨12131919750303422657344955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8087946500202281771563303 12131919750303422657344955)
        ·
          refine ⟨18197879625455133986017433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12131919750303422657344955 18197879625455133986017433)
          ·
            refine ⟨13648409719091350489513075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18197879625455133986017433 13648409719091350489513075)
            ·
              refine ⟨20472614578637025734269613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13648409719091350489513075 20472614578637025734269613)
              ·
                refine ⟨7677230466988884650351105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20472614578637025734269613 7677230466988884650351105)
                ·
                  refine ⟨5757922850241663487763329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7677230466988884650351105 5757922850241663487763329)
                  ·
                    refine ⟨4318442137681247615822497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5757922850241663487763329 4318442137681247615822497)
                    ·
                      refine ⟨3238831603260935711866873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4318442137681247615822497 3238831603260935711866873)
                      ·
                        rfl

theorem cell23_6307602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 1, 3, 2, 2, 2].length) (baseStart_6307602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6307602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6307602 prefixEnd_6307602 := by exact prefixLift 6307602
  have htrace : WordTrace (prefixWord ++ tailWord_6307602) baseStart_6307602 baseEnd_6307602 := by
    simpa [prefixWord, tailWord_6307602, baseEnd_6307602] using wordTrace_append hprefix tailTrace_6307602
  have hstable : (prefixWord ++ tailWord_6307602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6307602).length < 2 ^ (prefixWord ++ tailWord_6307602).sum := by decide
  have hdescent : baseEnd_6307602 < baseStart_6307602 := by decide
  rcases family_descends (prefixWord ++ tailWord_6307602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6307621 : List Nat := [1, 3, 1, 2, 3, 3, 2, 1, 2, 5]
def baseStart_6307621 : Nat := 118140960795 + 6307621 * 2 ^ 59
def prefixEnd_6307621 : Nat := 4983230072969 + 3 ^ 40 * 6307621 * 2
def baseEnd_6307621 : Nat := 1079613786464457045843095

theorem tailTrace_6307621 : CollatzResearch.WordTrace tailWord_6307621 prefixEnd_6307621 1079613786464457045843095 := by
  unfold tailWord_6307621
  simp only [CollatzResearch.WordTrace]
  refine ⟨230057837881573847747186717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153371891921049231831457811 230057837881573847747186717)
  ·
    refine ⟨86271689205590192905195019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 230057837881573847747186717 86271689205590192905195019)
    ·
      refine ⟨129407533808385289357792529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86271689205590192905195019 129407533808385289357792529)
      ·
        refine ⟨97055650356288967018344397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129407533808385289357792529 97055650356288967018344397)
        ·
          refine ⟨36395868883608362631879149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 97055650356288967018344397 36395868883608362631879149)
          ·
            refine ⟨13648450831353135986954681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36395868883608362631879149 13648450831353135986954681)
            ·
              refine ⟨10236338123514851990216011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13648450831353135986954681 10236338123514851990216011)
              ·
                refine ⟨15354507185272277985324017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10236338123514851990216011 15354507185272277985324017)
                ·
                  refine ⟨11515880388954208488993013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15354507185272277985324017 11515880388954208488993013)
                  ·
                    refine ⟨1079613786464457045843095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11515880388954208488993013 1079613786464457045843095)
                    ·
                      rfl

theorem cell23_6307621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 2, 1, 2, 5].length) (baseStart_6307621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6307621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6307621 prefixEnd_6307621 := by exact prefixLift 6307621
  have htrace : WordTrace (prefixWord ++ tailWord_6307621) baseStart_6307621 baseEnd_6307621 := by
    simpa [prefixWord, tailWord_6307621, baseEnd_6307621] using wordTrace_append hprefix tailTrace_6307621
  have hstable : (prefixWord ++ tailWord_6307621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6307621).length < 2 ^ (prefixWord ++ tailWord_6307621).sum := by decide
  have hdescent : baseEnd_6307621 < baseStart_6307621 := by decide
  rcases family_descends (prefixWord ++ tailWord_6307621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6307638 : List Nat := [5, 1, 2, 2, 1, 1, 2, 2, 2, 5]
def baseStart_6307638 : Nat := 118140960795 + 6307638 * 2 ^ 59
def prefixEnd_6307638 : Nat := 4983230072969 + 3 ^ 40 * 6307638 * 2
def baseEnd_6307638 : Nat := 1079616696188165857005569

theorem tailTrace_6307638 : CollatzResearch.WordTrace tailWord_6307638 prefixEnd_6307638 1079616696188165857005569 := by
  unfold tailWord_6307638
  simp only [CollatzResearch.WordTrace]
  refine ⟨14378653620157016228159723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 153372305281674839767037045 14378653620157016228159723)
  ·
    refine ⟨21567980430235524342239585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14378653620157016228159723 21567980430235524342239585)
    ·
      refine ⟨16175985322676643256679689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21567980430235524342239585 16175985322676643256679689)
      ·
        refine ⟨12131988992007482442509767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16175985322676643256679689 12131988992007482442509767)
        ·
          refine ⟨18197983488011223663764651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12131988992007482442509767 18197983488011223663764651)
          ·
            refine ⟨27296975232016835495646977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18197983488011223663764651 27296975232016835495646977)
            ·
              refine ⟨20472731424012626621735233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27296975232016835495646977 20472731424012626621735233)
              ·
                refine ⟨15354548568009469966301425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20472731424012626621735233 15354548568009469966301425)
                ·
                  refine ⟨11515911426007102474726069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15354548568009469966301425 11515911426007102474726069)
                  ·
                    refine ⟨1079616696188165857005569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11515911426007102474726069 1079616696188165857005569)
                    ·
                      rfl

theorem cell23_6307638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 2, 2, 2, 5].length) (baseStart_6307638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6307638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6307638 prefixEnd_6307638 := by exact prefixLift 6307638
  have htrace : WordTrace (prefixWord ++ tailWord_6307638) baseStart_6307638 baseEnd_6307638 := by
    simpa [prefixWord, tailWord_6307638, baseEnd_6307638] using wordTrace_append hprefix tailTrace_6307638
  have hstable : (prefixWord ++ tailWord_6307638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6307638).length < 2 ^ (prefixWord ++ tailWord_6307638).sum := by decide
  have hdescent : baseEnd_6307638 < baseStart_6307638 := by decide
  rcases family_descends (prefixWord ++ tailWord_6307638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6307668 : List Nat := [2, 4, 1, 1, 3, 2, 1, 2, 3, 4]
def baseStart_6307668 : Nat := 118140960795 + 6307668 * 2 ^ 59
def prefixEnd_6307668 : Nat := 4983230072969 + 3 ^ 40 * 6307668 * 2
def baseEnd_6307668 : Nat := 1079621830994710817880523

theorem tailTrace_6307668 : CollatzResearch.WordTrace tailWord_6307668 prefixEnd_6307668 1079621830994710817880523 := by
  unfold tailWord_6307668
  simp only [CollatzResearch.WordTrace]
  refine ⟨115029776056201787387073829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153373034741602383182765105 115029776056201787387073829)
  ·
    refine ⟨21568083010537835135076343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 115029776056201787387073829 21568083010537835135076343)
    ·
      refine ⟨32352124515806752702614515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21568083010537835135076343 32352124515806752702614515)
      ·
        refine ⟨48528186773710129053921773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32352124515806752702614515 48528186773710129053921773)
        ·
          refine ⟨18198070040141298395220665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48528186773710129053921773 18198070040141298395220665)
          ·
            refine ⟨13648552530105973796415499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18198070040141298395220665 13648552530105973796415499)
            ·
              refine ⟨20472828795158960694623249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13648552530105973796415499 20472828795158960694623249)
              ·
                refine ⟨15354621596369220520967437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20472828795158960694623249 15354621596369220520967437)
                ·
                  refine ⟨5757983098638457695362789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15354621596369220520967437 5757983098638457695362789)
                  ·
                    refine ⟨1079621830994710817880523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5757983098638457695362789 1079621830994710817880523)
                    ·
                      rfl

theorem cell23_6307668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 1, 2, 3, 4].length) (baseStart_6307668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6307668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6307668 prefixEnd_6307668 := by exact prefixLift 6307668
  have htrace : WordTrace (prefixWord ++ tailWord_6307668) baseStart_6307668 baseEnd_6307668 := by
    simpa [prefixWord, tailWord_6307668, baseEnd_6307668] using wordTrace_append hprefix tailTrace_6307668
  have hstable : (prefixWord ++ tailWord_6307668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6307668).length < 2 ^ (prefixWord ++ tailWord_6307668).sum := by decide
  have hdescent : baseEnd_6307668 < baseStart_6307668 := by decide
  rcases family_descends (prefixWord ++ tailWord_6307668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6307691 : List Nat := [1, 1, 1, 1, 2, 2, 3, 1, 7, 1, 3]
def baseStart_6307691 : Nat := 118140960795 + 6307691 * 2 ^ 59
def prefixEnd_6307691 : Nat := 4983230072969 + 3 ^ 40 * 6307691 * 2
def baseEnd_6307691 : Nat := 3238877303039185863653963

theorem tailTrace_6307691 : CollatzResearch.WordTrace tailWord_6307691 prefixEnd_6307691 3238877303039185863653963 := by
  unfold tailWord_6307691
  simp only [CollatzResearch.WordTrace]
  refine ⟨230060390991320249702234927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153373593994213499801489951 230060390991320249702234927)
  ·
    refine ⟨345090586486980374553352391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230060390991320249702234927 345090586486980374553352391)
    ·
      refine ⟨517635879730470561830028587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 345090586486980374553352391 517635879730470561830028587)
      ·
        refine ⟨776453819595705842745042881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 517635879730470561830028587 776453819595705842745042881)
        ·
          refine ⟨582340364696779382058782161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 776453819595705842745042881 582340364696779382058782161)
          ·
            refine ⟨436755273522584536544086621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 582340364696779382058782161 436755273522584536544086621)
            ·
              refine ⟨163783227570969201204032483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 436755273522584536544086621 163783227570969201204032483)
              ·
                refine ⟨245674841356453801806048725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 163783227570969201204032483 245674841356453801806048725)
                ·
                  refine ⟨5758004094291885979829267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 245674841356453801806048725 5758004094291885979829267)
                  ·
                    refine ⟨8637006141437828969743901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5758004094291885979829267 8637006141437828969743901)
                    ·
                      refine ⟨3238877303039185863653963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8637006141437828969743901 3238877303039185863653963)
                      ·
                        rfl

theorem cell23_6307691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 1, 7, 1, 3].length) (baseStart_6307691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6307691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6307691 prefixEnd_6307691 := by exact prefixLift 6307691
  have htrace : WordTrace (prefixWord ++ tailWord_6307691) baseStart_6307691 baseEnd_6307691 := by
    simpa [prefixWord, tailWord_6307691, baseEnd_6307691] using wordTrace_append hprefix tailTrace_6307691
  have hstable : (prefixWord ++ tailWord_6307691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6307691).length < 2 ^ (prefixWord ++ tailWord_6307691).sum := by decide
  have hdescent : baseEnd_6307691 < baseStart_6307691 := by decide
  rcases family_descends (prefixWord ++ tailWord_6307691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6307748 : List Nat := [2, 3, 1, 2, 1, 3, 2, 3, 1, 1, 4]
def baseStart_6307748 : Nat := 118140960795 + 6307748 * 2 ^ 59
def prefixEnd_6307748 : Nat := 4983230072969 + 3 ^ 40 * 6307748 * 2
def baseEnd_6307748 : Nat := 3238906571436492140641201

theorem tailTrace_6307748 : CollatzResearch.WordTrace tailWord_6307748 prefixEnd_6307748 3238906571436492140641201 := by
  unfold tailWord_6307748
  simp only [CollatzResearch.WordTrace]
  refine ⟨115031234976056874218529949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153374979968075832291373265 115031234976056874218529949)
  ·
    refine ⟨43136713116021327831948731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115031234976056874218529949 43136713116021327831948731)
    ·
      refine ⟨64705069674031991747923097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43136713116021327831948731 64705069674031991747923097)
      ·
        refine ⟨48528802255523993810942323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64705069674031991747923097 48528802255523993810942323)
        ·
          refine ⟨72793203383285990716413485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48528802255523993810942323 72793203383285990716413485)
          ·
            refine ⟨27297451268732246518655057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72793203383285990716413485 27297451268732246518655057)
            ·
              refine ⟨20473088451549184888991293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27297451268732246518655057 20473088451549184888991293)
              ·
                refine ⟨7677408169330944333371735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20473088451549184888991293 7677408169330944333371735)
                ·
                  refine ⟨11516112253996416500057603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7677408169330944333371735 11516112253996416500057603)
                  ·
                    refine ⟨17274168380994624750086405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11516112253996416500057603 17274168380994624750086405)
                    ·
                      refine ⟨3238906571436492140641201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17274168380994624750086405 3238906571436492140641201)
                      ·
                        rfl

theorem cell23_6307748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 2, 3, 1, 1, 4].length) (baseStart_6307748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6307748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6307748 prefixEnd_6307748 := by exact prefixLift 6307748
  have htrace : WordTrace (prefixWord ++ tailWord_6307748) baseStart_6307748 baseEnd_6307748 := by
    simpa [prefixWord, tailWord_6307748, baseEnd_6307748] using wordTrace_append hprefix tailTrace_6307748
  have hstable : (prefixWord ++ tailWord_6307748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6307748).length < 2 ^ (prefixWord ++ tailWord_6307748).sum := by decide
  have hdescent : baseEnd_6307748 < baseStart_6307748 := by decide
  rcases family_descends (prefixWord ++ tailWord_6307748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6307761 : List Nat := [1, 2, 2, 4, 2, 1, 1, 2, 1, 1, 6]
def baseStart_6307761 : Nat := 118140960795 + 6307761 * 2 ^ 59
def prefixEnd_6307761 : Nat := 4983230072969 + 3 ^ 40 * 6307761 * 2
def baseEnd_6307761 : Nat := 3238913246685000589778641

theorem tailTrace_6307761 : CollatzResearch.WordTrace tailWord_6307761 prefixEnd_6307761 3238913246685000589778641 := by
  unfold tailWord_6307761
  simp only [CollatzResearch.WordTrace]
  refine ⟨230062944101066651657283137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153375296067377767771522091 230062944101066651657283137)
  ·
    refine ⟨172547208075799988742962353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 230062944101066651657283137 172547208075799988742962353)
    ·
      refine ⟨129410406056849991557221765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 172547208075799988742962353 129410406056849991557221765)
      ·
        refine ⟨24264451135659373416979081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 129410406056849991557221765 24264451135659373416979081)
        ·
          refine ⟨18198338351744530062734311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24264451135659373416979081 18198338351744530062734311)
          ·
            refine ⟨27297507527616795094101467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18198338351744530062734311 27297507527616795094101467)
            ·
              refine ⟨40946261291425192641152201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27297507527616795094101467 40946261291425192641152201)
              ·
                refine ⟨30709695968568894480864151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40946261291425192641152201 30709695968568894480864151)
                ·
                  refine ⟨46064543952853341721296227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30709695968568894480864151 46064543952853341721296227)
                  ·
                    refine ⟨69096815929280012581944341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 46064543952853341721296227 69096815929280012581944341)
                    ·
                      refine ⟨3238913246685000589778641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 69096815929280012581944341 3238913246685000589778641)
                      ·
                        rfl

theorem cell23_6307761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 2, 1, 1, 6].length) (baseStart_6307761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6307761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6307761 prefixEnd_6307761 := by exact prefixLift 6307761
  have htrace : WordTrace (prefixWord ++ tailWord_6307761) baseStart_6307761 baseEnd_6307761 := by
    simpa [prefixWord, tailWord_6307761, baseEnd_6307761] using wordTrace_append hprefix tailTrace_6307761
  have hstable : (prefixWord ++ tailWord_6307761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6307761).length < 2 ^ (prefixWord ++ tailWord_6307761).sum := by decide
  have hdescent : baseEnd_6307761 < baseStart_6307761 := by decide
  rcases family_descends (prefixWord ++ tailWord_6307761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6307802 : List Nat := [3, 1, 1, 2, 5, 1, 3, 1, 1, 2, 3]
def baseStart_6307802 : Nat := 118140960795 + 6307802 * 2 ^ 59
def prefixEnd_6307802 : Nat := 4983230072969 + 3 ^ 40 * 6307802 * 2
def baseEnd_6307802 : Nat := 3238934299391834929365953

theorem tailTrace_6307802 : CollatzResearch.WordTrace tailWord_6307802 prefixEnd_6307802 3238934299391834929365953 := by
  unfold tailWord_6307802
  simp only [CollatzResearch.WordTrace]
  refine ⟨57516109873479528914881415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153376292995945410439683773 57516109873479528914881415)
  ·
    refine ⟨86274164810219293372322123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57516109873479528914881415 86274164810219293372322123)
    ·
      refine ⟨129411247215328940058483185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86274164810219293372322123 129411247215328940058483185)
      ·
        refine ⟨97058435411496705043862389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129411247215328940058483185 97058435411496705043862389)
        ·
          refine ⟨9099228319827816097862099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 97058435411496705043862389 9099228319827816097862099)
          ·
            refine ⟨13648842479741724146793149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9099228319827816097862099 13648842479741724146793149)
            ·
              refine ⟨5118315929903146555047431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13648842479741724146793149 5118315929903146555047431)
              ·
                refine ⟨7677473894854719832571147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5118315929903146555047431 7677473894854719832571147)
                ·
                  refine ⟨11516210842282079748856721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7677473894854719832571147 11516210842282079748856721)
                  ·
                    refine ⟨8637158131711559811642541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11516210842282079748856721 8637158131711559811642541)
                    ·
                      refine ⟨3238934299391834929365953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8637158131711559811642541 3238934299391834929365953)
                      ·
                        rfl

theorem cell23_6307802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 3, 1, 1, 2, 3].length) (baseStart_6307802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6307802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6307802 prefixEnd_6307802 := by exact prefixLift 6307802
  have htrace : WordTrace (prefixWord ++ tailWord_6307802) baseStart_6307802 baseEnd_6307802 := by
    simpa [prefixWord, tailWord_6307802, baseEnd_6307802] using wordTrace_append hprefix tailTrace_6307802
  have hstable : (prefixWord ++ tailWord_6307802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6307802).length < 2 ^ (prefixWord ++ tailWord_6307802).sum := by decide
  have hdescent : baseEnd_6307802 < baseStart_6307802 := by decide
  rcases family_descends (prefixWord ++ tailWord_6307802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6307851 : List Nat := [1, 1, 1, 1, 6, 1, 1, 2, 1, 4, 4]
def baseStart_6307851 : Nat := 118140960795 + 6307851 * 2 ^ 59
def prefixEnd_6307851 : Nat := 4983230072969 + 3 ^ 40 * 6307851 * 2
def baseEnd_6307851 : Nat := 3238959459943905237653227

theorem tailTrace_6307851 : CollatzResearch.WordTrace tailWord_6307851 prefixEnd_6307851 3238959459943905237653227 := by
  unfold tailWord_6307851
  simp only [CollatzResearch.WordTrace]
  refine ⟨230066226670740597028059407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153377484447160398018706271 230066226670740597028059407)
  ·
    refine ⟨345099340006110895542089111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230066226670740597028059407 345099340006110895542089111)
    ·
      refine ⟨517649010009166343313133667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 345099340006110895542089111 517649010009166343313133667)
      ·
        refine ⟨776473515013749514969700501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 517649010009166343313133667 776473515013749514969700501)
        ·
          refine ⟨36397196016269508514204711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 776473515013749514969700501 36397196016269508514204711)
          ·
            refine ⟨54595794024404262771307067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36397196016269508514204711 54595794024404262771307067)
            ·
              refine ⟨81893691036606394156960601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54595794024404262771307067 81893691036606394156960601)
              ·
                refine ⟨61420268277454795617720451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 81893691036606394156960601 61420268277454795617720451)
                ·
                  refine ⟨92130402416182193426580677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61420268277454795617720451 92130402416182193426580677)
                  ·
                    refine ⟨17274450453034161267483877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 92130402416182193426580677 17274450453034161267483877)
                    ·
                      refine ⟨3238959459943905237653227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17274450453034161267483877 3238959459943905237653227)
                      ·
                        rfl

theorem cell23_6307851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 2, 1, 4, 4].length) (baseStart_6307851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6307851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6307851 prefixEnd_6307851 := by exact prefixLift 6307851
  have htrace : WordTrace (prefixWord ++ tailWord_6307851) baseStart_6307851 baseEnd_6307851 := by
    simpa [prefixWord, tailWord_6307851, baseEnd_6307851] using wordTrace_append hprefix tailTrace_6307851
  have hstable : (prefixWord ++ tailWord_6307851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6307851).length < 2 ^ (prefixWord ++ tailWord_6307851).sum := by decide
  have hdescent : baseEnd_6307851 < baseStart_6307851 := by decide
  rcases family_descends (prefixWord ++ tailWord_6307851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6307853 : List Nat := [1, 7, 1, 2, 1, 2, 2, 1, 1, 2, 3]
def baseStart_6307853 : Nat := 118140960795 + 6307853 * 2 ^ 59
def prefixEnd_6307853 : Nat := 4983230072969 + 3 ^ 40 * 6307853 * 2
def baseEnd_6307853 : Nat := 3238960486905214229828219

theorem tailTrace_6307853 : CollatzResearch.WordTrace tailWord_6307853 prefixEnd_6307853 3238960486905214229828219 := by
  unfold tailWord_6307853
  simp only [CollatzResearch.WordTrace]
  refine ⟨230066299616733351369632213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153377533077822234246421475 230066299616733351369632213)
  ·
    refine ⟨5392178897267187922725755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 230066299616733351369632213 5392178897267187922725755)
    ·
      refine ⟨8088268345900781884088633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5392178897267187922725755 8088268345900781884088633)
      ·
        refine ⟨6066201259425586413066475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8088268345900781884088633 6066201259425586413066475)
        ·
          refine ⟨9099301889138379619599713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6066201259425586413066475 9099301889138379619599713)
          ·
            refine ⟨6824476416853784714699785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9099301889138379619599713 6824476416853784714699785)
            ·
              refine ⟨5118357312640338536024839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6824476416853784714699785 5118357312640338536024839)
              ·
                refine ⟨7677535968960507804037259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5118357312640338536024839 7677535968960507804037259)
                ·
                  refine ⟨11516303953440761706055889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7677535968960507804037259 11516303953440761706055889)
                  ·
                    refine ⟨8637227965080571279541917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11516303953440761706055889 8637227965080571279541917)
                    ·
                      refine ⟨3238960486905214229828219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8637227965080571279541917 3238960486905214229828219)
                      ·
                        rfl

theorem cell23_6307853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 2, 2, 1, 1, 2, 3].length) (baseStart_6307853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6307853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6307853 prefixEnd_6307853 := by exact prefixLift 6307853
  have htrace : WordTrace (prefixWord ++ tailWord_6307853) baseStart_6307853 baseEnd_6307853 := by
    simpa [prefixWord, tailWord_6307853, baseEnd_6307853] using wordTrace_append hprefix tailTrace_6307853
  have hstable : (prefixWord ++ tailWord_6307853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6307853).length < 2 ^ (prefixWord ++ tailWord_6307853).sum := by decide
  have hdescent : baseEnd_6307853 < baseStart_6307853 := by decide
  rcases family_descends (prefixWord ++ tailWord_6307853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6307868 : List Nat := [2, 2, 3, 1, 3, 1, 1, 2, 2, 2, 4]
def baseStart_6307868 : Nat := 118140960795 + 6307868 * 2 ^ 59
def prefixEnd_6307868 : Nat := 4983230072969 + 3 ^ 40 * 6307868 * 2
def baseEnd_6307868 : Nat := 3238968189115031671140649

theorem tailTrace_6307868 : CollatzResearch.WordTrace tailWord_6307868 prefixEnd_6307868 3238968189115031671140649 := by
  unfold tailWord_6307868
  simp only [CollatzResearch.WordTrace]
  refine ⟨115033423355839504465714129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153377897807786005954285505 115033423355839504465714129)
  ·
    refine ⟨86275067516879628349285597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115033423355839504465714129 86275067516879628349285597)
    ·
      refine ⟨32353150318829860630982099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86275067516879628349285597 32353150318829860630982099)
      ·
        refine ⟨48529725478244790946473149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32353150318829860630982099 48529725478244790946473149)
        ·
          refine ⟨18198647054341796604927431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48529725478244790946473149 18198647054341796604927431)
          ·
            refine ⟨27297970581512694907391147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18198647054341796604927431 27297970581512694907391147)
            ·
              refine ⟨40946955872269042361086721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27297970581512694907391147 40946955872269042361086721)
              ·
                refine ⟨30710216904201781770815041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40946955872269042361086721 30710216904201781770815041)
                ·
                  refine ⟨23032662678151336328111281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30710216904201781770815041 23032662678151336328111281)
                  ·
                    refine ⟨17274497008613502246083461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23032662678151336328111281 17274497008613502246083461)
                    ·
                      refine ⟨3238968189115031671140649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17274497008613502246083461 3238968189115031671140649)
                      ·
                        rfl

theorem cell23_6307868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 2, 2, 2, 4].length) (baseStart_6307868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6307868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6307868 prefixEnd_6307868 := by exact prefixLift 6307868
  have htrace : WordTrace (prefixWord ++ tailWord_6307868) baseStart_6307868 baseEnd_6307868 := by
    simpa [prefixWord, tailWord_6307868, baseEnd_6307868] using wordTrace_append hprefix tailTrace_6307868
  have hstable : (prefixWord ++ tailWord_6307868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6307868).length < 2 ^ (prefixWord ++ tailWord_6307868).sum := by decide
  have hdescent : baseEnd_6307868 < baseStart_6307868 := by decide
  rcases family_descends (prefixWord ++ tailWord_6307868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6307888 : List Nat := [2, 1, 1, 1, 2, 5, 2, 1, 2, 3, 3]
def baseStart_6307888 : Nat := 118140960795 + 6307888 * 2 ^ 59
def prefixEnd_6307888 : Nat := 4983230072969 + 3 ^ 40 * 6307888 * 2
def baseEnd_6307888 : Nat := 3238978458728121592890557

theorem tailTrace_6307888 : CollatzResearch.WordTrace tailWord_6307888 prefixEnd_6307888 3238978458728121592890557 := by
  unfold tailWord_6307888
  simp only [CollatzResearch.WordTrace]
  refine ⟨115033788085803276173578159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153378384114404368231437545 115033788085803276173578159)
  ·
    refine ⟨172550682128704914260367239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115033788085803276173578159 172550682128704914260367239)
    ·
      refine ⟨258826023193057371390550859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172550682128704914260367239 258826023193057371390550859)
      ·
        refine ⟨388239034789586057085826289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 258826023193057371390550859 388239034789586057085826289)
        ·
          refine ⟨291179276092189542814369717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 388239034789586057085826289 291179276092189542814369717)
          ·
            refine ⟨27298057133642769638847161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 291179276092189542814369717 27298057133642769638847161)
            ·
              refine ⟨20473542850232077229135371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27298057133642769638847161 20473542850232077229135371)
              ·
                refine ⟨30710314275348115843703057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20473542850232077229135371 30710314275348115843703057)
                ·
                  refine ⟨23032735706511086882777293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30710314275348115843703057 23032735706511086882777293)
                  ·
                    refine ⟨8637275889941657581041485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23032735706511086882777293 8637275889941657581041485)
                    ·
                      refine ⟨3238978458728121592890557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8637275889941657581041485 3238978458728121592890557)
                      ·
                        rfl

theorem cell23_6307888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 2, 1, 2, 3, 3].length) (baseStart_6307888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6307888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6307888 prefixEnd_6307888 := by exact prefixLift 6307888
  have htrace : WordTrace (prefixWord ++ tailWord_6307888) baseStart_6307888 baseEnd_6307888 := by
    simpa [prefixWord, tailWord_6307888, baseEnd_6307888] using wordTrace_append hprefix tailTrace_6307888
  have hstable : (prefixWord ++ tailWord_6307888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6307888).length < 2 ^ (prefixWord ++ tailWord_6307888).sum := by decide
  have hdescent : baseEnd_6307888 < baseStart_6307888 := by decide
  rcases family_descends (prefixWord ++ tailWord_6307888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6307889 : List Nat := [1, 2, 2, 3, 1, 4, 3, 1, 2, 2, 2]
def baseStart_6307889 : Nat := 118140960795 + 6307889 * 2 ^ 59
def prefixEnd_6307889 : Nat := 4983230072969 + 3 ^ 40 * 6307889 * 2
def baseEnd_6307889 : Nat := 3238978972208776088978053

theorem tailTrace_6307889 : CollatzResearch.WordTrace tailWord_6307889 prefixEnd_6307889 3238978972208776088978053 := by
  unfold tailWord_6307889
  simp only [CollatzResearch.WordTrace]
  refine ⟨230067612644602929517942721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153378408429735286345295147 230067612644602929517942721)
  ·
    refine ⟨172550709483452197138457041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 230067612644602929517942721 172550709483452197138457041)
    ·
      refine ⟨129413032112589147853842781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 172550709483452197138457041 129413032112589147853842781)
      ·
        refine ⟨48529887042220930445191043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 129413032112589147853842781 48529887042220930445191043)
        ·
          refine ⟨72794830563331395667786565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48529887042220930445191043 72794830563331395667786565)
          ·
            refine ⟨13649030730624636687709981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 72794830563331395667786565 13649030730624636687709981)
            ·
              refine ⟨5118386523984238757891243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13649030730624636687709981 5118386523984238757891243)
              ·
                refine ⟨7677579785976358136836865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5118386523984238757891243 7677579785976358136836865)
                ·
                  refine ⟨5758184839482268602627649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7677579785976358136836865 5758184839482268602627649)
                  ·
                    refine ⟨4318638629611701451970737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5758184839482268602627649 4318638629611701451970737)
                    ·
                      refine ⟨3238978972208776088978053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4318638629611701451970737 3238978972208776088978053)
                      ·
                        rfl

theorem cell23_6307889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 3, 1, 2, 2, 2].length) (baseStart_6307889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6307889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6307889 prefixEnd_6307889 := by exact prefixLift 6307889
  have htrace : WordTrace (prefixWord ++ tailWord_6307889) baseStart_6307889 baseEnd_6307889 := by
    simpa [prefixWord, tailWord_6307889, baseEnd_6307889] using wordTrace_append hprefix tailTrace_6307889
  have hstable : (prefixWord ++ tailWord_6307889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6307889).length < 2 ^ (prefixWord ++ tailWord_6307889).sum := by decide
  have hdescent : baseEnd_6307889 < baseStart_6307889 := by decide
  rcases family_descends (prefixWord ++ tailWord_6307889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6307891 : List Nat := [1, 1, 1, 2, 4, 1, 3, 2, 1, 7]
def baseStart_6307891 : Nat := 118140960795 + 6307891 * 2 ^ 59
def prefixEnd_6307891 : Nat := 4983230072969 + 3 ^ 40 * 6307891 * 2
def baseEnd_6307891 : Nat := 1079659999723361693717681

theorem tailTrace_6307891 : CollatzResearch.WordTrace tailWord_6307891 prefixEnd_6307891 1079659999723361693717681 := by
  unfold tailWord_6307891
  simp only [CollatzResearch.WordTrace]
  refine ⟨230067685590595683859515527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153378457060397122573010351 230067685590595683859515527)
  ·
    refine ⟨345101528385893525789273291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230067685590595683859515527 345101528385893525789273291)
    ·
      refine ⟨517652292578840288683909937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 345101528385893525789273291 517652292578840288683909937)
      ·
        refine ⟨388239219434130216512932453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 517652292578840288683909937 388239219434130216512932453)
        ·
          refine ⟨72794853643899415596174835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 388239219434130216512932453 72794853643899415596174835)
          ·
            refine ⟨109192280465849123394262253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72794853643899415596174835 109192280465849123394262253)
            ·
              refine ⟨40947105174693421272848345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 109192280465849123394262253 40947105174693421272848345)
              ·
                refine ⟨30710328881020065954636259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40947105174693421272848345 30710328881020065954636259)
                ·
                  refine ⟨46065493321530098931954389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30710328881020065954636259 46065493321530098931954389)
                  ·
                    refine ⟨1079659999723361693717681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 46065493321530098931954389 1079659999723361693717681)
                    ·
                      rfl

theorem cell23_6307891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 2, 1, 7].length) (baseStart_6307891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6307891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6307891 prefixEnd_6307891 := by exact prefixLift 6307891
  have htrace : WordTrace (prefixWord ++ tailWord_6307891) baseStart_6307891 baseEnd_6307891 := by
    simpa [prefixWord, tailWord_6307891, baseEnd_6307891] using wordTrace_append hprefix tailTrace_6307891
  have hstable : (prefixWord ++ tailWord_6307891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6307891).length < 2 ^ (prefixWord ++ tailWord_6307891).sum := by decide
  have hdescent : baseEnd_6307891 < baseStart_6307891 := by decide
  rcases family_descends (prefixWord ++ tailWord_6307891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6307928 : List Nat := [2, 1, 2, 2, 1, 4, 1, 1, 4, 1, 4]
def baseStart_6307928 : Nat := 118140960795 + 6307928 * 2 ^ 59
def prefixEnd_6307928 : Nat := 4983230072969 + 3 ^ 40 * 6307928 * 2
def baseEnd_6307928 : Nat := 3238998997954301436390373

theorem tailTrace_6307928 : CollatzResearch.WordTrace tailWord_6307928 prefixEnd_6307928 3238998997954301436390373 := by
  unfold tailWord_6307928
  simp only [CollatzResearch.WordTrace]
  refine ⟨115034517545730819589306219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153379356727641092785741625 115034517545730819589306219)
  ·
    refine ⟨172551776318596229383959329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115034517545730819589306219 172551776318596229383959329)
    ·
      refine ⟨129413832238947172037969497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 172551776318596229383959329 129413832238947172037969497)
      ·
        refine ⟨97060374179210379028477123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129413832238947172037969497 97060374179210379028477123)
        ·
          refine ⟨145590561268815568542715685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97060374179210379028477123 145590561268815568542715685)
          ·
            refine ⟨27298230237902919101759191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 145590561268815568542715685 27298230237902919101759191)
            ·
              refine ⟨40947345356854378652638787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27298230237902919101759191 40947345356854378652638787)
              ·
                refine ⟨61421018035281567978958181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40947345356854378652638787 61421018035281567978958181)
                ·
                  refine ⟨11516440881615293996054659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 61421018035281567978958181 11516440881615293996054659)
                  ·
                    refine ⟨17274661322422940994081989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11516440881615293996054659 17274661322422940994081989)
                    ·
                      refine ⟨3238998997954301436390373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17274661322422940994081989 3238998997954301436390373)
                      ·
                        rfl

theorem cell23_6307928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 1, 4, 1, 4].length) (baseStart_6307928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6307928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6307928 prefixEnd_6307928 := by exact prefixLift 6307928
  have htrace : WordTrace (prefixWord ++ tailWord_6307928) baseStart_6307928 baseEnd_6307928 := by
    simpa [prefixWord, tailWord_6307928, baseEnd_6307928] using wordTrace_append hprefix tailTrace_6307928
  have hstable : (prefixWord ++ tailWord_6307928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6307928).length < 2 ^ (prefixWord ++ tailWord_6307928).sum := by decide
  have hdescent : baseEnd_6307928 < baseStart_6307928 := by decide
  rcases family_descends (prefixWord ++ tailWord_6307928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6307965 : List Nat := [1, 4, 1, 1, 3, 2, 1, 3, 2, 2, 3]
def baseStart_6307965 : Nat := 118140960795 + 6307965 * 2 ^ 59
def prefixEnd_6307965 : Nat := 4983230072969 + 3 ^ 40 * 6307965 * 2
def baseEnd_6307965 : Nat := 3239017996738517791627703

theorem tailTrace_6307965 : CollatzResearch.WordTrace tailWord_6307965 prefixEnd_6307965 3239017996738517791627703 := by
  unfold tailWord_6307965
  simp only [CollatzResearch.WordTrace]
  refine ⟨230070384592327594497709349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153380256394885062998472899 230070384592327594497709349)
  ·
    refine ⟨43138197111061423968320503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 230070384592327594497709349 43138197111061423968320503)
    ·
      refine ⟨64707295666592135952480755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43138197111061423968320503 64707295666592135952480755)
      ·
        refine ⟨97060943499888203928721133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64707295666592135952480755 97060943499888203928721133)
        ·
          refine ⟨36397853812458076473270425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 97060943499888203928721133 36397853812458076473270425)
          ·
            refine ⟨27298390359343557354952819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36397853812458076473270425 27298390359343557354952819)
            ·
              refine ⟨40947585539015336032429229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27298390359343557354952819 40947585539015336032429229)
              ·
                refine ⟨15355344577130751012160961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40947585539015336032429229 15355344577130751012160961)
                ·
                  refine ⟨11516508432848063259120721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15355344577130751012160961 11516508432848063259120721)
                  ·
                    refine ⟨8637381324636047444340541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11516508432848063259120721 8637381324636047444340541)
                    ·
                      refine ⟨3239017996738517791627703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8637381324636047444340541 3239017996738517791627703)
                      ·
                        rfl

theorem cell23_6307965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 3, 2, 2, 3].length) (baseStart_6307965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6307965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6307965 prefixEnd_6307965 := by exact prefixLift 6307965
  have htrace : WordTrace (prefixWord ++ tailWord_6307965) baseStart_6307965 baseEnd_6307965 := by
    simpa [prefixWord, tailWord_6307965, baseEnd_6307965] using wordTrace_append hprefix tailTrace_6307965
  have hstable : (prefixWord ++ tailWord_6307965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6307965).length < 2 ^ (prefixWord ++ tailWord_6307965).sum := by decide
  have hdescent : baseEnd_6307965 < baseStart_6307965 := by decide
  rcases family_descends (prefixWord ++ tailWord_6307965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6307972 : List Nat := [2, 3, 2, 1, 2, 1, 2, 5, 1, 4]
def baseStart_6307972 : Nat := 118140960795 + 6307972 * 2 ^ 59
def prefixEnd_6307972 : Nat := 4983230072969 + 3 ^ 40 * 6307972 * 2
def baseEnd_6307972 : Nat := 1079673863701033088080057

theorem tailTrace_6307972 : CollatzResearch.WordTrace tailWord_6307972 prefixEnd_6307972 1079673863701033088080057 := by
  unfold tailWord_6307972
  simp only [CollatzResearch.WordTrace]
  refine ⟨115035319951651117346607085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153380426602201489795476113 115035319951651117346607085)
  ·
    refine ⟨43138244981869169004977657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115035319951651117346607085 43138244981869169004977657)
    ·
      refine ⟨32353683736401876753733243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43138244981869169004977657 32353683736401876753733243)
      ·
        refine ⟨48530525604602815130599865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32353683736401876753733243 48530525604602815130599865)
        ·
          refine ⟨36397894203452111347949899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48530525604602815130599865 36397894203452111347949899)
          ·
            refine ⟨54596841305178167021924849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36397894203452111347949899 54596841305178167021924849)
            ·
              refine ⟨40947630978883625266443637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54596841305178167021924849 40947630978883625266443637)
              ·
                refine ⟨3838840404270339868729091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 40947630978883625266443637 3838840404270339868729091)
                ·
                  refine ⟨5758260606405509803093637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3838840404270339868729091 5758260606405509803093637)
                  ·
                    refine ⟨1079673863701033088080057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5758260606405509803093637 1079673863701033088080057)
                    ·
                      rfl

theorem cell23_6307972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 5, 1, 4].length) (baseStart_6307972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6307972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6307972 prefixEnd_6307972 := by exact prefixLift 6307972
  have htrace : WordTrace (prefixWord ++ tailWord_6307972) baseStart_6307972 baseEnd_6307972 := by
    simpa [prefixWord, tailWord_6307972, baseEnd_6307972] using wordTrace_append hprefix tailTrace_6307972
  have hstable : (prefixWord ++ tailWord_6307972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6307972).length < 2 ^ (prefixWord ++ tailWord_6307972).sum := by decide
  have hdescent : baseEnd_6307972 < baseStart_6307972 := by decide
  rcases family_descends (prefixWord ++ tailWord_6307972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6308005 : List Nat := [1, 3, 1, 2, 1, 3, 2, 2, 1, 5, 2]
def baseStart_6308005 : Nat := 118140960795 + 6308005 * 2 ^ 59
def prefixEnd_6308005 : Nat := 4983230072969 + 3 ^ 40 * 6308005 * 2
def baseEnd_6308005 : Nat := 3239038535964697635127519

theorem tailTrace_6308005 : CollatzResearch.WordTrace tailWord_6308005 prefixEnd_6308005 3239038535964697635127519 := by
  unfold tailWord_6308005
  simp only [CollatzResearch.WordTrace]
  refine ⟨230071843512182681329165469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153381229008121787552776979 230071843512182681329165469)
  ·
    refine ⟨86276941317068505498437051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 230071843512182681329165469 86276941317068505498437051)
    ·
      refine ⟨129415411975602758247655577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86276941317068505498437051 129415411975602758247655577)
      ·
        refine ⟨97061558981702068685741683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129415411975602758247655577 97061558981702068685741683)
        ·
          refine ⟨145592338472553103028612525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97061558981702068685741683 145592338472553103028612525)
          ·
            refine ⟨54597126927207413635729697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 145592338472553103028612525 54597126927207413635729697)
            ·
              refine ⟨40947845195405560226797273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54597126927207413635729697 40947845195405560226797273)
              ·
                refine ⟨30710883896554170170097955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40947845195405560226797273 30710883896554170170097955)
                ·
                  refine ⟨46066325844831255255146933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30710883896554170170097955 46066325844831255255146933)
                  ·
                    refine ⟨4318718047952930180170025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 46066325844831255255146933 4318718047952930180170025)
                    ·
                      refine ⟨3239038535964697635127519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4318718047952930180170025 3239038535964697635127519)
                      ·
                        rfl

theorem cell23_6308005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 2, 1, 5, 2].length) (baseStart_6308005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6308005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6308005 prefixEnd_6308005 := by exact prefixLift 6308005
  have htrace : WordTrace (prefixWord ++ tailWord_6308005) baseStart_6308005 baseEnd_6308005 := by
    simpa [prefixWord, tailWord_6308005, baseEnd_6308005] using wordTrace_append hprefix tailTrace_6308005
  have hstable : (prefixWord ++ tailWord_6308005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6308005).length < 2 ^ (prefixWord ++ tailWord_6308005).sum := by decide
  have hdescent : baseEnd_6308005 < baseStart_6308005 := by decide
  rcases family_descends (prefixWord ++ tailWord_6308005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6308032 : List Nat := [2, 1, 1, 2, 5, 1, 4, 1, 1, 5]
def baseStart_6308032 : Nat := 118140960795 + 6308032 * 2 ^ 59
def prefixEnd_6308032 : Nat := 4983230072969 + 3 ^ 40 * 6308032 * 2
def baseEnd_6308032 : Nat := 1079684133314123009829965

theorem tailTrace_6308032 : CollatzResearch.WordTrace tailWord_6308032 prefixEnd_6308032 1079684133314123009829965 := by
  unfold tailWord_6308032
  simp only [CollatzResearch.WordTrace]
  refine ⟨115036414141542432470199175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153381885522056576626932233 115036414141542432470199175)
  ·
    refine ⟨172554621212313648705298763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115036414141542432470199175 172554621212313648705298763)
    ·
      refine ⟨258831931818470473057948145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172554621212313648705298763 258831931818470473057948145)
      ·
        refine ⟨194123948863852854793461109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 258831931818470473057948145 194123948863852854793461109)
        ·
          refine ⟨18199120205986205136886979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 194123948863852854793461109 18199120205986205136886979)
          ·
            refine ⟨27298680308979307705330469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18199120205986205136886979 27298680308979307705330469)
            ·
              refine ⟨5118502557933620194749463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27298680308979307705330469 5118502557933620194749463)
              ·
                refine ⟨7677753836900430292124195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5118502557933620194749463 7677753836900430292124195)
                ·
                  refine ⟨11516630755350645438186293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7677753836900430292124195 11516630755350645438186293)
                  ·
                    refine ⟨1079684133314123009829965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11516630755350645438186293 1079684133314123009829965)
                    ·
                      rfl

theorem cell23_6308032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 4, 1, 1, 5].length) (baseStart_6308032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6308032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6308032 prefixEnd_6308032 := by exact prefixLift 6308032
  have htrace : WordTrace (prefixWord ++ tailWord_6308032) baseStart_6308032 baseEnd_6308032 := by
    simpa [prefixWord, tailWord_6308032, baseEnd_6308032] using wordTrace_append hprefix tailTrace_6308032
  have hstable : (prefixWord ++ tailWord_6308032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6308032).length < 2 ^ (prefixWord ++ tailWord_6308032).sum := by decide
  have hdescent : baseEnd_6308032 < baseStart_6308032 := by decide
  rcases family_descends (prefixWord ++ tailWord_6308032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6308069 : List Nat := [1, 3, 1, 4, 2, 1, 2, 2, 3, 2, 2]
def baseStart_6308069 : Nat := 118140960795 + 6308069 * 2 ^ 59
def prefixEnd_6308069 : Nat := 4983230072969 + 3 ^ 40 * 6308069 * 2
def baseEnd_6308069 : Nat := 3239071398726585384727225

theorem tailTrace_6308069 : CollatzResearch.WordTrace tailWord_6308069 prefixEnd_6308069 3239071398726585384727225 := by
  unfold tailWord_6308069
  simp only [CollatzResearch.WordTrace]
  refine ⟨230074177783950820259495261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153382785189300546839663507 230074177783950820259495261)
  ·
    refine ⟨86277816668981557597310723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 230074177783950820259495261 86277816668981557597310723)
    ·
      refine ⟨129416725003472336395966085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86277816668981557597310723 129416725003472336395966085)
      ·
        refine ⟨24265635938151063074243641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 129416725003472336395966085 24265635938151063074243641)
        ·
          refine ⟨18199226953613297305682731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24265635938151063074243641 18199226953613297305682731)
          ·
            refine ⟨27298840430419945958524097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18199226953613297305682731 27298840430419945958524097)
            ·
              refine ⟨20474130322814959468893073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27298840430419945958524097 20474130322814959468893073)
              ·
                refine ⟨15355597742111219601669805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20474130322814959468893073 15355597742111219601669805)
                ·
                  refine ⟨5758349153291707350626177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15355597742111219601669805 5758349153291707350626177)
                  ·
                    refine ⟨4318761864968780512969633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5758349153291707350626177 4318761864968780512969633)
                    ·
                      refine ⟨3239071398726585384727225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4318761864968780512969633 3239071398726585384727225)
                      ·
                        rfl

theorem cell23_6308069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 2, 2, 3, 2, 2].length) (baseStart_6308069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6308069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6308069 prefixEnd_6308069 := by exact prefixLift 6308069
  have htrace : WordTrace (prefixWord ++ tailWord_6308069) baseStart_6308069 baseEnd_6308069 := by
    simpa [prefixWord, tailWord_6308069, baseEnd_6308069] using wordTrace_append hprefix tailTrace_6308069
  have hstable : (prefixWord ++ tailWord_6308069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6308069).length < 2 ^ (prefixWord ++ tailWord_6308069).sum := by decide
  have hdescent : baseEnd_6308069 < baseStart_6308069 := by decide
  rcases family_descends (prefixWord ++ tailWord_6308069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6308072 : List Nat := [2, 1, 4, 1, 2, 2, 1, 4, 1, 2, 3]
def baseStart_6308072 : Nat := 118140960795 + 6308072 * 2 ^ 59
def prefixEnd_6308072 : Nat := 4983230072969 + 3 ^ 40 * 6308072 * 2
def baseEnd_6308072 : Nat := 3239072939168548872989711

theorem tailTrace_6308072 : CollatzResearch.WordTrace tailWord_6308072 prefixEnd_6308072 3239072939168548872989711 := by
  unfold tailWord_6308072
  simp only [CollatzResearch.WordTrace]
  refine ⟨115037143601469975885927235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153382858135293301181236313 115037143601469975885927235)
  ·
    refine ⟨172555715402204963828890853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115037143601469975885927235 172555715402204963828890853)
    ·
      refine ⟨32354196637913430717917035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 172555715402204963828890853 32354196637913430717917035)
      ·
        refine ⟨48531294956870146076875553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32354196637913430717917035 48531294956870146076875553)
        ·
          refine ⟨36398471217652609557656665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48531294956870146076875553 36398471217652609557656665)
          ·
            refine ⟨27298853413239457168242499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36398471217652609557656665 27298853413239457168242499)
            ·
              refine ⟨40948280119859185752363749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27298853413239457168242499 40948280119859185752363749)
              ·
                refine ⟨7677802522473597328568203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40948280119859185752363749 7677802522473597328568203)
                ·
                  refine ⟨11516703783710395992852305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7677802522473597328568203 11516703783710395992852305)
                  ·
                    refine ⟨8637527837782796994639229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11516703783710395992852305 8637527837782796994639229)
                    ·
                      refine ⟨3239072939168548872989711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8637527837782796994639229 3239072939168548872989711)
                      ·
                        rfl

theorem cell23_6308072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 4, 1, 2, 3].length) (baseStart_6308072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6308072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6308072 prefixEnd_6308072 := by exact prefixLift 6308072
  have htrace : WordTrace (prefixWord ++ tailWord_6308072) baseStart_6308072 baseEnd_6308072 := by
    simpa [prefixWord, tailWord_6308072, baseEnd_6308072] using wordTrace_append hprefix tailTrace_6308072
  have hstable : (prefixWord ++ tailWord_6308072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6308072).length < 2 ^ (prefixWord ++ tailWord_6308072).sum := by decide
  have hdescent : baseEnd_6308072 < baseStart_6308072 := by decide
  rcases family_descends (prefixWord ++ tailWord_6308072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6308103 : List Nat := [1, 1, 4, 5, 1, 2, 1, 1, 3, 2, 2]
def baseStart_6308103 : Nat := 118140960795 + 6308103 * 2 ^ 59
def prefixEnd_6308103 : Nat := 4983230072969 + 3 ^ 40 * 6308103 * 2
def baseEnd_6308103 : Nat := 3239088857068838251702069

theorem tailTrace_6308103 : CollatzResearch.WordTrace tailWord_6308103 prefixEnd_6308103 3239088857068838251702069 := by
  unfold tailWord_6308103
  simp only [CollatzResearch.WordTrace]
  refine ⟨230075417865827644066232963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153383611910551762710821975 230075417865827644066232963)
  ·
    refine ⟨345113126798741466099349445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230075417865827644066232963 345113126798741466099349445)
    ·
      refine ⟨64708711274764024893628021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 345113126798741466099349445 64708711274764024893628021)
      ·
        refine ⟨6066441682009127333777627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 64708711274764024893628021 6066441682009127333777627)
        ·
          refine ⟨9099662523013691000666441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6066441682009127333777627 9099662523013691000666441)
          ·
            refine ⟨6824746892260268250499831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9099662523013691000666441 6824746892260268250499831)
            ·
              refine ⟨10237120338390402375749747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6824746892260268250499831 10237120338390402375749747)
              ·
                refine ⟨15355680507585603563624621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10237120338390402375749747 15355680507585603563624621)
                ·
                  refine ⟨5758380190344601336359233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15355680507585603563624621 5758380190344601336359233)
                  ·
                    refine ⟨4318785142758451002269425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5758380190344601336359233 4318785142758451002269425)
                    ·
                      refine ⟨3239088857068838251702069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4318785142758451002269425 3239088857068838251702069)
                      ·
                        rfl

theorem cell23_6308103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 2, 1, 1, 3, 2, 2].length) (baseStart_6308103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6308103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6308103 prefixEnd_6308103 := by exact prefixLift 6308103
  have htrace : WordTrace (prefixWord ++ tailWord_6308103) baseStart_6308103 baseEnd_6308103 := by
    simpa [prefixWord, tailWord_6308103, baseEnd_6308103] using wordTrace_append hprefix tailTrace_6308103
  have hstable : (prefixWord ++ tailWord_6308103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6308103).length < 2 ^ (prefixWord ++ tailWord_6308103).sum := by decide
  have hdescent : baseEnd_6308103 < baseStart_6308103 := by decide
  rcases family_descends (prefixWord ++ tailWord_6308103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6308119 : List Nat := [1, 1, 3, 4, 1, 3, 1, 3, 2, 1, 3]
def baseStart_6308119 : Nat := 118140960795 + 6308119 * 2 ^ 59
def prefixEnd_6308119 : Nat := 4983230072969 + 3 ^ 40 * 6308119 * 2
def baseEnd_6308119 : Nat := 3239097072759310189101995

theorem tailTrace_6308119 : CollatzResearch.WordTrace tailWord_6308119 prefixEnd_6308119 3239097072759310189101995 := by
  unfold tailWord_6308119
  simp only [CollatzResearch.WordTrace]
  refine ⟨230076001433769678798815411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153384000955846452532543607 230076001433769678798815411)
  ·
    refine ⟨345114002150654518198223117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230076001433769678798815411 345114002150654518198223117)
    ·
      refine ⟨129417750806495444324333669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 345114002150654518198223117 129417750806495444324333669)
      ·
        refine ⟨24265828276217895810812563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 129417750806495444324333669 24265828276217895810812563)
        ·
          refine ⟨36398742414326843716218845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24265828276217895810812563 36398742414326843716218845)
          ·
            refine ⟨13649528405372566393582067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36398742414326843716218845 13649528405372566393582067)
            ·
              refine ⟨20474292608058849590373101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13649528405372566393582067 20474292608058849590373101)
              ·
                refine ⟨7677859728022068596389913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20474292608058849590373101 7677859728022068596389913)
                ·
                  refine ⟨5758394796016551447292435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7677859728022068596389913 5758394796016551447292435)
                  ·
                    refine ⟨8637592194024827170938653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5758394796016551447292435 8637592194024827170938653)
                    ·
                      refine ⟨3239097072759310189101995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8637592194024827170938653 3239097072759310189101995)
                      ·
                        rfl

theorem cell23_6308119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 1, 3, 2, 1, 3].length) (baseStart_6308119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6308119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6308119 prefixEnd_6308119 := by exact prefixLift 6308119
  have htrace : WordTrace (prefixWord ++ tailWord_6308119) baseStart_6308119 baseEnd_6308119 := by
    simpa [prefixWord, tailWord_6308119, baseEnd_6308119] using wordTrace_append hprefix tailTrace_6308119
  have hstable : (prefixWord ++ tailWord_6308119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6308119).length < 2 ^ (prefixWord ++ tailWord_6308119).sum := by decide
  have hdescent : baseEnd_6308119 < baseStart_6308119 := by decide
  rcases family_descends (prefixWord ++ tailWord_6308119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6308129 : List Nat := [1, 2, 3, 2, 1, 1, 5, 2, 1, 3, 2]
def baseStart_6308129 : Nat := 118140960795 + 6308129 * 2 ^ 59
def prefixEnd_6308129 : Nat := 4983230072969 + 3 ^ 40 * 6308129 * 2
def baseEnd_6308129 : Nat := 3239102207565855149976949

theorem tailTrace_6308129 : CollatzResearch.WordTrace tailWord_6308129 prefixEnd_6308129 3239102207565855149976949 := by
  unfold tailWord_6308129
  simp only [CollatzResearch.WordTrace]
  refine ⟨230076366163733450506679441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153384244109155633671119627 230076366163733450506679441)
  ·
    refine ⟨172557274622800087880009581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 230076366163733450506679441 172557274622800087880009581)
    ·
      refine ⟨64708977983550032955003593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 172557274622800087880009581 64708977983550032955003593)
      ·
        refine ⟨48531733487662524716252695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64708977983550032955003593 48531733487662524716252695)
        ·
          refine ⟨72797600231493787074379043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48531733487662524716252695 72797600231493787074379043)
          ·
            refine ⟨109196400347240680611568565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72797600231493787074379043 109196400347240680611568565)
            ·
              refine ⟨10237162532553813807334553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 109196400347240680611568565 10237162532553813807334553)
              ·
                refine ⟨7677871899415360355500915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10237162532553813807334553 7677871899415360355500915)
                ·
                  refine ⟨11516807849123040533251373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7677871899415360355500915 11516807849123040533251373)
                  ·
                    refine ⟨4318802943421140199969265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11516807849123040533251373 4318802943421140199969265)
                    ·
                      refine ⟨3239102207565855149976949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4318802943421140199969265 3239102207565855149976949)
                      ·
                        rfl

theorem cell23_6308129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 5, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 5, 2, 1, 3, 2].length) (baseStart_6308129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6308129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6308129 prefixEnd_6308129 := by exact prefixLift 6308129
  have htrace : WordTrace (prefixWord ++ tailWord_6308129) baseStart_6308129 baseEnd_6308129 := by
    simpa [prefixWord, tailWord_6308129, baseEnd_6308129] using wordTrace_append hprefix tailTrace_6308129
  have hstable : (prefixWord ++ tailWord_6308129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6308129).length < 2 ^ (prefixWord ++ tailWord_6308129).sum := by decide
  have hdescent : baseEnd_6308129 < baseStart_6308129 := by decide
  rcases family_descends (prefixWord ++ tailWord_6308129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6308195 : List Nat := [1, 1, 1, 5, 2, 1, 3, 1, 1, 7]
def baseStart_6308195 : Nat := 118140960795 + 6308195 * 2 ^ 59
def prefixEnd_6308195 : Nat := 4983230072969 + 3 ^ 40 * 6308195 * 2
def baseEnd_6308195 : Nat := 1079712032429683963917215

theorem tailTrace_6308195 : CollatzResearch.WordTrace tailWord_6308195 prefixEnd_6308195 1079712032429683963917215 := by
  unfold tailWord_6308195
  simp only [CollatzResearch.WordTrace]
  refine ⟨230078773381494343778582039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153385848920996229185721359 230078773381494343778582039)
  ·
    refine ⟨345118160072241515667873059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230078773381494343778582039 345118160072241515667873059)
    ·
      refine ⟨517677240108362273501809589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 345118160072241515667873059 517677240108362273501809589)
      ·
        refine ⟨48532241260158963140794649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 517677240108362273501809589 48532241260158963140794649)
        ·
          refine ⟨36399180945119222355595987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48532241260158963140794649 36399180945119222355595987)
          ·
            refine ⟨54598771417678833533393981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36399180945119222355595987 54598771417678833533393981)
            ·
              refine ⟨20474539281629562575022743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54598771417678833533393981 20474539281629562575022743)
              ·
                refine ⟨30711808922444343862534115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20474539281629562575022743 30711808922444343862534115)
                ·
                  refine ⟨46067713383666515793801173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30711808922444343862534115 46067713383666515793801173)
                  ·
                    refine ⟨1079712032429683963917215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 46067713383666515793801173 1079712032429683963917215)
                    ·
                      rfl

theorem cell23_6308195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 3, 1, 1, 7].length) (baseStart_6308195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6308195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6308195 prefixEnd_6308195 := by exact prefixLift 6308195
  have htrace : WordTrace (prefixWord ++ tailWord_6308195) baseStart_6308195 baseEnd_6308195 := by
    simpa [prefixWord, tailWord_6308195, baseEnd_6308195] using wordTrace_append hprefix tailTrace_6308195
  have hstable : (prefixWord ++ tailWord_6308195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6308195).length < 2 ^ (prefixWord ++ tailWord_6308195).sum := by decide
  have hdescent : baseEnd_6308195 < baseStart_6308195 := by decide
  rcases family_descends (prefixWord ++ tailWord_6308195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6308199 : List Nat := [1, 1, 5, 1, 3, 2, 2, 3, 5]
def baseStart_6308199 : Nat := 118140960795 + 6308199 * 2 ^ 59
def prefixEnd_6308199 : Nat := 4983230072969 + 3 ^ 40 * 6308199 * 2
def baseEnd_6308199 : Nat := 359904239023518875122403

theorem tailTrace_6308199 : CollatzResearch.WordTrace tailWord_6308199 prefixEnd_6308199 359904239023518875122403 := by
  unfold tailWord_6308199
  simp only [CollatzResearch.WordTrace]
  refine ⟨230078919273479852461727651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153385946182319901641151767 230078919273479852461727651)
  ·
    refine ⟨345118378910219778692591477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230078919273479852461727651 345118378910219778692591477)
    ·
      refine ⟨32354848022833104252430451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 345118378910219778692591477 32354848022833104252430451)
      ·
        refine ⟨48532272034249656378645677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32354848022833104252430451 48532272034249656378645677)
        ·
          refine ⟨18199602012843621141992129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48532272034249656378645677 18199602012843621141992129)
          ·
            refine ⟨13649701509632715856494097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18199602012843621141992129 13649701509632715856494097)
            ·
              refine ⟨10237276132224536892370573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13649701509632715856494097 10237276132224536892370573)
              ·
                refine ⟨3838978549584201334638965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10237276132224536892370573 3838978549584201334638965)
                ·
                  refine ⟨359904239023518875122403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3838978549584201334638965 359904239023518875122403)
                  ·
                    rfl

theorem cell23_6308199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 2, 3, 5].length) (baseStart_6308199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6308199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6308199 prefixEnd_6308199 := by exact prefixLift 6308199
  have htrace : WordTrace (prefixWord ++ tailWord_6308199) baseStart_6308199 baseEnd_6308199 := by
    simpa [prefixWord, tailWord_6308199, baseEnd_6308199] using wordTrace_append hprefix tailTrace_6308199
  have hstable : (prefixWord ++ tailWord_6308199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6308199).length < 2 ^ (prefixWord ++ tailWord_6308199).sum := by decide
  have hdescent : baseEnd_6308199 < baseStart_6308199 := by decide
  rcases family_descends (prefixWord ++ tailWord_6308199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6308245 : List Nat := [1, 3, 2, 1, 1, 2, 1, 1, 1, 6, 4]
def baseStart_6308245 : Nat := 118140960795 + 6308245 * 2 ^ 59
def prefixEnd_6308245 : Nat := 4983230072969 + 3 ^ 40 * 6308245 * 2
def baseEnd_6308245 : Nat := 3239161771321776696126415

theorem tailTrace_6308245 : CollatzResearch.WordTrace tailWord_6308245 prefixEnd_6308245 3239161771321776696126415 := by
  unfold tailWord_6308245
  simp only [CollatzResearch.WordTrace]
  refine ⟨230080597031313202317902189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153387064687542134878601459 230080597031313202317902189)
  ·
    refine ⟨86280223886742450869213321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 230080597031313202317902189 86280223886742450869213321)
    ·
      refine ⟨64710167915056838151909991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86280223886742450869213321 64710167915056838151909991)
      ·
        refine ⟨97065251872585257227864987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64710167915056838151909991 97065251872585257227864987)
        ·
          refine ⟨145597877808877885841797481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97065251872585257227864987 145597877808877885841797481)
          ·
            refine ⟨109198408356658414381348111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 145597877808877885841797481 109198408356658414381348111)
            ·
              refine ⟨163797612534987621572022167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109198408356658414381348111 163797612534987621572022167)
              ·
                refine ⟨245696418802481432358033251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 163797612534987621572022167 245696418802481432358033251)
                ·
                  refine ⟨368544628203722148537049877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 245696418802481432358033251 368544628203722148537049877)
                  ·
                    refine ⟨17275529447049475712674213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 368544628203722148537049877 17275529447049475712674213)
                    ·
                      refine ⟨3239161771321776696126415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17275529447049475712674213 3239161771321776696126415)
                      ·
                        rfl

theorem cell23_6308245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 1, 1, 6, 4].length) (baseStart_6308245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6308245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6308245 prefixEnd_6308245 := by exact prefixLift 6308245
  have htrace : WordTrace (prefixWord ++ tailWord_6308245) baseStart_6308245 baseEnd_6308245 := by
    simpa [prefixWord, tailWord_6308245, baseEnd_6308245] using wordTrace_append hprefix tailTrace_6308245
  have hstable : (prefixWord ++ tailWord_6308245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6308245).length < 2 ^ (prefixWord ++ tailWord_6308245).sum := by decide
  have hdescent : baseEnd_6308245 < baseStart_6308245 := by decide
  rcases family_descends (prefixWord ++ tailWord_6308245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6308255 : List Nat := [1, 1, 2, 5, 1, 1, 1, 1, 10]
def baseStart_6308255 : Nat := 118140960795 + 6308255 * 2 ^ 59
def prefixEnd_6308255 : Nat := 4983230072969 + 3 ^ 40 * 6308255 * 2
def baseEnd_6308255 : Nat := 359907434014257961889041

theorem tailTrace_6308255 : CollatzResearch.WordTrace tailWord_6308255 prefixEnd_6308255 359907434014257961889041 := by
  unfold tailWord_6308255
  simp only [CollatzResearch.WordTrace]
  refine ⟨230080961761276974025766219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153387307840851316017177479 230080961761276974025766219)
  ·
    refine ⟨345121442641915461038649329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230080961761276974025766219 345121442641915461038649329)
    ·
      refine ⟨258841081981436595778986997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 345121442641915461038649329 258841081981436595778986997)
      ·
        refine ⟨24266351435759680854280031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 258841081981436595778986997 24266351435759680854280031)
        ·
          refine ⟨36399527153639521281420047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24266351435759680854280031 36399527153639521281420047)
          ·
            refine ⟨54599290730459281922130071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36399527153639521281420047 54599290730459281922130071)
            ·
              refine ⟨81898936095688922883195107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54599290730459281922130071 81898936095688922883195107)
              ·
                refine ⟨122848404143533384324792661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81898936095688922883195107 122848404143533384324792661)
                ·
                  refine ⟨359907434014257961889041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 122848404143533384324792661 359907434014257961889041)
                  ·
                    rfl

theorem cell23_6308255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 1, 10].length) (baseStart_6308255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6308255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6308255 prefixEnd_6308255 := by exact prefixLift 6308255
  have htrace : WordTrace (prefixWord ++ tailWord_6308255) baseStart_6308255 baseEnd_6308255 := by
    simpa [prefixWord, tailWord_6308255, baseEnd_6308255] using wordTrace_append hprefix tailTrace_6308255
  have hstable : (prefixWord ++ tailWord_6308255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6308255).length < 2 ^ (prefixWord ++ tailWord_6308255).sum := by decide
  have hdescent : baseEnd_6308255 < baseStart_6308255 := by decide
  rcases family_descends (prefixWord ++ tailWord_6308255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6308349 : List Nat := [1, 4, 1, 1, 1, 3, 1, 5, 2, 4]
def baseStart_6308349 : Nat := 118140960795 + 6308349 * 2 ^ 59
def prefixEnd_6308349 : Nat := 4983230072969 + 3 ^ 40 * 6308349 * 2
def baseEnd_6308349 : Nat := 1079738391103281429741979

theorem tailTrace_6308349 : CollatzResearch.WordTrace tailWord_6308349 prefixEnd_6308349 1079738391103281429741979 := by
  unfold tailWord_6308349
  simp only [CollatzResearch.WordTrace]
  refine ⟨230084390222936428079688101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153389593481957618719792067 230084390222936428079688101)
  ·
    refine ⟨43140823166800580264941519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 230084390222936428079688101 43140823166800580264941519)
    ·
      refine ⟨64711234750200870397412279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43140823166800580264941519 64711234750200870397412279)
      ·
        refine ⟨97066852125301305596118419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64711234750200870397412279 97066852125301305596118419)
        ·
          refine ⟨145600278187951958394177629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97066852125301305596118419 145600278187951958394177629)
          ·
            refine ⟨54600104320481984397816611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 145600278187951958394177629 54600104320481984397816611)
            ·
              refine ⟨81900156480722976596724917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54600104320481984397816611 81900156480722976596724917)
              ·
                refine ⟨7678139670067779055942961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 81900156480722976596724917 7678139670067779055942961)
                ·
                  refine ⟨5758604752550834291957221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7678139670067779055942961 5758604752550834291957221)
                  ·
                    refine ⟨1079738391103281429741979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5758604752550834291957221 1079738391103281429741979)
                    ·
                      rfl

theorem cell23_6308349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 5, 2, 4].length) (baseStart_6308349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6308349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6308349 prefixEnd_6308349 := by exact prefixLift 6308349
  have htrace : WordTrace (prefixWord ++ tailWord_6308349) baseStart_6308349 baseEnd_6308349 := by
    simpa [prefixWord, tailWord_6308349, baseEnd_6308349] using wordTrace_append hprefix tailTrace_6308349
  have hstable : (prefixWord ++ tailWord_6308349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6308349).length < 2 ^ (prefixWord ++ tailWord_6308349).sum := by decide
  have hdescent : baseEnd_6308349 < baseStart_6308349 := by decide
  rcases family_descends (prefixWord ++ tailWord_6308349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6308376 : List Nat := [2, 1, 2, 3, 3, 2, 1, 3, 1, 2, 3]
def baseStart_6308376 : Nat := 118140960795 + 6308376 * 2 ^ 59
def prefixEnd_6308376 : Nat := 4983230072969 + 3 ^ 40 * 6308376 * 2
def baseEnd_6308376 : Nat := 3239229037287515683588313

theorem tailTrace_6308376 : CollatzResearch.WordTrace tailWord_6308376 prefixEnd_6308376 3239229037287515683588313 := by
  unfold tailWord_6308376
  simp only [CollatzResearch.WordTrace]
  refine ⟨115042687496919305845460491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153390249995892407793947321 115042687496919305845460491)
  ·
    refine ⟨172564031245378958768190737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115042687496919305845460491 172564031245378958768190737)
    ·
      refine ⟨129423023434034219076143053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 172564031245378958768190737 129423023434034219076143053)
      ·
        refine ⟨48533633787762832153553645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 129423023434034219076143053 48533633787762832153553645)
        ·
          refine ⟨18200112670411062057582617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48533633787762832153553645 18200112670411062057582617)
          ·
            refine ⟨13650084502808296543186963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18200112670411062057582617 13650084502808296543186963)
            ·
              refine ⟨20475126754212444814780445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13650084502808296543186963 20475126754212444814780445)
              ·
                refine ⟨7678172532829666805542667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20475126754212444814780445 7678172532829666805542667)
                ·
                  refine ⟨11517258799244500208314001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7678172532829666805542667 11517258799244500208314001)
                  ·
                    refine ⟨8637944099433375156235501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11517258799244500208314001 8637944099433375156235501)
                    ·
                      refine ⟨3239229037287515683588313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8637944099433375156235501 3239229037287515683588313)
                      ·
                        rfl

theorem cell23_6308376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 1, 3, 1, 2, 3].length) (baseStart_6308376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6308376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6308376 prefixEnd_6308376 := by exact prefixLift 6308376
  have htrace : WordTrace (prefixWord ++ tailWord_6308376) baseStart_6308376 baseEnd_6308376 := by
    simpa [prefixWord, tailWord_6308376, baseEnd_6308376] using wordTrace_append hprefix tailTrace_6308376
  have hstable : (prefixWord ++ tailWord_6308376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6308376).length < 2 ^ (prefixWord ++ tailWord_6308376).sum := by decide
  have hdescent : baseEnd_6308376 < baseStart_6308376 := by decide
  rcases family_descends (prefixWord ++ tailWord_6308376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6308416 : List Nat := [2, 1, 1, 2, 2, 2, 3, 4, 1, 3, 2]
def baseStart_6308416 : Nat := 118140960795 + 6308416 * 2 ^ 59
def prefixEnd_6308416 : Nat := 4983230072969 + 3 ^ 40 * 6308416 * 2
def baseEnd_6308416 : Nat := 3239249576513695527088129

theorem tailTrace_6308416 : CollatzResearch.WordTrace tailWord_6308416 prefixEnd_6308416 3239249576513695527088129 := by
  unfold tailWord_6308416
  simp only [CollatzResearch.WordTrace]
  refine ⟨115043416956846849261188551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153391222609129132348251401 115043416956846849261188551)
  ·
    refine ⟨172565125435270273891782827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115043416956846849261188551 172565125435270273891782827)
    ·
      refine ⟨258847688152905410837674241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172565125435270273891782827 258847688152905410837674241)
      ·
        refine ⟨194135766114679058128255681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 258847688152905410837674241 194135766114679058128255681)
        ·
          refine ⟨145601824586009293596191761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 194135766114679058128255681 145601824586009293596191761)
          ·
            refine ⟨109201368439506970197143821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 145601824586009293596191761 109201368439506970197143821)
            ·
              refine ⟨40950513164815113823928933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 109201368439506970197143821 40950513164815113823928933)
              ·
                refine ⟨7678221218402833841986675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40950513164815113823928933 7678221218402833841986675)
                ·
                  refine ⟨11517331827604250762980013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7678221218402833841986675 11517331827604250762980013)
                  ·
                    refine ⟨4318999435351594036117505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11517331827604250762980013 4318999435351594036117505)
                    ·
                      refine ⟨3239249576513695527088129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4318999435351594036117505 3239249576513695527088129)
                      ·
                        rfl

theorem cell23_6308416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 4, 1, 3, 2].length) (baseStart_6308416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6308416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6308416 prefixEnd_6308416 := by exact prefixLift 6308416
  have htrace : WordTrace (prefixWord ++ tailWord_6308416) baseStart_6308416 baseEnd_6308416 := by
    simpa [prefixWord, tailWord_6308416, baseEnd_6308416] using wordTrace_append hprefix tailTrace_6308416
  have hstable : (prefixWord ++ tailWord_6308416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6308416).length < 2 ^ (prefixWord ++ tailWord_6308416).sum := by decide
  have hdescent : baseEnd_6308416 < baseStart_6308416 := by decide
  rcases family_descends (prefixWord ++ tailWord_6308416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6308509 : List Nat := [1, 4, 2, 1, 1, 1, 4, 1, 1, 2, 5]
def baseStart_6308509 : Nat := 118140960795 + 6308509 * 2 ^ 59
def prefixEnd_6308509 : Nat := 4983230072969 + 3 ^ 40 * 6308509 * 2
def baseEnd_6308509 : Nat := 3239297330214563663225201

theorem tailTrace_6308509 : CollatzResearch.WordTrace tailWord_6308509 prefixEnd_6308509 3239297330214563663225201 := by
  unfold tailWord_6308509
  simp only [CollatzResearch.WordTrace]
  refine ⟨230090225902356775405512581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153393483934904516937008387 230090225902356775405512581)
  ·
    refine ⟨43141917356691895388533609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 230090225902356775405512581 43141917356691895388533609)
    ·
      refine ⟨32356438017518921541400207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43141917356691895388533609 32356438017518921541400207)
      ·
        refine ⟨48534657026278382312100311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32356438017518921541400207 48534657026278382312100311)
        ·
          refine ⟨72801985539417573468150467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48534657026278382312100311 72801985539417573468150467)
          ·
            refine ⟨109202978309126360202225701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72801985539417573468150467 109202978309126360202225701)
            ·
              refine ⟨20475558432961192537917319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 109202978309126360202225701 20475558432961192537917319)
              ·
                refine ⟨30713337649441788806875979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20475558432961192537917319 30713337649441788806875979)
                ·
                  refine ⟨46070006474162683210313969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30713337649441788806875979 46070006474162683210313969)
                  ·
                    refine ⟨34552504855622012407735477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 46070006474162683210313969 34552504855622012407735477)
                    ·
                      refine ⟨3239297330214563663225201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34552504855622012407735477 3239297330214563663225201)
                      ·
                        rfl

theorem cell23_6308509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 4, 1, 1, 2, 5].length) (baseStart_6308509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6308509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6308509 prefixEnd_6308509 := by exact prefixLift 6308509
  have htrace : WordTrace (prefixWord ++ tailWord_6308509) baseStart_6308509 baseEnd_6308509 := by
    simpa [prefixWord, tailWord_6308509, baseEnd_6308509] using wordTrace_append hprefix tailTrace_6308509
  have hstable : (prefixWord ++ tailWord_6308509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6308509).length < 2 ^ (prefixWord ++ tailWord_6308509).sum := by decide
  have hdescent : baseEnd_6308509 < baseStart_6308509 := by decide
  rcases family_descends (prefixWord ++ tailWord_6308509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6308533 : List Nat := [1, 3, 3, 3, 1, 3, 1, 1, 2, 5]
def baseStart_6308533 : Nat := 118140960795 + 6308533 * 2 ^ 59
def prefixEnd_6308533 : Nat := 4983230072969 + 3 ^ 40 * 6308533 * 2
def baseEnd_6308533 : Nat := 1079769884583423856441697

theorem tailTrace_6308533 : CollatzResearch.WordTrace tailWord_6308533 prefixEnd_6308533 1079769884583423856441697 := by
  unfold tailWord_6308533
  simp only [CollatzResearch.WordTrace]
  refine ⟨230091101254269827504386253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153394067502846551669590835 230091101254269827504386253)
  ·
    refine ⟨86284162970351185314144845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 230091101254269827504386253 86284162970351185314144845)
    ·
      refine ⟨32356561113881694492804317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86284162970351185314144845 32356561113881694492804317)
      ·
        refine ⟨12133710417705635434801619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32356561113881694492804317 12133710417705635434801619)
        ·
          refine ⟨18200565626558453152202429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12133710417705635434801619 18200565626558453152202429)
          ·
            refine ⟨6825212109959419932075911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18200565626558453152202429 6825212109959419932075911)
            ·
              refine ⟨10237818164939129898113867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6825212109959419932075911 10237818164939129898113867)
              ·
                refine ⟨15356727247408694847170801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10237818164939129898113867 15356727247408694847170801)
                ·
                  refine ⟨11517545435556521135378101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15356727247408694847170801 11517545435556521135378101)
                  ·
                    refine ⟨1079769884583423856441697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11517545435556521135378101 1079769884583423856441697)
                    ·
                      rfl

theorem cell23_6308533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 3, 1, 1, 2, 5].length) (baseStart_6308533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6308533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6308533 prefixEnd_6308533 := by exact prefixLift 6308533
  have htrace : WordTrace (prefixWord ++ tailWord_6308533) baseStart_6308533 baseEnd_6308533 := by
    simpa [prefixWord, tailWord_6308533, baseEnd_6308533] using wordTrace_append hprefix tailTrace_6308533
  have hstable : (prefixWord ++ tailWord_6308533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6308533).length < 2 ^ (prefixWord ++ tailWord_6308533).sum := by decide
  have hdescent : baseEnd_6308533 < baseStart_6308533 := by decide
  rcases family_descends (prefixWord ++ tailWord_6308533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6308643 : List Nat := [1, 1, 1, 4, 2, 1, 1, 3, 5, 2, 2]
def baseStart_6308643 : Nat := 118140960795 + 6308643 * 2 ^ 59
def prefixEnd_6308643 : Nat := 4983230072969 + 3 ^ 40 * 6308643 * 2
def baseEnd_6308643 : Nat := 3239366136622266138949585

theorem tailTrace_6308643 : CollatzResearch.WordTrace tailWord_6308643 prefixEnd_6308643 3239366136622266138949585 := by
  unfold tailWord_6308643
  simp only [CollatzResearch.WordTrace]
  refine ⟨230095113283871316290890583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153396742189247544193927055 230095113283871316290890583)
  ·
    refine ⟨345142669925806974436335875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230095113283871316290890583 345142669925806974436335875)
    ·
      refine ⟨517714004888710461654503813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 345142669925806974436335875 517714004888710461654503813)
      ·
        refine ⟨97071375916633211560219465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 517714004888710461654503813 97071375916633211560219465)
        ·
          refine ⟨72803531937474908670164599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97071375916633211560219465 72803531937474908670164599)
          ·
            refine ⟨109205297906212363005246899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72803531937474908670164599 109205297906212363005246899)
            ·
              refine ⟨163807946859318544507870349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109205297906212363005246899 163807946859318544507870349)
              ·
                refine ⟨61427980072244454190451381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 163807946859318544507870349 61427980072244454190451381)
                ·
                  refine ⟨5758873131772917580354817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 61427980072244454190451381 5758873131772917580354817)
                  ·
                    refine ⟨4319154848829688185266113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5758873131772917580354817 4319154848829688185266113)
                    ·
                      refine ⟨3239366136622266138949585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4319154848829688185266113 3239366136622266138949585)
                      ·
                        rfl

theorem cell23_6308643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 3, 5, 2, 2].length) (baseStart_6308643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6308643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6308643 prefixEnd_6308643 := by exact prefixLift 6308643
  have htrace : WordTrace (prefixWord ++ tailWord_6308643) baseStart_6308643 baseEnd_6308643 := by
    simpa [prefixWord, tailWord_6308643, baseEnd_6308643] using wordTrace_append hprefix tailTrace_6308643
  have hstable : (prefixWord ++ tailWord_6308643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6308643).length < 2 ^ (prefixWord ++ tailWord_6308643).sum := by decide
  have hdescent : baseEnd_6308643 < baseStart_6308643 := by decide
  rcases family_descends (prefixWord ++ tailWord_6308643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6308666 : List Nat := [3, 1, 1, 1, 7, 10]
def baseStart_6308666 : Nat := 118140960795 + 6308666 * 2 ^ 59
def prefixEnd_6308666 : Nat := 4983230072969 + 3 ^ 40 * 6308666 * 2
def baseEnd_6308666 : Nat := 13330773443116541353753

theorem tailTrace_6308666 : CollatzResearch.WordTrace tailWord_6308666 prefixEnd_6308666 13330773443116541353753 := by
  unfold tailWord_6308666
  simp only [CollatzResearch.WordTrace]
  refine ⟨57523988040696997804744463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153397301441858660812651901 57523988040696997804744463)
  ·
    refine ⟨86285982061045496707116695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57523988040696997804744463 86285982061045496707116695)
    ·
      refine ⟨129428973091568245060675043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86285982061045496707116695 129428973091568245060675043)
      ·
        refine ⟨194143459637352367591012565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129428973091568245060675043 194143459637352367591012565)
        ·
          refine ⟨4550237335250446115414357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 194143459637352367591012565 4550237335250446115414357)
          ·
            refine ⟨13330773443116541353753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 4550237335250446115414357 13330773443116541353753)
            ·
              rfl

theorem cell23_6308666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 7, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 7, 10].length) (baseStart_6308666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6308666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6308666 prefixEnd_6308666 := by exact prefixLift 6308666
  have htrace : WordTrace (prefixWord ++ tailWord_6308666) baseStart_6308666 baseEnd_6308666 := by
    simpa [prefixWord, tailWord_6308666, baseEnd_6308666] using wordTrace_append hprefix tailTrace_6308666
  have hstable : (prefixWord ++ tailWord_6308666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6308666).length < 2 ^ (prefixWord ++ tailWord_6308666).sum := by decide
  have hdescent : baseEnd_6308666 < baseStart_6308666 := by decide
  rcases family_descends (prefixWord ++ tailWord_6308666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6308693 : List Nat := [1, 3, 2, 2, 2, 1, 4, 1, 1, 3, 3]
def baseStart_6308693 : Nat := 118140960795 + 6308693 * 2 ^ 59
def prefixEnd_6308693 : Nat := 4983230072969 + 3 ^ 40 * 6308693 * 2
def baseEnd_6308693 : Nat := 3239391810654990943324355

theorem tailTrace_6308693 : CollatzResearch.WordTrace tailWord_6308693 prefixEnd_6308693 3239391810654990943324355 := by
  unfold tailWord_6308693
  simp only [CollatzResearch.WordTrace]
  refine ⟨230096936933690174830210733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153397957955793449886807155 230096936933690174830210733)
  ·
    refine ⟨86286351350133815561329025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 230096936933690174830210733 86286351350133815561329025)
    ·
      refine ⟨64714763512600361670996769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86286351350133815561329025 64714763512600361670996769)
      ·
        refine ⟨48536072634450271253247577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64714763512600361670996769 48536072634450271253247577)
        ·
          refine ⟨36402054475837703439935683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48536072634450271253247577 36402054475837703439935683)
          ·
            refine ⟨54603081713756555159903525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36402054475837703439935683 54603081713756555159903525)
            ·
              refine ⟨10238077821329354092481911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 54603081713756555159903525 10238077821329354092481911)
              ·
                refine ⟨15357116731994031138722867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10238077821329354092481911 15357116731994031138722867)
                ·
                  refine ⟨23035675097991046708084301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15357116731994031138722867 23035675097991046708084301)
                  ·
                    refine ⟨8638378161746642515531613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23035675097991046708084301 8638378161746642515531613)
                    ·
                      refine ⟨3239391810654990943324355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8638378161746642515531613 3239391810654990943324355)
                      ·
                        rfl

theorem cell23_6308693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 4, 1, 1, 3, 3].length) (baseStart_6308693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6308693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6308693 prefixEnd_6308693 := by exact prefixLift 6308693
  have htrace : WordTrace (prefixWord ++ tailWord_6308693) baseStart_6308693 baseEnd_6308693 := by
    simpa [prefixWord, tailWord_6308693, baseEnd_6308693] using wordTrace_append hprefix tailTrace_6308693
  have hstable : (prefixWord ++ tailWord_6308693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6308693).length < 2 ^ (prefixWord ++ tailWord_6308693).sum := by decide
  have hdescent : baseEnd_6308693 < baseStart_6308693 := by decide
  rcases family_descends (prefixWord ++ tailWord_6308693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6308703 : List Nat := [1, 1, 2, 3, 1, 3, 1, 3, 3, 3, 2]
def baseStart_6308703 : Nat := 118140960795 + 6308703 * 2 ^ 59
def prefixEnd_6308703 : Nat := 4983230072969 + 3 ^ 40 * 6308703 * 2
def baseEnd_6308703 : Nat := 3239396945461535904199309

theorem tailTrace_6308703 : CollatzResearch.WordTrace tailWord_6308703 prefixEnd_6308703 3239396945461535904199309 := by
  unfold tailWord_6308703
  simp only [CollatzResearch.WordTrace]
  refine ⟨230097301663653946538074763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153398201109102631025383175 230097301663653946538074763)
  ·
    refine ⟨345145952495480919807112145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230097301663653946538074763 345145952495480919807112145)
    ·
      refine ⟨258859464371610689855334109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 345145952495480919807112145 258859464371610689855334109)
      ·
        refine ⟨97072299139354008695750291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 258859464371610689855334109 97072299139354008695750291)
        ·
          refine ⟨145608448709031013043625437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97072299139354008695750291 145608448709031013043625437)
          ·
            refine ⟨54603168265886629891359539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 145608448709031013043625437 54603168265886629891359539)
            ·
              refine ⟨81904752398829944837039309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54603168265886629891359539 81904752398829944837039309)
              ·
                refine ⟨30714282149561229313889741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 81904752398829944837039309 30714282149561229313889741)
                ·
                  refine ⟨11517855806085460992708653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30714282149561229313889741 11517855806085460992708653)
                  ·
                    refine ⟨4319195927282047872265745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11517855806085460992708653 4319195927282047872265745)
                    ·
                      refine ⟨3239396945461535904199309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4319195927282047872265745 3239396945461535904199309)
                      ·
                        rfl

theorem cell23_6308703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 3, 3, 3, 2].length) (baseStart_6308703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6308703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6308703 prefixEnd_6308703 := by exact prefixLift 6308703
  have htrace : WordTrace (prefixWord ++ tailWord_6308703) baseStart_6308703 baseEnd_6308703 := by
    simpa [prefixWord, tailWord_6308703, baseEnd_6308703] using wordTrace_append hprefix tailTrace_6308703
  have hstable : (prefixWord ++ tailWord_6308703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6308703).length < 2 ^ (prefixWord ++ tailWord_6308703).sum := by decide
  have hdescent : baseEnd_6308703 < baseStart_6308703 := by decide
  rcases family_descends (prefixWord ++ tailWord_6308703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6308733 : List Nat := [1, 4, 1, 1, 2, 1, 2, 2, 3, 4, 2]
def baseStart_6308733 : Nat := 118140960795 + 6308733 * 2 ^ 59
def prefixEnd_6308733 : Nat := 4983230072969 + 3 ^ 40 * 6308733 * 2
def baseEnd_6308733 : Nat := 3239412349881170786824171

theorem tailTrace_6308733 : CollatzResearch.WordTrace tailWord_6308733 prefixEnd_6308733 3239412349881170786824171 := by
  unfold tailWord_6308733
  simp only [CollatzResearch.WordTrace]
  refine ⟨230098395853545261661666853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153398930569030174441111235 230098395853545261661666853)
  ·
    refine ⟨43143449222539736561562535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 230098395853545261661666853 43143449222539736561562535)
    ·
      refine ⟨64715173833809604842343803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43143449222539736561562535 64715173833809604842343803)
      ·
        refine ⟨97072760750714407263515705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64715173833809604842343803 97072760750714407263515705)
        ·
          refine ⟨72804570563035805447636779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97072760750714407263515705 72804570563035805447636779)
          ·
            refine ⟨109206855844553708171455169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72804570563035805447636779 109206855844553708171455169)
            ·
              refine ⟨81905141883415281128591377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 109206855844553708171455169 81905141883415281128591377)
              ·
                refine ⟨61428856412561460846443533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 81905141883415281128591377 61428856412561460846443533)
                ·
                  refine ⟨23035821154710547817416325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 61428856412561460846443533 23035821154710547817416325)
                  ·
                    refine ⟨4319216466508227715765561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23035821154710547817416325 4319216466508227715765561)
                    ·
                      refine ⟨3239412349881170786824171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4319216466508227715765561 3239412349881170786824171)
                      ·
                        rfl

theorem cell23_6308733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 2, 3, 4, 2].length) (baseStart_6308733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6308733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6308733 prefixEnd_6308733 := by exact prefixLift 6308733
  have htrace : WordTrace (prefixWord ++ tailWord_6308733) baseStart_6308733 baseEnd_6308733 := by
    simpa [prefixWord, tailWord_6308733, baseEnd_6308733] using wordTrace_append hprefix tailTrace_6308733
  have hstable : (prefixWord ++ tailWord_6308733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6308733).length < 2 ^ (prefixWord ++ tailWord_6308733).sum := by decide
  have hdescent : baseEnd_6308733 < baseStart_6308733 := by decide
  rcases family_descends (prefixWord ++ tailWord_6308733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6308736 : List Nat := [2, 1, 1, 2, 1, 2, 2, 3, 2, 4, 3]
def baseStart_6308736 : Nat := 118140960795 + 6308736 * 2 ^ 59
def prefixEnd_6308736 : Nat := 4983230072969 + 3 ^ 40 * 6308736 * 2
def baseEnd_6308736 : Nat := 3239413890323134275086657

theorem tailTrace_6308736 : CollatzResearch.WordTrace tailWord_6308736 prefixEnd_6308736 3239413890323134275086657 := by
  unfold tailWord_6308736
  simp only [CollatzResearch.WordTrace]
  refine ⟨115049252636267196587013031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153399003515022928782684041 115049252636267196587013031)
  ·
    refine ⟨172573878954400794880519547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115049252636267196587013031 172573878954400794880519547)
    ·
      refine ⟨258860818431601192320779321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172573878954400794880519547 258860818431601192320779321)
      ·
        refine ⟨194145613823700894240584491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 258860818431601192320779321 194145613823700894240584491)
        ·
          refine ⟨291218420735551341360876737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 194145613823700894240584491 291218420735551341360876737)
          ·
            refine ⟨218413815551663506020657553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 291218420735551341360876737 218413815551663506020657553)
            ·
              refine ⟨163810361663747629515493165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 218413815551663506020657553 163810361663747629515493165)
              ·
                refine ⟨61428885623905361068309937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 163810361663747629515493165 61428885623905361068309937)
                ·
                  refine ⟨46071664217929020801232453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 61428885623905361068309937 46071664217929020801232453)
                  ·
                    refine ⟨8638437040861691400231085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 46071664217929020801232453 8638437040861691400231085)
                    ·
                      refine ⟨3239413890323134275086657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8638437040861691400231085 3239413890323134275086657)
                      ·
                        rfl

theorem cell23_6308736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 3, 2, 4, 3].length) (baseStart_6308736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6308736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6308736 prefixEnd_6308736 := by exact prefixLift 6308736
  have htrace : WordTrace (prefixWord ++ tailWord_6308736) baseStart_6308736 baseEnd_6308736 := by
    simpa [prefixWord, tailWord_6308736, baseEnd_6308736] using wordTrace_append hprefix tailTrace_6308736
  have hstable : (prefixWord ++ tailWord_6308736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6308736).length < 2 ^ (prefixWord ++ tailWord_6308736).sum := by decide
  have hdescent : baseEnd_6308736 < baseStart_6308736 := by decide
  rcases family_descends (prefixWord ++ tailWord_6308736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6308754 : List Nat := [3, 2, 3, 2, 2, 1, 2, 2, 1, 3, 2]
def baseStart_6308754 : Nat := 118140960795 + 6308754 * 2 ^ 59
def prefixEnd_6308754 : Nat := 4983230072969 + 3 ^ 40 * 6308754 * 2
def baseEnd_6308754 : Nat := 3239423132974915204661575

theorem tailTrace_6308754 : CollatzResearch.WordTrace tailWord_6308754 prefixEnd_6308754 3239423132974915204661575 := by
  unfold tailWord_6308754
  simp only [CollatzResearch.WordTrace]
  refine ⟨57524790446617295562045329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153399441190979454832120877 57524790446617295562045329)
  ·
    refine ⟨43143592834962971671533997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57524790446617295562045329 43143592834962971671533997)
    ·
      refine ⟨16178847313111114376825249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43143592834962971671533997 16178847313111114376825249)
      ·
        refine ⟨12134135484833335782618937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16178847313111114376825249 12134135484833335782618937)
        ·
          refine ⟨9100601613625001836964203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12134135484833335782618937 9100601613625001836964203)
          ·
            refine ⟨13650902420437502755446305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9100601613625001836964203 13650902420437502755446305)
            ·
              refine ⟨10238176815328127066584729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13650902420437502755446305 10238176815328127066584729)
              ·
                refine ⟨7678632611496095299938547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10238176815328127066584729 7678632611496095299938547)
                ·
                  refine ⟨11517948917244142949907821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7678632611496095299938547 11517948917244142949907821)
                  ·
                    refine ⟨4319230843966553606215433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11517948917244142949907821 4319230843966553606215433)
                    ·
                      refine ⟨3239423132974915204661575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4319230843966553606215433 3239423132974915204661575)
                      ·
                        rfl

theorem cell23_6308754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 2, 2, 1, 3, 2].length) (baseStart_6308754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6308754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6308754 prefixEnd_6308754 := by exact prefixLift 6308754
  have htrace : WordTrace (prefixWord ++ tailWord_6308754) baseStart_6308754 baseEnd_6308754 := by
    simpa [prefixWord, tailWord_6308754, baseEnd_6308754] using wordTrace_append hprefix tailTrace_6308754
  have hstable : (prefixWord ++ tailWord_6308754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6308754).length < 2 ^ (prefixWord ++ tailWord_6308754).sum := by decide
  have hdescent : baseEnd_6308754 < baseStart_6308754 := by decide
  rcases family_descends (prefixWord ++ tailWord_6308754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6308820 : List Nat := [2, 4, 1, 2, 1, 3, 2, 1, 2, 5]
def baseStart_6308820 : Nat := 118140960795 + 6308820 * 2 ^ 59
def prefixEnd_6308820 : Nat := 4983230072969 + 3 ^ 40 * 6308820 * 2
def baseEnd_6308820 : Nat := 1079819007566037315478757

theorem tailTrace_6308820 : CollatzResearch.WordTrace tailWord_6308820 prefixEnd_6308820 1079819007566037315478757 := by
  unfold tailWord_6308820
  simp only [CollatzResearch.WordTrace]
  refine ⟨115050784502115037760041957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153401046002820050346722609 115050784502115037760041957)
  ·
    refine ⟨21572022094146569580007867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 115050784502115037760041957 21572022094146569580007867)
    ·
      refine ⟨32358033141219854370011801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21572022094146569580007867 32358033141219854370011801)
      ·
        refine ⟨24268524855914890777508851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32358033141219854370011801 24268524855914890777508851)
        ·
          refine ⟨36402787283872336166263277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24268524855914890777508851 36402787283872336166263277)
          ·
            refine ⟨13651045231452126062348729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36402787283872336166263277 13651045231452126062348729)
            ·
              refine ⟨10238283923589094546761547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13651045231452126062348729 10238283923589094546761547)
              ·
                refine ⟨15357425885383641820142321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10238283923589094546761547 15357425885383641820142321)
                ·
                  refine ⟨11518069414037731365106741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15357425885383641820142321 11518069414037731365106741)
                  ·
                    refine ⟨1079819007566037315478757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11518069414037731365106741 1079819007566037315478757)
                    ·
                      rfl

theorem cell23_6308820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 2, 1, 2, 5].length) (baseStart_6308820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6308820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6308820 prefixEnd_6308820 := by exact prefixLift 6308820
  have htrace : WordTrace (prefixWord ++ tailWord_6308820) baseStart_6308820 baseEnd_6308820 := by
    simpa [prefixWord, tailWord_6308820, baseEnd_6308820] using wordTrace_append hprefix tailTrace_6308820
  have hstable : (prefixWord ++ tailWord_6308820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6308820).length < 2 ^ (prefixWord ++ tailWord_6308820).sum := by decide
  have hdescent : baseEnd_6308820 < baseStart_6308820 := by decide
  rcases family_descends (prefixWord ++ tailWord_6308820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6308823 : List Nat := [1, 1, 3, 2, 1, 1, 2, 1, 3, 6, 2]
def baseStart_6308823 : Nat := 118140960795 + 6308823 * 2 ^ 59
def prefixEnd_6308823 : Nat := 4983230072969 + 3 ^ 40 * 6308823 * 2
def baseEnd_6308823 : Nat := 3239458563140075434698757

theorem tailTrace_6308823 : CollatzResearch.WordTrace tailWord_6308823 prefixEnd_6308823 3239458563140075434698757 := by
  unfold tailWord_6308823
  simp only [CollatzResearch.WordTrace]
  refine ⟨230101678423219207032443123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153401118948812804688295415 230101678423219207032443123)
  ·
    refine ⟨345152517634828810548664685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230101678423219207032443123 345152517634828810548664685)
    ·
      refine ⟨129432194113060803955749257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 345152517634828810548664685 129432194113060803955749257)
      ·
        refine ⟨97074145584795602966811943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129432194113060803955749257 97074145584795602966811943)
        ·
          refine ⟨145611218377193404450217915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97074145584795602966811943 145611218377193404450217915)
          ·
            refine ⟨218416827565790106675326873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 145611218377193404450217915 218416827565790106675326873)
            ·
              refine ⟨163812620674342580006495155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 218416827565790106675326873 163812620674342580006495155)
              ·
                refine ⟨245718931011513870009742733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 163812620674342580006495155 245718931011513870009742733)
                ·
                  refine ⟨92144599129317701253653525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 245718931011513870009742733 92144599129317701253653525)
                  ·
                    refine ⟨4319278084186767246265009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 92144599129317701253653525 4319278084186767246265009)
                    ·
                      refine ⟨3239458563140075434698757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4319278084186767246265009 3239458563140075434698757)
                      ·
                        rfl

theorem cell23_6308823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 1, 3, 6, 2].length) (baseStart_6308823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6308823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6308823 prefixEnd_6308823 := by exact prefixLift 6308823
  have htrace : WordTrace (prefixWord ++ tailWord_6308823) baseStart_6308823 baseEnd_6308823 := by
    simpa [prefixWord, tailWord_6308823, baseEnd_6308823] using wordTrace_append hprefix tailTrace_6308823
  have hstable : (prefixWord ++ tailWord_6308823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6308823).length < 2 ^ (prefixWord ++ tailWord_6308823).sum := by decide
  have hdescent : baseEnd_6308823 < baseStart_6308823 := by decide
  rcases family_descends (prefixWord ++ tailWord_6308823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6308890 : List Nat := [3, 1, 1, 3, 1, 2, 1, 2, 5, 1, 3]
def baseStart_6308890 : Nat := 118140960795 + 6308890 * 2 ^ 59
def prefixEnd_6308890 : Nat := 4983230072969 + 3 ^ 40 * 6308890 * 2
def baseEnd_6308890 : Nat := 3239492966343926672560949

theorem tailTrace_6308890 : CollatzResearch.WordTrace tailWord_6308890 prefixEnd_6308890 3239492966343926672560949 := by
  unfold tailWord_6308890
  simp only [CollatzResearch.WordTrace]
  refine ⟨57526030528494119368783031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153402748075984318316754749 57526030528494119368783031)
  ·
    refine ⟨86289045792741179053174547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57526030528494119368783031 86289045792741179053174547)
    ·
      refine ⟨129433568689111768579761821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86289045792741179053174547 129433568689111768579761821)
      ·
        refine ⟨48537588258416913217410683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 129433568689111768579761821 48537588258416913217410683)
        ·
          refine ⟨72806382387625369826116025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48537588258416913217410683 72806382387625369826116025)
          ·
            refine ⟨54604786790719027369587019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72806382387625369826116025 54604786790719027369587019)
            ·
              refine ⟨81907180186078541054380529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54604786790719027369587019 81907180186078541054380529)
              ·
                refine ⟨61430385139558905790785397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 81907180186078541054380529 61430385139558905790785397)
                ·
                  refine ⟨5759098606833647417886131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 61430385139558905790785397 5759098606833647417886131)
                  ·
                    refine ⟨8638647910250471126829197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5759098606833647417886131 8638647910250471126829197)
                    ·
                      refine ⟨3239492966343926672560949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8638647910250471126829197 3239492966343926672560949)
                      ·
                        rfl

theorem cell23_6308890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 2, 5, 1, 3].length) (baseStart_6308890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6308890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6308890 prefixEnd_6308890 := by exact prefixLift 6308890
  have htrace : WordTrace (prefixWord ++ tailWord_6308890) baseStart_6308890 baseEnd_6308890 := by
    simpa [prefixWord, tailWord_6308890, baseEnd_6308890] using wordTrace_append hprefix tailTrace_6308890
  have hstable : (prefixWord ++ tailWord_6308890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6308890).length < 2 ^ (prefixWord ++ tailWord_6308890).sum := by decide
  have hdescent : baseEnd_6308890 < baseStart_6308890 := by decide
  rcases family_descends (prefixWord ++ tailWord_6308890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6308907 : List Nat := [1, 1, 1, 1, 2, 1, 5, 6, 1, 1, 3]
def baseStart_6308907 : Nat := 118140960795 + 6308907 * 2 ^ 59
def prefixEnd_6308907 : Nat := 4983230072969 + 3 ^ 40 * 6308907 * 2
def baseEnd_6308907 : Nat := 3239501695515053106048371

theorem tailTrace_6308907 : CollatzResearch.WordTrace tailWord_6308907 prefixEnd_6308907 3239501695515053106048371 := by
  unfold tailWord_6308907
  simp only [CollatzResearch.WordTrace]
  refine ⟨230104742154914889378500975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153403161436609926252333983 230104742154914889378500975)
  ·
    refine ⟨345157113232372334067751463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230104742154914889378500975 345157113232372334067751463)
    ·
      refine ⟨517735669848558501101627195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 345157113232372334067751463 517735669848558501101627195)
      ·
        refine ⟨776603504772837751652440793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 517735669848558501101627195 776603504772837751652440793)
        ·
          refine ⟨582452628579628313739330595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 776603504772837751652440793 582452628579628313739330595)
          ·
            refine ⟨873678942869442470608995893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 582452628579628313739330595 873678942869442470608995893)
            ·
              refine ⟨81907400894010231619593365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 873678942869442470608995893 81907400894010231619593365)
              ·
                refine ⟨3839409416906729607168439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 81907400894010231619593365 3839409416906729607168439)
                ·
                  refine ⟨5759114125360094410752659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3839409416906729607168439 5759114125360094410752659)
                  ·
                    refine ⟨8638671188040141616128989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5759114125360094410752659 8638671188040141616128989)
                    ·
                      refine ⟨3239501695515053106048371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8638671188040141616128989 3239501695515053106048371)
                      ·
                        rfl

theorem cell23_6308907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 6, 1, 1, 3].length) (baseStart_6308907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6308907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6308907 prefixEnd_6308907 := by exact prefixLift 6308907
  have htrace : WordTrace (prefixWord ++ tailWord_6308907) baseStart_6308907 baseEnd_6308907 := by
    simpa [prefixWord, tailWord_6308907, baseEnd_6308907] using wordTrace_append hprefix tailTrace_6308907
  have hstable : (prefixWord ++ tailWord_6308907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6308907).length < 2 ^ (prefixWord ++ tailWord_6308907).sum := by decide
  have hdescent : baseEnd_6308907 < baseStart_6308907 := by decide
  rcases family_descends (prefixWord ++ tailWord_6308907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6308923 : List Nat := [1, 1, 1, 1, 1, 2, 1, 3, 8, 4]
def baseStart_6308923 : Nat := 118140960795 + 6308923 * 2 ^ 59
def prefixEnd_6308923 : Nat := 4983230072969 + 3 ^ 40 * 6308923 * 2
def baseEnd_6308923 : Nat := 1079836637068508347816099

theorem tailTrace_6308923 : CollatzResearch.WordTrace tailWord_6308923 prefixEnd_6308923 1079836637068508347816099 := by
  unfold tailWord_6308923
  simp only [CollatzResearch.WordTrace]
  refine ⟨230105325722856924111083423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153403550481904616074055615 230105325722856924111083423)
  ·
    refine ⟨345157988584285386166625135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230105325722856924111083423 345157988584285386166625135)
    ·
      refine ⟨517736982876428079249937703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 345157988584285386166625135 517736982876428079249937703)
      ·
        refine ⟨776605474314642118874906555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 517736982876428079249937703 776605474314642118874906555)
        ·
          refine ⟨1164908211471963178312359833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 776605474314642118874906555 1164908211471963178312359833)
          ·
            refine ⟨873681158603972383734269875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1164908211471963178312359833 873681158603972383734269875)
            ·
              refine ⟨1310521737905958575601404813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 873681158603972383734269875 1310521737905958575601404813)
              ·
                refine ⟨491445651714734465850526805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1310521737905958575601404813 491445651714734465850526805)
                ·
                  refine ⟨5759128731032044521685861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 491445651714734465850526805 5759128731032044521685861)
                  ·
                    refine ⟨1079836637068508347816099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5759128731032044521685861 1079836637068508347816099)
                    ·
                      rfl

theorem cell23_6308923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 3, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 3, 8, 4].length) (baseStart_6308923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6308923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6308923 prefixEnd_6308923 := by exact prefixLift 6308923
  have htrace : WordTrace (prefixWord ++ tailWord_6308923) baseStart_6308923 baseEnd_6308923 := by
    simpa [prefixWord, tailWord_6308923, baseEnd_6308923] using wordTrace_append hprefix tailTrace_6308923
  have hstable : (prefixWord ++ tailWord_6308923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6308923).length < 2 ^ (prefixWord ++ tailWord_6308923).sum := by decide
  have hdescent : baseEnd_6308923 < baseStart_6308923 := by decide
  rcases family_descends (prefixWord ++ tailWord_6308923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6308934 : List Nat := [6, 1, 1, 1, 1, 2, 2, 1, 1, 5, 2]
def baseStart_6308934 : Nat := 118140960795 + 6308934 * 2 ^ 59
def prefixEnd_6308934 : Nat := 4983230072969 + 3 ^ 40 * 6308934 * 2
def baseEnd_6308934 : Nat := 3239515559492724500410747

theorem tailTrace_6308934 : CollatzResearch.WordTrace tailWord_6308934 prefixEnd_6308934 3239515559492724500410747 := by
  unfold tailWord_6308934
  simp only [CollatzResearch.WordTrace]
  refine ⟨7190803966431783530929183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 153403817950544715326489237 7190803966431783530929183)
  ·
    refine ⟨10786205949647675296393775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7190803966431783530929183 10786205949647675296393775)
    ·
      refine ⟨16179308924471512944590663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10786205949647675296393775 16179308924471512944590663)
      ·
        refine ⟨24268963386707269416885995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16179308924471512944590663 24268963386707269416885995)
        ·
          refine ⟨36403445080060904125328993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24268963386707269416885995 36403445080060904125328993)
          ·
            refine ⟨27302583810045678093996745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36403445080060904125328993 27302583810045678093996745)
            ·
              refine ⟨20476937857534258570497559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27302583810045678093996745 20476937857534258570497559)
              ·
                refine ⟨30715406786301387855746339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20476937857534258570497559 30715406786301387855746339)
                ·
                  refine ⟨46073110179452081783619509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30715406786301387855746339 46073110179452081783619509)
                  ·
                    refine ⟨4319354079323632667214329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 46073110179452081783619509 4319354079323632667214329)
                    ·
                      refine ⟨3239515559492724500410747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4319354079323632667214329 3239515559492724500410747)
                      ·
                        rfl

theorem cell23_6308934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 2, 1, 1, 5, 2].length) (baseStart_6308934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6308934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6308934 prefixEnd_6308934 := by exact prefixLift 6308934
  have htrace : WordTrace (prefixWord ++ tailWord_6308934) baseStart_6308934 baseEnd_6308934 := by
    simpa [prefixWord, tailWord_6308934, baseEnd_6308934] using wordTrace_append hprefix tailTrace_6308934
  have hstable : (prefixWord ++ tailWord_6308934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6308934).length < 2 ^ (prefixWord ++ tailWord_6308934).sum := by decide
  have hdescent : baseEnd_6308934 < baseStart_6308934 := by decide
  rcases family_descends (prefixWord ++ tailWord_6308934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6308941 : List Nat := [1, 6, 1, 1, 1, 2, 3, 3, 1, 1, 3]
def baseStart_6308941 : Nat := 118140960795 + 6308941 * 2 ^ 59
def prefixEnd_6308941 : Nat := 4983230072969 + 3 ^ 40 * 6308941 * 2
def baseEnd_6308941 : Nat := 3239519153857305973023215

theorem tailTrace_6308941 : CollatzResearch.WordTrace tailWord_6308941 prefixEnd_6308941 3239519153857305973023215 := by
  unfold tailWord_6308941
  simp only [CollatzResearch.WordTrace]
  refine ⟨230105982236791713185238677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153403988157861142123492451 230105982236791713185238677)
  ·
    refine ⟨10786217917349611555558063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 230105982236791713185238677 10786217917349611555558063)
    ·
      refine ⟨16179326876024417333337095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10786217917349611555558063 16179326876024417333337095)
      ·
        refine ⟨24268990314036626000005643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16179326876024417333337095 24268990314036626000005643)
        ·
          refine ⟨36403485471054939000008465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24268990314036626000005643 36403485471054939000008465)
          ·
            refine ⟨27302614103291204250006349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36403485471054939000008465 27302614103291204250006349)
            ·
              refine ⟨10238480288734201593752381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27302614103291204250006349 10238480288734201593752381)
              ·
                refine ⟨3839430108275325597657143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10238480288734201593752381 3839430108275325597657143)
                ·
                  refine ⟨5759145162412988396485715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3839430108275325597657143 5759145162412988396485715)
                  ·
                    refine ⟨8638717743619482594728573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5759145162412988396485715 8638717743619482594728573)
                    ·
                      refine ⟨3239519153857305973023215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8638717743619482594728573 3239519153857305973023215)
                      ·
                        rfl

theorem cell23_6308941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 3, 3, 1, 1, 3].length) (baseStart_6308941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6308941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6308941 prefixEnd_6308941 := by exact prefixLift 6308941
  have htrace : WordTrace (prefixWord ++ tailWord_6308941) baseStart_6308941 baseEnd_6308941 := by
    simpa [prefixWord, tailWord_6308941, baseEnd_6308941] using wordTrace_append hprefix tailTrace_6308941
  have hstable : (prefixWord ++ tailWord_6308941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6308941).length < 2 ^ (prefixWord ++ tailWord_6308941).sum := by decide
  have hdescent : baseEnd_6308941 < baseStart_6308941 := by decide
  rcases family_descends (prefixWord ++ tailWord_6308941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6308958 : List Nat := [4, 4, 1, 1, 1, 3, 1, 1, 3, 1, 3]
def baseStart_6308958 : Nat := 118140960795 + 6308958 * 2 ^ 59
def prefixEnd_6308958 : Nat := 4983230072969 + 3 ^ 40 * 6308958 * 2
def baseEnd_6308958 : Nat := 3239527883028432406510637

theorem tailTrace_6308958 : CollatzResearch.WordTrace tailWord_6308958 prefixEnd_6308958 3239527883028432406510637 := by
  unfold tailWord_6308958
  simp only [CollatzResearch.WordTrace]
  refine ⟨28763325284716265636075941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 153404401518486750059071685 28763325284716265636075941)
  ·
    refine ⟨5393123490884299806764239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28763325284716265636075941 5393123490884299806764239)
    ·
      refine ⟨8089685236326449710146359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5393123490884299806764239 8089685236326449710146359)
      ·
        refine ⟨12134527854489674565219539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8089685236326449710146359 12134527854489674565219539)
        ·
          refine ⟨18201791781734511847829309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12134527854489674565219539 18201791781734511847829309)
          ·
            refine ⟨6825671918150441942935991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18201791781734511847829309 6825671918150441942935991)
            ·
              refine ⟨10238507877225662914403987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6825671918150441942935991 10238507877225662914403987)
              ·
                refine ⟨15357761815838494371605981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10238507877225662914403987 15357761815838494371605981)
                ·
                  refine ⟨5759160680939435389352243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15357761815838494371605981 5759160680939435389352243)
                  ·
                    refine ⟨8638741021409153084028365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5759160680939435389352243 8638741021409153084028365)
                    ·
                      refine ⟨3239527883028432406510637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8638741021409153084028365 3239527883028432406510637)
                      ·
                        rfl

theorem cell23_6308958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 3, 1, 1, 3, 1, 3].length) (baseStart_6308958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6308958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6308958 prefixEnd_6308958 := by exact prefixLift 6308958
  have htrace : WordTrace (prefixWord ++ tailWord_6308958) baseStart_6308958 baseEnd_6308958 := by
    simpa [prefixWord, tailWord_6308958, baseEnd_6308958] using wordTrace_append hprefix tailTrace_6308958
  have hstable : (prefixWord ++ tailWord_6308958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6308958).length < 2 ^ (prefixWord ++ tailWord_6308958).sum := by decide
  have hdescent : baseEnd_6308958 < baseStart_6308958 := by decide
  rcases family_descends (prefixWord ++ tailWord_6308958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6308970 : List Nat := [3, 1, 3, 2, 2, 2, 2, 8]
def baseStart_6308970 : Nat := 118140960795 + 6308970 * 2 ^ 59
def prefixEnd_6308970 : Nat := 4983230072969 + 3 ^ 40 * 6308970 * 2
def baseEnd_6308970 : Nat := 119982742399862457761503

theorem tailTrace_6308970 : CollatzResearch.WordTrace tailWord_6308970 prefixEnd_6308970 119982742399862457761503 := by
  unfold tailWord_6308970
  simp only [CollatzResearch.WordTrace]
  refine ⟨57526759988421662784511091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153404693302457767425362909 57526759988421662784511091)
  ·
    refine ⟨86290139982632494176766637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57526759988421662784511091 86290139982632494176766637)
    ·
      refine ⟨32358802493487185316287489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86290139982632494176766637 32358802493487185316287489)
      ·
        refine ⟨24269101870115388987215617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32358802493487185316287489 24269101870115388987215617)
        ·
          refine ⟨18201826402586541740411713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24269101870115388987215617 18201826402586541740411713)
          ·
            refine ⟨13651369801939906305308785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18201826402586541740411713 13651369801939906305308785)
            ·
              refine ⟨10238527351454929728981589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13651369801939906305308785 10238527351454929728981589)
              ·
                refine ⟨119982742399862457761503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10238527351454929728981589 119982742399862457761503)
                ·
                  rfl

theorem cell23_6308970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 2, 8].length) (baseStart_6308970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6308970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6308970 prefixEnd_6308970 := by exact prefixLift 6308970
  have htrace : WordTrace (prefixWord ++ tailWord_6308970) baseStart_6308970 baseEnd_6308970 := by
    simpa [prefixWord, tailWord_6308970, baseEnd_6308970] using wordTrace_append hprefix tailTrace_6308970
  have hstable : (prefixWord ++ tailWord_6308970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6308970).length < 2 ^ (prefixWord ++ tailWord_6308970).sum := by decide
  have hdescent : baseEnd_6308970 < baseStart_6308970 := by decide
  rcases family_descends (prefixWord ++ tailWord_6308970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6308974 : List Nat := [4, 1, 2, 2, 1, 2, 4, 1, 2, 4]
def baseStart_6308974 : Nat := 118140960795 + 6308974 * 2 ^ 59
def prefixEnd_6308974 : Nat := 4983230072969 + 3 ^ 40 * 6308974 * 2
def baseEnd_6308974 : Nat := 1079845366239634781303521

theorem tailTrace_6308974 : CollatzResearch.WordTrace tailWord_6308974 prefixEnd_6308974 1079845366239634781303521 := by
  unfold tailWord_6308974
  simp only [CollatzResearch.WordTrace]
  refine ⟨28763398230709019977648747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 153404790563781439880793317 28763398230709019977648747)
  ·
    refine ⟨43145097346063529966473121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28763398230709019977648747 43145097346063529966473121)
    ·
      refine ⟨32358823009547647474854841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43145097346063529966473121 32358823009547647474854841)
      ·
        refine ⟨24269117257160735606141131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32358823009547647474854841 24269117257160735606141131)
        ·
          refine ⟨36403675885741103409211697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24269117257160735606141131 36403675885741103409211697)
          ·
            refine ⟨27302756914305827556908773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36403675885741103409211697 27302756914305827556908773)
            ·
              refine ⟨5119266921432342666920395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27302756914305827556908773 5119266921432342666920395)
              ·
                refine ⟨7678900382148514000380593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5119266921432342666920395 7678900382148514000380593)
                ·
                  refine ⟨5759175286611385500285445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7678900382148514000380593 5759175286611385500285445)
                  ·
                    refine ⟨1079845366239634781303521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5759175286611385500285445 1079845366239634781303521)
                    ·
                      rfl

theorem cell23_6308974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 4, 1, 2, 4].length) (baseStart_6308974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6308974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6308974 prefixEnd_6308974 := by exact prefixLift 6308974
  have htrace : WordTrace (prefixWord ++ tailWord_6308974) baseStart_6308974 baseEnd_6308974 := by
    simpa [prefixWord, tailWord_6308974, baseEnd_6308974] using wordTrace_append hprefix tailTrace_6308974
  have hstable : (prefixWord ++ tailWord_6308974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6308974).length < 2 ^ (prefixWord ++ tailWord_6308974).sum := by decide
  have hdescent : baseEnd_6308974 < baseStart_6308974 := by decide
  rcases family_descends (prefixWord ++ tailWord_6308974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6308981 : List Nat := [1, 3, 4, 3, 1, 2, 1, 2, 1, 1, 4]
def baseStart_6308981 : Nat := 118140960795 + 6308981 * 2 ^ 59
def prefixEnd_6308981 : Nat := 4983230072969 + 3 ^ 40 * 6308981 * 2
def baseEnd_6308981 : Nat := 3239539693083485816523031

theorem tailTrace_6308981 : CollatzResearch.WordTrace tailWord_6308981 prefixEnd_6308981 3239539693083485816523031 := by
  unfold tailWord_6308981
  simp only [CollatzResearch.WordTrace]
  refine ⟨230107441156646800016694797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153404960771097866677796531 230107441156646800016694797)
  ·
    refine ⟨86290290433742550006260549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 230107441156646800016694797 86290290433742550006260549)
    ·
      refine ⟨16179429456326728126173853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 86290290433742550006260549 16179429456326728126173853)
      ·
        refine ⟨6067286046122523047315195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16179429456326728126173853 6067286046122523047315195)
        ·
          refine ⟨9100929069183784570972793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6067286046122523047315195 9100929069183784570972793)
          ·
            refine ⟨6825696801887838428229595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9100929069183784570972793 6825696801887838428229595)
            ·
              refine ⟨10238545202831757642344393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6825696801887838428229595 10238545202831757642344393)
              ·
                refine ⟨7678908902123818231758295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10238545202831757642344393 7678908902123818231758295)
                ·
                  refine ⟨11518363353185727347637443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7678908902123818231758295 11518363353185727347637443)
                  ·
                    refine ⟨17277545029778591021456165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11518363353185727347637443 17277545029778591021456165)
                    ·
                      refine ⟨3239539693083485816523031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17277545029778591021456165 3239539693083485816523031)
                      ·
                        rfl

theorem cell23_6308981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 2, 1, 2, 1, 1, 4].length) (baseStart_6308981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6308981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6308981 prefixEnd_6308981 := by exact prefixLift 6308981
  have htrace : WordTrace (prefixWord ++ tailWord_6308981) baseStart_6308981 baseEnd_6308981 := by
    simpa [prefixWord, tailWord_6308981, baseEnd_6308981] using wordTrace_append hprefix tailTrace_6308981
  have hstable : (prefixWord ++ tailWord_6308981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6308981).length < 2 ^ (prefixWord ++ tailWord_6308981).sum := by decide
  have hdescent : baseEnd_6308981 < baseStart_6308981 := by decide
  rcases family_descends (prefixWord ++ tailWord_6308981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6308997 : List Nat := [1, 3, 1, 1, 6, 1, 1, 2, 1, 3, 3]
def baseStart_6308997 : Nat := 118140960795 + 6308997 * 2 ^ 59
def prefixEnd_6308997 : Nat := 4983230072969 + 3 ^ 40 * 6308997 * 2
def baseEnd_6308997 : Nat := 3239547908773957753922957

theorem tailTrace_6308997 : CollatzResearch.WordTrace tailWord_6308997 prefixEnd_6308997 3239547908773957753922957 := by
  unfold tailWord_6308997
  simp only [CollatzResearch.WordTrace]
  refine ⟨230108024724588834749277245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153405349816392556499518163 230108024724588834749277245)
  ·
    refine ⟨86290509271720813030978967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 230108024724588834749277245 86290509271720813030978967)
    ·
      refine ⟨129435763907581219546468451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86290509271720813030978967 129435763907581219546468451)
      ·
        refine ⟨194153645861371829319702677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129435763907581219546468451 194153645861371829319702677)
        ·
          refine ⟨9100952149751804499361063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 194153645861371829319702677 9100952149751804499361063)
          ·
            refine ⟨13651428224627706749041595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9100952149751804499361063 13651428224627706749041595)
            ·
              refine ⟨20477142336941560123562393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13651428224627706749041595 20477142336941560123562393)
              ·
                refine ⟨15357856752706170092671795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20477142336941560123562393 15357856752706170092671795)
                ·
                  refine ⟨23036785129059255139007693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15357856752706170092671795 23036785129059255139007693)
                  ·
                    refine ⟨8638794423397220677127885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23036785129059255139007693 8638794423397220677127885)
                    ·
                      refine ⟨3239547908773957753922957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8638794423397220677127885 3239547908773957753922957)
                      ·
                        rfl

theorem cell23_6308997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 1, 2, 1, 3, 3].length) (baseStart_6308997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6308997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6308997 prefixEnd_6308997 := by exact prefixLift 6308997
  have htrace : WordTrace (prefixWord ++ tailWord_6308997) baseStart_6308997 baseEnd_6308997 := by
    simpa [prefixWord, tailWord_6308997, baseEnd_6308997] using wordTrace_append hprefix tailTrace_6308997
  have hstable : (prefixWord ++ tailWord_6308997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6308997).length < 2 ^ (prefixWord ++ tailWord_6308997).sum := by decide
  have hdescent : baseEnd_6308997 < baseStart_6308997 := by decide
  rcases family_descends (prefixWord ++ tailWord_6308997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6309003 : List Nat := [1, 1, 1, 1, 4, 1, 1, 2, 4, 3, 4]
def baseStart_6309003 : Nat := 118140960795 + 6309003 * 2 ^ 59
def prefixEnd_6309003 : Nat := 4983230072969 + 3 ^ 40 * 6309003 * 2
def baseEnd_6309003 : Nat := 3239550989657884730447929

theorem tailTrace_6309003 : CollatzResearch.WordTrace tailWord_6309003 prefixEnd_6309003 3239550989657884730447929 := by
  unfold tailWord_6309003
  simp only [CollatzResearch.WordTrace]
  refine ⟨230108243562567097773995663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153405495708378065182663775 230108243562567097773995663)
  ·
    refine ⟨345162365343850646660993495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230108243562567097773995663 345162365343850646660993495)
    ·
      refine ⟨517743548015775969991490243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 345162365343850646660993495 517743548015775969991490243)
      ·
        refine ⟨776615322023663954987235365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 517743548015775969991490243 776615322023663954987235365)
        ·
          refine ⟨145615372879436991560106631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 776615322023663954987235365 145615372879436991560106631)
          ·
            refine ⟨218423059319155487340159947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 145615372879436991560106631 218423059319155487340159947)
            ·
              refine ⟨327634588978733231010239921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 218423059319155487340159947 327634588978733231010239921)
              ·
                refine ⟨245725941734049923257679941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 327634588978733231010239921 245725941734049923257679941)
                ·
                  refine ⟨46073614075134360610814989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 245725941734049923257679941 46073614075134360610814989)
                  ·
                    refine ⟨17277605278175385229055621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 46073614075134360610814989 17277605278175385229055621)
                    ·
                      refine ⟨3239550989657884730447929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17277605278175385229055621 3239550989657884730447929)
                      ·
                        rfl

theorem cell23_6309003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 2, 4, 3, 4].length) (baseStart_6309003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6309003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6309003 prefixEnd_6309003 := by exact prefixLift 6309003
  have htrace : WordTrace (prefixWord ++ tailWord_6309003) baseStart_6309003 baseEnd_6309003 := by
    simpa [prefixWord, tailWord_6309003, baseEnd_6309003] using wordTrace_append hprefix tailTrace_6309003
  have hstable : (prefixWord ++ tailWord_6309003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6309003).length < 2 ^ (prefixWord ++ tailWord_6309003).sum := by decide
  have hdescent : baseEnd_6309003 < baseStart_6309003 := by decide
  rcases family_descends (prefixWord ++ tailWord_6309003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6309020 : List Nat := [2, 2, 3, 2, 1, 2, 1, 1, 2, 3, 4]
def baseStart_6309020 : Nat := 118140960795 + 6309020 * 2 ^ 59
def prefixEnd_6309020 : Nat := 4983230072969 + 3 ^ 40 * 6309020 * 2
def baseEnd_6309020 : Nat := 3239559718829011163935351

theorem tailTrace_6309020 : CollatzResearch.WordTrace tailWord_6309020 prefixEnd_6309020 3239559718829011163935351 := by
  unfold tailWord_6309020
  simp only [CollatzResearch.WordTrace]
  refine ⟨115054431801752754838682257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153405909069003673118243009 115054431801752754838682257)
  ·
    refine ⟨86290823851314566129011693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115054431801752754838682257 86290823851314566129011693)
    ·
      refine ⟨32359058944242962298379385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86290823851314566129011693 32359058944242962298379385)
      ·
        refine ⟨24269294208182221723784539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32359058944242962298379385 24269294208182221723784539)
        ·
          refine ⟨36403941312273332585676809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24269294208182221723784539 36403941312273332585676809)
          ·
            refine ⟨27302955984204999439257607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36403941312273332585676809 27302955984204999439257607)
            ·
              refine ⟨40954433976307499158886411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27302955984204999439257607 40954433976307499158886411)
              ·
                refine ⟨61431650964461248738329617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40954433976307499158886411 61431650964461248738329617)
                ·
                  refine ⟨46073738223345936553747213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 61431650964461248738329617 46073738223345936553747213)
                  ·
                    refine ⟨17277651833754726207655205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 46073738223345936553747213 17277651833754726207655205)
                    ·
                      refine ⟨3239559718829011163935351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17277651833754726207655205 3239559718829011163935351)
                      ·
                        rfl

theorem cell23_6309020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 1, 2, 3, 4].length) (baseStart_6309020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6309020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6309020 prefixEnd_6309020 := by exact prefixLift 6309020
  have htrace : WordTrace (prefixWord ++ tailWord_6309020) baseStart_6309020 baseEnd_6309020 := by
    simpa [prefixWord, tailWord_6309020, baseEnd_6309020] using wordTrace_append hprefix tailTrace_6309020
  have hstable : (prefixWord ++ tailWord_6309020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6309020).length < 2 ^ (prefixWord ++ tailWord_6309020).sum := by decide
  have hdescent : baseEnd_6309020 < baseStart_6309020 := by decide
  rcases family_descends (prefixWord ++ tailWord_6309020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6309043 : List Nat := [1, 1, 1, 2, 3, 2, 3, 1, 9]
def baseStart_6309043 : Nat := 118140960795 + 6309043 * 2 ^ 59
def prefixEnd_6309043 : Nat := 4983230072969 + 3 ^ 40 * 6309043 * 2
def baseEnd_6309043 : Nat := 359952392098229397105305

theorem tailTrace_6309043 : CollatzResearch.WordTrace tailWord_6309043 prefixEnd_6309043 359952392098229397105305 := by
  unfold tailWord_6309043
  simp only [CollatzResearch.WordTrace]
  refine ⟨230109702482422184605451783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153406468321614789736967855 230109702482422184605451783)
  ·
    refine ⟨345164553723633276908177675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230109702482422184605451783 345164553723633276908177675)
    ·
      refine ⟨517746830585449915362266513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 345164553723633276908177675 517746830585449915362266513)
      ·
        refine ⟨388310122939087436521699885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 517746830585449915362266513 388310122939087436521699885)
        ·
          refine ⟨145616296102157788695637457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 388310122939087436521699885 145616296102157788695637457)
          ·
            refine ⟨109212222076618341521728093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 145616296102157788695637457 109212222076618341521728093)
            ·
              refine ⟨40954583278731878070648035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 109212222076618341521728093 40954583278731878070648035)
              ·
                refine ⟨61431874918097817105972053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40954583278731878070648035 61431874918097817105972053)
                ·
                  refine ⟨359952392098229397105305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 61431874918097817105972053 359952392098229397105305)
                  ·
                    rfl

theorem cell23_6309043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 1, 9].length) (baseStart_6309043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6309043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6309043 prefixEnd_6309043 := by exact prefixLift 6309043
  have htrace : WordTrace (prefixWord ++ tailWord_6309043) baseStart_6309043 baseEnd_6309043 := by
    simpa [prefixWord, tailWord_6309043, baseEnd_6309043] using wordTrace_append hprefix tailTrace_6309043
  have hstable : (prefixWord ++ tailWord_6309043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6309043).length < 2 ^ (prefixWord ++ tailWord_6309043).sum := by decide
  have hdescent : baseEnd_6309043 < baseStart_6309043 := by decide
  rcases family_descends (prefixWord ++ tailWord_6309043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6309054 : List Nat := [4, 2, 1, 1, 3, 1, 2, 2, 1, 4, 2]
def baseStart_6309054 : Nat := 118140960795 + 6309054 * 2 ^ 59
def prefixEnd_6309054 : Nat := 4983230072969 + 3 ^ 40 * 6309054 * 2
def baseEnd_6309054 : Nat := 3239577177171264030910195

theorem tailTrace_6309054 : CollatzResearch.WordTrace tailWord_6309054 prefixEnd_6309054 3239577177171264030910195 := by
  unfold tailWord_6309054
  simp only [CollatzResearch.WordTrace]
  refine ⟨28763762960672791685512777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 153406735790254888989401477 28763762960672791685512777)
  ·
    refine ⟨21572822220504593764134583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28763762960672791685512777 21572822220504593764134583)
    ·
      refine ⟨32359233330756890646201875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21572822220504593764134583 32359233330756890646201875)
      ·
        refine ⟨48538849996135335969302813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32359233330756890646201875 48538849996135335969302813)
        ·
          refine ⟨18202068748550750988488555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48538849996135335969302813 18202068748550750988488555)
          ·
            refine ⟨27303103122826126482732833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18202068748550750988488555 27303103122826126482732833)
            ·
              refine ⟨20477327342119594862049625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27303103122826126482732833 20477327342119594862049625)
              ·
                refine ⟨15357995506589696146537219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20477327342119594862049625 15357995506589696146537219)
                ·
                  refine ⟨23036993259884544219805829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15357995506589696146537219 23036993259884544219805829)
                  ·
                    refine ⟨4319436236228352041213593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23036993259884544219805829 4319436236228352041213593)
                    ·
                      refine ⟨3239577177171264030910195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4319436236228352041213593 3239577177171264030910195)
                      ·
                        rfl

theorem cell23_6309054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 2, 2, 1, 4, 2].length) (baseStart_6309054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6309054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6309054 prefixEnd_6309054 := by exact prefixLift 6309054
  have htrace : WordTrace (prefixWord ++ tailWord_6309054) baseStart_6309054 baseEnd_6309054 := by
    simpa [prefixWord, tailWord_6309054, baseEnd_6309054] using wordTrace_append hprefix tailTrace_6309054
  have hstable : (prefixWord ++ tailWord_6309054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6309054).length < 2 ^ (prefixWord ++ tailWord_6309054).sum := by decide
  have hdescent : baseEnd_6309054 < baseStart_6309054 := by decide
  rcases family_descends (prefixWord ++ tailWord_6309054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6309077 : List Nat := [1, 3, 2, 4, 1, 2, 2, 1, 7]
def baseStart_6309077 : Nat := 118140960795 + 6309077 * 2 ^ 59
def prefixEnd_6309077 : Nat := 4983230072969 + 3 ^ 40 * 6309077 * 2
def baseEnd_6309077 : Nat := 359954331914035271213621

theorem tailTrace_6309077 : CollatzResearch.WordTrace tailWord_6309077 prefixEnd_6309077 359954331914035271213621 := by
  unfold tailWord_6309077
  simp only [CollatzResearch.WordTrace]
  refine ⟨230110942564299008412189485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153407295042866005608126323 230110942564299008412189485)
  ·
    refine ⟨86291603461612128154571057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 230110942564299008412189485 86291603461612128154571057)
    ·
      refine ⟨64718702596209096115928293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86291603461612128154571057 64718702596209096115928293)
      ·
        refine ⟨12134756736789205521736555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 64718702596209096115928293 12134756736789205521736555)
        ·
          refine ⟨18202135105183808282604833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12134756736789205521736555 18202135105183808282604833)
          ·
            refine ⟨13651601328887856211953625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18202135105183808282604833 13651601328887856211953625)
            ·
              refine ⟨10238700996665892158965219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13651601328887856211953625 10238700996665892158965219)
              ·
                refine ⟨15358051494998838238447829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10238700996665892158965219 15358051494998838238447829)
                ·
                  refine ⟨359954331914035271213621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15358051494998838238447829 359954331914035271213621)
                  ·
                    rfl

theorem cell23_6309077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 2, 1, 7].length) (baseStart_6309077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6309077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6309077 prefixEnd_6309077 := by exact prefixLift 6309077
  have htrace : WordTrace (prefixWord ++ tailWord_6309077) baseStart_6309077 baseEnd_6309077 := by
    simpa [prefixWord, tailWord_6309077, baseEnd_6309077] using wordTrace_append hprefix tailTrace_6309077
  have hstable : (prefixWord ++ tailWord_6309077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6309077).length < 2 ^ (prefixWord ++ tailWord_6309077).sum := by decide
  have hdescent : baseEnd_6309077 < baseStart_6309077 := by decide
  rcases family_descends (prefixWord ++ tailWord_6309077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6309187 : List Nat := [1, 1, 1, 3, 1, 3, 1, 2, 3, 5, 2]
def baseStart_6309187 : Nat := 118140960795 + 6309187 * 2 ^ 59
def prefixEnd_6309187 : Nat := 4983230072969 + 3 ^ 40 * 6309187 * 2
def baseEnd_6309187 : Nat := 3239645470098312010547083

theorem tailTrace_6309187 : CollatzResearch.WordTrace tailWord_6309187 prefixEnd_6309187 3239645470098312010547083 := by
  unfold tailWord_6309187
  simp only [CollatzResearch.WordTrace]
  refine ⟨230114954593900497198693815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153409969729266998132462543 230114954593900497198693815)
  ·
    refine ⟨345172431890850745798040723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230114954593900497198693815 345172431890850745798040723)
    ·
      refine ⟨517758647836276118697061085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 345172431890850745798040723 517758647836276118697061085)
      ·
        refine ⟨194159492938603544511397907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 517758647836276118697061085 194159492938603544511397907)
        ·
          refine ⟨291239239407905316767096861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 194159492938603544511397907 291239239407905316767096861)
          ·
            refine ⟨109214714777964493787661323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 291239239407905316767096861 109214714777964493787661323)
            ·
              refine ⟨163822072166946740681491985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109214714777964493787661323 163822072166946740681491985)
              ·
                refine ⟨122866554125210055511118989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 163822072166946740681491985 122866554125210055511118989)
                ·
                  refine ⟨46074957796953770816669621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 122866554125210055511118989 46074957796953770816669621)
                  ·
                    refine ⟨4319527293464416014062777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 46074957796953770816669621 4319527293464416014062777)
                    ·
                      refine ⟨3239645470098312010547083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4319527293464416014062777 3239645470098312010547083)
                      ·
                        rfl

theorem cell23_6309187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 2, 3, 5, 2].length) (baseStart_6309187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6309187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6309187 prefixEnd_6309187 := by exact prefixLift 6309187
  have htrace : WordTrace (prefixWord ++ tailWord_6309187) baseStart_6309187 baseEnd_6309187 := by
    simpa [prefixWord, tailWord_6309187, baseEnd_6309187] using wordTrace_append hprefix tailTrace_6309187
  have hstable : (prefixWord ++ tailWord_6309187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6309187).length < 2 ^ (prefixWord ++ tailWord_6309187).sum := by decide
  have hdescent : baseEnd_6309187 < baseStart_6309187 := by decide
  rcases family_descends (prefixWord ++ tailWord_6309187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6309188 : List Nat := [2, 3, 4, 1, 1, 2, 1, 4, 1, 4]
def baseStart_6309188 : Nat := 118140960795 + 6309188 * 2 ^ 59
def prefixEnd_6309188 : Nat := 4983230072969 + 3 ^ 40 * 6309188 * 2
def baseEnd_6309188 : Nat := 1079881994526322168878193

theorem tailTrace_6309188 : CollatzResearch.WordTrace tailWord_6309188 prefixEnd_6309188 1079881994526322168878193 := by
  unfold tailWord_6309188
  simp only [CollatzResearch.WordTrace]
  refine ⟨115057495533448437184740109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153409994044597916246320145 115057495533448437184740109)
  ·
    refine ⟨43146560825043163944277541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115057495533448437184740109 43146560825043163944277541)
    ·
      refine ⟨8089980154695593239552039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43146560825043163944277541 8089980154695593239552039)
      ·
        refine ⟨12134970232043389859328059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8089980154695593239552039 12134970232043389859328059)
        ·
          refine ⟨18202455348065084788992089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12134970232043389859328059 18202455348065084788992089)
          ·
            refine ⟨13651841511048813591744067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18202455348065084788992089 13651841511048813591744067)
            ·
              refine ⟨20477762266573220387616101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13651841511048813591744067 20477762266573220387616101)
              ·
                refine ⟨3839580424982478822678019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20477762266573220387616101 3839580424982478822678019)
                ·
                  refine ⟨5759370637473718234017029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3839580424982478822678019 5759370637473718234017029)
                  ·
                    refine ⟨1079881994526322168878193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5759370637473718234017029 1079881994526322168878193)
                    ·
                      rfl

theorem cell23_6309188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 1, 4, 1, 4].length) (baseStart_6309188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6309188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6309188 prefixEnd_6309188 := by exact prefixLift 6309188
  have htrace : WordTrace (prefixWord ++ tailWord_6309188) baseStart_6309188 baseEnd_6309188 := by
    simpa [prefixWord, tailWord_6309188, baseEnd_6309188] using wordTrace_append hprefix tailTrace_6309188
  have hstable : (prefixWord ++ tailWord_6309188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6309188).length < 2 ^ (prefixWord ++ tailWord_6309188).sum := by decide
  have hdescent : baseEnd_6309188 < baseStart_6309188 := by decide
  rcases family_descends (prefixWord ++ tailWord_6309188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6309204 : List Nat := [2, 4, 1, 1, 2, 1, 2, 2, 1, 5, 2]
def baseStart_6309204 : Nat := 118140960795 + 6309204 * 2 ^ 59
def prefixEnd_6309204 : Nat := 4983230072969 + 3 ^ 40 * 6309204 * 2
def baseEnd_6309204 : Nat := 3239654199269438444034505

theorem tailTrace_6309204 : CollatzResearch.WordTrace tailWord_6309204 prefixEnd_6309204 3239654199269438444034505 := by
  unfold tailWord_6309204
  simp only [CollatzResearch.WordTrace]
  refine ⟨115057787317419454551031333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153410383089892606068041777 115057787317419454551031333)
  ·
    refine ⟨21573335122016147728318375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 115057787317419454551031333 21573335122016147728318375)
    ·
      refine ⟨32360002683024221592477563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21573335122016147728318375 32360002683024221592477563)
      ·
        refine ⟨48540004024536332388716345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32360002683024221592477563 48540004024536332388716345)
        ·
          refine ⟨36405003018402249291537259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48540004024536332388716345 36405003018402249291537259)
          ·
            refine ⟨54607504527603373937305889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36405003018402249291537259 54607504527603373937305889)
            ·
              refine ⟨40955628395702530452979417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54607504527603373937305889 40955628395702530452979417)
              ·
                refine ⟨30716721296776897839734563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40955628395702530452979417 30716721296776897839734563)
                ·
                  refine ⟨46075081945165346759601845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30716721296776897839734563 46075081945165346759601845)
                  ·
                    refine ⟨4319538932359251258712673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 46075081945165346759601845 4319538932359251258712673)
                    ·
                      refine ⟨3239654199269438444034505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4319538932359251258712673 3239654199269438444034505)
                      ·
                        rfl

theorem cell23_6309204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 2, 1, 5, 2].length) (baseStart_6309204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6309204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6309204 prefixEnd_6309204 := by exact prefixLift 6309204
  have htrace : WordTrace (prefixWord ++ tailWord_6309204) baseStart_6309204 baseEnd_6309204 := by
    simpa [prefixWord, tailWord_6309204, baseEnd_6309204] using wordTrace_append hprefix tailTrace_6309204
  have hstable : (prefixWord ++ tailWord_6309204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6309204).length < 2 ^ (prefixWord ++ tailWord_6309204).sum := by decide
  have hdescent : baseEnd_6309204 < baseStart_6309204 := by decide
  rcases family_descends (prefixWord ++ tailWord_6309204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6309228 : List Nat := [2, 2, 1, 1, 5, 2, 2, 3, 1, 1, 3]
def baseStart_6309228 : Nat := 118140960795 + 6309228 * 2 ^ 59
def prefixEnd_6309228 : Nat := 4983230072969 + 3 ^ 40 * 6309228 * 2
def baseEnd_6309228 : Nat := 3239666522805146350134395

theorem tailTrace_6309228 : CollatzResearch.WordTrace tailWord_6309228 prefixEnd_6309228 3239666522805146350134395 := by
  unfold tailWord_6309228
  simp only [CollatzResearch.WordTrace]
  refine ⟨115058224993375980600468169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153410966657834640800624225 115058224993375980600468169)
  ·
    refine ⟨86293668745031985450351127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115058224993375980600468169 86293668745031985450351127)
    ·
      refine ⟨129440503117547978175526691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86293668745031985450351127 129440503117547978175526691)
      ·
        refine ⟨194160754676321967263290037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129440503117547978175526691 194160754676321967263290037)
        ·
          refine ⟨18202570750905184430933441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 194160754676321967263290037 18202570750905184430933441)
          ·
            refine ⟨13651928063178888323200081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18202570750905184430933441 13651928063178888323200081)
            ·
              refine ⟨10238946047384166242400061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13651928063178888323200081 10238946047384166242400061)
              ·
                refine ⟨3839604767769062340900023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10238946047384166242400061 3839604767769062340900023)
                ·
                  refine ⟨5759407151653593511350035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3839604767769062340900023 5759407151653593511350035)
                  ·
                    refine ⟨8639110727480390267025053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5759407151653593511350035 8639110727480390267025053)
                    ·
                      refine ⟨3239666522805146350134395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8639110727480390267025053 3239666522805146350134395)
                      ·
                        rfl

theorem cell23_6309228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 2, 3, 1, 1, 3].length) (baseStart_6309228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6309228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6309228 prefixEnd_6309228 := by exact prefixLift 6309228
  have htrace : WordTrace (prefixWord ++ tailWord_6309228) baseStart_6309228 baseEnd_6309228 := by
    simpa [prefixWord, tailWord_6309228, baseEnd_6309228] using wordTrace_append hprefix tailTrace_6309228
  have hstable : (prefixWord ++ tailWord_6309228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6309228).length < 2 ^ (prefixWord ++ tailWord_6309228).sum := by decide
  have hdescent : baseEnd_6309228 < baseStart_6309228 := by decide
  rcases family_descends (prefixWord ++ tailWord_6309228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6309234 : List Nat := [3, 2, 1, 2, 1, 2, 3, 3, 1, 1, 4]
def baseStart_6309234 : Nat := 118140960795 + 6309234 * 2 ^ 59
def prefixEnd_6309234 : Nat := 4983230072969 + 3 ^ 40 * 6309234 * 2
def baseEnd_6309234 : Nat := 3239669603689073326659367

theorem tailTrace_6309234 : CollatzResearch.WordTrace tailWord_6309234 prefixEnd_6309234 3239669603689073326659367 := by
  unfold tailWord_6309234
  simp only [CollatzResearch.WordTrace]
  refine ⟨57529167206182556056413689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153411112549820149483769837 57529167206182556056413689)
  ·
    refine ⟨43146875404636917042310267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57529167206182556056413689 43146875404636917042310267)
    ·
      refine ⟨64720313106955375563465401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43146875404636917042310267 64720313106955375563465401)
      ·
        refine ⟨48540234830216531672599051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64720313106955375563465401 48540234830216531672599051)
        ·
          refine ⟨72810352245324797508898577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48540234830216531672599051 72810352245324797508898577)
          ·
            refine ⟨54607764183993598131673933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72810352245324797508898577 54607764183993598131673933)
            ·
              refine ⟨20477911568997599299377725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54607764183993598131673933 20477911568997599299377725)
              ·
                refine ⟨7679216838374099737266647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20477911568997599299377725 7679216838374099737266647)
                ·
                  refine ⟨11518825257561149605899971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7679216838374099737266647 11518825257561149605899971)
                  ·
                    refine ⟨17278237886341724408849957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11518825257561149605899971 17278237886341724408849957)
                    ·
                      refine ⟨3239669603689073326659367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17278237886341724408849957 3239669603689073326659367)
                      ·
                        rfl

theorem cell23_6309234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 3, 3, 1, 1, 4].length) (baseStart_6309234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6309234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6309234 prefixEnd_6309234 := by exact prefixLift 6309234
  have htrace : WordTrace (prefixWord ++ tailWord_6309234) baseStart_6309234 baseEnd_6309234 := by
    simpa [prefixWord, tailWord_6309234, baseEnd_6309234] using wordTrace_append hprefix tailTrace_6309234
  have hstable : (prefixWord ++ tailWord_6309234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6309234).length < 2 ^ (prefixWord ++ tailWord_6309234).sum := by decide
  have hdescent : baseEnd_6309234 < baseStart_6309234 := by decide
  rcases family_descends (prefixWord ++ tailWord_6309234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6309251 : List Nat := [1, 1, 1, 3, 5, 1, 1, 3, 3, 2, 2]
def baseStart_6309251 : Nat := 118140960795 + 6309251 * 2 ^ 59
def prefixEnd_6309251 : Nat := 4983230072969 + 3 ^ 40 * 6309251 * 2
def baseEnd_6309251 : Nat := 3239678332860199760146789

theorem tailTrace_6309251 : CollatzResearch.WordTrace tailWord_6309251 prefixEnd_6309251 3239678332860199760146789 := by
  unfold tailWord_6309251
  simp only [CollatzResearch.WordTrace]
  refine ⟨230117288865668636129023607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153411525910445757419349071 230117288865668636129023607)
  ·
    refine ⟨345175933298502954193535411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230117288865668636129023607 345175933298502954193535411)
    ·
      refine ⟨517763899947754431290303117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 345175933298502954193535411 517763899947754431290303117)
      ·
        refine ⟨194161462480407911733863669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 517763899947754431290303117 194161462480407911733863669)
        ·
          refine ⟨18202637107538241725049719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 194161462480407911733863669 18202637107538241725049719)
          ·
            refine ⟨27303955661307362587574579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18202637107538241725049719 27303955661307362587574579)
            ·
              refine ⟨40955933491961043881361869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27303955661307362587574579 40955933491961043881361869)
              ·
                refine ⟨15358475059485391455510701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40955933491961043881361869 15358475059485391455510701)
                ·
                  refine ⟨5759428147307021795816513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15358475059485391455510701 5759428147307021795816513)
                  ·
                    refine ⟨4319571110480266346862385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5759428147307021795816513 4319571110480266346862385)
                    ·
                      refine ⟨3239678332860199760146789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4319571110480266346862385 3239678332860199760146789)
                      ·
                        rfl

theorem cell23_6309251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 3, 3, 2, 2].length) (baseStart_6309251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6309251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6309251 prefixEnd_6309251 := by exact prefixLift 6309251
  have htrace : WordTrace (prefixWord ++ tailWord_6309251) baseStart_6309251 baseEnd_6309251 := by
    simpa [prefixWord, tailWord_6309251, baseEnd_6309251] using wordTrace_append hprefix tailTrace_6309251
  have hstable : (prefixWord ++ tailWord_6309251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6309251).length < 2 ^ (prefixWord ++ tailWord_6309251).sum := by decide
  have hdescent : baseEnd_6309251 < baseStart_6309251 := by decide
  rcases family_descends (prefixWord ++ tailWord_6309251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6309268 : List Nat := [2, 4, 2, 1, 2, 1, 2, 2, 3, 2, 2]
def baseStart_6309268 : Nat := 118140960795 + 6309268 * 2 ^ 59
def prefixEnd_6309268 : Nat := 4983230072969 + 3 ^ 40 * 6309268 * 2
def baseEnd_6309268 : Nat := 3239687062031326193634211

theorem tailTrace_6309268 : CollatzResearch.WordTrace tailWord_6309268 prefixEnd_6309268 3239687062031326193634211 := by
  unfold tailWord_6309268
  simp only [CollatzResearch.WordTrace]
  refine ⟨115058954453303524016196229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153411939271071365354928305 115058954453303524016196229)
  ·
    refine ⟨21573553959994410753036793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 115058954453303524016196229 21573553959994410753036793)
    ·
      refine ⟨16180165469995808064777595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21573553959994410753036793 16180165469995808064777595)
      ·
        refine ⟨24270248204993712097166393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16180165469995808064777595 24270248204993712097166393)
        ·
          refine ⟨18202686153745284072874795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24270248204993712097166393 18202686153745284072874795)
          ·
            refine ⟨27304029230617926109312193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18202686153745284072874795 27304029230617926109312193)
            ·
              refine ⟨20478021922963444581984145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27304029230617926109312193 20478021922963444581984145)
              ·
                refine ⟨15358516442222583436488109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20478021922963444581984145 15358516442222583436488109)
                ·
                  refine ⟨5759443665833468788683041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15358516442222583436488109 5759443665833468788683041)
                  ·
                    refine ⟨4319582749375101591512281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5759443665833468788683041 4319582749375101591512281)
                    ·
                      refine ⟨3239687062031326193634211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4319582749375101591512281 3239687062031326193634211)
                      ·
                        rfl

theorem cell23_6309268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 2, 2, 3, 2, 2].length) (baseStart_6309268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6309268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6309268 prefixEnd_6309268 := by exact prefixLift 6309268
  have htrace : WordTrace (prefixWord ++ tailWord_6309268) baseStart_6309268 baseEnd_6309268 := by
    simpa [prefixWord, tailWord_6309268, baseEnd_6309268] using wordTrace_append hprefix tailTrace_6309268
  have hstable : (prefixWord ++ tailWord_6309268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6309268).length < 2 ^ (prefixWord ++ tailWord_6309268).sum := by decide
  have hdescent : baseEnd_6309268 < baseStart_6309268 := by decide
  rcases family_descends (prefixWord ++ tailWord_6309268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6309297 : List Nat := [1, 2, 2, 4, 1, 1, 1, 2, 2, 2, 5]
def baseStart_6309297 : Nat := 118140960795 + 6309297 * 2 ^ 59
def prefixEnd_6309297 : Nat := 4983230072969 + 3 ^ 40 * 6309297 * 2
def baseEnd_6309297 : Nat := 3239701952970306580171577

theorem tailTrace_6309297 : CollatzResearch.WordTrace tailWord_6309297 prefixEnd_6309297 3239701952970306580171577 := by
  unfold tailWord_6309297
  simp only [CollatzResearch.WordTrace]
  refine ⟨230118966623501985985198145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153412644415667990656798763 230118966623501985985198145)
  ·
    refine ⟨172589224967626489488898609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 230118966623501985985198145 172589224967626489488898609)
    ·
      refine ⟨129441918725719867116673957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 172589224967626489488898609 129441918725719867116673957)
      ·
        refine ⟨24270359761072475084376367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 129441918725719867116673957 24270359761072475084376367)
        ·
          refine ⟨36405539641608712626564551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24270359761072475084376367 36405539641608712626564551)
          ·
            refine ⟨54608309462413068939846827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36405539641608712626564551 54608309462413068939846827)
            ·
              refine ⟨81912464193619603409770241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54608309462413068939846827 81912464193619603409770241)
              ·
                refine ⟨61434348145214702557327681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 81912464193619603409770241 61434348145214702557327681)
                ·
                  refine ⟨46075761108911026917995761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 61434348145214702557327681 46075761108911026917995761)
                  ·
                    refine ⟨34556820831683270188496821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 46075761108911026917995761 34556820831683270188496821)
                    ·
                      refine ⟨3239701952970306580171577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34556820831683270188496821 3239701952970306580171577)
                      ·
                        rfl

theorem cell23_6309297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 2, 2, 2, 5].length) (baseStart_6309297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6309297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6309297 prefixEnd_6309297 := by exact prefixLift 6309297
  have htrace : WordTrace (prefixWord ++ tailWord_6309297) baseStart_6309297 baseEnd_6309297 := by
    simpa [prefixWord, tailWord_6309297, baseEnd_6309297] using wordTrace_append hprefix tailTrace_6309297
  have hstable : (prefixWord ++ tailWord_6309297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6309297).length < 2 ^ (prefixWord ++ tailWord_6309297).sum := by decide
  have hdescent : baseEnd_6309297 < baseStart_6309297 := by decide
  rcases family_descends (prefixWord ++ tailWord_6309297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6309301 : List Nat := [1, 3, 3, 2, 2, 1, 2, 1, 4, 1, 3]
def baseStart_6309301 : Nat := 118140960795 + 6309301 * 2 ^ 59
def prefixEnd_6309301 : Nat := 4983230072969 + 3 ^ 40 * 6309301 * 2
def baseEnd_6309301 : Nat := 3239704006892924564521559

theorem tailTrace_6309301 : CollatzResearch.WordTrace tailWord_6309301 prefixEnd_6309301 3239704006892924564521559 := by
  unfold tailWord_6309301
  simp only [CollatzResearch.WordTrace]
  refine ⟨230119112515487494668343757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153412741676991663112229171 230119112515487494668343757)
  ·
    refine ⟨86294667193307810500628909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 230119112515487494668343757 86294667193307810500628909)
    ·
      refine ⟨32360500197490428937735841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86294667193307810500628909 32360500197490428937735841)
      ·
        refine ⟨24270375148117821703301881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32360500197490428937735841 24270375148117821703301881)
        ·
          refine ⟨18202781361088366277476411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24270375148117821703301881 18202781361088366277476411)
          ·
            refine ⟨27304172041632549416214617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18202781361088366277476411 27304172041632549416214617)
            ·
              refine ⟨20478129031224412062160963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27304172041632549416214617 20478129031224412062160963)
              ·
                refine ⟨30717193546836618093241445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20478129031224412062160963 30717193546836618093241445)
                ·
                  refine ⟨5759473790031865892482771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30717193546836618093241445 5759473790031865892482771)
                  ·
                    refine ⟨8639210685047798838724157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5759473790031865892482771 8639210685047798838724157)
                    ·
                      refine ⟨3239704006892924564521559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8639210685047798838724157 3239704006892924564521559)
                      ·
                        rfl

theorem cell23_6309301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 2, 1, 4, 1, 3].length) (baseStart_6309301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6309301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6309301 prefixEnd_6309301 := by exact prefixLift 6309301
  have htrace : WordTrace (prefixWord ++ tailWord_6309301) baseStart_6309301 baseEnd_6309301 := by
    simpa [prefixWord, tailWord_6309301, baseEnd_6309301] using wordTrace_append hprefix tailTrace_6309301
  have hstable : (prefixWord ++ tailWord_6309301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6309301).length < 2 ^ (prefixWord ++ tailWord_6309301).sum := by decide
  have hdescent : baseEnd_6309301 < baseStart_6309301 := by decide
  rcases family_descends (prefixWord ++ tailWord_6309301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6309327 : List Nat := [1, 1, 2, 1, 1, 4, 3, 2, 2, 1, 5]
def baseStart_6309327 : Nat := 118140960795 + 6309327 * 2 ^ 59
def prefixEnd_6309327 : Nat := 4983230072969 + 3 ^ 40 * 6309327 * 2
def baseEnd_6309327 : Nat := 3239717357389941462796439

theorem tailTrace_6309327 : CollatzResearch.WordTrace tailWord_6309327 prefixEnd_6309327 3239717357389941462796439 := by
  unfold tailWord_6309327
  simp only [CollatzResearch.WordTrace]
  refine ⟨230120060813393301108790235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153413373875595534072526823 230120060813393301108790235)
  ·
    refine ⟨345180091220089951663185353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230120060813393301108790235 345180091220089951663185353)
    ·
      refine ⟨258885068415067463747389015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 345180091220089951663185353 258885068415067463747389015)
      ·
        refine ⟨388327602622601195621083523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 258885068415067463747389015 388327602622601195621083523)
        ·
          refine ⟨582491403933901793431625285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 388327602622601195621083523 582491403933901793431625285)
          ·
            refine ⟨109217138237606586268429741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 582491403933901793431625285 109217138237606586268429741)
            ·
              refine ⟨40956426839102469850661153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 109217138237606586268429741 40956426839102469850661153)
              ·
                refine ⟨30717320129326852387995865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40956426839102469850661153 30717320129326852387995865)
                ·
                  refine ⟨23037990096995139290996899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30717320129326852387995865 23037990096995139290996899)
                  ·
                    refine ⟨34556985145492708936495349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23037990096995139290996899 34556985145492708936495349)
                    ·
                      refine ⟨3239717357389941462796439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34556985145492708936495349 3239717357389941462796439)
                      ·
                        rfl

theorem cell23_6309327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 2, 2, 1, 5].length) (baseStart_6309327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6309327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6309327 prefixEnd_6309327 := by exact prefixLift 6309327
  have htrace : WordTrace (prefixWord ++ tailWord_6309327) baseStart_6309327 baseEnd_6309327 := by
    simpa [prefixWord, tailWord_6309327, baseEnd_6309327] using wordTrace_append hprefix tailTrace_6309327
  have hstable : (prefixWord ++ tailWord_6309327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6309327).length < 2 ^ (prefixWord ++ tailWord_6309327).sum := by decide
  have hdescent : baseEnd_6309327 < baseStart_6309327 := by decide
  rcases family_descends (prefixWord ++ tailWord_6309327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6309341 : List Nat := [1, 4, 3, 1, 1, 2, 1, 1, 3, 4, 2]
def baseStart_6309341 : Nat := 118140960795 + 6309341 * 2 ^ 59
def prefixEnd_6309341 : Nat := 4983230072969 + 3 ^ 40 * 6309341 * 2
def baseEnd_6309341 : Nat := 3239724546119104408021375

theorem tailTrace_6309341 : CollatzResearch.WordTrace tailWord_6309341 prefixEnd_6309341 3239724546119104408021375 := by
  unfold tailWord_6309341
  simp only [CollatzResearch.WordTrace]
  refine ⟨230120571435342581499799877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153413714290228387666533251 230120571435342581499799877)
  ·
    refine ⟨43147607144126734031212477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 230120571435342581499799877 43147607144126734031212477)
    ·
      refine ⟨16180352679047525261704679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43147607144126734031212477 16180352679047525261704679)
      ·
        refine ⟨24270529018571287892557019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16180352679047525261704679 24270529018571287892557019)
        ·
          refine ⟨36405793527856931838835529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24270529018571287892557019 36405793527856931838835529)
          ·
            refine ⟨27304345145892698879126647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36405793527856931838835529 27304345145892698879126647)
            ·
              refine ⟨40956517718839048318689971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27304345145892698879126647 40956517718839048318689971)
              ·
                refine ⟨61434776578258572478034957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40956517718839048318689971 61434776578258572478034957)
                ·
                  refine ⟨23038041216846964679263109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 61434776578258572478034957 23038041216846964679263109)
                  ·
                    refine ⟨4319632728158805877361833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23038041216846964679263109 4319632728158805877361833)
                    ·
                      refine ⟨3239724546119104408021375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4319632728158805877361833 3239724546119104408021375)
                      ·
                        rfl

theorem cell23_6309341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 1, 3, 4, 2].length) (baseStart_6309341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6309341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6309341 prefixEnd_6309341 := by exact prefixLift 6309341
  have htrace : WordTrace (prefixWord ++ tailWord_6309341) baseStart_6309341 baseEnd_6309341 := by
    simpa [prefixWord, tailWord_6309341, baseEnd_6309341] using wordTrace_append hprefix tailTrace_6309341
  have hstable : (prefixWord ++ tailWord_6309341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6309341).length < 2 ^ (prefixWord ++ tailWord_6309341).sum := by decide
  have hdescent : baseEnd_6309341 < baseStart_6309341 := by decide
  rcases family_descends (prefixWord ++ tailWord_6309341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6309431 : List Nat := [1, 1, 3, 1, 2, 4, 2, 1, 2, 4, 2]
def baseStart_6309431 : Nat := 118140960795 + 6309431 * 2 ^ 59
def prefixEnd_6309431 : Nat := 4983230072969 + 3 ^ 40 * 6309431 * 2
def baseEnd_6309431 : Nat := 3239770759378009055895961

theorem tailTrace_6309431 : CollatzResearch.WordTrace tailWord_6309431 prefixEnd_6309431 3239770759378009055895961 := by
  unfold tailWord_6309431
  simp only [CollatzResearch.WordTrace]
  refine ⟨230123854005016526870576147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153415902670011017913717431 230123854005016526870576147)
  ·
    refine ⟨345185781007524790305864221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230123854005016526870576147 345185781007524790305864221)
    ·
      refine ⟨129444667877821796364699083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 345185781007524790305864221 129444667877821796364699083)
      ·
        refine ⟨194167001816732694547048625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129444667877821796364699083 194167001816732694547048625)
        ·
          refine ⟨145625251362549520910286469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 194167001816732694547048625 145625251362549520910286469)
          ·
            refine ⟨27304734630478035170678713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 145625251362549520910286469 27304734630478035170678713)
            ·
              refine ⟨20478550972858526378009035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27304734630478035170678713 20478550972858526378009035)
              ·
                refine ⟨30717826459287789567013553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20478550972858526378009035 30717826459287789567013553)
                ·
                  refine ⟨23038369844465842175260165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30717826459287789567013553 23038369844465842175260165)
                  ·
                    refine ⟨4319694345837345407861281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23038369844465842175260165 4319694345837345407861281)
                    ·
                      refine ⟨3239770759378009055895961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4319694345837345407861281 3239770759378009055895961)
                      ·
                        rfl

theorem cell23_6309431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 2, 1, 2, 4, 2].length) (baseStart_6309431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6309431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6309431 prefixEnd_6309431 := by exact prefixLift 6309431
  have htrace : WordTrace (prefixWord ++ tailWord_6309431) baseStart_6309431 baseEnd_6309431 := by
    simpa [prefixWord, tailWord_6309431, baseEnd_6309431] using wordTrace_append hprefix tailTrace_6309431
  have hstable : (prefixWord ++ tailWord_6309431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6309431).length < 2 ^ (prefixWord ++ tailWord_6309431).sum := by decide
  have hdescent : baseEnd_6309431 < baseStart_6309431 := by decide
  rcases family_descends (prefixWord ++ tailWord_6309431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6309434 : List Nat := [3, 1, 1, 1, 3, 2, 1, 1, 3, 4, 3]
def baseStart_6309434 : Nat := 118140960795 + 6309434 * 2 ^ 59
def prefixEnd_6309434 : Nat := 4983230072969 + 3 ^ 40 * 6309434 * 2
def baseEnd_6309434 : Nat := 3239772299819972544158447

theorem tailTrace_6309434 : CollatzResearch.WordTrace tailWord_6309434 prefixEnd_6309434 3239772299819972544158447 := by
  unfold tailWord_6309434
  simp only [CollatzResearch.WordTrace]
  refine ⟨57530990856001414595733839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153415975616003772255290237 57530990856001414595733839)
  ·
    refine ⟨86296486284002121893600759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57530990856001414595733839 86296486284002121893600759)
    ·
      refine ⟨129444729426003182840401139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86296486284002121893600759 129444729426003182840401139)
      ·
        refine ⟨194167094139004774260601709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129444729426003182840401139 194167094139004774260601709)
        ·
          refine ⟨72812660302126790347725641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 194167094139004774260601709 72812660302126790347725641)
          ·
            refine ⟨54609495226595092760794231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72812660302126790347725641 54609495226595092760794231)
            ·
              refine ⟨81914242839892639141191347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54609495226595092760794231 81914242839892639141191347)
              ·
                refine ⟨122871364259838958711787021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81914242839892639141191347 122871364259838958711787021)
                ·
                  refine ⟨46076761597439609516920133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 122871364259838958711787021 46076761597439609516920133)
                  ·
                    refine ⟨8639392799519926784422525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 46076761597439609516920133 8639392799519926784422525)
                    ·
                      refine ⟨3239772299819972544158447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8639392799519926784422525 3239772299819972544158447)
                      ·
                        rfl

theorem cell23_6309434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 1, 3, 4, 3].length) (baseStart_6309434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6309434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6309434 prefixEnd_6309434 := by exact prefixLift 6309434
  have htrace : WordTrace (prefixWord ++ tailWord_6309434) baseStart_6309434 baseEnd_6309434 := by
    simpa [prefixWord, tailWord_6309434, baseEnd_6309434] using wordTrace_append hprefix tailTrace_6309434
  have hstable : (prefixWord ++ tailWord_6309434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6309434).length < 2 ^ (prefixWord ++ tailWord_6309434).sum := by decide
  have hdescent : baseEnd_6309434 < baseStart_6309434 := by decide
  rcases family_descends (prefixWord ++ tailWord_6309434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6309441 : List Nat := [1, 2, 5, 1, 1, 1, 1, 4, 3, 4]
def baseStart_6309441 : Nat := 118140960795 + 6309441 * 2 ^ 59
def prefixEnd_6309441 : Nat := 4983230072969 + 3 ^ 40 * 6309441 * 2
def baseEnd_6309441 : Nat := 1079925298061518005590305

theorem tailTrace_6309441 : CollatzResearch.WordTrace tailWord_6309441 prefixEnd_6309441 1079925298061518005590305 := by
  unfold tailWord_6309441
  simp only [CollatzResearch.WordTrace]
  refine ⟨230124218734980298578440177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153416145823320199052293451 230124218734980298578440177)
  ·
    refine ⟨172593164051235223933830133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 230124218734980298578440177 172593164051235223933830133)
    ·
      refine ⟨16180609129803302243796575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 172593164051235223933830133 16180609129803302243796575)
      ·
        refine ⟨24270913694704953365694863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16180609129803302243796575 24270913694704953365694863)
        ·
          refine ⟨36406370542057430048542295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24270913694704953365694863 36406370542057430048542295)
          ·
            refine ⟨54609555813086145072813443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36406370542057430048542295 54609555813086145072813443)
            ·
              refine ⟨81914333719629217609220165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54609555813086145072813443 81914333719629217609220165)
              ·
                refine ⟨15358937572430478301728781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 81914333719629217609220165 15358937572430478301728781)
                ·
                  refine ⟨5759601589661429363148293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15358937572430478301728781 5759601589661429363148293)
                  ·
                    refine ⟨1079925298061518005590305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5759601589661429363148293 1079925298061518005590305)
                    ·
                      rfl

theorem cell23_6309441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 4, 3, 4].length) (baseStart_6309441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6309441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6309441 prefixEnd_6309441 := by exact prefixLift 6309441
  have htrace : WordTrace (prefixWord ++ tailWord_6309441) baseStart_6309441 baseEnd_6309441 := by
    simpa [prefixWord, tailWord_6309441, baseEnd_6309441] using wordTrace_append hprefix tailTrace_6309441
  have hstable : (prefixWord ++ tailWord_6309441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6309441).length < 2 ^ (prefixWord ++ tailWord_6309441).sum := by decide
  have hdescent : baseEnd_6309441 < baseStart_6309441 := by decide
  rcases family_descends (prefixWord ++ tailWord_6309441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6309468 : List Nat := [2, 2, 4, 1, 2, 2, 1, 2, 2, 2, 3]
def baseStart_6309468 : Nat := 118140960795 + 6309468 * 2 ^ 59
def prefixEnd_6309468 : Nat := 4983230072969 + 3 ^ 40 * 6309468 * 2
def baseEnd_6309468 : Nat := 3239789758162225411133291

theorem tailTrace_6309468 : CollatzResearch.WordTrace tailWord_6309468 prefixEnd_6309468 3239789758162225411133291 := by
  unfold tailWord_6309468
  simp only [CollatzResearch.WordTrace]
  refine ⟨115062601752941241094836529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153416802337254988126448705 115062601752941241094836529)
  ·
    refine ⟨86296951314705930821127397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115062601752941241094836529 86296951314705930821127397)
    ·
      refine ⟨16180678371507362028961387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 86296951314705930821127397 16180678371507362028961387)
      ·
        refine ⟨24271017557261043043442081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16180678371507362028961387 24271017557261043043442081)
        ·
          refine ⟨18203263167945782282581561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24271017557261043043442081 18203263167945782282581561)
          ·
            refine ⟨13652447375959336711936171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18203263167945782282581561 13652447375959336711936171)
            ·
              refine ⟨20478671063939005067904257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13652447375959336711936171 20478671063939005067904257)
              ·
                refine ⟨15359003297954253800928193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20478671063939005067904257 15359003297954253800928193)
                ·
                  refine ⟨11519252473465690350696145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15359003297954253800928193 11519252473465690350696145)
                  ·
                    refine ⟨8639439355099267763022109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11519252473465690350696145 8639439355099267763022109)
                    ·
                      refine ⟨3239789758162225411133291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8639439355099267763022109 3239789758162225411133291)
                      ·
                        rfl

theorem cell23_6309468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 1, 2, 2, 2, 3].length) (baseStart_6309468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6309468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6309468 prefixEnd_6309468 := by exact prefixLift 6309468
  have htrace : WordTrace (prefixWord ++ tailWord_6309468) baseStart_6309468 baseEnd_6309468 := by
    simpa [prefixWord, tailWord_6309468, baseEnd_6309468] using wordTrace_append hprefix tailTrace_6309468
  have hstable : (prefixWord ++ tailWord_6309468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6309468).length < 2 ^ (prefixWord ++ tailWord_6309468).sum := by decide
  have hdescent : baseEnd_6309468 < baseStart_6309468 := by decide
  rcases family_descends (prefixWord ++ tailWord_6309468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6309475 : List Nat := [1, 1, 1, 5, 1, 4, 3, 2, 1, 4]
def baseStart_6309475 : Nat := 118140960795 + 6309475 * 2 ^ 59
def prefixEnd_6309475 : Nat := 4983230072969 + 3 ^ 40 * 6309475 * 2
def baseEnd_6309475 : Nat := 1079931117508935627915253

theorem tailTrace_6309475 : CollatzResearch.WordTrace tailWord_6309475 prefixEnd_6309475 1079931117508935627915253 := by
  unfold tailWord_6309475
  simp only [CollatzResearch.WordTrace]
  refine ⟨230125458816857122385177879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153416972544571414923451919 230125458816857122385177879)
  ·
    refine ⟨345188188225285683577766819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230125458816857122385177879 345188188225285683577766819)
    ·
      refine ⟨517782282337928525366650229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 345188188225285683577766819 517782282337928525366650229)
      ·
        refine ⟨48542088969180799253123459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 517782282337928525366650229 48542088969180799253123459)
        ·
          refine ⟨72813133453771198879685189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48542088969180799253123459 72813133453771198879685189)
          ·
            refine ⟨13652462522582099789940973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 72813133453771198879685189 13652462522582099789940973)
            ·
              refine ⟨5119673445968287421227865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13652462522582099789940973 5119673445968287421227865)
              ·
                refine ⟨3839755084476215565920899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5119673445968287421227865 3839755084476215565920899)
                ·
                  refine ⟨5759632626714323348881349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3839755084476215565920899 5759632626714323348881349)
                  ·
                    refine ⟨1079931117508935627915253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5759632626714323348881349 1079931117508935627915253)
                    ·
                      rfl

theorem cell23_6309475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 3, 2, 1, 4].length) (baseStart_6309475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6309475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6309475 prefixEnd_6309475 := by exact prefixLift 6309475
  have htrace : WordTrace (prefixWord ++ tailWord_6309475) baseStart_6309475 baseEnd_6309475 := by
    simpa [prefixWord, tailWord_6309475, baseEnd_6309475] using wordTrace_append hprefix tailTrace_6309475
  have hstable : (prefixWord ++ tailWord_6309475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6309475).length < 2 ^ (prefixWord ++ tailWord_6309475).sum := by decide
  have hdescent : baseEnd_6309475 < baseStart_6309475 := by decide
  rcases family_descends (prefixWord ++ tailWord_6309475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6309484 : List Nat := [2, 2, 1, 1, 3, 1, 1, 4, 3, 5]
def baseStart_6309484 : Nat := 118140960795 + 6309484 * 2 ^ 59
def prefixEnd_6309484 : Nat := 4983230072969 + 3 ^ 40 * 6309484 * 2
def baseEnd_6309484 : Nat := 1079932657950899116177739

theorem tailTrace_6309484 : CollatzResearch.WordTrace tailWord_6309484 prefixEnd_6309484 1079932657950899116177739 := by
  unfold tailWord_6309484
  simp only [CollatzResearch.WordTrace]
  refine ⟨115062893536912258461127753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153417191382549677948170337 115062893536912258461127753)
  ·
    refine ⟨86297170152684193845845815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115062893536912258461127753 86297170152684193845845815)
    ·
      refine ⟨129445755229026290768768723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86297170152684193845845815 129445755229026290768768723)
      ·
        refine ⟨194168632843539436153153085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129445755229026290768768723 194168632843539436153153085)
        ·
          refine ⟨72813237316327288557432407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 194168632843539436153153085 72813237316327288557432407)
          ·
            refine ⟨109219855974490932836148611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72813237316327288557432407 109219855974490932836148611)
            ·
              refine ⟨163829783961736399254222917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109219855974490932836148611 163829783961736399254222917)
              ·
                refine ⟨30718084492825574860166797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 163829783961736399254222917 30718084492825574860166797)
                ·
                  refine ⟨11519281684809590572562549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30718084492825574860166797 11519281684809590572562549)
                  ·
                    refine ⟨1079932657950899116177739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11519281684809590572562549 1079932657950899116177739)
                    ·
                      rfl

theorem cell23_6309484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 5].length) (baseStart_6309484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6309484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6309484 prefixEnd_6309484 := by exact prefixLift 6309484
  have htrace : WordTrace (prefixWord ++ tailWord_6309484) baseStart_6309484 baseEnd_6309484 := by
    simpa [prefixWord, tailWord_6309484, baseEnd_6309484] using wordTrace_append hprefix tailTrace_6309484
  have hstable : (prefixWord ++ tailWord_6309484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6309484).length < 2 ^ (prefixWord ++ tailWord_6309484).sum := by decide
  have hdescent : baseEnd_6309484 < baseStart_6309484 := by decide
  rcases family_descends (prefixWord ++ tailWord_6309484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6309488 : List Nat := [2, 1, 1, 1, 6, 3, 2, 1, 6]
def baseStart_6309488 : Nat := 118140960795 + 6309488 * 2 ^ 59
def prefixEnd_6309488 : Nat := 4983230072969 + 3 ^ 40 * 6309488 * 2
def baseEnd_6309488 : Nat := 359977780863923925875911

theorem tailTrace_6309488 : CollatzResearch.WordTrace tailWord_6309488 prefixEnd_6309488 359977780863923925875911 := by
  unfold tailWord_6309488
  simp only [CollatzResearch.WordTrace]
  refine ⟨115062966482905012802700559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153417288643873350403600745 115062966482905012802700559)
  ·
    refine ⟨172594449724357519204050839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115062966482905012802700559 172594449724357519204050839)
    ·
      refine ⟨258891674586536278806076259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172594449724357519204050839 258891674586536278806076259)
      ·
        refine ⟨388337511879804418209114389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 258891674586536278806076259 388337511879804418209114389)
        ·
          refine ⟨18203320869365832103552237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 388337511879804418209114389 18203320869365832103552237)
          ·
            refine ⟨6826245326012187038832089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18203320869365832103552237 6826245326012187038832089)
            ·
              refine ⟨5119683994509140279124067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6826245326012187038832089 5119683994509140279124067)
              ·
                refine ⟨7679525991763710418686101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5119683994509140279124067 7679525991763710418686101)
                ·
                  refine ⟨359977780863923925875911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7679525991763710418686101 359977780863923925875911)
                  ·
                    rfl

theorem cell23_6309488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 3, 2, 1, 6].length) (baseStart_6309488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6309488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6309488 prefixEnd_6309488 := by exact prefixLift 6309488
  have htrace : WordTrace (prefixWord ++ tailWord_6309488) baseStart_6309488 baseEnd_6309488 := by
    simpa [prefixWord, tailWord_6309488, baseEnd_6309488] using wordTrace_append hprefix tailTrace_6309488
  have hstable : (prefixWord ++ tailWord_6309488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6309488).length < 2 ^ (prefixWord ++ tailWord_6309488).sum := by decide
  have hdescent : baseEnd_6309488 < baseStart_6309488 := by decide
  rcases family_descends (prefixWord ++ tailWord_6309488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6309501 : List Nat := [1, 4, 1, 1, 4, 2, 1, 1, 3, 5]
def baseStart_6309501 : Nat := 118140960795 + 6309501 * 2 ^ 59
def prefixEnd_6309501 : Nat := 4983230072969 + 3 ^ 40 * 6309501 * 2
def baseEnd_6309501 : Nat := 1079935567674607927340213

theorem tailTrace_6309501 : CollatzResearch.WordTrace tailWord_6309501 prefixEnd_6309501 1079935567674607927340213 := by
  unfold tailWord_6309501
  simp only [CollatzResearch.WordTrace]
  refine ⟨230126407114762928825624357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153417604743175285883749571 230126407114762928825624357)
  ·
    refine ⟨43148701334018049154804567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 230126407114762928825624357 43148701334018049154804567)
    ·
      refine ⟨64723052001027073732206851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43148701334018049154804567 64723052001027073732206851)
      ·
        refine ⟨97084578001540610598310277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64723052001027073732206851 97084578001540610598310277)
        ·
          refine ⟨18203358375288864487183177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 97084578001540610598310277 18203358375288864487183177)
          ·
            refine ⟨13652518781466648365387383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18203358375288864487183177 13652518781466648365387383)
            ·
              refine ⟨20478778172199972548081075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13652518781466648365387383 20478778172199972548081075)
              ·
                refine ⟨30718167258299958822121613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20478778172199972548081075 30718167258299958822121613)
                ·
                  refine ⟨11519312721862484558295605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30718167258299958822121613 11519312721862484558295605)
                  ·
                    refine ⟨1079935567674607927340213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11519312721862484558295605 1079935567674607927340213)
                    ·
                      rfl

theorem cell23_6309501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 1, 1, 3, 5].length) (baseStart_6309501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6309501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6309501 prefixEnd_6309501 := by exact prefixLift 6309501
  have htrace : WordTrace (prefixWord ++ tailWord_6309501) baseStart_6309501 baseEnd_6309501 := by
    simpa [prefixWord, tailWord_6309501, baseEnd_6309501] using wordTrace_append hprefix tailTrace_6309501
  have hstable : (prefixWord ++ tailWord_6309501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6309501).length < 2 ^ (prefixWord ++ tailWord_6309501).sum := by decide
  have hdescent : baseEnd_6309501 < baseStart_6309501 := by decide
  rcases family_descends (prefixWord ++ tailWord_6309501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6309532 : List Nat := [2, 2, 3, 2, 3, 1, 1, 4, 1, 1, 3]
def baseStart_6309532 : Nat := 118140960795 + 6309532 * 2 ^ 59
def prefixEnd_6309532 : Nat := 4983230072969 + 3 ^ 40 * 6309532 * 2
def baseEnd_6309532 : Nat := 3239822620924113160732997

theorem tailTrace_6309532 : CollatzResearch.WordTrace tailWord_6309532 prefixEnd_6309532 3239822620924113160732997 := by
  unfold tailWord_6309532
  simp only [CollatzResearch.WordTrace]
  refine ⟨115063768888825310560001425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153418358518433747413335233 115063768888825310560001425)
  ·
    refine ⟨86297826666618982920001069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115063768888825310560001425 86297826666618982920001069)
    ·
      refine ⟨32361684999982118595000401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86297826666618982920001069 32361684999982118595000401)
      ·
        refine ⟨24271263749986588946250301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32361684999982118595000401 24271263749986588946250301)
        ·
          refine ⟨9101723906244970854843863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24271263749986588946250301 9101723906244970854843863)
          ·
            refine ⟨13652585859367456282265795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9101723906244970854843863 13652585859367456282265795)
            ·
              refine ⟨20478878789051184423398693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13652585859367456282265795 20478878789051184423398693)
              ·
                refine ⟨3839789772947097079387255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20478878789051184423398693 3839789772947097079387255)
                ·
                  refine ⟨5759684659420645619080883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3839789772947097079387255 5759684659420645619080883)
                  ·
                    refine ⟨8639526989130968428621325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5759684659420645619080883 8639526989130968428621325)
                    ·
                      refine ⟨3239822620924113160732997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8639526989130968428621325 3239822620924113160732997)
                      ·
                        rfl

theorem cell23_6309532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 1, 4, 1, 1, 3].length) (baseStart_6309532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6309532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6309532 prefixEnd_6309532 := by exact prefixLift 6309532
  have htrace : WordTrace (prefixWord ++ tailWord_6309532) baseStart_6309532 baseEnd_6309532 := by
    simpa [prefixWord, tailWord_6309532, baseEnd_6309532] using wordTrace_append hprefix tailTrace_6309532
  have hstable : (prefixWord ++ tailWord_6309532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6309532).length < 2 ^ (prefixWord ++ tailWord_6309532).sum := by decide
  have hdescent : baseEnd_6309532 < baseStart_6309532 := by decide
  rcases family_descends (prefixWord ++ tailWord_6309532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6309541 : List Nat := [1, 3, 1, 2, 1, 2, 3, 2, 3, 2, 3]
def baseStart_6309541 : Nat := 118140960795 + 6309541 * 2 ^ 59
def prefixEnd_6309541 : Nat := 4983230072969 + 3 ^ 40 * 6309541 * 2
def baseEnd_6309541 : Nat := 3239827242250003625520455

theorem tailTrace_6309541 : CollatzResearch.WordTrace tailWord_6309541 prefixEnd_6309541 3239827242250003625520455 := by
  unfold tailWord_6309541
  simp only [CollatzResearch.WordTrace]
  refine ⟨230127866034618015657080477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153418577356412010438053651 230127866034618015657080477)
  ·
    refine ⟨86297949762981755871405179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 230127866034618015657080477 86297949762981755871405179)
    ·
      refine ⟨129446924644472633807107769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86297949762981755871405179 129446924644472633807107769)
      ·
        refine ⟨97085193483354475355330827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129446924644472633807107769 97085193483354475355330827)
        ·
          refine ⟨145627790225031713032996241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97085193483354475355330827 145627790225031713032996241)
          ·
            refine ⟨109220842668773784774747181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 145627790225031713032996241 109220842668773784774747181)
            ·
              refine ⟨40957816000790169290530193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 109220842668773784774747181 40957816000790169290530193)
              ·
                refine ⟨30718362000592626967897645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40957816000790169290530193 30718362000592626967897645)
                ·
                  refine ⟨11519385750222235112961617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30718362000592626967897645 11519385750222235112961617)
                  ·
                    refine ⟨8639539312666676334721213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11519385750222235112961617 8639539312666676334721213)
                    ·
                      refine ⟨3239827242250003625520455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8639539312666676334721213 3239827242250003625520455)
                      ·
                        rfl

theorem cell23_6309541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 2, 3, 2, 3].length) (baseStart_6309541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6309541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6309541 prefixEnd_6309541 := by exact prefixLift 6309541
  have htrace : WordTrace (prefixWord ++ tailWord_6309541) baseStart_6309541 baseEnd_6309541 := by
    simpa [prefixWord, tailWord_6309541, baseEnd_6309541] using wordTrace_append hprefix tailTrace_6309541
  have hstable : (prefixWord ++ tailWord_6309541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6309541).length < 2 ^ (prefixWord ++ tailWord_6309541).sum := by decide
  have hdescent : baseEnd_6309541 < baseStart_6309541 := by decide
  rcases family_descends (prefixWord ++ tailWord_6309541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6309551 : List Nat := [1, 1, 2, 1, 2, 4, 4, 1, 1, 2, 4]
def baseStart_6309551 : Nat := 118140960795 + 6309551 * 2 ^ 59
def prefixEnd_6309551 : Nat := 4983230072969 + 3 ^ 40 * 6309551 * 2
def baseEnd_6309551 : Nat := 3239832377056548586395409

theorem tailTrace_6309551 : CollatzResearch.WordTrace tailWord_6309551 prefixEnd_6309551 3239832377056548586395409 := by
  unfold tailWord_6309551
  simp only [CollatzResearch.WordTrace]
  refine ⟨230128230764581787364944507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153418820509721191576629671 230128230764581787364944507)
  ·
    refine ⟨345192346146872681047416761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230128230764581787364944507 345192346146872681047416761)
    ·
      refine ⟨258894259610154510785562571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 345192346146872681047416761 258894259610154510785562571)
      ·
        refine ⟨388341389415231766178343857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 258894259610154510785562571 388341389415231766178343857)
        ·
          refine ⟨291256042061423824633757893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 388341389415231766178343857 291256042061423824633757893)
          ·
            refine ⟨54610507886516967118829605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 291256042061423824633757893 54610507886516967118829605)
            ·
              refine ⟨10239470228721931334780551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 54610507886516967118829605 10239470228721931334780551)
              ·
                refine ⟨15359205343082897002170827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10239470228721931334780551 15359205343082897002170827)
                ·
                  refine ⟨23038808014624345503256241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15359205343082897002170827 23038808014624345503256241)
                  ·
                    refine ⟨17279106010968259127442181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23038808014624345503256241 17279106010968259127442181)
                    ·
                      refine ⟨3239832377056548586395409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17279106010968259127442181 3239832377056548586395409)
                      ·
                        rfl

theorem cell23_6309551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 4, 1, 1, 2, 4].length) (baseStart_6309551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6309551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6309551 prefixEnd_6309551 := by exact prefixLift 6309551
  have htrace : WordTrace (prefixWord ++ tailWord_6309551) baseStart_6309551 baseEnd_6309551 := by
    simpa [prefixWord, tailWord_6309551, baseEnd_6309551] using wordTrace_append hprefix tailTrace_6309551
  have hstable : (prefixWord ++ tailWord_6309551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6309551).length < 2 ^ (prefixWord ++ tailWord_6309551).sum := by decide
  have hdescent : baseEnd_6309551 < baseStart_6309551 := by decide
  rcases family_descends (prefixWord ++ tailWord_6309551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6309584 : List Nat := [2, 1, 1, 1, 1, 2, 1, 3, 4, 2, 5]
def baseStart_6309584 : Nat := 118140960795 + 6309584 * 2 ^ 59
def prefixEnd_6309584 : Nat := 4983230072969 + 3 ^ 40 * 6309584 * 2
def baseEnd_6309584 : Nat := 3239849321918146957282757

theorem tailTrace_6309584 : CollatzResearch.WordTrace tailWord_6309584 prefixEnd_6309584 3239849321918146957282757 := by
  unfold tailWord_6309584
  simp only [CollatzResearch.WordTrace]
  refine ⟨115064717186731117000447903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153419622915641489333930537 115064717186731117000447903)
  ·
    refine ⟨172597075780096675500671855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115064717186731117000447903 172597075780096675500671855)
    ·
      refine ⟨258895613670145013251007783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172597075780096675500671855 258895613670145013251007783)
      ·
        refine ⟨388343420505217519876511675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 258895613670145013251007783 388343420505217519876511675)
        ·
          refine ⟨582515130757826279814767513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 388343420505217519876511675 582515130757826279814767513)
          ·
            refine ⟨436886348068369709861075635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 582515130757826279814767513 436886348068369709861075635)
            ·
              refine ⟨655329522102554564791613453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 436886348068369709861075635 655329522102554564791613453)
              ·
                refine ⟨245748570788457961796855045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 655329522102554564791613453 245748570788457961796855045)
                ·
                  refine ⟨46077857022835867836910321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 245748570788457961796855045 46077857022835867836910321)
                  ·
                    refine ⟨34558392767126900877682741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 46077857022835867836910321 34558392767126900877682741)
                    ·
                      refine ⟨3239849321918146957282757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34558392767126900877682741 3239849321918146957282757)
                      ·
                        rfl

theorem cell23_6309584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 3, 4, 2, 5].length) (baseStart_6309584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6309584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6309584 prefixEnd_6309584 := by exact prefixLift 6309584
  have htrace : WordTrace (prefixWord ++ tailWord_6309584) baseStart_6309584 baseEnd_6309584 := by
    simpa [prefixWord, tailWord_6309584, baseEnd_6309584] using wordTrace_append hprefix tailTrace_6309584
  have hstable : (prefixWord ++ tailWord_6309584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6309584).length < 2 ^ (prefixWord ++ tailWord_6309584).sum := by decide
  have hdescent : baseEnd_6309584 < baseStart_6309584 := by decide
  rcases family_descends (prefixWord ++ tailWord_6309584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6309615 : List Nat := [1, 1, 2, 1, 5, 1, 4, 2, 1, 3, 2]
def baseStart_6309615 : Nat := 118140960795 + 6309615 * 2 ^ 59
def prefixEnd_6309615 : Nat := 4983230072969 + 3 ^ 40 * 6309615 * 2
def baseEnd_6309615 : Nat := 3239865239818436335995115

theorem tailTrace_6309615 : CollatzResearch.WordTrace tailWord_6309615 prefixEnd_6309615 3239865239818436335995115 := by
  unfold tailWord_6309615
  simp only [CollatzResearch.WordTrace]
  refine ⟨230130565036349926295274299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153420376690899950863516199 230130565036349926295274299)
  ·
    refine ⟨345195847554524889442911449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230130565036349926295274299 345195847554524889442911449)
    ·
      refine ⟨258896885665893667082183587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 345195847554524889442911449 258896885665893667082183587)
      ·
        refine ⟨388345328498840500623275381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 258896885665893667082183587 388345328498840500623275381)
        ·
          refine ⟨36407374546766296933432067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 388345328498840500623275381 36407374546766296933432067)
          ·
            refine ⟨54611061820149445400148101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36407374546766296933432067 54611061820149445400148101)
            ·
              refine ⟨10239574091278021012527769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 54611061820149445400148101 10239574091278021012527769)
              ·
                refine ⟨7679680568458515759395827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10239574091278021012527769 7679680568458515759395827)
                ·
                  refine ⟨11519520852687773639093741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7679680568458515759395827 11519520852687773639093741)
                  ·
                    refine ⟨4319820319757915114660153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11519520852687773639093741 4319820319757915114660153)
                    ·
                      refine ⟨3239865239818436335995115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4319820319757915114660153 3239865239818436335995115)
                      ·
                        rfl

theorem cell23_6309615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 4, 2, 1, 3, 2].length) (baseStart_6309615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6309615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6309615 prefixEnd_6309615 := by exact prefixLift 6309615
  have htrace : WordTrace (prefixWord ++ tailWord_6309615) baseStart_6309615 baseEnd_6309615 := by
    simpa [prefixWord, tailWord_6309615, baseEnd_6309615] using wordTrace_append hprefix tailTrace_6309615
  have hstable : (prefixWord ++ tailWord_6309615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6309615).length < 2 ^ (prefixWord ++ tailWord_6309615).sum := by decide
  have hdescent : baseEnd_6309615 < baseStart_6309615 := by decide
  rcases family_descends (prefixWord ++ tailWord_6309615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6309628 : List Nat := [2, 2, 2, 1, 3, 1, 2, 1, 3, 4, 2]
def baseStart_6309628 : Nat := 118140960795 + 6309628 * 2 ^ 59
def prefixEnd_6309628 : Nat := 4983230072969 + 3 ^ 40 * 6309628 * 2
def baseEnd_6309628 : Nat := 3239871915066944785132555

theorem tailTrace_6309628 : CollatzResearch.WordTrace tailWord_6309628 prefixEnd_6309628 3239871915066944785132555 := by
  unfold tailWord_6309628
  simp only [CollatzResearch.WordTrace]
  refine ⟨115065519592651414757748769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153420692790201886343665025 115065519592651414757748769)
  ·
    refine ⟨86299139694488561068311577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115065519592651414757748769 86299139694488561068311577)
    ·
      refine ⟨64724354770866420801233683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86299139694488561068311577 64724354770866420801233683)
      ·
        refine ⟨97086532156299631201850525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64724354770866420801233683 97086532156299631201850525)
        ·
          refine ⟨36407449558612361700693947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 97086532156299631201850525 36407449558612361700693947)
          ·
            refine ⟨54611174337918542551040921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36407449558612361700693947 54611174337918542551040921)
            ·
              refine ⟨40958380753438906913280691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54611174337918542551040921 40958380753438906913280691)
              ·
                refine ⟨61437571130158360369921037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40958380753438906913280691 61437571130158360369921037)
                ·
                  refine ⟨23039089173809385138720389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 61437571130158360369921037 23039089173809385138720389)
                  ·
                    refine ⟨4319829220089259713510073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23039089173809385138720389 4319829220089259713510073)
                    ·
                      refine ⟨3239871915066944785132555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4319829220089259713510073 3239871915066944785132555)
                      ·
                        rfl

theorem cell23_6309628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 1, 3, 4, 2].length) (baseStart_6309628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6309628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6309628 prefixEnd_6309628 := by exact prefixLift 6309628
  have htrace : WordTrace (prefixWord ++ tailWord_6309628) baseStart_6309628 baseEnd_6309628 := by
    simpa [prefixWord, tailWord_6309628, baseEnd_6309628] using wordTrace_append hprefix tailTrace_6309628
  have hstable : (prefixWord ++ tailWord_6309628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6309628).length < 2 ^ (prefixWord ++ tailWord_6309628).sum := by decide
  have hdescent : baseEnd_6309628 < baseStart_6309628 := by decide
  rcases family_descends (prefixWord ++ tailWord_6309628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6309728 : List Nat := [2, 1, 1, 3, 3, 2, 1, 1, 5, 4]
def baseStart_6309728 : Nat := 118140960795 + 6309728 * 2 ^ 59
def prefixEnd_6309728 : Nat := 4983230072969 + 3 ^ 40 * 6309728 * 2
def baseEnd_6309728 : Nat := 1079974421044131464627365

theorem tailTrace_6309728 : CollatzResearch.WordTrace tailWord_6309728 prefixEnd_6309728 1079974421044131464627365 := by
  unfold tailWord_6309728
  simp only [CollatzResearch.WordTrace]
  refine ⟨115067343242470273297068919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153423124323293697729425225 115067343242470273297068919)
  ·
    refine ⟨172601014863705409945603379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115067343242470273297068919 172601014863705409945603379)
    ·
      refine ⟨258901522295558114918405069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172601014863705409945603379 258901522295558114918405069)
      ·
        refine ⟨97088070860834293094401901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 258901522295558114918405069 97088070860834293094401901)
        ·
          refine ⟨36408026572812859910400713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 97088070860834293094401901 36408026572812859910400713)
          ·
            refine ⟨27306019929609644932800535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36408026572812859910400713 27306019929609644932800535)
            ·
              refine ⟨40959029894414467399200803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27306019929609644932800535 40959029894414467399200803)
              ·
                refine ⟨61438544841621701098801205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40959029894414467399200803 61438544841621701098801205)
                ·
                  refine ⟨5759863578902034478012613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 61438544841621701098801205 5759863578902034478012613)
                  ·
                    refine ⟨1079974421044131464627365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5759863578902034478012613 1079974421044131464627365)
                    ·
                      rfl

theorem cell23_6309728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 1, 5, 4].length) (baseStart_6309728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6309728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6309728 prefixEnd_6309728 := by exact prefixLift 6309728
  have htrace : WordTrace (prefixWord ++ tailWord_6309728) baseStart_6309728 baseEnd_6309728 := by
    simpa [prefixWord, tailWord_6309728, baseEnd_6309728] using wordTrace_append hprefix tailTrace_6309728
  have hstable : (prefixWord ++ tailWord_6309728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6309728).length < 2 ^ (prefixWord ++ tailWord_6309728).sum := by decide
  have hdescent : baseEnd_6309728 < baseStart_6309728 := by decide
  rcases family_descends (prefixWord ++ tailWord_6309728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6309732 : List Nat := [2, 3, 1, 1, 6, 1, 1, 1, 2, 5]
def baseStart_6309732 : Nat := 118140960795 + 6309732 * 2 ^ 59
def prefixEnd_6309732 : Nat := 4983230072969 + 3 ^ 40 * 6309732 * 2
def baseEnd_6309732 : Nat := 1079975105685004126077359

theorem tailTrace_6309732 : CollatzResearch.WordTrace tailWord_6309732 prefixEnd_6309732 1079975105685004126077359 := by
  unfold tailWord_6309732
  simp only [CollatzResearch.WordTrace]
  refine ⟨115067416188463027638641725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153423221584617370184855633 115067416188463027638641725)
  ·
    refine ⟨43150281070673635364490647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115067416188463027638641725 43150281070673635364490647)
    ·
      refine ⟨64725421606010453046735971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43150281070673635364490647 64725421606010453046735971)
      ·
        refine ⟨97088132409015679570103957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64725421606010453046735971 97088132409015679570103957)
        ·
          refine ⟨4551006206672609979848623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 97088132409015679570103957 4551006206672609979848623)
          ·
            refine ⟨6826509310008914969772935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4551006206672609979848623 6826509310008914969772935)
            ·
              refine ⟨10239763965013372454659403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6826509310008914969772935 10239763965013372454659403)
              ·
                refine ⟨15359645947520058681989105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10239763965013372454659403 15359645947520058681989105)
                ·
                  refine ⟨11519734460640044011491829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15359645947520058681989105 11519734460640044011491829)
                  ·
                    refine ⟨1079975105685004126077359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11519734460640044011491829 1079975105685004126077359)
                    ·
                      rfl

theorem cell23_6309732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 6, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 6, 1, 1, 1, 2, 5].length) (baseStart_6309732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6309732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6309732 prefixEnd_6309732 := by exact prefixLift 6309732
  have htrace : WordTrace (prefixWord ++ tailWord_6309732) baseStart_6309732 baseEnd_6309732 := by
    simpa [prefixWord, tailWord_6309732, baseEnd_6309732] using wordTrace_append hprefix tailTrace_6309732
  have hstable : (prefixWord ++ tailWord_6309732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6309732).length < 2 ^ (prefixWord ++ tailWord_6309732).sum := by decide
  have hdescent : baseEnd_6309732 < baseStart_6309732 := by decide
  rcases family_descends (prefixWord ++ tailWord_6309732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6309785 : List Nat := [1, 2, 1, 2, 1, 3, 4, 2, 3, 1, 3]
def baseStart_6309785 : Nat := 118140960795 + 6309785 * 2 ^ 59
def prefixEnd_6309785 : Nat := 4983230072969 + 3 ^ 40 * 6309785 * 2
def baseEnd_6309785 : Nat := 3239952531529700670869333

theorem tailTrace_6309785 : CollatzResearch.WordTrace tailWord_6309785 prefixEnd_6309785 3239952531529700670869333 := by
  unfold tailWord_6309785
  simp only [CollatzResearch.WordTrace]
  refine ⟨230136765445734045328962809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153424510297156030219308539 230136765445734045328962809)
  ·
    refine ⟨172602574084300533996722107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 230136765445734045328962809 172602574084300533996722107)
    ·
      refine ⟨258903861126450800995083161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172602574084300533996722107 258903861126450800995083161)
      ·
        refine ⟨194177895844838100746312371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 258903861126450800995083161 194177895844838100746312371)
        ·
          refine ⟨291266843767257151119468557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 194177895844838100746312371 291266843767257151119468557)
          ·
            refine ⟨109225066412721431669800709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 291266843767257151119468557 109225066412721431669800709)
            ·
              refine ⟨20479699952385268438087633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 109225066412721431669800709 20479699952385268438087633)
              ·
                refine ⟨15359774964288951328565725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20479699952385268438087633 15359774964288951328565725)
                ·
                  refine ⟨5759915611608356748212147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15359774964288951328565725 5759915611608356748212147)
                  ·
                    refine ⟨8639873417412535122318221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5759915611608356748212147 8639873417412535122318221)
                    ·
                      refine ⟨3239952531529700670869333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8639873417412535122318221 3239952531529700670869333)
                      ·
                        rfl

theorem cell23_6309785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 4, 2, 3, 1, 3].length) (baseStart_6309785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6309785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6309785 prefixEnd_6309785 := by exact prefixLift 6309785
  have htrace : WordTrace (prefixWord ++ tailWord_6309785) baseStart_6309785 baseEnd_6309785 := by
    simpa [prefixWord, tailWord_6309785, baseEnd_6309785] using wordTrace_append hprefix tailTrace_6309785
  have hstable : (prefixWord ++ tailWord_6309785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6309785).length < 2 ^ (prefixWord ++ tailWord_6309785).sum := by decide
  have hdescent : baseEnd_6309785 < baseStart_6309785 := by decide
  rcases family_descends (prefixWord ++ tailWord_6309785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6309795 : List Nat := [1, 1, 1, 4, 1, 2, 1, 5, 2, 3, 2]
def baseStart_6309795 : Nat := 118140960795 + 6309795 * 2 ^ 59
def prefixEnd_6309795 : Nat := 4983230072969 + 3 ^ 40 * 6309795 * 2
def baseEnd_6309795 : Nat := 3239957666336245631744287

theorem tailTrace_6309795 : CollatzResearch.WordTrace tailWord_6309795 prefixEnd_6309795 3239957666336245631744287 := by
  unfold tailWord_6309795
  simp only [CollatzResearch.WordTrace]
  refine ⟨230137130175697817036826839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153424753450465211357884559 230137130175697817036826839)
  ·
    refine ⟨345205695263546725555240259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230137130175697817036826839 345205695263546725555240259)
    ·
      refine ⟨517808542895320088332860389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 345205695263546725555240259 517808542895320088332860389)
      ·
        refine ⟨97089101792872516562411323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 517808542895320088332860389 97089101792872516562411323)
        ·
          refine ⟨145633652689308774843616985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97089101792872516562411323 145633652689308774843616985)
          ·
            refine ⟨109225239516981581132712739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 145633652689308774843616985 109225239516981581132712739)
            ·
              refine ⟨163837859275472371699069109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109225239516981581132712739 163837859275472371699069109)
              ·
                refine ⟨15359799307075534846787729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 163837859275472371699069109 15359799307075534846787729)
                ·
                  refine ⟨11519849480306651135090797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15359799307075534846787729 11519849480306651135090797)
                  ·
                    refine ⟨4319943555114994175659049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11519849480306651135090797 4319943555114994175659049)
                    ·
                      refine ⟨3239957666336245631744287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4319943555114994175659049 3239957666336245631744287)
                      ·
                        rfl

theorem cell23_6309795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 5, 2, 3, 2].length) (baseStart_6309795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6309795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6309795 prefixEnd_6309795 := by exact prefixLift 6309795
  have htrace : WordTrace (prefixWord ++ tailWord_6309795) baseStart_6309795 baseEnd_6309795 := by
    simpa [prefixWord, tailWord_6309795, baseEnd_6309795] using wordTrace_append hprefix tailTrace_6309795
  have hstable : (prefixWord ++ tailWord_6309795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6309795).length < 2 ^ (prefixWord ++ tailWord_6309795).sum := by decide
  have hdescent : baseEnd_6309795 < baseStart_6309795 := by decide
  rcases family_descends (prefixWord ++ tailWord_6309795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6309806 : List Nat := [4, 1, 5, 1, 1, 1, 1, 2, 2, 2, 3]
def baseStart_6309806 : Nat := 118140960795 + 6309806 * 2 ^ 59
def prefixEnd_6309806 : Nat := 4983230072969 + 3 ^ 40 * 6309806 * 2
def baseEnd_6309806 : Nat := 3239963314623445088706737

theorem tailTrace_6309806 : CollatzResearch.WordTrace tailWord_6309806 prefixEnd_6309806 3239963314623445088706737 := by
  unfold tailWord_6309806
  simp only [CollatzResearch.WordTrace]
  refine ⟨28767191422332245739434659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 153425020919105310610318181 28767191422332245739434659)
  ·
    refine ⟨43150787133498368609151989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28767191422332245739434659 43150787133498368609151989)
    ·
      refine ⟨4045386293765472057107999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 43150787133498368609151989 4045386293765472057107999)
      ·
        refine ⟨6068079440648208085661999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4045386293765472057107999 6068079440648208085661999)
        ·
          refine ⟨9102119160972312128492999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6068079440648208085661999 9102119160972312128492999)
          ·
            refine ⟨13653178741458468192739499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9102119160972312128492999 13653178741458468192739499)
            ·
              refine ⟨20479768112187702289109249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13653178741458468192739499 20479768112187702289109249)
              ·
                refine ⟨15359826084140776716831937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20479768112187702289109249 15359826084140776716831937)
                ·
                  refine ⟨11519869563105582537623953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15359826084140776716831937 11519869563105582537623953)
                  ·
                    refine ⟨8639902172329186903217965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11519869563105582537623953 8639902172329186903217965)
                    ·
                      refine ⟨3239963314623445088706737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8639902172329186903217965 3239963314623445088706737)
                      ·
                        rfl

theorem cell23_6309806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 1, 2, 2, 2, 3].length) (baseStart_6309806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6309806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6309806 prefixEnd_6309806 := by exact prefixLift 6309806
  have htrace : WordTrace (prefixWord ++ tailWord_6309806) baseStart_6309806 baseEnd_6309806 := by
    simpa [prefixWord, tailWord_6309806, baseEnd_6309806] using wordTrace_append hprefix tailTrace_6309806
  have hstable : (prefixWord ++ tailWord_6309806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6309806).length < 2 ^ (prefixWord ++ tailWord_6309806).sum := by decide
  have hdescent : baseEnd_6309806 < baseStart_6309806 := by decide
  rcases family_descends (prefixWord ++ tailWord_6309806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6309835 : List Nat := [1, 1, 1, 1, 3, 4, 3, 3, 2, 4]
def baseStart_6309835 : Nat := 118140960795 + 6309835 * 2 ^ 59
def prefixEnd_6309835 : Nat := 4983230072969 + 3 ^ 40 * 6309835 * 2
def baseEnd_6309835 : Nat := 1079992735187475158414701

theorem tailTrace_6309835 : CollatzResearch.WordTrace tailWord_6309835 prefixEnd_6309835 1079992735187475158414701 := by
  unfold tailWord_6309835
  simp only [CollatzResearch.WordTrace]
  refine ⟨230138589095552903868282959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153425726063701935912188639 230138589095552903868282959)
  ·
    refine ⟨345207883643329355802424439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230138589095552903868282959 345207883643329355802424439)
    ·
      refine ⟨517811825464994033703636659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 345207883643329355802424439 517811825464994033703636659)
      ·
        refine ⟨776717738197491050555454989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 517811825464994033703636659 776717738197491050555454989)
        ·
          refine ⟨291269151824059143958295621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 776717738197491050555454989 291269151824059143958295621)
          ·
            refine ⟨54612965967011089492180429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 291269151824059143958295621 54612965967011089492180429)
            ·
              refine ⟨20479862237629158559567661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54612965967011089492180429 20479862237629158559567661)
              ·
                refine ⟨7679948339110934459837873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20479862237629158559567661 7679948339110934459837873)
                ·
                  refine ⟨5759961254333200844878405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7679948339110934459837873 5759961254333200844878405)
                  ·
                    refine ⟨1079992735187475158414701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5759961254333200844878405 1079992735187475158414701)
                    ·
                      rfl

theorem cell23_6309835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 3, 3, 2, 4].length) (baseStart_6309835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6309835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6309835 prefixEnd_6309835 := by exact prefixLift 6309835
  have htrace : WordTrace (prefixWord ++ tailWord_6309835) baseStart_6309835 baseEnd_6309835 := by
    simpa [prefixWord, tailWord_6309835, baseEnd_6309835] using wordTrace_append hprefix tailTrace_6309835
  have hstable : (prefixWord ++ tailWord_6309835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6309835).length < 2 ^ (prefixWord ++ tailWord_6309835).sum := by decide
  have hdescent : baseEnd_6309835 < baseStart_6309835 := by decide
  rcases family_descends (prefixWord ++ tailWord_6309835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6309838 : List Nat := [4, 1, 1, 1, 2, 2, 1, 3, 1, 1, 6]
def baseStart_6309838 : Nat := 118140960795 + 6309838 * 2 ^ 59
def prefixEnd_6309838 : Nat := 4983230072969 + 3 ^ 40 * 6309838 * 2
def baseEnd_6309838 : Nat := 3239979746004388963506589

theorem tailTrace_6309838 : CollatzResearch.WordTrace tailWord_6309838 prefixEnd_6309838 3239979746004388963506589 := by
  unfold tailWord_6309838
  simp only [CollatzResearch.WordTrace]
  refine ⟨28767337314317754422580271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 153425799009694690253761445 28767337314317754422580271)
  ·
    refine ⟨43151005971476631633870407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28767337314317754422580271 43151005971476631633870407)
    ·
      refine ⟨64726508957214947450805611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43151005971476631633870407 64726508957214947450805611)
      ·
        refine ⟨97089763435822421176208417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64726508957214947450805611 97089763435822421176208417)
        ·
          refine ⟨72817322576866815882156313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97089763435822421176208417 72817322576866815882156313)
          ·
            refine ⟨54612991932650111911617235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72817322576866815882156313 54612991932650111911617235)
            ·
              refine ⟨81919487898975167867425853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54612991932650111911617235 81919487898975167867425853)
              ·
                refine ⟨30719807962115687950284695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 81919487898975167867425853 30719807962115687950284695)
                ·
                  refine ⟨46079711943173531925427043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30719807962115687950284695 46079711943173531925427043)
                  ·
                    refine ⟨69119567914760297888140565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 46079711943173531925427043 69119567914760297888140565)
                    ·
                      refine ⟨3239979746004388963506589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 69119567914760297888140565 3239979746004388963506589)
                      ·
                        rfl

theorem cell23_6309838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 3, 1, 1, 6].length) (baseStart_6309838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6309838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6309838 prefixEnd_6309838 := by exact prefixLift 6309838
  have htrace : WordTrace (prefixWord ++ tailWord_6309838) baseStart_6309838 baseEnd_6309838 := by
    simpa [prefixWord, tailWord_6309838, baseEnd_6309838] using wordTrace_append hprefix tailTrace_6309838
  have hstable : (prefixWord ++ tailWord_6309838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6309838).length < 2 ^ (prefixWord ++ tailWord_6309838).sum := by decide
  have hdescent : baseEnd_6309838 < baseStart_6309838 := by decide
  rcases family_descends (prefixWord ++ tailWord_6309838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6309842 : List Nat := [3, 2, 2, 3, 2, 1, 1, 1, 3, 1, 4]
def baseStart_6309842 : Nat := 118140960795 + 6309842 * 2 ^ 59
def prefixEnd_6309842 : Nat := 4983230072969 + 3 ^ 40 * 6309842 * 2
def baseEnd_6309842 : Nat := 3239981799927006947856571

theorem tailTrace_6309842 : CollatzResearch.WordTrace tailWord_6309842 prefixEnd_6309842 3239981799927006947856571 := by
  unfold tailWord_6309842
  simp only [CollatzResearch.WordTrace]
  refine ⟨57534711101631886015946945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153425896271018362709191853 57534711101631886015946945)
  ·
    refine ⟨43151033326223914511960209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57534711101631886015946945 43151033326223914511960209)
    ·
      refine ⟨32363274994667935883970157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43151033326223914511960209 32363274994667935883970157)
      ·
        refine ⟨12136228123000475956488809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32363274994667935883970157 12136228123000475956488809)
        ·
          refine ⟨9102171092250356967366607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12136228123000475956488809 9102171092250356967366607)
          ·
            refine ⟨13653256638375535451049911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9102171092250356967366607 13653256638375535451049911)
            ·
              refine ⟨20479884957563303176574867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13653256638375535451049911 20479884957563303176574867)
              ·
                refine ⟨30719827436344954764862301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20479884957563303176574867 30719827436344954764862301)
                ·
                  refine ⟨11519935288629358036823363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30719827436344954764862301 11519935288629358036823363)
                  ·
                    refine ⟨17279902932944037055235045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11519935288629358036823363 17279902932944037055235045)
                    ·
                      refine ⟨3239981799927006947856571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17279902932944037055235045 3239981799927006947856571)
                      ·
                        rfl

theorem cell23_6309842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 1, 1, 3, 1, 4].length) (baseStart_6309842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6309842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6309842 prefixEnd_6309842 := by exact prefixLift 6309842
  have htrace : WordTrace (prefixWord ++ tailWord_6309842) baseStart_6309842 baseEnd_6309842 := by
    simpa [prefixWord, tailWord_6309842, baseEnd_6309842] using wordTrace_append hprefix tailTrace_6309842
  have hstable : (prefixWord ++ tailWord_6309842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6309842).length < 2 ^ (prefixWord ++ tailWord_6309842).sum := by decide
  have hdescent : baseEnd_6309842 < baseStart_6309842 := by decide
  rcases family_descends (prefixWord ++ tailWord_6309842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6309846 : List Nat := [5, 2, 1, 1, 3, 1, 2, 1, 2, 3, 2]
def baseStart_6309846 : Nat := 118140960795 + 6309846 * 2 ^ 59
def prefixEnd_6309846 : Nat := 4983230072969 + 3 ^ 40 * 6309846 * 2
def baseEnd_6309846 : Nat := 3239983853849624932206553

theorem tailTrace_6309846 : CollatzResearch.WordTrace tailWord_6309846 prefixEnd_6309846 3239983853849624932206553 := by
  unfold tailWord_6309846
  simp only [CollatzResearch.WordTrace]
  refine ⟨14383686893657065796683337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 153425993532342035164622261 14383686893657065796683337)
  ·
    refine ⟨10787765170242799347512503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14383686893657065796683337 10787765170242799347512503)
    ·
      refine ⟨16181647755364199021268755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10787765170242799347512503 16181647755364199021268755)
      ·
        refine ⟨24272471633046298531903133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16181647755364199021268755 24272471633046298531903133)
        ·
          refine ⟨9102176862392361949463675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24272471633046298531903133 9102176862392361949463675)
          ·
            refine ⟨13653265293588542924195513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9102176862392361949463675 13653265293588542924195513)
            ·
              refine ⟨10239948970191407193146635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13653265293588542924195513 10239948970191407193146635)
              ·
                refine ⟨15359923455287110789719953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10239948970191407193146635 15359923455287110789719953)
                ·
                  refine ⟨11519942591465333092289965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15359923455287110789719953 11519942591465333092289965)
                  ·
                    refine ⟨4319978471799499909608737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11519942591465333092289965 4319978471799499909608737)
                    ·
                      refine ⟨3239983853849624932206553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4319978471799499909608737 3239983853849624932206553)
                      ·
                        rfl

theorem cell23_6309846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 2, 1, 2, 3, 2].length) (baseStart_6309846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6309846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6309846 prefixEnd_6309846 := by exact prefixLift 6309846
  have htrace : WordTrace (prefixWord ++ tailWord_6309846) baseStart_6309846 baseEnd_6309846 := by
    simpa [prefixWord, tailWord_6309846, baseEnd_6309846] using wordTrace_append hprefix tailTrace_6309846
  have hstable : (prefixWord ++ tailWord_6309846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6309846).length < 2 ^ (prefixWord ++ tailWord_6309846).sum := by decide
  have hdescent : baseEnd_6309846 < baseStart_6309846 := by decide
  rcases family_descends (prefixWord ++ tailWord_6309846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6309855 : List Nat := [1, 1, 2, 3, 4, 2, 1, 2, 1, 2, 4]
def baseStart_6309855 : Nat := 118140960795 + 6309855 * 2 ^ 59
def prefixEnd_6309855 : Nat := 4983230072969 + 3 ^ 40 * 6309855 * 2
def baseEnd_6309855 : Nat := 3239988475175515396994011

theorem tailTrace_6309855 : CollatzResearch.WordTrace tailWord_6309855 prefixEnd_6309855 3239988475175515396994011 := by
  unfold tailWord_6309855
  simp only [CollatzResearch.WordTrace]
  refine ⟨230139318555480447284011019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153426212370320298189340679 230139318555480447284011019)
  ·
    refine ⟨345208977833220670926016529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230139318555480447284011019 345208977833220670926016529)
    ·
      refine ⟨258906733374915503194512397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 345208977833220670926016529 258906733374915503194512397)
      ·
        refine ⟨97090025015593313697942149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 258906733374915503194512397 97090025015593313697942149)
        ·
          refine ⟨18204379690423746318364153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 97090025015593313697942149 18204379690423746318364153)
          ·
            refine ⟨13653284767817809738773115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18204379690423746318364153 13653284767817809738773115)
            ·
              refine ⟨20479927151726714608159673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13653284767817809738773115 20479927151726714608159673)
              ·
                refine ⟨15359945363795035956119755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20479927151726714608159673 15359945363795035956119755)
                ·
                  refine ⟨23039918045692553934179633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15359945363795035956119755 23039918045692553934179633)
                  ·
                    refine ⟨17279938534269415450634725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23039918045692553934179633 17279938534269415450634725)
                    ·
                      refine ⟨3239988475175515396994011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17279938534269415450634725 3239988475175515396994011)
                      ·
                        rfl

theorem cell23_6309855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 1, 2, 1, 2, 4].length) (baseStart_6309855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6309855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6309855 prefixEnd_6309855 := by exact prefixLift 6309855
  have htrace : WordTrace (prefixWord ++ tailWord_6309855) baseStart_6309855 baseEnd_6309855 := by
    simpa [prefixWord, tailWord_6309855, baseEnd_6309855] using wordTrace_append hprefix tailTrace_6309855
  have hstable : (prefixWord ++ tailWord_6309855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6309855).length < 2 ^ (prefixWord ++ tailWord_6309855).sum := by decide
  have hdescent : baseEnd_6309855 < baseStart_6309855 := by decide
  rcases family_descends (prefixWord ++ tailWord_6309855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6309875 : List Nat := [1, 1, 1, 2, 2, 2, 1, 5, 4, 1, 3]
def baseStart_6309875 : Nat := 118140960795 + 6309875 * 2 ^ 59
def prefixEnd_6309875 : Nat := 4983230072969 + 3 ^ 40 * 6309875 * 2
def baseEnd_6309875 : Nat := 3239998744788605318743919

theorem tailTrace_6309875 : CollatzResearch.WordTrace tailWord_6309875 prefixEnd_6309875 3239998744788605318743919 := by
  unfold tailWord_6309875
  simp only [CollatzResearch.WordTrace]
  refine ⟨230140048015407990699739079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153426698676938660466492719 230140048015407990699739079)
  ·
    refine ⟨345210072023111986049608619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230140048015407990699739079 345210072023111986049608619)
    ·
      refine ⟨517815108034667979074412929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 345210072023111986049608619 517815108034667979074412929)
      ·
        refine ⟨388361331026000984305809697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 517815108034667979074412929 388361331026000984305809697)
        ·
          refine ⟨291270998269500738229357273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 388361331026000984305809697 291270998269500738229357273)
          ·
            refine ⟨218453248702125553672017955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 291270998269500738229357273 218453248702125553672017955)
            ·
              refine ⟨327679873053188330508026933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 218453248702125553672017955 327679873053188330508026933)
              ·
                refine ⟨30719988098736405985127525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 327679873053188330508026933 30719988098736405985127525)
                ·
                  refine ⟨5759997768513076122211411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30719988098736405985127525 5759997768513076122211411)
                  ·
                    refine ⟨8639996652769614183317117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5759997768513076122211411 8639996652769614183317117)
                    ·
                      refine ⟨3239998744788605318743919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8639996652769614183317117 3239998744788605318743919)
                      ·
                        rfl

theorem cell23_6309875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 5, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 5, 4, 1, 3].length) (baseStart_6309875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6309875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6309875 prefixEnd_6309875 := by exact prefixLift 6309875
  have htrace : WordTrace (prefixWord ++ tailWord_6309875) baseStart_6309875 baseEnd_6309875 := by
    simpa [prefixWord, tailWord_6309875, baseEnd_6309875] using wordTrace_append hprefix tailTrace_6309875
  have hstable : (prefixWord ++ tailWord_6309875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6309875).length < 2 ^ (prefixWord ++ tailWord_6309875).sum := by decide
  have hdescent : baseEnd_6309875 < baseStart_6309875 := by decide
  rcases family_descends (prefixWord ++ tailWord_6309875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6309902 : List Nat := [4, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2]
def baseStart_6309902 : Nat := 118140960795 + 6309902 * 2 ^ 59
def prefixEnd_6309902 : Nat := 4983230072969 + 3 ^ 40 * 6309902 * 2
def baseEnd_6309902 : Nat := 3240012608766276713106295

theorem tailTrace_6309902 : CollatzResearch.WordTrace tailWord_6309902 prefixEnd_6309902 3240012608766276713106295 := by
  unfold tailWord_6309902
  simp only [CollatzResearch.WordTrace]
  refine ⟨28767629098288771788871495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 153427355190873449540647973 28767629098288771788871495)
  ·
    refine ⟨43151443647433157683307243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28767629098288771788871495 43151443647433157683307243)
    ·
      refine ⟨64727165471149736524960865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43151443647433157683307243 64727165471149736524960865)
      ·
        refine ⟨48545374103362302393720649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64727165471149736524960865 48545374103362302393720649)
        ·
          refine ⟨36409030577521726795290487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48545374103362302393720649 36409030577521726795290487)
          ·
            refine ⟨54613545866282590192935731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36409030577521726795290487 54613545866282590192935731)
            ·
              refine ⟨81920318799423885289403597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54613545866282590192935731 81920318799423885289403597)
              ·
                refine ⟨30720119549783956983526349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 81920318799423885289403597 30720119549783956983526349)
                ·
                  refine ⟨11520044831168983868822381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30720119549783956983526349 11520044831168983868822381)
                  ·
                    refine ⟨4320016811688368950808393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11520044831168983868822381 4320016811688368950808393)
                    ·
                      refine ⟨3240012608766276713106295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4320016811688368950808393 3240012608766276713106295)
                      ·
                        rfl

theorem cell23_6309902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2].length) (baseStart_6309902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6309902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6309902 prefixEnd_6309902 := by exact prefixLift 6309902
  have htrace : WordTrace (prefixWord ++ tailWord_6309902) baseStart_6309902 baseEnd_6309902 := by
    simpa [prefixWord, tailWord_6309902, baseEnd_6309902] using wordTrace_append hprefix tailTrace_6309902
  have hstable : (prefixWord ++ tailWord_6309902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6309902).length < 2 ^ (prefixWord ++ tailWord_6309902).sum := by decide
  have hdescent : baseEnd_6309902 < baseStart_6309902 := by decide
  rcases family_descends (prefixWord ++ tailWord_6309902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6309915 : List Nat := [1, 1, 1, 1, 1, 1, 3, 5, 3, 4, 2]
def baseStart_6309915 : Nat := 118140960795 + 6309915 * 2 ^ 59
def prefixEnd_6309915 : Nat := 4983230072969 + 3 ^ 40 * 6309915 * 2
def baseEnd_6309915 : Nat := 3240019284014785162243735

theorem tailTrace_6309915 : CollatzResearch.WordTrace tailWord_6309915 prefixEnd_6309915 3240019284014785162243735 := by
  unfold tailWord_6309915
  simp only [CollatzResearch.WordTrace]
  refine ⟨230141506935263077531195199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153427671290175385020796799 230141506935263077531195199)
  ·
    refine ⟨345212260402894616296792799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230141506935263077531195199 345212260402894616296792799)
    ·
      refine ⟨517818390604341924445189199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 345212260402894616296792799 517818390604341924445189199)
      ·
        refine ⟨776727585906512886667783799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 517818390604341924445189199 776727585906512886667783799)
        ·
          refine ⟨1165091378859769330001675699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 776727585906512886667783799 1165091378859769330001675699)
          ·
            refine ⟨1747637068289653995002513549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1165091378859769330001675699 1747637068289653995002513549)
            ·
              refine ⟨655363900608620248125942581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1747637068289653995002513549 655363900608620248125942581)
              ·
                refine ⟨61440365682058148261807117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 655363900608620248125942581 61440365682058148261807117)
                ·
                  refine ⟨23040137130771805598177669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 61440365682058148261807117 23040137130771805598177669)
                  ·
                    refine ⟨4320025712019713549658313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23040137130771805598177669 4320025712019713549658313)
                    ·
                      refine ⟨3240019284014785162243735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4320025712019713549658313 3240019284014785162243735)
                      ·
                        rfl

theorem cell23_6309915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 5, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 5, 3, 4, 2].length) (baseStart_6309915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6309915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6309915 prefixEnd_6309915 := by exact prefixLift 6309915
  have htrace : WordTrace (prefixWord ++ tailWord_6309915) baseStart_6309915 baseEnd_6309915 := by
    simpa [prefixWord, tailWord_6309915, baseEnd_6309915] using wordTrace_append hprefix tailTrace_6309915
  have hstable : (prefixWord ++ tailWord_6309915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6309915).length < 2 ^ (prefixWord ++ tailWord_6309915).sum := by decide
  have hdescent : baseEnd_6309915 < baseStart_6309915 := by decide
  rcases family_descends (prefixWord ++ tailWord_6309915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6309989 : List Nat := [1, 3, 1, 3, 2, 3, 3, 2, 5]
def baseStart_6309989 : Nat := 118140960795 + 6309989 * 2 ^ 59
def prefixEnd_6309989 : Nat := 4983230072969 + 3 ^ 40 * 6309989 * 2
def baseEnd_6309989 : Nat := 360006364620357541413155

theorem tailTrace_6309989 : CollatzResearch.WordTrace tailWord_6309989 prefixEnd_6309989 360006364620357541413155 := by
  unfold tailWord_6309989
  simp only [CollatzResearch.WordTrace]
  refine ⟨230144205936994988169389021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153429470624663325446259347 230144205936994988169389021)
  ·
    refine ⟨86304077226373120563520883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 230144205936994988169389021 86304077226373120563520883)
    ·
      refine ⟨129456115839559680845281325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86304077226373120563520883 129456115839559680845281325)
      ·
        refine ⟨48546043439834880316980497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 129456115839559680845281325 48546043439834880316980497)
        ·
          refine ⟨36409532579876160237735373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48546043439834880316980497 36409532579876160237735373)
          ·
            refine ⟨13653574717453560089150765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36409532579876160237735373 13653574717453560089150765)
            ·
              refine ⟨5120090519045085033431537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13653574717453560089150765 5120090519045085033431537)
              ·
                refine ⟨3840067889283813775073653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5120090519045085033431537 3840067889283813775073653)
                ·
                  refine ⟨360006364620357541413155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3840067889283813775073653 360006364620357541413155)
                  ·
                    rfl

theorem cell23_6309989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 3, 2, 5].length) (baseStart_6309989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6309989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6309989 prefixEnd_6309989 := by exact prefixLift 6309989
  have htrace : WordTrace (prefixWord ++ tailWord_6309989) baseStart_6309989 baseEnd_6309989 := by
    simpa [prefixWord, tailWord_6309989, baseEnd_6309989] using wordTrace_append hprefix tailTrace_6309989
  have hstable : (prefixWord ++ tailWord_6309989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6309989).length < 2 ^ (prefixWord ++ tailWord_6309989).sum := by decide
  have hdescent : baseEnd_6309989 < baseStart_6309989 := by decide
  rcases family_descends (prefixWord ++ tailWord_6309989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6310075 : List Nat := [1, 1, 1, 1, 1, 2, 5, 3, 3, 5]
def baseStart_6310075 : Nat := 118140960795 + 6310075 * 2 ^ 59
def prefixEnd_6310075 : Nat := 4983230072969 + 3 ^ 40 * 6310075 * 2
def baseEnd_6310075 : Nat := 1080033813639834845414333

theorem tailTrace_6310075 : CollatzResearch.WordTrace tailWord_6310075 prefixEnd_6310075 1080033813639834845414333 := by
  unfold tailWord_6310075
  simp only [CollatzResearch.WordTrace]
  refine ⟨230147342614683424857019679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153431561743122283238013119 230147342614683424857019679)
  ·
    refine ⟨345221013922025137285529519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230147342614683424857019679 345221013922025137285529519)
    ·
      refine ⟨517831520883037705928294279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 345221013922025137285529519 517831520883037705928294279)
      ·
        refine ⟨776747281324556558892441419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 517831520883037705928294279 776747281324556558892441419)
        ·
          refine ⟨1165120921986834838338662129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 776747281324556558892441419 1165120921986834838338662129)
          ·
            refine ⟨873840691490126128753996597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1165120921986834838338662129 873840691490126128753996597)
            ·
              refine ⟨81922564827199324570687181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 873840691490126128753996597 81922564827199324570687181)
              ·
                refine ⟨30720961810199746714007693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 81922564827199324570687181 30720961810199746714007693)
                ·
                  refine ⟨11520360678824905017752885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30720961810199746714007693 11520360678824905017752885)
                  ·
                    refine ⟨1080033813639834845414333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11520360678824905017752885 1080033813639834845414333)
                    ·
                      rfl

theorem cell23_6310075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 3, 3, 5].length) (baseStart_6310075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6310075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6310075 prefixEnd_6310075 := by exact prefixLift 6310075
  have htrace : WordTrace (prefixWord ++ tailWord_6310075) baseStart_6310075 baseEnd_6310075 := by
    simpa [prefixWord, tailWord_6310075, baseEnd_6310075] using wordTrace_append hprefix tailTrace_6310075
  have hstable : (prefixWord ++ tailWord_6310075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6310075).length < 2 ^ (prefixWord ++ tailWord_6310075).sum := by decide
  have hdescent : baseEnd_6310075 < baseStart_6310075 := by decide
  rcases family_descends (prefixWord ++ tailWord_6310075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6310076 : List Nat := [2, 2, 2, 3, 3, 2, 1, 1, 2, 2, 3]
def baseStart_6310076 : Nat := 118140960795 + 6310076 * 2 ^ 59
def prefixEnd_6310076 : Nat := 4983230072969 + 3 ^ 40 * 6310076 * 2
def baseEnd_6310076 : Nat := 3240101954400159032330495

theorem tailTrace_6310076 : CollatzResearch.WordTrace tailWord_6310076 prefixEnd_6310076 3240101954400159032330495 := by
  unfold tailWord_6310076
  simp only [CollatzResearch.WordTrace]
  refine ⟨115073689543839901013903041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153431586058453201351870721 115073689543839901013903041)
  ·
    refine ⟨86305267157879925760427281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115073689543839901013903041 86305267157879925760427281)
    ·
      refine ⟨64728950368409944320320461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86305267157879925760427281 64728950368409944320320461)
      ·
        refine ⟨24273356388153729120120173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64728950368409944320320461 24273356388153729120120173)
        ·
          refine ⟨9102508645557648420045065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24273356388153729120120173 9102508645557648420045065)
          ·
            refine ⟨6826881484168236315033799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9102508645557648420045065 6826881484168236315033799)
            ·
              refine ⟨10240322226252354472550699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6826881484168236315033799 10240322226252354472550699)
              ·
                refine ⟨15360483339378531708826049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10240322226252354472550699 15360483339378531708826049)
                ·
                  refine ⟨11520362504533898781619537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15360483339378531708826049 11520362504533898781619537)
                  ·
                    refine ⟨8640271878400424086214653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11520362504533898781619537 8640271878400424086214653)
                    ·
                      refine ⟨3240101954400159032330495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8640271878400424086214653 3240101954400159032330495)
                      ·
                        rfl

theorem cell23_6310076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 2, 1, 1, 2, 2, 3].length) (baseStart_6310076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6310076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6310076 prefixEnd_6310076 := by exact prefixLift 6310076
  have htrace : WordTrace (prefixWord ++ tailWord_6310076) baseStart_6310076 baseEnd_6310076 := by
    simpa [prefixWord, tailWord_6310076, baseEnd_6310076] using wordTrace_append hprefix tailTrace_6310076
  have hstable : (prefixWord ++ tailWord_6310076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6310076).length < 2 ^ (prefixWord ++ tailWord_6310076).sum := by decide
  have hdescent : baseEnd_6310076 < baseStart_6310076 := by decide
  rcases family_descends (prefixWord ++ tailWord_6310076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6310105 : List Nat := [1, 2, 1, 2, 3, 1, 2, 2, 3, 6]
def baseStart_6310105 : Nat := 118140960795 + 6310105 * 2 ^ 59
def prefixEnd_6310105 : Nat := 4983230072969 + 3 ^ 40 * 6310105 * 2
def baseEnd_6310105 : Nat := 1080038948446379806289287

theorem tailTrace_6310105 : CollatzResearch.WordTrace tailWord_6310105 prefixEnd_6310105 1080038948446379806289287 := by
  unfold tailWord_6310105
  simp only [CollatzResearch.WordTrace]
  refine ⟨230148436804574739980611769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153432291203049826653741179 230148436804574739980611769)
  ·
    refine ⟨172611327603431054985458827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 230148436804574739980611769 172611327603431054985458827)
    ·
      refine ⟨258916991405146582478188241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172611327603431054985458827 258916991405146582478188241)
      ·
        refine ⟨194187743553859936858641181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 258916991405146582478188241 194187743553859936858641181)
        ·
          refine ⟨72820403832697476321990443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 194187743553859936858641181 72820403832697476321990443)
          ·
            refine ⟨109230605749046214482985665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72820403832697476321990443 109230605749046214482985665)
            ·
              refine ⟨81922954311784660862239249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 109230605749046214482985665 81922954311784660862239249)
              ·
                refine ⟨61442215733838495646679437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 81922954311784660862239249 61442215733838495646679437)
                ·
                  refine ⟨23040830900189435867504789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 61442215733838495646679437 23040830900189435867504789)
                  ·
                    refine ⟨1080038948446379806289287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23040830900189435867504789 1080038948446379806289287)
                    ·
                      rfl

theorem cell23_6310105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 2, 3, 6].length) (baseStart_6310105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6310105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6310105 prefixEnd_6310105 := by exact prefixLift 6310105
  have htrace : WordTrace (prefixWord ++ tailWord_6310105) baseStart_6310105 baseEnd_6310105 := by
    simpa [prefixWord, tailWord_6310105, baseEnd_6310105] using wordTrace_append hprefix tailTrace_6310105
  have hstable : (prefixWord ++ tailWord_6310105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6310105).length < 2 ^ (prefixWord ++ tailWord_6310105).sum := by decide
  have hdescent : baseEnd_6310105 < baseStart_6310105 := by decide
  rcases family_descends (prefixWord ++ tailWord_6310105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6310106 : List Nat := [3, 1, 1, 2, 2, 1, 4, 4, 1, 1, 3]
def baseStart_6310106 : Nat := 118140960795 + 6310106 * 2 ^ 59
def prefixEnd_6310106 : Nat := 4983230072969 + 3 ^ 40 * 6310106 * 2
def baseEnd_6310106 : Nat := 3240117358819793914955357

theorem tailTrace_6310106 : CollatzResearch.WordTrace tailWord_6310106 prefixEnd_6310106 3240117358819793914955357 := by
  unfold tailWord_6310106
  simp only [CollatzResearch.WordTrace]
  refine ⟨57537118319392779287849543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153432315518380744767598781 57537118319392779287849543)
  ·
    refine ⟨86305677479089168931774315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57537118319392779287849543 86305677479089168931774315)
    ·
      refine ⟨129458516218633753397661473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86305677479089168931774315 129458516218633753397661473)
      ·
        refine ⟨97093887163975315048246105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129458516218633753397661473 97093887163975315048246105)
        ·
          refine ⟨72820415372981486286184579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97093887163975315048246105 72820415372981486286184579)
          ·
            refine ⟨109230623059472229429276869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72820415372981486286184579 109230623059472229429276869)
            ·
              refine ⟨20480741823651043017989413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 109230623059472229429276869 20480741823651043017989413)
              ·
                refine ⟨3840139091934570565873015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20480741823651043017989413 3840139091934570565873015)
                ·
                  refine ⟨5760208637901855848809523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3840139091934570565873015 5760208637901855848809523)
                  ·
                    refine ⟨8640312956852783773214285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5760208637901855848809523 8640312956852783773214285)
                    ·
                      refine ⟨3240117358819793914955357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8640312956852783773214285 3240117358819793914955357)
                      ·
                        rfl

theorem cell23_6310106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 4, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 4, 4, 1, 1, 3].length) (baseStart_6310106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6310106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6310106 prefixEnd_6310106 := by exact prefixLift 6310106
  have htrace : WordTrace (prefixWord ++ tailWord_6310106) baseStart_6310106 baseEnd_6310106 := by
    simpa [prefixWord, tailWord_6310106, baseEnd_6310106] using wordTrace_append hprefix tailTrace_6310106
  have hstable : (prefixWord ++ tailWord_6310106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6310106).length < 2 ^ (prefixWord ++ tailWord_6310106).sum := by decide
  have hdescent : baseEnd_6310106 < baseStart_6310106 := by decide
  rcases family_descends (prefixWord ++ tailWord_6310106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6310146 : List Nat := [3, 4, 1, 1, 2, 1, 2, 3, 1, 1, 4]
def baseStart_6310146 : Nat := 118140960795 + 6310146 * 2 ^ 59
def prefixEnd_6310146 : Nat := 4983230072969 + 3 ^ 40 * 6310146 * 2
def baseEnd_6310146 : Nat := 3240137898045973758455173

theorem tailTrace_6310146 : CollatzResearch.WordTrace tailWord_6310146 prefixEnd_6310146 3240137898045973758455173 := by
  unfold tailWord_6310146
  simp only [CollatzResearch.WordTrace]
  refine ⟨57537483049356550995713573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153433288131617469321902861 57537483049356550995713573)
  ·
    refine ⟨10788278071754353311696295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57537483049356550995713573 10788278071754353311696295)
    ·
      refine ⟨16182417107631529967544443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10788278071754353311696295 16182417107631529967544443)
      ·
        refine ⟨24273625661447294951316665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16182417107631529967544443 24273625661447294951316665)
        ·
          refine ⟨18205219246085471213487499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24273625661447294951316665 18205219246085471213487499)
          ·
            refine ⟨27307828869128206820231249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18205219246085471213487499 27307828869128206820231249)
            ·
              refine ⟨20480871651846155115173437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27307828869128206820231249 20480871651846155115173437)
              ·
                refine ⟨7680326869442308168190039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20480871651846155115173437 7680326869442308168190039)
                ·
                  refine ⟨11520490304163462252285059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7680326869442308168190039 11520490304163462252285059)
                  ·
                    refine ⟨17280735456245193378427589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11520490304163462252285059 17280735456245193378427589)
                    ·
                      refine ⟨3240137898045973758455173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17280735456245193378427589 3240137898045973758455173)
                      ·
                        rfl

theorem cell23_6310146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 2, 3, 1, 1, 4].length) (baseStart_6310146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6310146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6310146 prefixEnd_6310146 := by exact prefixLift 6310146
  have htrace : WordTrace (prefixWord ++ tailWord_6310146) baseStart_6310146 baseEnd_6310146 := by
    simpa [prefixWord, tailWord_6310146, baseEnd_6310146] using wordTrace_append hprefix tailTrace_6310146
  have hstable : (prefixWord ++ tailWord_6310146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6310146).length < 2 ^ (prefixWord ++ tailWord_6310146).sum := by decide
  have hdescent : baseEnd_6310146 < baseStart_6310146 := by decide
  rcases family_descends (prefixWord ++ tailWord_6310146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6310152 : List Nat := [2, 1, 3, 2, 3, 3, 9]
def baseStart_6310152 : Nat := 118140960795 + 6310152 * 2 ^ 59
def prefixEnd_6310152 : Nat := 4983230072969 + 3 ^ 40 * 6310152 * 2
def baseEnd_6310152 : Nat := 40001740480616058456545

theorem tailTrace_6310152 : CollatzResearch.WordTrace tailWord_6310152 prefixEnd_6310152 40001740480616058456545 := by
  unfold tailWord_6310152
  simp only [CollatzResearch.WordTrace]
  refine ⟨115075075517702233503786355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153433434023602978005048473 115075075517702233503786355)
  ·
    refine ⟨172612613276553350255679533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115075075517702233503786355 172612613276553350255679533)
    ·
      refine ⟨64729729978707506345879825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 172612613276553350255679533 64729729978707506345879825)
      ·
        refine ⟨48547297484030629759409869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64729729978707506345879825 48547297484030629759409869)
        ·
          refine ⟨18205236556511486159778701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48547297484030629759409869 18205236556511486159778701)
          ·
            refine ⟨6826963708691807309917013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18205236556511486159778701 6826963708691807309917013)
            ·
              refine ⟨40001740480616058456545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6826963708691807309917013 40001740480616058456545)
              ·
                rfl

theorem cell23_6310152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 3, 9].length) (baseStart_6310152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6310152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6310152 prefixEnd_6310152 := by exact prefixLift 6310152
  have htrace : WordTrace (prefixWord ++ tailWord_6310152) baseStart_6310152 baseEnd_6310152 := by
    simpa [prefixWord, tailWord_6310152, baseEnd_6310152] using wordTrace_append hprefix tailTrace_6310152
  have hstable : (prefixWord ++ tailWord_6310152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6310152).length < 2 ^ (prefixWord ++ tailWord_6310152).sum := by decide
  have hdescent : baseEnd_6310152 < baseStart_6310152 := by decide
  rcases family_descends (prefixWord ++ tailWord_6310152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6310196 : List Nat := [2, 5, 1, 1, 1, 3, 1, 2, 1, 3, 3]
def baseStart_6310196 : Nat := 118140960795 + 6310196 * 2 ^ 59
def prefixEnd_6310196 : Nat := 4983230072969 + 3 ^ 40 * 6310196 * 2
def baseEnd_6310196 : Nat := 3240163572078698562829943

theorem tailTrace_6310196 : CollatzResearch.WordTrace tailWord_6310196 prefixEnd_6310196 3240163572078698562829943 := by
  unfold tailWord_6310196
  simp only [CollatzResearch.WordTrace]
  refine ⟨115075877923622531261087221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153434503898163375014782961 115075877923622531261087221)
  ·
    refine ⟨10788363555339612305726927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 115075877923622531261087221 10788363555339612305726927)
    ·
      refine ⟨16182545333009418458590391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10788363555339612305726927 16182545333009418458590391)
      ·
        refine ⟨24273817999514127687885587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16182545333009418458590391 24273817999514127687885587)
        ·
          refine ⟨36410726999271191531828381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24273817999514127687885587 36410726999271191531828381)
          ·
            refine ⟨13654022624726696824435643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36410726999271191531828381 13654022624726696824435643)
            ·
              refine ⟨20481033937090045236653465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13654022624726696824435643 20481033937090045236653465)
              ·
                refine ⟨15360775452817533927490099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20481033937090045236653465 15360775452817533927490099)
                ·
                  refine ⟨23041163179226300891235149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15360775452817533927490099 23041163179226300891235149)
                  ·
                    refine ⟨8640436192209862834213181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23041163179226300891235149 8640436192209862834213181)
                    ·
                      refine ⟨3240163572078698562829943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8640436192209862834213181 3240163572078698562829943)
                      ·
                        rfl

theorem cell23_6310196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 1, 2, 1, 3, 3].length) (baseStart_6310196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6310196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6310196 prefixEnd_6310196 := by exact prefixLift 6310196
  have htrace : WordTrace (prefixWord ++ tailWord_6310196) baseStart_6310196 baseEnd_6310196 := by
    simpa [prefixWord, tailWord_6310196, baseEnd_6310196] using wordTrace_append hprefix tailTrace_6310196
  have hstable : (prefixWord ++ tailWord_6310196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6310196).length < 2 ^ (prefixWord ++ tailWord_6310196).sum := by decide
  have hdescent : baseEnd_6310196 < baseStart_6310196 := by decide
  rcases family_descends (prefixWord ++ tailWord_6310196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6310222 : List Nat := [4, 1, 1, 1, 1, 1, 2, 2, 4, 1, 5]
def baseStart_6310222 : Nat := 118140960795 + 6310222 * 2 ^ 59
def prefixEnd_6310222 : Nat := 4983230072969 + 3 ^ 40 * 6310222 * 2
def baseEnd_6310222 : Nat := 3240176922575715461104823

theorem tailTrace_6310222 : CollatzResearch.WordTrace tailWord_6310222 prefixEnd_6310222 3240176922575715461104823 := by
  unfold tailWord_6310222
  simp only [CollatzResearch.WordTrace]
  refine ⟨28769088018143858620327615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 153435136096767245975080613 28769088018143858620327615)
  ·
    refine ⟨43153632027215787930491423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28769088018143858620327615 43153632027215787930491423)
    ·
      refine ⟨64730448040823681895737135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43153632027215787930491423 64730448040823681895737135)
      ·
        refine ⟨97095672061235522843605703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64730448040823681895737135 97095672061235522843605703)
        ·
          refine ⟨145643508091853284265408555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97095672061235522843605703 145643508091853284265408555)
          ·
            refine ⟨218465262137779926398112833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 145643508091853284265408555 218465262137779926398112833)
            ·
              refine ⟨163848946603334944798584625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 218465262137779926398112833 163848946603334944798584625)
              ·
                refine ⟨122886709952501208598938469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 163848946603334944798584625 122886709952501208598938469)
                ·
                  refine ⟨23041258116093976612300963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 122886709952501208598938469 23041258116093976612300963)
                  ·
                    refine ⟨34561887174140964918451445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23041258116093976612300963 34561887174140964918451445)
                    ·
                      refine ⟨3240176922575715461104823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34561887174140964918451445 3240176922575715461104823)
                      ·
                        rfl

theorem cell23_6310222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 2, 4, 1, 5].length) (baseStart_6310222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6310222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6310222 prefixEnd_6310222 := by exact prefixLift 6310222
  have htrace : WordTrace (prefixWord ++ tailWord_6310222) baseStart_6310222 baseEnd_6310222 := by
    simpa [prefixWord, tailWord_6310222, baseEnd_6310222] using wordTrace_append hprefix tailTrace_6310222
  have hstable : (prefixWord ++ tailWord_6310222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6310222).length < 2 ^ (prefixWord ++ tailWord_6310222).sum := by decide
  have hdescent : baseEnd_6310222 < baseStart_6310222 := by decide
  rcases family_descends (prefixWord ++ tailWord_6310222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6310229 : List Nat := [1, 3, 2, 2, 4, 1, 1, 1, 2, 6]
def baseStart_6310229 : Nat := 118140960795 + 6310229 * 2 ^ 59
def prefixEnd_6310229 : Nat := 4983230072969 + 3 ^ 40 * 6310229 * 2
def baseEnd_6310229 : Nat := 1080060172313432311239097

theorem tailTrace_6310229 : CollatzResearch.WordTrace tailWord_6310229 prefixEnd_6310229 1080060172313432311239097 := by
  unfold tailWord_6310229
  simp only [CollatzResearch.WordTrace]
  refine ⟨230152959456125509158125741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153435306304083672772083827 230152959456125509158125741)
  ·
    refine ⟨86307359796047065934297153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 230152959456125509158125741 86307359796047065934297153)
    ·
      refine ⟨64730519847035299450722865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86307359796047065934297153 64730519847035299450722865)
      ·
        refine ⟨48547889885276474588042149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64730519847035299450722865 48547889885276474588042149)
        ·
          refine ⟨9102729353489338985257903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48547889885276474588042149 9102729353489338985257903)
          ·
            refine ⟨13654094030234008477886855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9102729353489338985257903 13654094030234008477886855)
            ·
              refine ⟨20481141045351012716830283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13654094030234008477886855 20481141045351012716830283)
              ·
                refine ⟨30721711568026519075245425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20481141045351012716830283 30721711568026519075245425)
                ·
                  refine ⟨23041283676019889306434069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30721711568026519075245425 23041283676019889306434069)
                  ·
                    refine ⟨1080060172313432311239097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23041283676019889306434069 1080060172313432311239097)
                    ·
                      rfl

theorem cell23_6310229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 1, 1, 2, 6].length) (baseStart_6310229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6310229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6310229 prefixEnd_6310229 := by exact prefixLift 6310229
  have htrace : WordTrace (prefixWord ++ tailWord_6310229) baseStart_6310229 baseEnd_6310229 := by
    simpa [prefixWord, tailWord_6310229, baseEnd_6310229] using wordTrace_append hprefix tailTrace_6310229
  have hstable : (prefixWord ++ tailWord_6310229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6310229).length < 2 ^ (prefixWord ++ tailWord_6310229).sum := by decide
  have hdescent : baseEnd_6310229 < baseStart_6310229 := by decide
  rcases family_descends (prefixWord ++ tailWord_6310229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6310269 : List Nat := [1, 4, 1, 1, 2, 3, 1, 2, 2, 3, 3]
def baseStart_6310269 : Nat := 118140960795 + 6310269 * 2 ^ 59
def prefixEnd_6310269 : Nat := 4983230072969 + 3 ^ 40 * 6310269 * 2
def baseEnd_6310269 : Nat := 3240201056166476777217107

theorem tailTrace_6310269 : CollatzResearch.WordTrace tailWord_6310269 prefixEnd_6310269 3240201056166476777217107 := by
  unfold tailWord_6310269
  simp only [CollatzResearch.WordTrace]
  refine ⟨230154418375980595989581861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153436278917320397326387907 230154418375980595989581861)
  ·
    refine ⟨43153953445496361748046599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 230154418375980595989581861 43153953445496361748046599)
    ·
      refine ⟨64730930168244542622069899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43153953445496361748046599 64730930168244542622069899)
      ·
        refine ⟨97096395252366813933104849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64730930168244542622069899 97096395252366813933104849)
        ·
          refine ⟨72822296439275110449828637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97096395252366813933104849 72822296439275110449828637)
          ·
            refine ⟨27308361164728166418685739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72822296439275110449828637 27308361164728166418685739)
            ·
              refine ⟨40962541747092249628028609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27308361164728166418685739 40962541747092249628028609)
              ·
                refine ⟨30721906310319187221021457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40962541747092249628028609 30721906310319187221021457)
                ·
                  refine ⟨23041429732739390415766093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30721906310319187221021457 23041429732739390415766093)
                  ·
                    refine ⟨8640536149777271405912285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23041429732739390415766093 8640536149777271405912285)
                    ·
                      refine ⟨3240201056166476777217107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8640536149777271405912285 3240201056166476777217107)
                      ·
                        rfl

theorem cell23_6310269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 2, 2, 3, 3].length) (baseStart_6310269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6310269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6310269 prefixEnd_6310269 := by exact prefixLift 6310269
  have htrace : WordTrace (prefixWord ++ tailWord_6310269) baseStart_6310269 baseEnd_6310269 := by
    simpa [prefixWord, tailWord_6310269, baseEnd_6310269] using wordTrace_append hprefix tailTrace_6310269
  have hstable : (prefixWord ++ tailWord_6310269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6310269).length < 2 ^ (prefixWord ++ tailWord_6310269).sum := by decide
  have hdescent : baseEnd_6310269 < baseStart_6310269 := by decide
  rcases family_descends (prefixWord ++ tailWord_6310269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6310286 : List Nat := [4, 1, 1, 4, 1, 1, 2, 1, 2, 3, 3]
def baseStart_6310286 : Nat := 118140960795 + 6310286 * 2 ^ 59
def prefixEnd_6310286 : Nat := 4983230072969 + 3 ^ 40 * 6310286 * 2
def baseEnd_6310286 : Nat := 3240209785337603210704529

theorem tailTrace_6310286 : CollatzResearch.WordTrace tailWord_6310286 prefixEnd_6310286 3240209785337603210704529 := by
  unfold tailWord_6310286
  simp only [CollatzResearch.WordTrace]
  refine ⟨28769379802114875986618839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 153436692277946005261967141 28769379802114875986618839)
  ·
    refine ⟨43154069703172313979928259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28769379802114875986618839 43154069703172313979928259)
    ·
      refine ⟨64731104554758470969892389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43154069703172313979928259 64731104554758470969892389)
      ·
        refine ⟨12137082104017213306854823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 64731104554758470969892389 12137082104017213306854823)
        ·
          refine ⟨18205623156025819960282235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12137082104017213306854823 18205623156025819960282235)
          ·
            refine ⟨27308434734038729940423353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18205623156025819960282235 27308434734038729940423353)
            ·
              refine ⟨20481326050529047455317515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27308434734038729940423353 20481326050529047455317515)
              ·
                refine ⟨30721989075793571182976273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20481326050529047455317515 30721989075793571182976273)
                ·
                  refine ⟨23041491806845178387232205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30721989075793571182976273 23041491806845178387232205)
                  ·
                    refine ⟨8640559427566941895212077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23041491806845178387232205 8640559427566941895212077)
                    ·
                      refine ⟨3240209785337603210704529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8640559427566941895212077 3240209785337603210704529)
                      ·
                        rfl

theorem cell23_6310286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 2, 1, 2, 3, 3].length) (baseStart_6310286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6310286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6310286 prefixEnd_6310286 := by exact prefixLift 6310286
  have htrace : WordTrace (prefixWord ++ tailWord_6310286) baseStart_6310286 baseEnd_6310286 := by
    simpa [prefixWord, tailWord_6310286, baseEnd_6310286] using wordTrace_append hprefix tailTrace_6310286
  have hstable : (prefixWord ++ tailWord_6310286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6310286).length < 2 ^ (prefixWord ++ tailWord_6310286).sum := by decide
  have hdescent : baseEnd_6310286 < baseStart_6310286 := by decide
  rcases family_descends (prefixWord ++ tailWord_6310286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6310309 : List Nat := [1, 3, 1, 2, 1, 1, 4, 3, 2, 1, 4]
def baseStart_6310309 : Nat := 118140960795 + 6310309 * 2 ^ 59
def prefixEnd_6310309 : Nat := 4983230072969 + 3 ^ 40 * 6310309 * 2
def baseEnd_6310309 : Nat := 3240221595392656620716923

theorem tailTrace_6310309 : CollatzResearch.WordTrace tailWord_6310309 prefixEnd_6310309 3240221595392656620716923 := by
  unfold tailWord_6310309
  simp only [CollatzResearch.WordTrace]
  refine ⟨230155877295835682821037981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153437251530557121880691987 230155877295835682821037981)
  ·
    refine ⟨86308453985938381057889243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 230155877295835682821037981 86308453985938381057889243)
    ·
      refine ⟨129462680978907571586833865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86308453985938381057889243 129462680978907571586833865)
      ·
        refine ⟨97097010734180678690125399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129462680978907571586833865 97097010734180678690125399)
        ·
          refine ⟨145645516101271018035188099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97097010734180678690125399 145645516101271018035188099)
          ·
            refine ⟨218468274151906527052782149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 145645516101271018035188099 218468274151906527052782149)
            ·
              refine ⟨40962801403482473822396653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 218468274151906527052782149 40962801403482473822396653)
              ·
                refine ⟨15361050526305927683398745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40962801403482473822396653 15361050526305927683398745)
                ·
                  refine ⟨11520787894729445762549059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15361050526305927683398745 11520787894729445762549059)
                  ·
                    refine ⟨17281181842094168643823589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11520787894729445762549059 17281181842094168643823589)
                    ·
                      refine ⟨3240221595392656620716923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17281181842094168643823589 3240221595392656620716923)
                      ·
                        rfl

theorem cell23_6310309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 3, 2, 1, 4].length) (baseStart_6310309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6310309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6310309 prefixEnd_6310309 := by exact prefixLift 6310309
  have htrace : WordTrace (prefixWord ++ tailWord_6310309) baseStart_6310309 baseEnd_6310309 := by
    simpa [prefixWord, tailWord_6310309, baseEnd_6310309] using wordTrace_append hprefix tailTrace_6310309
  have hstable : (prefixWord ++ tailWord_6310309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6310309).length < 2 ^ (prefixWord ++ tailWord_6310309).sum := by decide
  have hdescent : baseEnd_6310309 < baseStart_6310309 := by decide
  rcases family_descends (prefixWord ++ tailWord_6310309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6310399 : List Nat := [1, 1, 2, 2, 1, 2, 3, 1, 5, 1, 4]
def baseStart_6310399 : Nat := 118140960795 + 6310399 * 2 ^ 59
def prefixEnd_6310399 : Nat := 4983230072969 + 3 ^ 40 * 6310399 * 2
def baseEnd_6310399 : Nat := 3240267808651561268591509

theorem tailTrace_6310399 : CollatzResearch.WordTrace tailWord_6310399 prefixEnd_6310399 3240267808651561268591509 := by
  unfold tailWord_6310399
  simp only [CollatzResearch.WordTrace]
  refine ⟨230159159865509628191814251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153439439910339752127876167 230159159865509628191814251)
  ·
    refine ⟨345238739798264442287721377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230159159865509628191814251 345238739798264442287721377)
    ·
      refine ⟨258929054848698331715791033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 345238739798264442287721377 258929054848698331715791033)
      ·
        refine ⟨194196791136523748786843275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 258929054848698331715791033 194196791136523748786843275)
        ·
          refine ⟨291295186704785623180264913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 194196791136523748786843275 291295186704785623180264913)
          ·
            refine ⟨218471390028589217385198685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 291295186704785623180264913 218471390028589217385198685)
            ·
              refine ⟨81926771260720956519449507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 218471390028589217385198685 81926771260720956519449507)
              ·
                refine ⟨122890156891081434779174261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81926771260720956519449507 122890156891081434779174261)
                ·
                  refine ⟨11520952208538884510547587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 122890156891081434779174261 11520952208538884510547587)
                  ·
                    refine ⟨17281428312808326765821381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11520952208538884510547587 17281428312808326765821381)
                    ·
                      refine ⟨3240267808651561268591509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17281428312808326765821381 3240267808651561268591509)
                      ·
                        rfl

theorem cell23_6310399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 1, 5, 1, 4].length) (baseStart_6310399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6310399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6310399 prefixEnd_6310399 := by exact prefixLift 6310399
  have htrace : WordTrace (prefixWord ++ tailWord_6310399) baseStart_6310399 baseEnd_6310399 := by
    simpa [prefixWord, tailWord_6310399, baseEnd_6310399] using wordTrace_append hprefix tailTrace_6310399
  have hstable : (prefixWord ++ tailWord_6310399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6310399).length < 2 ^ (prefixWord ++ tailWord_6310399).sum := by decide
  have hdescent : baseEnd_6310399 < baseStart_6310399 := by decide
  rcases family_descends (prefixWord ++ tailWord_6310399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6310420 : List Nat := [2, 4, 3, 1, 1, 2, 1, 1, 1, 5, 2]
def baseStart_6310420 : Nat := 118140960795 + 6310420 * 2 ^ 59
def prefixEnd_6310420 : Nat := 4983230072969 + 3 ^ 40 * 6310420 * 2
def baseEnd_6310420 : Nat := 3240278591745305686428913

theorem tailTrace_6310420 : CollatzResearch.WordTrace tailWord_6310420 prefixEnd_6310420 3240278591745305686428913 := by
  unfold tailWord_6310420
  simp only [CollatzResearch.WordTrace]
  refine ⟨115079962899216774389164357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153439950532289032518885809 115079962899216774389164357)
  ·
    refine ⟨21577493043603145197968317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 115079962899216774389164357 21577493043603145197968317)
    ·
      refine ⟨8091559891351179449238119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21577493043603145197968317 8091559891351179449238119)
      ·
        refine ⟨12137339837026769173857179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8091559891351179449238119 12137339837026769173857179)
        ·
          refine ⟨18206009755540153760785769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12137339837026769173857179 18206009755540153760785769)
          ·
            refine ⟨13654507316655115320589327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18206009755540153760785769 13654507316655115320589327)
            ·
              refine ⟨20481760974982672980883991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13654507316655115320589327 20481760974982672980883991)
              ·
                refine ⟨30722641462474009471325987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20481760974982672980883991 30722641462474009471325987)
                ·
                  refine ⟨46083962193711014206988981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30722641462474009471325987 46083962193711014206988981)
                  ·
                    refine ⟨4320371455660407581905217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 46083962193711014206988981 4320371455660407581905217)
                    ·
                      refine ⟨3240278591745305686428913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4320371455660407581905217 3240278591745305686428913)
                      ·
                        rfl

theorem cell23_6310420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 1, 1, 1, 5, 2].length) (baseStart_6310420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6310420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6310420 prefixEnd_6310420 := by exact prefixLift 6310420
  have htrace : WordTrace (prefixWord ++ tailWord_6310420) baseStart_6310420 baseEnd_6310420 := by
    simpa [prefixWord, tailWord_6310420, baseEnd_6310420] using wordTrace_append hprefix tailTrace_6310420
  have hstable : (prefixWord ++ tailWord_6310420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6310420).length < 2 ^ (prefixWord ++ tailWord_6310420).sum := by decide
  have hdescent : baseEnd_6310420 < baseStart_6310420 := by decide
  rcases family_descends (prefixWord ++ tailWord_6310420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6310433 : List Nat := [1, 2, 3, 2, 2, 1, 1, 2, 5, 2, 2]
def baseStart_6310433 : Nat := 118140960795 + 6310433 * 2 ^ 59
def prefixEnd_6310433 : Nat := 4983230072969 + 3 ^ 40 * 6310433 * 2
def baseEnd_6310433 : Nat := 3240285266993814135566353

theorem tailTrace_6310433 : CollatzResearch.WordTrace tailWord_6310433 prefixEnd_6310433 3240285266993814135566353 := by
  unfold tailWord_6310433
  simp only [CollatzResearch.WordTrace]
  refine ⟨230160399947386451998551953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153440266631590967999034635 230160399947386451998551953)
  ·
    refine ⟨172620299960539838998913965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 230160399947386451998551953 172620299960539838998913965)
    ·
      refine ⟨64732612485202439624592737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 172620299960539838998913965 64732612485202439624592737)
      ·
        refine ⟨48549459363901829718444553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64732612485202439624592737 48549459363901829718444553)
        ·
          refine ⟨36412094522926372288833415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48549459363901829718444553 36412094522926372288833415)
          ·
            refine ⟨54618141784389558433250123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36412094522926372288833415 54618141784389558433250123)
            ·
              refine ⟨81927212676584337649875185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54618141784389558433250123 81927212676584337649875185)
              ·
                refine ⟨61445409507438253237406389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 81927212676584337649875185 61445409507438253237406389)
                ·
                  refine ⟨5760507141322336241006849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 61445409507438253237406389 5760507141322336241006849)
                  ·
                    refine ⟨4320380355991752180755137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5760507141322336241006849 4320380355991752180755137)
                    ·
                      refine ⟨3240285266993814135566353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4320380355991752180755137 3240285266993814135566353)
                      ·
                        rfl

theorem cell23_6310433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 2, 5, 2, 2].length) (baseStart_6310433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6310433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6310433 prefixEnd_6310433 := by exact prefixLift 6310433
  have htrace : WordTrace (prefixWord ++ tailWord_6310433) baseStart_6310433 baseEnd_6310433 := by
    simpa [prefixWord, tailWord_6310433, baseEnd_6310433] using wordTrace_append hprefix tailTrace_6310433
  have hstable : (prefixWord ++ tailWord_6310433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6310433).length < 2 ^ (prefixWord ++ tailWord_6310433).sum := by decide
  have hdescent : baseEnd_6310433 < baseStart_6310433 := by decide
  rcases family_descends (prefixWord ++ tailWord_6310433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6310460 : List Nat := [2, 2, 2, 2, 3, 2, 3, 1, 2, 4]
def baseStart_6310460 : Nat := 118140960795 + 6310460 * 2 ^ 59
def prefixEnd_6310460 : Nat := 4983230072969 + 3 ^ 40 * 6310460 * 2
def baseEnd_6310460 : Nat := 1080099710323828509976243

theorem tailTrace_6310460 : CollatzResearch.WordTrace tailWord_6310460 prefixEnd_6310460 1080099710323828509976243 := by
  unfold tailWord_6310460
  simp only [CollatzResearch.WordTrace]
  refine ⟨115080692359144317804892417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153440923145525757073189889 115080692359144317804892417)
  ·
    refine ⟨86310519269358238353669313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115080692359144317804892417 86310519269358238353669313)
    ·
      refine ⟨64732889452018678765251985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86310519269358238353669313 64732889452018678765251985)
      ·
        refine ⟨48549667089014009073938989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64732889452018678765251985 48549667089014009073938989)
        ·
          refine ⟨18206125158380253402727121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48549667089014009073938989 18206125158380253402727121)
          ·
            refine ⟨13654593868785190052045341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18206125158380253402727121 13654593868785190052045341)
            ·
              refine ⟨5120472700794446269517003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13654593868785190052045341 5120472700794446269517003)
              ·
                refine ⟨7680709051191669404275505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5120472700794446269517003 7680709051191669404275505)
                ·
                  refine ⟨5760531788393752053206629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7680709051191669404275505 5760531788393752053206629)
                  ·
                    refine ⟨1080099710323828509976243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5760531788393752053206629 1080099710323828509976243)
                    ·
                      rfl

theorem cell23_6310460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 3, 1, 2, 4].length) (baseStart_6310460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6310460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6310460 prefixEnd_6310460 := by exact prefixLift 6310460
  have htrace : WordTrace (prefixWord ++ tailWord_6310460) baseStart_6310460 baseEnd_6310460 := by
    simpa [prefixWord, tailWord_6310460, baseEnd_6310460] using wordTrace_append hprefix tailTrace_6310460
  have hstable : (prefixWord ++ tailWord_6310460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6310460).length < 2 ^ (prefixWord ++ tailWord_6310460).sum := by decide
  have hdescent : baseEnd_6310460 < baseStart_6310460 := by decide
  rcases family_descends (prefixWord ++ tailWord_6310460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6310479 : List Nat := [1, 1, 2, 1, 1, 2, 5, 1, 2, 2, 5]
def baseStart_6310479 : Nat := 118140960795 + 6310479 * 2 ^ 59
def prefixEnd_6310479 : Nat := 4983230072969 + 3 ^ 40 * 6310479 * 2
def baseEnd_6310479 : Nat := 3240308887103920955591141

theorem tailTrace_6310479 : CollatzResearch.WordTrace tailWord_6310479 prefixEnd_6310479 3240308887103920955591141 := by
  unfold tailWord_6310479
  simp only [CollatzResearch.WordTrace]
  refine ⟨230162077705219801854726491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153441385136813201236484327 230162077705219801854726491)
  ·
    refine ⟨345243116557829702782089737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230162077705219801854726491 345243116557829702782089737)
    ·
      refine ⟨258932337418372277086567303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 345243116557829702782089737 258932337418372277086567303)
      ·
        refine ⟨388398506127558415629850955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 258932337418372277086567303 388398506127558415629850955)
        ·
          refine ⟨582597759191337623444776433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 388398506127558415629850955 582597759191337623444776433)
          ·
            refine ⟨436948319393503217583582325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 582597759191337623444776433 436948319393503217583582325)
            ·
              refine ⟨40963904943140926648460843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 436948319393503217583582325 40963904943140926648460843)
              ·
                refine ⟨61445857414711389972691265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40963904943140926648460843 61445857414711389972691265)
                ·
                  refine ⟨46084393061033542479518449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 61445857414711389972691265 46084393061033542479518449)
                  ·
                    refine ⟨34563294795775156859638837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 46084393061033542479518449 34563294795775156859638837)
                    ·
                      refine ⟨3240308887103920955591141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34563294795775156859638837 3240308887103920955591141)
                      ·
                        rfl

theorem cell23_6310479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 1, 2, 2, 5].length) (baseStart_6310479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6310479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6310479 prefixEnd_6310479 := by exact prefixLift 6310479
  have htrace : WordTrace (prefixWord ++ tailWord_6310479) baseStart_6310479 baseEnd_6310479 := by
    simpa [prefixWord, tailWord_6310479, baseEnd_6310479] using wordTrace_append hprefix tailTrace_6310479
  have hstable : (prefixWord ++ tailWord_6310479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6310479).length < 2 ^ (prefixWord ++ tailWord_6310479).sum := by decide
  have hdescent : baseEnd_6310479 < baseStart_6310479 := by decide
  rcases family_descends (prefixWord ++ tailWord_6310479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6310484 : List Nat := [2, 4, 1, 1, 1, 5, 1, 3, 1, 2, 2]
def baseStart_6310484 : Nat := 118140960795 + 6310484 * 2 ^ 59
def prefixEnd_6310484 : Nat := 4983230072969 + 3 ^ 40 * 6310484 * 2
def baseEnd_6310484 : Nat := 3240311454507193436028619

theorem tailTrace_6310484 : CollatzResearch.WordTrace tailWord_6310484 prefixEnd_6310484 3240311454507193436028619 := by
  unfold tailWord_6310484
  simp only [CollatzResearch.WordTrace]
  refine ⟨115081130035100843854329253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153441506713467791805772337 115081130035100843854329253)
  ·
    refine ⟨21577711881581408222686735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 115081130035100843854329253 21577711881581408222686735)
    ·
      refine ⟨32366567822372112334030103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21577711881581408222686735 32366567822372112334030103)
      ·
        refine ⟨48549851733558168501045155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32366567822372112334030103 48549851733558168501045155)
        ·
          refine ⟨72824777600337252751567733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48549851733558168501045155 72824777600337252751567733)
          ·
            refine ⟨6827322900031617445459475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 72824777600337252751567733 6827322900031617445459475)
            ·
              refine ⟨10240984350047426168189213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6827322900031617445459475 10240984350047426168189213)
              ·
                refine ⟨3840369131267784813070955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10240984350047426168189213 3840369131267784813070955)
                ·
                  refine ⟨5760553696901677219606433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3840369131267784813070955 5760553696901677219606433)
                  ·
                    refine ⟨4320415272676257914704825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5760553696901677219606433 4320415272676257914704825)
                    ·
                      refine ⟨3240311454507193436028619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4320415272676257914704825 3240311454507193436028619)
                      ·
                        rfl

theorem cell23_6310484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 5, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 5, 1, 3, 1, 2, 2].length) (baseStart_6310484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6310484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6310484 prefixEnd_6310484 := by exact prefixLift 6310484
  have htrace : WordTrace (prefixWord ++ tailWord_6310484) baseStart_6310484 baseEnd_6310484 := by
    simpa [prefixWord, tailWord_6310484, baseEnd_6310484] using wordTrace_append hprefix tailTrace_6310484
  have hstable : (prefixWord ++ tailWord_6310484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6310484).length < 2 ^ (prefixWord ++ tailWord_6310484).sum := by decide
  have hdescent : baseEnd_6310484 < baseStart_6310484 := by decide
  rcases family_descends (prefixWord ++ tailWord_6310484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6310489 : List Nat := [1, 2, 1, 2, 2, 1, 1, 1, 3, 5, 4]
def baseStart_6310489 : Nat := 118140960795 + 6310489 * 2 ^ 59
def prefixEnd_6310489 : Nat := 4983230072969 + 3 ^ 40 * 6310489 * 2
def baseEnd_6310489 : Nat := 3240314021910465916466095

theorem tailTrace_6310489 : CollatzResearch.WordTrace tailWord_6310489 prefixEnd_6310489 3240314021910465916466095 := by
  unfold tailWord_6310489
  simp only [CollatzResearch.WordTrace]
  refine ⟨230162442435183573562590521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153441628290122382375060347 230162442435183573562590521)
  ·
    refine ⟨172621831826387680171942891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 230162442435183573562590521 172621831826387680171942891)
    ·
      refine ⟨258932747739581520257914337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172621831826387680171942891 258932747739581520257914337)
      ·
        refine ⟨194199560804686140193435753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 258932747739581520257914337 194199560804686140193435753)
        ·
          refine ⟨145649670603514605145076815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 194199560804686140193435753 145649670603514605145076815)
          ·
            refine ⟨218474505905271907717615223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 145649670603514605145076815 218474505905271907717615223)
            ·
              refine ⟨327711758857907861576422835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 218474505905271907717615223 327711758857907861576422835)
              ·
                refine ⟨491567638286861792364634253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 327711758857907861576422835 491567638286861792364634253)
                ·
                  refine ⟨184337864357573172136737845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 491567638286861792364634253 184337864357573172136737845)
                  ·
                    refine ⟨17281674783522484887819173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 184337864357573172136737845 17281674783522484887819173)
                    ·
                      refine ⟨3240314021910465916466095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17281674783522484887819173 3240314021910465916466095)
                      ·
                        rfl

theorem cell23_6310489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 1, 3, 5, 4].length) (baseStart_6310489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6310489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6310489 prefixEnd_6310489 := by exact prefixLift 6310489
  have htrace : WordTrace (prefixWord ++ tailWord_6310489) baseStart_6310489 baseEnd_6310489 := by
    simpa [prefixWord, tailWord_6310489, baseEnd_6310489] using wordTrace_append hprefix tailTrace_6310489
  have hstable : (prefixWord ++ tailWord_6310489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6310489).length < 2 ^ (prefixWord ++ tailWord_6310489).sum := by decide
  have hdescent : baseEnd_6310489 < baseStart_6310489 := by decide
  rcases family_descends (prefixWord ++ tailWord_6310489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6310506 : List Nat := [3, 1, 3, 2, 1, 1, 2, 1, 2, 3, 4]
def baseStart_6310506 : Nat := 118140960795 + 6310506 * 2 ^ 59
def prefixEnd_6310506 : Nat := 4983230072969 + 3 ^ 40 * 6310506 * 2
def baseEnd_6310506 : Nat := 3240322751081592349953517

theorem tailTrace_6310506 : CollatzResearch.WordTrace tailWord_6310506 prefixEnd_6310506 3240322751081592349953517 := by
  unfold tailWord_6310506
  simp only [CollatzResearch.WordTrace]
  refine ⟨57540765619030496366489843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153442041650747990310639581 57540765619030496366489843)
  ·
    refine ⟨86311148428545744549734765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57540765619030496366489843 86311148428545744549734765)
    ·
      refine ⟨32366680660704654206150537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86311148428545744549734765 32366680660704654206150537)
      ·
        refine ⟨24275010495528490654612903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32366680660704654206150537 24275010495528490654612903)
        ·
          refine ⟨36412515743292735981919355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24275010495528490654612903 36412515743292735981919355)
          ·
            refine ⟨54618773614939103972879033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36412515743292735981919355 54618773614939103972879033)
            ·
              refine ⟨40964080211204327979659275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54618773614939103972879033 40964080211204327979659275)
              ·
                refine ⟨61446120316806491969488913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40964080211204327979659275 61446120316806491969488913)
                ·
                  refine ⟨46084590237604868977116685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 61446120316806491969488913 46084590237604868977116685)
                  ·
                    refine ⟨17281721339101825866418757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 46084590237604868977116685 17281721339101825866418757)
                    ·
                      refine ⟨3240322751081592349953517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17281721339101825866418757 3240322751081592349953517)
                      ·
                        rfl

theorem cell23_6310506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 1, 2, 3, 4].length) (baseStart_6310506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6310506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6310506 prefixEnd_6310506 := by exact prefixLift 6310506
  have htrace : WordTrace (prefixWord ++ tailWord_6310506) baseStart_6310506 baseEnd_6310506 := by
    simpa [prefixWord, tailWord_6310506, baseEnd_6310506] using wordTrace_append hprefix tailTrace_6310506
  have hstable : (prefixWord ++ tailWord_6310506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6310506).length < 2 ^ (prefixWord ++ tailWord_6310506).sum := by decide
  have hdescent : baseEnd_6310506 < baseStart_6310506 := by decide
  rcases family_descends (prefixWord ++ tailWord_6310506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6310517 : List Nat := [1, 3, 4, 2, 2, 1, 1, 3, 2, 1, 3]
def baseStart_6310517 : Nat := 118140960795 + 6310517 * 2 ^ 59
def prefixEnd_6310517 : Nat := 4983230072969 + 3 ^ 40 * 6310517 * 2
def baseEnd_6310517 : Nat := 3240328399368791806915967

theorem tailTrace_6310517 : CollatzResearch.WordTrace tailWord_6310517 prefixEnd_6310517 3240328399368791806915967 := by
  unfold tailWord_6310517
  simp only [CollatzResearch.WordTrace]
  refine ⟨230163463679082134344609805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153442309119388089563073203 230163463679082134344609805)
  ·
    refine ⟨86311298879655800379228677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 230163463679082134344609805 86311298879655800379228677)
    ·
      refine ⟨16183368539935462571105377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 86311298879655800379228677 16183368539935462571105377)
      ·
        refine ⟨12137526404951596928329033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16183368539935462571105377 12137526404951596928329033)
        ·
          refine ⟨9103144803713697696246775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12137526404951596928329033 9103144803713697696246775)
          ·
            refine ⟨13654717205570546544370163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9103144803713697696246775 13654717205570546544370163)
            ·
              refine ⟨20482075808355819816555245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13654717205570546544370163 20482075808355819816555245)
              ·
                refine ⟨7680778428133432431208217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20482075808355819816555245 7680778428133432431208217)
                ·
                  refine ⟨5760583821100074323406163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7680778428133432431208217 5760583821100074323406163)
                  ·
                    refine ⟨8640875731650111485109245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5760583821100074323406163 8640875731650111485109245)
                    ·
                      refine ⟨3240328399368791806915967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8640875731650111485109245 3240328399368791806915967)
                      ·
                        rfl

theorem cell23_6310517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 1, 3, 2, 1, 3].length) (baseStart_6310517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6310517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6310517 prefixEnd_6310517 := by exact prefixLift 6310517
  have htrace : WordTrace (prefixWord ++ tailWord_6310517) baseStart_6310517 baseEnd_6310517 := by
    simpa [prefixWord, tailWord_6310517, baseEnd_6310517] using wordTrace_append hprefix tailTrace_6310517
  have hstable : (prefixWord ++ tailWord_6310517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6310517).length < 2 ^ (prefixWord ++ tailWord_6310517).sum := by decide
  have hdescent : baseEnd_6310517 < baseStart_6310517 := by decide
  rcases family_descends (prefixWord ++ tailWord_6310517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6310523 : List Nat := [1, 1, 1, 1, 1, 4, 2, 2, 6, 2, 2]
def baseStart_6310523 : Nat := 118140960795 + 6310523 * 2 ^ 59
def prefixEnd_6310523 : Nat := 4983230072969 + 3 ^ 40 * 6310523 * 2
def baseEnd_6310523 : Nat := 3240331480252718783440939

theorem tailTrace_6310523 : CollatzResearch.WordTrace tailWord_6310523 prefixEnd_6310523 3240331480252718783440939 := by
  unfold tailWord_6310523
  simp only [CollatzResearch.WordTrace]
  refine ⟨230163682517060397369328223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153442455011373598246218815 230163682517060397369328223)
  ·
    refine ⟨345245523775590596053992335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230163682517060397369328223 345245523775590596053992335)
    ·
      refine ⟨517868285663385894080988503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 345245523775590596053992335 517868285663385894080988503)
      ·
        refine ⟨776802428495078841121482755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 517868285663385894080988503 776802428495078841121482755)
        ·
          refine ⟨1165203642742618261682224133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 776802428495078841121482755 1165203642742618261682224133)
          ·
            refine ⟨218475683014240924065417025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1165203642742618261682224133 218475683014240924065417025)
            ·
              refine ⟨163856762260680693049062769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 218475683014240924065417025 163856762260680693049062769)
              ·
                refine ⟨122892571695510519786797077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 163856762260680693049062769 122892571695510519786797077)
                ·
                  refine ⟨5760589298227055615006113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 122892571695510519786797077 5760589298227055615006113)
                  ·
                    refine ⟨4320441973670291711254585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5760589298227055615006113 4320441973670291711254585)
                    ·
                      refine ⟨3240331480252718783440939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4320441973670291711254585 3240331480252718783440939)
                      ·
                        rfl

theorem cell23_6310523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 2, 6, 2, 2].length) (baseStart_6310523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6310523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6310523 prefixEnd_6310523 := by exact prefixLift 6310523
  have htrace : WordTrace (prefixWord ++ tailWord_6310523) baseStart_6310523 baseEnd_6310523 := by
    simpa [prefixWord, tailWord_6310523, baseEnd_6310523] using wordTrace_append hprefix tailTrace_6310523
  have hstable : (prefixWord ++ tailWord_6310523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6310523).length < 2 ^ (prefixWord ++ tailWord_6310523).sum := by decide
  have hdescent : baseEnd_6310523 < baseStart_6310523 := by decide
  rcases family_descends (prefixWord ++ tailWord_6310523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6310539 : List Nat := [1, 1, 1, 1, 4, 1, 2, 2, 1, 2, 7]
def baseStart_6310539 : Nat := 118140960795 + 6310539 * 2 ^ 59
def prefixEnd_6310539 : Nat := 4983230072969 + 3 ^ 40 * 6310539 * 2
def baseEnd_6310539 : Nat := 3240339695943190720840865

theorem tailTrace_6310539 : CollatzResearch.WordTrace tailWord_6310539 prefixEnd_6310539 3240339695943190720840865 := by
  unfold tailWord_6310539
  simp only [CollatzResearch.WordTrace]
  refine ⟨230164266085002432101910671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153442844056668288067940447 230164266085002432101910671)
  ·
    refine ⟨345246399127503648152866007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230164266085002432101910671 345246399127503648152866007)
    ·
      refine ⟨517869598691255472229299011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 345246399127503648152866007 517869598691255472229299011)
      ·
        refine ⟨776804398036883208343948517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 517869598691255472229299011 776804398036883208343948517)
        ·
          refine ⟨145650824631915601564490347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 776804398036883208343948517 145650824631915601564490347)
          ·
            refine ⟨218476236947873402346735521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 145650824631915601564490347 218476236947873402346735521)
            ·
              refine ⟨163857177710905051760051641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 218476236947873402346735521 163857177710905051760051641)
              ·
                refine ⟨122892883283178788820038731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 163857177710905051760051641 122892883283178788820038731)
                ·
                  refine ⟨184339324924768183230058097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 122892883283178788820038731 184339324924768183230058097)
                  ·
                    refine ⟨138254493693576137422543573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 184339324924768183230058097 138254493693576137422543573)
                    ·
                      refine ⟨3240339695943190720840865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 138254493693576137422543573 3240339695943190720840865)
                      ·
                        rfl

theorem cell23_6310539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 2, 1, 2, 7].length) (baseStart_6310539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6310539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6310539 prefixEnd_6310539 := by exact prefixLift 6310539
  have htrace : WordTrace (prefixWord ++ tailWord_6310539) baseStart_6310539 baseEnd_6310539 := by
    simpa [prefixWord, tailWord_6310539, baseEnd_6310539] using wordTrace_append hprefix tailTrace_6310539
  have hstable : (prefixWord ++ tailWord_6310539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6310539).length < 2 ^ (prefixWord ++ tailWord_6310539).sum := by decide
  have hdescent : baseEnd_6310539 < baseStart_6310539 := by decide
  rcases family_descends (prefixWord ++ tailWord_6310539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6310573 : List Nat := [1, 5, 2, 1, 1, 2, 1, 1, 1, 5, 3]
def baseStart_6310573 : Nat := 118140960795 + 6310573 * 2 ^ 59
def prefixEnd_6310573 : Nat := 4983230072969 + 3 ^ 40 * 6310573 * 2
def baseEnd_6310573 : Nat := 3240357154285443587815709

theorem tailTrace_6310573 : CollatzResearch.WordTrace tailWord_6310573 prefixEnd_6310573 3240357154285443587815709 := by
  unfold tailWord_6310573
  simp only [CollatzResearch.WordTrace]
  refine ⟨230165506166879255908648373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153443670777919503939098915 230165506166879255908648373)
  ·
    refine ⟨21578016203144930241435785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 230165506166879255908648373 21578016203144930241435785)
    ·
      refine ⟨16183512152358697681076839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21578016203144930241435785 16183512152358697681076839)
      ·
        refine ⟨24275268228538046521615259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16183512152358697681076839 24275268228538046521615259)
        ·
          refine ⟨36412902342807069782422889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24275268228538046521615259 36412902342807069782422889)
          ·
            refine ⟨27309676757105302336817167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36412902342807069782422889 27309676757105302336817167)
            ·
              refine ⟨40964515135657953505225751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27309676757105302336817167 40964515135657953505225751)
              ·
                refine ⟨61446772703486930257838627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40964515135657953505225751 61446772703486930257838627)
                ·
                  refine ⟨92170159055230395386757941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61446772703486930257838627 92170159055230395386757941)
                  ·
                    refine ⟨8640952411427849567508557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 92170159055230395386757941 8640952411427849567508557)
                    ·
                      refine ⟨3240357154285443587815709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8640952411427849567508557 3240357154285443587815709)
                      ·
                        rfl

theorem cell23_6310573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 1, 1, 5, 3].length) (baseStart_6310573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6310573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6310573 prefixEnd_6310573 := by exact prefixLift 6310573
  have htrace : WordTrace (prefixWord ++ tailWord_6310573) baseStart_6310573 baseEnd_6310573 := by
    simpa [prefixWord, tailWord_6310573, baseEnd_6310573] using wordTrace_append hprefix tailTrace_6310573
  have hstable : (prefixWord ++ tailWord_6310573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6310573).length < 2 ^ (prefixWord ++ tailWord_6310573).sum := by decide
  have hdescent : baseEnd_6310573 < baseStart_6310573 := by decide
  rcases family_descends (prefixWord ++ tailWord_6310573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6310574 : List Nat := [4, 1, 4, 1, 1, 1, 2, 3, 2, 2, 2]
def baseStart_6310574 : Nat := 118140960795 + 6310574 * 2 ^ 59
def prefixEnd_6310574 : Nat := 4983230072969 + 3 ^ 40 * 6310574 * 2
def baseEnd_6310574 : Nat := 3240357667766098083903205

theorem tailTrace_6310574 : CollatzResearch.WordTrace tailWord_6310574 prefixEnd_6310574 3240357667766098083903205 := by
  unfold tailWord_6310574
  simp only [CollatzResearch.WordTrace]
  refine ⟨28770692829984454134929347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 153443695093250422052956517 28770692829984454134929347)
  ·
    refine ⟨43156039244976681202394021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28770692829984454134929347 43156039244976681202394021)
    ·
      refine ⟨8091757358433127725448879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43156039244976681202394021 8091757358433127725448879)
      ·
        refine ⟨12137636037649691588173319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8091757358433127725448879 12137636037649691588173319)
        ·
          refine ⟨18206454056474537382259979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12137636037649691588173319 18206454056474537382259979)
          ·
            refine ⟨27309681084711806073389969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18206454056474537382259979 27309681084711806073389969)
            ·
              refine ⟨20482260813533854555042477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27309681084711806073389969 20482260813533854555042477)
              ·
                refine ⟨7680847805075195458140929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20482260813533854555042477 7680847805075195458140929)
                ·
                  refine ⟨5760635853806396593605697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7680847805075195458140929 5760635853806396593605697)
                  ·
                    refine ⟨4320476890354797445204273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5760635853806396593605697 4320476890354797445204273)
                    ·
                      refine ⟨3240357667766098083903205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4320476890354797445204273 3240357667766098083903205)
                      ·
                        rfl

theorem cell23_6310574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 2, 3, 2, 2, 2].length) (baseStart_6310574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6310574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6310574 prefixEnd_6310574 := by exact prefixLift 6310574
  have htrace : WordTrace (prefixWord ++ tailWord_6310574) baseStart_6310574 baseEnd_6310574 := by
    simpa [prefixWord, tailWord_6310574, baseEnd_6310574] using wordTrace_append hprefix tailTrace_6310574
  have hstable : (prefixWord ++ tailWord_6310574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6310574).length < 2 ^ (prefixWord ++ tailWord_6310574).sum := by decide
  have hdescent : baseEnd_6310574 < baseStart_6310574 := by decide
  rcases family_descends (prefixWord ++ tailWord_6310574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6310623 : List Nat := [1, 1, 2, 3, 2, 3, 1, 3, 3, 4]
def baseStart_6310623 : Nat := 118140960795 + 6310623 * 2 ^ 59
def prefixEnd_6310623 : Nat := 4983230072969 + 3 ^ 40 * 6310623 * 2
def baseEnd_6310623 : Nat := 1080127609439389464063493

theorem tailTrace_6310623 : CollatzResearch.WordTrace tailWord_6310623 prefixEnd_6310623 1080127609439389464063493 := by
  unfold tailWord_6310623
  simp only [CollatzResearch.WordTrace]
  refine ⟨230167329816698114447968523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153444886544465409631979015 230167329816698114447968523)
  ·
    refine ⟨345250994725047171671952785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230167329816698114447968523 345250994725047171671952785)
    ·
      refine ⟨258938246043785378753964589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 345250994725047171671952785 258938246043785378753964589)
      ·
        refine ⟨97101842266419517032736721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 258938246043785378753964589 97101842266419517032736721)
        ·
          refine ⟨72826381699814637774552541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97101842266419517032736721 72826381699814637774552541)
          ·
            refine ⟨27309893137430489165457203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72826381699814637774552541 27309893137430489165457203)
            ·
              refine ⟨40964839706145733748185805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27309893137430489165457203 40964839706145733748185805)
              ·
                refine ⟨15361814889804650155569677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40964839706145733748185805 15361814889804650155569677)
                ·
                  refine ⟨5760680583676743808338629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15361814889804650155569677 5760680583676743808338629)
                  ·
                    refine ⟨1080127609439389464063493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5760680583676743808338629 1080127609439389464063493)
                    ·
                      rfl

theorem cell23_6310623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 3, 3, 4].length) (baseStart_6310623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6310623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6310623 prefixEnd_6310623 := by exact prefixLift 6310623
  have htrace : WordTrace (prefixWord ++ tailWord_6310623) baseStart_6310623 baseEnd_6310623 := by
    simpa [prefixWord, tailWord_6310623, baseEnd_6310623] using wordTrace_append hprefix tailTrace_6310623
  have hstable : (prefixWord ++ tailWord_6310623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6310623).length < 2 ^ (prefixWord ++ tailWord_6310623).sum := by decide
  have hdescent : baseEnd_6310623 < baseStart_6310623 := by decide
  rcases family_descends (prefixWord ++ tailWord_6310623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6310674 : List Nat := [3, 2, 4, 1, 2, 2, 1, 1, 3, 4]
def baseStart_6310674 : Nat := 118140960795 + 6310674 * 2 ^ 59
def prefixEnd_6310674 : Nat := 4983230072969 + 3 ^ 40 * 6310674 * 2
def baseEnd_6310674 : Nat := 1080136338610515897550915

theorem tailTrace_6310674 : CollatzResearch.WordTrace tailWord_6310674 prefixEnd_6310674 1080136338610515897550915 := by
  unfold tailWord_6310674
  simp only [CollatzResearch.WordTrace]
  refine ⟨57542297484878337539518769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153446126626342233438716717 57542297484878337539518769)
  ·
    refine ⟨43156723113658753154639077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57542297484878337539518769 43156723113658753154639077)
    ·
      refine ⟨8091885583811016216494827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43156723113658753154639077 8091885583811016216494827)
      ·
        refine ⟨12137828375716524324742241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8091885583811016216494827 12137828375716524324742241)
        ·
          refine ⟨9103371281787393243556681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12137828375716524324742241 9103371281787393243556681)
          ·
            refine ⟨6827528461340544932667511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9103371281787393243556681 6827528461340544932667511)
            ·
              refine ⟨10241292692010817399001267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6827528461340544932667511 10241292692010817399001267)
              ·
                refine ⟨15361939038016226098501901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10241292692010817399001267 15361939038016226098501901)
                ·
                  refine ⟨5760727139256084786938213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15361939038016226098501901 5760727139256084786938213)
                  ·
                    refine ⟨1080136338610515897550915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5760727139256084786938213 1080136338610515897550915)
                    ·
                      rfl

theorem cell23_6310674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 2, 1, 1, 3, 4].length) (baseStart_6310674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6310674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6310674 prefixEnd_6310674 := by exact prefixLift 6310674
  have htrace : WordTrace (prefixWord ++ tailWord_6310674) baseStart_6310674 baseEnd_6310674 := by
    simpa [prefixWord, tailWord_6310674, baseEnd_6310674] using wordTrace_append hprefix tailTrace_6310674
  have hstable : (prefixWord ++ tailWord_6310674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6310674).length < 2 ^ (prefixWord ++ tailWord_6310674).sum := by decide
  have hdescent : baseEnd_6310674 < baseStart_6310674 := by decide
  rcases family_descends (prefixWord ++ tailWord_6310674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6310707 : List Nat := [1, 1, 1, 2, 6, 2, 2, 1, 2, 3, 2]
def baseStart_6310707 : Nat := 118140960795 + 6310707 * 2 ^ 59
def prefixEnd_6310707 : Nat := 4983230072969 + 3 ^ 40 * 6310707 * 2
def baseEnd_6310707 : Nat := 3240425960693146063540093

theorem tailTrace_6310707 : CollatzResearch.WordTrace tailWord_6310707 prefixEnd_6310707 3240425960693146063540093 := by
  unfold tailWord_6310707
  simp only [CollatzResearch.WordTrace]
  refine ⟨230170393548393796794026375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153446929032262531196017583 230170393548393796794026375)
  ·
    refine ⟨345255590322590695191039563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230170393548393796794026375 345255590322590695191039563)
    ·
      refine ⟨517883385483886042786559345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 345255590322590695191039563 517883385483886042786559345)
      ·
        refine ⟨388412539112914532089919509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 517883385483886042786559345 388412539112914532089919509)
        ·
          refine ⟨18206837770917868691714977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 388412539112914532089919509 18206837770917868691714977)
          ·
            refine ⟨13655128328188401518786233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18206837770917868691714977 13655128328188401518786233)
            ·
              refine ⟨10241346246141301139089675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13655128328188401518786233 10241346246141301139089675)
              ·
                refine ⟨15362019369211951708634513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10241346246141301139089675 15362019369211951708634513)
                ·
                  refine ⟨11521514526908963781475885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15362019369211951708634513 11521514526908963781475885)
                  ·
                    refine ⟨4320567947590861418053457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11521514526908963781475885 4320567947590861418053457)
                    ·
                      refine ⟨3240425960693146063540093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4320567947590861418053457 3240425960693146063540093)
                      ·
                        rfl

theorem cell23_6310707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 2, 1, 2, 3, 2].length) (baseStart_6310707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6310707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6310707 prefixEnd_6310707 := by exact prefixLift 6310707
  have htrace : WordTrace (prefixWord ++ tailWord_6310707) baseStart_6310707 baseEnd_6310707 := by
    simpa [prefixWord, tailWord_6310707, baseEnd_6310707] using wordTrace_append hprefix tailTrace_6310707
  have hstable : (prefixWord ++ tailWord_6310707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6310707).length < 2 ^ (prefixWord ++ tailWord_6310707).sum := by decide
  have hdescent : baseEnd_6310707 < baseStart_6310707 := by decide
  rcases family_descends (prefixWord ++ tailWord_6310707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6310743 : List Nat := [1, 1, 3, 2, 4, 1, 3, 8]
def baseStart_6310743 : Nat := 118140960795 + 6310743 * 2 ^ 59
def prefixEnd_6310743 : Nat := 4983230072969 + 3 ^ 40 * 6310743 * 2
def baseEnd_6310743 : Nat := 120016460962841034173701

theorem tailTrace_6310743 : CollatzResearch.WordTrace tailWord_6310743 prefixEnd_6310743 120016460962841034173701 := by
  unfold tailWord_6310743
  simp only [CollatzResearch.WordTrace]
  refine ⟨230171706576263374942336883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153447804384175583294891255 230171706576263374942336883)
  ·
    refine ⟨345257559864395062413505325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230171706576263374942336883 345257559864395062413505325)
    ·
      refine ⟨129471584949148148405064497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 345257559864395062413505325 129471584949148148405064497)
      ·
        refine ⟨97103688711861111303798373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129471584949148148405064497 97103688711861111303798373)
        ·
          refine ⟨18206941633473958369462195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 97103688711861111303798373 18206941633473958369462195)
          ·
            refine ⟨27310412450210937554193293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18206941633473958369462195 27310412450210937554193293)
            ·
              refine ⟨10241404668829101582822485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27310412450210937554193293 10241404668829101582822485)
              ·
                refine ⟨120016460962841034173701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10241404668829101582822485 120016460962841034173701)
                ·
                  rfl

theorem cell23_6310743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 3, 8].length) (baseStart_6310743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6310743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6310743 prefixEnd_6310743 := by exact prefixLift 6310743
  have htrace : WordTrace (prefixWord ++ tailWord_6310743) baseStart_6310743 baseEnd_6310743 := by
    simpa [prefixWord, tailWord_6310743, baseEnd_6310743] using wordTrace_append hprefix tailTrace_6310743
  have hstable : (prefixWord ++ tailWord_6310743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6310743).length < 2 ^ (prefixWord ++ tailWord_6310743).sum := by decide
  have hdescent : baseEnd_6310743 < baseStart_6310743 := by decide
  rcases family_descends (prefixWord ++ tailWord_6310743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6310760 : List Nat := [2, 1, 4, 2, 1, 3, 3, 7]
def baseStart_6310760 : Nat := 118140960795 + 6310760 * 2 ^ 59
def prefixEnd_6310760 : Nat := 4983230072969 + 3 ^ 40 * 6310760 * 2
def baseEnd_6310760 : Nat := 120016784265475346525087

theorem tailTrace_6310760 : CollatzResearch.WordTrace tailWord_6310760 prefixEnd_6310760 120016784265475346525087 := by
  unfold tailWord_6310760
  simp only [CollatzResearch.WordTrace]
  refine ⟨115086163308600893422852867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153448217744801191230470489 115086163308600893422852867)
  ·
    refine ⟨172629244962901340134279301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115086163308600893422852867 172629244962901340134279301)
    ·
      refine ⟨32367983430544001275177369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 172629244962901340134279301 32367983430544001275177369)
      ·
        refine ⟨24275987572908000956383027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32367983430544001275177369 24275987572908000956383027)
        ·
          refine ⟨36413981359362001434574541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24275987572908000956383027 36413981359362001434574541)
          ·
            refine ⟨13655243009760750537965453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36413981359362001434574541 13655243009760750537965453)
            ·
              refine ⟨5120716128660281451737045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13655243009760750537965453 5120716128660281451737045)
              ·
                refine ⟨120016784265475346525087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5120716128660281451737045 120016784265475346525087)
                ·
                  rfl

theorem cell23_6310760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 3, 7].length) (baseStart_6310760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6310760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6310760 prefixEnd_6310760 := by exact prefixLift 6310760
  have htrace : WordTrace (prefixWord ++ tailWord_6310760) baseStart_6310760 baseEnd_6310760 := by
    simpa [prefixWord, tailWord_6310760, baseEnd_6310760] using wordTrace_append hprefix tailTrace_6310760
  have hstable : (prefixWord ++ tailWord_6310760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6310760).length < 2 ^ (prefixWord ++ tailWord_6310760).sum := by decide
  have hdescent : baseEnd_6310760 < baseStart_6310760 := by decide
  rcases family_descends (prefixWord ++ tailWord_6310760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6310770 : List Nat := [3, 2, 1, 2, 1, 1, 4, 2, 1, 3, 3]
def baseStart_6310770 : Nat := 118140960795 + 6310770 * 2 ^ 59
def prefixEnd_6310770 : Nat := 4983230072969 + 3 ^ 40 * 6310770 * 2
def baseEnd_6310770 : Nat := 3240458309974379317052303

theorem tailTrace_6310770 : CollatzResearch.WordTrace tailWord_6310770 prefixEnd_6310770 3240458309974379317052303 := by
  unfold tailWord_6310770
  simp only [CollatzResearch.WordTrace]
  refine ⟨57543172836791389638392441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153448460898110372369046509 57543172836791389638392441)
  ·
    refine ⟨43157379627593542228794331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57543172836791389638392441 43157379627593542228794331)
    ·
      refine ⟨64736069441390313343191497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43157379627593542228794331 64736069441390313343191497)
      ·
        refine ⟨48552052081042735007393623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64736069441390313343191497 48552052081042735007393623)
        ·
          refine ⟨72828078121564102511090435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48552052081042735007393623 72828078121564102511090435)
          ·
            refine ⟨109242117182346153766635653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72828078121564102511090435 109242117182346153766635653)
            ·
              refine ⟨20482896971689903831244185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 109242117182346153766635653 20482896971689903831244185)
              ·
                refine ⟨15362172728767427873433139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20482896971689903831244185 15362172728767427873433139)
                ·
                  refine ⟨23043259093151141810149709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15362172728767427873433139 23043259093151141810149709)
                  ·
                    refine ⟨8641222159931678178806141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23043259093151141810149709 8641222159931678178806141)
                    ·
                      refine ⟨3240458309974379317052303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8641222159931678178806141 3240458309974379317052303)
                      ·
                        rfl

theorem cell23_6310770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 4, 2, 1, 3, 3].length) (baseStart_6310770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6310770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6310770 prefixEnd_6310770 := by exact prefixLift 6310770
  have htrace : WordTrace (prefixWord ++ tailWord_6310770) baseStart_6310770 baseEnd_6310770 := by
    simpa [prefixWord, tailWord_6310770, baseEnd_6310770] using wordTrace_append hprefix tailTrace_6310770
  have hstable : (prefixWord ++ tailWord_6310770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6310770).length < 2 ^ (prefixWord ++ tailWord_6310770).sum := by decide
  have hdescent : baseEnd_6310770 < baseStart_6310770 := by decide
  rcases family_descends (prefixWord ++ tailWord_6310770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6310774 : List Nat := [5, 1, 1, 3, 1, 2, 1, 3, 1, 2, 3]
def baseStart_6310774 : Nat := 118140960795 + 6310774 * 2 ^ 59
def prefixEnd_6310774 : Nat := 4983230072969 + 3 ^ 40 * 6310774 * 2
def baseEnd_6310774 : Nat := 3240460363896997301402285

theorem tailTrace_6310774 : CollatzResearch.WordTrace tailWord_6310774 prefixEnd_6310774 3240460363896997301402285 := by
  unfold tailWord_6310774
  simp only [CollatzResearch.WordTrace]
  refine ⟨14385802327446941702294711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 153448558159434044824476917 14385802327446941702294711)
  ·
    refine ⟨21578703491170412553442067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14385802327446941702294711 21578703491170412553442067)
    ·
      refine ⟨32368055236755618830163101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21578703491170412553442067 32368055236755618830163101)
      ·
        refine ⟨12138020713783357061311163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32368055236755618830163101 12138020713783357061311163)
        ·
          refine ⟨18207031070675035591966745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12138020713783357061311163 18207031070675035591966745)
          ·
            refine ⟨13655273303006276693975059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18207031070675035591966745 13655273303006276693975059)
            ·
              refine ⟨20482909954509415040962589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13655273303006276693975059 20482909954509415040962589)
              ·
                refine ⟨7681091232941030640360971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20482909954509415040962589 7681091232941030640360971)
                ·
                  refine ⟨11521636849411545960541457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7681091232941030640360971 11521636849411545960541457)
                  ·
                    refine ⟨8641227637058659470406093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11521636849411545960541457 8641227637058659470406093)
                    ·
                      refine ⟨3240460363896997301402285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8641227637058659470406093 3240460363896997301402285)
                      ·
                        rfl

theorem cell23_6310774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 1, 3, 1, 2, 3].length) (baseStart_6310774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6310774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6310774 prefixEnd_6310774 := by exact prefixLift 6310774
  have htrace : WordTrace (prefixWord ++ tailWord_6310774) baseStart_6310774 baseEnd_6310774 := by
    simpa [prefixWord, tailWord_6310774, baseEnd_6310774] using wordTrace_append hprefix tailTrace_6310774
  have hstable : (prefixWord ++ tailWord_6310774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6310774).length < 2 ^ (prefixWord ++ tailWord_6310774).sum := by decide
  have hdescent : baseEnd_6310774 < baseStart_6310774 := by decide
  rcases family_descends (prefixWord ++ tailWord_6310774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6310860 : List Nat := [2, 2, 1, 4, 1, 1, 2, 1, 1, 5, 3]
def baseStart_6310860 : Nat := 118140960795 + 6310860 * 2 ^ 59
def prefixEnd_6310860 : Nat := 4983230072969 + 3 ^ 40 * 6310860 * 2
def baseEnd_6310860 : Nat := 3240504523233283964926889

theorem tailTrace_6310860 : CollatzResearch.WordTrace tailWord_6310860 prefixEnd_6310860 3240504523233283964926889 := by
  unfold tailWord_6310860
  simp only [CollatzResearch.WordTrace]
  refine ⟨115087986958419751962173017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153450649277893002616230689 115087986958419751962173017)
  ·
    refine ⟨86315990218814813971629763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115087986958419751962173017 86315990218814813971629763)
    ·
      refine ⟨129473985328222220957444645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86315990218814813971629763 129473985328222220957444645)
      ·
        refine ⟨24276372249041666429520871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 129473985328222220957444645 24276372249041666429520871)
        ·
          refine ⟨36414558373562499644281307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24276372249041666429520871 36414558373562499644281307)
          ·
            refine ⟨54621837560343749466421961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36414558373562499644281307 54621837560343749466421961)
            ·
              refine ⟨40966378170257812099816471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54621837560343749466421961 40966378170257812099816471)
              ·
                refine ⟨61449567255386718149724707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40966378170257812099816471 61449567255386718149724707)
                ·
                  refine ⟨92174350883080077224587061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61449567255386718149724707 92174350883080077224587061)
                  ·
                    refine ⟨8641345395288757239805037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 92174350883080077224587061 8641345395288757239805037)
                    ·
                      refine ⟨3240504523233283964926889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8641345395288757239805037 3240504523233283964926889)
                      ·
                        rfl

theorem cell23_6310860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 1, 1, 5, 3].length) (baseStart_6310860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6310860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6310860 prefixEnd_6310860 := by exact prefixLift 6310860
  have htrace : WordTrace (prefixWord ++ tailWord_6310860) baseStart_6310860 baseEnd_6310860 := by
    simpa [prefixWord, tailWord_6310860, baseEnd_6310860] using wordTrace_append hprefix tailTrace_6310860
  have hstable : (prefixWord ++ tailWord_6310860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6310860).length < 2 ^ (prefixWord ++ tailWord_6310860).sum := by decide
  have hdescent : baseEnd_6310860 < baseStart_6310860 := by decide
  rcases family_descends (prefixWord ++ tailWord_6310860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6310890 : List Nat := [3, 1, 3, 1, 2, 2, 1, 2, 1, 2, 5]
def baseStart_6310890 : Nat := 118140960795 + 6310890 * 2 ^ 59
def prefixEnd_6310890 : Nat := 4983230072969 + 3 ^ 40 * 6310890 * 2
def baseEnd_6310890 : Nat := 3240519927652918847551751

theorem tailTrace_6310890 : CollatzResearch.WordTrace tailWord_6310890 prefixEnd_6310890 3240519927652918847551751 := by
  unfold tailWord_6310890
  simp only [CollatzResearch.WordTrace]
  refine ⟨57544267026682704761984531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153451378737820546031958749 57544267026682704761984531)
  ·
    refine ⟨86316400540024057142976797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57544267026682704761984531 86316400540024057142976797)
    ·
      refine ⟨32368650202509021428616299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86316400540024057142976797 32368650202509021428616299)
      ·
        refine ⟨48552975303763532142924449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32368650202509021428616299 48552975303763532142924449)
        ·
          refine ⟨36414731477822649107193337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48552975303763532142924449 36414731477822649107193337)
          ·
            refine ⟨27311048608366986830395003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36414731477822649107193337 27311048608366986830395003)
            ·
              refine ⟨40966572912550480245592505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27311048608366986830395003 40966572912550480245592505)
              ·
                refine ⟨30724929684412860184194379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40966572912550480245592505 30724929684412860184194379)
                ·
                  refine ⟨46087394526619290276291569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30724929684412860184194379 46087394526619290276291569)
                  ·
                    refine ⟨34565545894964467707218677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 46087394526619290276291569 34565545894964467707218677)
                    ·
                      refine ⟨3240519927652918847551751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34565545894964467707218677 3240519927652918847551751)
                      ·
                        rfl

theorem cell23_6310890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 2, 1, 2, 5].length) (baseStart_6310890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6310890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6310890 prefixEnd_6310890 := by exact prefixLift 6310890
  have htrace : WordTrace (prefixWord ++ tailWord_6310890) baseStart_6310890 baseEnd_6310890 := by
    simpa [prefixWord, tailWord_6310890, baseEnd_6310890] using wordTrace_append hprefix tailTrace_6310890
  have hstable : (prefixWord ++ tailWord_6310890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6310890).length < 2 ^ (prefixWord ++ tailWord_6310890).sum := by decide
  have hdescent : baseEnd_6310890 < baseStart_6310890 := by decide
  rcases family_descends (prefixWord ++ tailWord_6310890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6310901 : List Nat := [1, 3, 5, 2, 1, 1, 1, 4, 5]
def baseStart_6310901 : Nat := 118140960795 + 6310901 * 2 ^ 59
def prefixEnd_6310901 : Nat := 4983230072969 + 3 ^ 40 * 6310901 * 2
def baseEnd_6310901 : Nat := 360058397326679811612689

theorem tailTrace_6310901 : CollatzResearch.WordTrace tailWord_6310901 prefixEnd_6310901 360058397326679811612689 := by
  unfold tailWord_6310901
  simp only [CollatzResearch.WordTrace]
  refine ⟨230177469309690967926588557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153451646206460645284392371 230177469309690967926588557)
  ·
    refine ⟨86316550991134112972470709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 230177469309690967926588557 86316550991134112972470709)
    ·
      refine ⟨8092176655418823091169129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 86316550991134112972470709 8092176655418823091169129)
      ·
        refine ⟨6069132491564117318376847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8092176655418823091169129 6069132491564117318376847)
        ·
          refine ⟨9103698737346175977565271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6069132491564117318376847 9103698737346175977565271)
          ·
            refine ⟨13655548106019263966347907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9103698737346175977565271 13655548106019263966347907)
            ·
              refine ⟨20483322159028895949521861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13655548106019263966347907 20483322159028895949521861)
              ·
                refine ⟨3840622904817917990535349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20483322159028895949521861 3840622904817917990535349)
                ·
                  refine ⟨360058397326679811612689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3840622904817917990535349 360058397326679811612689)
                  ·
                    rfl

theorem cell23_6310901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 1, 4, 5].length) (baseStart_6310901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6310901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6310901 prefixEnd_6310901 := by exact prefixLift 6310901
  have htrace : WordTrace (prefixWord ++ tailWord_6310901) baseStart_6310901 baseEnd_6310901 := by
    simpa [prefixWord, tailWord_6310901, baseEnd_6310901] using wordTrace_append hprefix tailTrace_6310901
  have hstable : (prefixWord ++ tailWord_6310901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6310901).length < 2 ^ (prefixWord ++ tailWord_6310901).sum := by decide
  have hdescent : baseEnd_6310901 < baseStart_6310901 := by decide
  rcases family_descends (prefixWord ++ tailWord_6310901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6310917 : List Nat := [1, 3, 1, 1, 2, 3, 3, 1, 2, 4, 2]
def baseStart_6310917 : Nat := 118140960795 + 6310917 * 2 ^ 59
def prefixEnd_6310917 : Nat := 4983230072969 + 3 ^ 40 * 6310917 * 2
def baseEnd_6310917 : Nat := 3240533791630590241914127

theorem tailTrace_6310917 : CollatzResearch.WordTrace tailWord_6310917 prefixEnd_6310917 3240533791630590241914127 := by
  unfold tailWord_6310917
  simp only [CollatzResearch.WordTrace]
  refine ⟨230178052877633002659171005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153452035251755335106114003 230178052877633002659171005)
  ·
    refine ⟨86316769829112375997189127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 230178052877633002659171005 86316769829112375997189127)
    ·
      refine ⟨129475154743668563995783691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86316769829112375997189127 129475154743668563995783691)
      ·
        refine ⟨194212732115502845993675537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129475154743668563995783691 194212732115502845993675537)
        ·
          refine ⟨145659549086627134495256653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 194212732115502845993675537 145659549086627134495256653)
          ·
            refine ⟨54622330907485175435721245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 145659549086627134495256653 54622330907485175435721245)
            ·
              refine ⟨20483374090306940788395467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54622330907485175435721245 20483374090306940788395467)
              ·
                refine ⟨30725061135460411182593201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20483374090306940788395467 30725061135460411182593201)
                ·
                  refine ⟨23043795851595308386944901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30725061135460411182593201 23043795851595308386944901)
                  ·
                    refine ⟨4320711722174120322552169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23043795851595308386944901 4320711722174120322552169)
                    ·
                      refine ⟨3240533791630590241914127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4320711722174120322552169 3240533791630590241914127)
                      ·
                        rfl

theorem cell23_6310917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 3, 1, 2, 4, 2].length) (baseStart_6310917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6310917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6310917 prefixEnd_6310917 := by exact prefixLift 6310917
  have htrace : WordTrace (prefixWord ++ tailWord_6310917) baseStart_6310917 baseEnd_6310917 := by
    simpa [prefixWord, tailWord_6310917, baseEnd_6310917] using wordTrace_append hprefix tailTrace_6310917
  have hstable : (prefixWord ++ tailWord_6310917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6310917).length < 2 ^ (prefixWord ++ tailWord_6310917).sum := by decide
  have hdescent : baseEnd_6310917 < baseStart_6310917 := by decide
  rcases family_descends (prefixWord ++ tailWord_6310917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6310937 : List Nat := [1, 2, 1, 2, 1, 1, 7, 1, 2, 2, 3]
def baseStart_6310937 : Nat := 118140960795 + 6310937 * 2 ^ 59
def prefixEnd_6310937 : Nat := 4983230072969 + 3 ^ 40 * 6310937 * 2
def baseEnd_6310937 : Nat := 3240544061243680163664035

theorem tailTrace_6310937 : CollatzResearch.WordTrace tailWord_6310937 prefixEnd_6310937 3240544061243680163664035 := by
  unfold tailWord_6310937
  simp only [CollatzResearch.WordTrace]
  refine ⟨230178782337560546074899065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153452521558373697383266043 230178782337560546074899065)
  ·
    refine ⟨172634086753170409556174299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 230178782337560546074899065 172634086753170409556174299)
    ·
      refine ⟨258951130129755614334261449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172634086753170409556174299 258951130129755614334261449)
      ·
        refine ⟨194213347597316710750696087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 258951130129755614334261449 194213347597316710750696087)
        ·
          refine ⟨291320021395975066126044131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 194213347597316710750696087 291320021395975066126044131)
          ·
            refine ⟨436980032093962599189066197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 291320021395975066126044131 436980032093962599189066197)
            ·
              refine ⟨10241719502202248418493739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 436980032093962599189066197 10241719502202248418493739)
              ·
                refine ⟨15362579253303372627740609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10241719502202248418493739 15362579253303372627740609)
                ·
                  refine ⟨11521934439977529470805457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15362579253303372627740609 11521934439977529470805457)
                  ·
                    refine ⟨8641450829983147103104093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11521934439977529470805457 8641450829983147103104093)
                    ·
                      refine ⟨3240544061243680163664035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8641450829983147103104093 3240544061243680163664035)
                      ·
                        rfl

theorem cell23_6310937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 7, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 7, 1, 2, 2, 3].length) (baseStart_6310937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6310937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6310937 prefixEnd_6310937 := by exact prefixLift 6310937
  have htrace : WordTrace (prefixWord ++ tailWord_6310937) baseStart_6310937 baseEnd_6310937 := by
    simpa [prefixWord, tailWord_6310937, baseEnd_6310937] using wordTrace_append hprefix tailTrace_6310937
  have hstable : (prefixWord ++ tailWord_6310937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6310937).length < 2 ^ (prefixWord ++ tailWord_6310937).sum := by decide
  have hdescent : baseEnd_6310937 < baseStart_6310937 := by decide
  rcases family_descends (prefixWord ++ tailWord_6310937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6310970 : List Nat := [3, 1, 1, 1, 3, 1, 2, 1, 5, 5]
def baseStart_6310970 : Nat := 118140960795 + 6310970 * 2 ^ 59
def prefixEnd_6310970 : Nat := 4983230072969 + 3 ^ 40 * 6310970 * 2
def baseEnd_6310970 : Nat := 1080187002035092844850461

theorem tailTrace_6310970 : CollatzResearch.WordTrace tailWord_6310970 prefixEnd_6310970 1080187002035092844850461 := by
  unfold tailWord_6310970
  simp only [CollatzResearch.WordTrace]
  refine ⟨57544996486610248177712591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153453323964293995140566909 57544996486610248177712591)
  ·
    refine ⟨86317494729915372266568887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57544996486610248177712591 86317494729915372266568887)
    ·
      refine ⟨129476242094873058399853331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86317494729915372266568887 129476242094873058399853331)
      ·
        refine ⟨194214363142309587599779997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129476242094873058399853331 194214363142309587599779997)
        ·
          refine ⟨72830386178366095349917499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 194214363142309587599779997 72830386178366095349917499)
          ·
            refine ⟨109245579267549143024876249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72830386178366095349917499 109245579267549143024876249)
            ·
              refine ⟨81934184450661857268657187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 109245579267549143024876249 81934184450661857268657187)
              ·
                refine ⟨122901276675992785902985781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81934184450661857268657187 122901276675992785902985781)
                ·
                  refine ⟨11521994688374323678404917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 122901276675992785902985781 11521994688374323678404917)
                  ·
                    refine ⟨1080187002035092844850461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11521994688374323678404917 1080187002035092844850461)
                    ·
                      rfl

theorem cell23_6310970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 1, 5, 5].length) (baseStart_6310970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6310970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6310970 prefixEnd_6310970 := by exact prefixLift 6310970
  have htrace : WordTrace (prefixWord ++ tailWord_6310970) baseStart_6310970 baseEnd_6310970 := by
    simpa [prefixWord, tailWord_6310970, baseEnd_6310970] using wordTrace_append hprefix tailTrace_6310970
  have hstable : (prefixWord ++ tailWord_6310970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6310970).length < 2 ^ (prefixWord ++ tailWord_6310970).sum := by decide
  have hdescent : baseEnd_6310970 < baseStart_6310970 := by decide
  rcases family_descends (prefixWord ++ tailWord_6310970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6310994 : List Nat := [3, 2, 2, 1, 3, 1, 2, 1, 1, 5, 2]
def baseStart_6310994 : Nat := 118140960795 + 6310994 * 2 ^ 59
def prefixEnd_6310994 : Nat := 4983230072969 + 3 ^ 40 * 6310994 * 2
def baseEnd_6310994 : Nat := 3240573329640986440651273

theorem tailTrace_6310994 : CollatzResearch.WordTrace tailWord_6310994 prefixEnd_6310994 3240573329640986440651273 := by
  unfold tailWord_6310994
  simp only [CollatzResearch.WordTrace]
  refine ⟨57545215324588511202431009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153453907532236029873149357 57545215324588511202431009)
  ·
    refine ⟨43158911493441383401823257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57545215324588511202431009 43158911493441383401823257)
    ·
      refine ⟨32369183620081037551367443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43158911493441383401823257 32369183620081037551367443)
      ·
        refine ⟨48553775430121556327051165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32369183620081037551367443 48553775430121556327051165)
        ·
          refine ⟨18207665786295583622644187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48553775430121556327051165 18207665786295583622644187)
          ·
            refine ⟨27311498679443375433966281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18207665786295583622644187 27311498679443375433966281)
            ·
              refine ⟨20483624009582531575474711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27311498679443375433966281 20483624009582531575474711)
              ·
                refine ⟨30725436014373797363212067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20483624009582531575474711 30725436014373797363212067)
                ·
                  refine ⟨46088154021560696044818101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30725436014373797363212067 46088154021560696044818101)
                  ·
                    refine ⟨4320764439521315254201697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 46088154021560696044818101 4320764439521315254201697)
                    ·
                      refine ⟨3240573329640986440651273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4320764439521315254201697 3240573329640986440651273)
                      ·
                        rfl

theorem cell23_6310994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 2, 1, 1, 5, 2].length) (baseStart_6310994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6310994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6310994 prefixEnd_6310994 := by exact prefixLift 6310994
  have htrace : WordTrace (prefixWord ++ tailWord_6310994) baseStart_6310994 baseEnd_6310994 := by
    simpa [prefixWord, tailWord_6310994, baseEnd_6310994] using wordTrace_append hprefix tailTrace_6310994
  have hstable : (prefixWord ++ tailWord_6310994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6310994).length < 2 ^ (prefixWord ++ tailWord_6310994).sum := by decide
  have hdescent : baseEnd_6310994 < baseStart_6310994 := by decide
  rcases family_descends (prefixWord ++ tailWord_6310994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6311000 : List Nat := [2, 1, 2, 2, 1, 3, 2, 1, 3, 6]
def baseStart_6311000 : Nat := 118140960795 + 6311000 * 2 ^ 59
def prefixEnd_6311000 : Nat := 4983230072969 + 3 ^ 40 * 6311000 * 2
def baseEnd_6311000 : Nat := 1080192136841637805725415

theorem tailTrace_6311000 : CollatzResearch.WordTrace tailWord_6311000 prefixEnd_6311000 1080192136841637805725415 := by
  unfold tailWord_6311000
  simp only [CollatzResearch.WordTrace]
  refine ⟨115090540068166153917221227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153454053424221538556294969 115090540068166153917221227)
  ·
    refine ⟨172635810102249230875831841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115090540068166153917221227 172635810102249230875831841)
    ·
      refine ⟨129476857576686923156873881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 172635810102249230875831841 129476857576686923156873881)
      ·
        refine ⟨97107643182515192367655411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129476857576686923156873881 97107643182515192367655411)
        ·
          refine ⟨145661464773772788551483117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97107643182515192367655411 145661464773772788551483117)
          ·
            refine ⟨54623049290164795706806169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 145661464773772788551483117 54623049290164795706806169)
            ·
              refine ⟨40967286967623596780104627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54623049290164795706806169 40967286967623596780104627)
              ·
                refine ⟨61450930451435395170156941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40967286967623596780104627 61450930451435395170156941)
                ·
                  refine ⟨23044098919288273188808853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 61450930451435395170156941 23044098919288273188808853)
                  ·
                    refine ⟨1080192136841637805725415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23044098919288273188808853 1080192136841637805725415)
                    ·
                      rfl

theorem cell23_6311000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 1, 3, 6].length) (baseStart_6311000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6311000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6311000 prefixEnd_6311000 := by exact prefixLift 6311000
  have htrace : WordTrace (prefixWord ++ tailWord_6311000) baseStart_6311000 baseEnd_6311000 := by
    simpa [prefixWord, tailWord_6311000, baseEnd_6311000] using wordTrace_append hprefix tailTrace_6311000
  have hstable : (prefixWord ++ tailWord_6311000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6311000).length < 2 ^ (prefixWord ++ tailWord_6311000).sum := by decide
  have hdescent : baseEnd_6311000 < baseStart_6311000 := by decide
  rcases family_descends (prefixWord ++ tailWord_6311000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6311007 : List Nat := [1, 1, 2, 3, 1, 1, 3, 5, 1, 1, 4]
def baseStart_6311007 : Nat := 118140960795 + 6311007 * 2 ^ 59
def prefixEnd_6311007 : Nat := 4983230072969 + 3 ^ 40 * 6311007 * 2
def baseEnd_6311007 : Nat := 3240580004889494889788713

theorem tailTrace_6311007 : CollatzResearch.WordTrace tailWord_6311007 prefixEnd_6311007 3240580004889494889788713 := by
  unfold tailWord_6311007
  simp only [CollatzResearch.WordTrace]
  refine ⟨230181335447306948029947275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153454223631537965353298183 230181335447306948029947275)
  ·
    refine ⟨345272003170960422044920913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230181335447306948029947275 345272003170960422044920913)
    ·
      refine ⟨258954002378220316533690685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 345272003170960422044920913 258954002378220316533690685)
      ·
        refine ⟨97107750891832618700134007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 258954002378220316533690685 97107750891832618700134007)
        ·
          refine ⟨145661626337748928050201011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97107750891832618700134007 145661626337748928050201011)
          ·
            refine ⟨218492439506623392075301517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 145661626337748928050201011 218492439506623392075301517)
            ·
              refine ⟨81934664814983772028238069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 218492439506623392075301517 81934664814983772028238069)
              ·
                refine ⟨7681374826404728627647319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 81934664814983772028238069 7681374826404728627647319)
                ·
                  refine ⟨11522062239607092941470979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7681374826404728627647319 11522062239607092941470979)
                  ·
                    refine ⟨17283093359410639412206469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11522062239607092941470979 17283093359410639412206469)
                    ·
                      refine ⟨3240580004889494889788713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17283093359410639412206469 3240580004889494889788713)
                      ·
                        rfl

theorem cell23_6311007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 5, 1, 1, 4].length) (baseStart_6311007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6311007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6311007 prefixEnd_6311007 := by exact prefixLift 6311007
  have htrace : WordTrace (prefixWord ++ tailWord_6311007) baseStart_6311007 baseEnd_6311007 := by
    simpa [prefixWord, tailWord_6311007, baseEnd_6311007] using wordTrace_append hprefix tailTrace_6311007
  have hstable : (prefixWord ++ tailWord_6311007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6311007).length < 2 ^ (prefixWord ++ tailWord_6311007).sum := by decide
  have hdescent : baseEnd_6311007 < baseStart_6311007 := by decide
  rcases family_descends (prefixWord ++ tailWord_6311007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6311017 : List Nat := [1, 2, 1, 1, 1, 6, 2, 1, 4, 4]
def baseStart_6311017 : Nat := 118140960795 + 6311017 * 2 ^ 59
def prefixEnd_6311017 : Nat := 4983230072969 + 3 ^ 40 * 6311017 * 2
def baseEnd_6311017 : Nat := 1080195046565346616887889

theorem tailTrace_6311017 : CollatzResearch.WordTrace tailWord_6311017 prefixEnd_6311017 1080195046565346616887889 := by
  unfold tailWord_6311017
  simp only [CollatzResearch.WordTrace]
  refine ⟨230181700177270719737811305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153454466784847146491874203 230181700177270719737811305)
  ·
    refine ⟨172636275132953039803358479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 230181700177270719737811305 172636275132953039803358479)
    ·
      refine ⟨258954412699429559705037719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172636275132953039803358479 258954412699429559705037719)
      ·
        refine ⟨388431619049144339557556579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 258954412699429559705037719 388431619049144339557556579)
        ·
          refine ⟨582647428573716509336334869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 388431619049144339557556579 582647428573716509336334869)
          ·
            refine ⟨27311598214392961375140697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 582647428573716509336334869 27311598214392961375140697)
            ·
              refine ⟨20483698660794721031355523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27311598214392961375140697 20483698660794721031355523)
              ·
                refine ⟨30725547991192081547033285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20483698660794721031355523 30725547991192081547033285)
                ·
                  refine ⟨5761040248348515290068741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30725547991192081547033285 5761040248348515290068741)
                  ·
                    refine ⟨1080195046565346616887889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5761040248348515290068741 1080195046565346616887889)
                    ·
                      rfl

theorem cell23_6311017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 2, 1, 4, 4].length) (baseStart_6311017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6311017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6311017 prefixEnd_6311017 := by exact prefixLift 6311017
  have htrace : WordTrace (prefixWord ++ tailWord_6311017) baseStart_6311017 baseEnd_6311017 := by
    simpa [prefixWord, tailWord_6311017, baseEnd_6311017] using wordTrace_append hprefix tailTrace_6311017
  have hstable : (prefixWord ++ tailWord_6311017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6311017).length < 2 ^ (prefixWord ++ tailWord_6311017).sum := by decide
  have hdescent : baseEnd_6311017 < baseStart_6311017 := by decide
  rcases family_descends (prefixWord ++ tailWord_6311017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
