import V185TrunkScan22Chunk130

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_1171837 : List Nat := [1, 4, 1, 1, 2, 4, 1, 8]
def baseStart_1171837 : Nat := 118140960795 + 1171837 * 2 ^ 59
def prefixEnd_1171837 : Nat := 4983230072969 + 3 ^ 40 * 1171837 * 2
def baseEnd_1171837 : Nat := 44571528127617549336913

theorem tailTrace_1171837 : CollatzResearch.WordTrace tailWord_1171837 prefixEnd_1171837 44571528127617549336913 := by
  unfold tailWord_1171837
  simp only [CollatzResearch.WordTrace]
  refine ⟨42740406655642157671241765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28493604437094771780827843 42740406655642157671241765)
  ·
    refine ⟨8013826247932904563357831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 42740406655642157671241765 8013826247932904563357831)
    ·
      refine ⟨12020739371899356845036747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8013826247932904563357831 12020739371899356845036747)
      ·
        refine ⟨18031109057849035267555121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12020739371899356845036747 18031109057849035267555121)
        ·
          refine ⟨13523331793386776450666341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18031109057849035267555121 13523331793386776450666341)
          ·
            refine ⟨2535624711260020584499939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13523331793386776450666341 2535624711260020584499939)
            ·
              refine ⟨3803437066890030876749909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2535624711260020584499939 3803437066890030876749909)
              ·
                refine ⟨44571528127617549336913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3803437066890030876749909 44571528127617549336913)
                ·
                  rfl

theorem cell22_1171837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 1, 8].length) (baseStart_1171837 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1171837 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1171837 prefixEnd_1171837 := by exact prefixLift 1171837
  have htrace : WordTrace (prefixWord ++ tailWord_1171837) baseStart_1171837 baseEnd_1171837 := by
    simpa [prefixWord, tailWord_1171837, baseEnd_1171837] using wordTrace_append hprefix tailTrace_1171837
  have hstable : (prefixWord ++ tailWord_1171837).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1171837).length < 2 ^ (prefixWord ++ tailWord_1171837).sum := by decide
  have hdescent : baseEnd_1171837 < baseStart_1171837 := by decide
  rcases family_descends (prefixWord ++ tailWord_1171837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1171843 : List Nat := [1, 1, 1, 3, 7, 1, 1, 3, 4]
def baseStart_1171843 : Nat := 118140960795 + 1171843 * 2 ^ 59
def prefixEnd_1171843 : Nat := 4983230072969 + 3 ^ 40 * 1171843 * 2
def baseEnd_1171843 : Nat := 133715269023725309460733

theorem tailTrace_1171843 : CollatzResearch.WordTrace tailWord_1171843 prefixEnd_1171843 133715269023725309460733 := by
  unfold tailWord_1171843
  simp only [CollatzResearch.WordTrace]
  refine ⟨42740625493620420695960183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28493750329080280463973455 42740625493620420695960183)
  ·
    refine ⟨64110938240430631043940275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42740625493620420695960183 64110938240430631043940275)
    ·
      refine ⟨96166407360645946565910413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64110938240430631043940275 96166407360645946565910413)
      ·
        refine ⟨36062402760242229962216405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 96166407360645946565910413 36062402760242229962216405)
        ·
          refine ⟨845212564693177264739447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 36062402760242229962216405 845212564693177264739447)
          ·
            refine ⟨1267818847039765897109171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 845212564693177264739447 1267818847039765897109171)
            ·
              refine ⟨1901728270559648845663757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1267818847039765897109171 1901728270559648845663757)
              ·
                refine ⟨713148101459868317123909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1901728270559648845663757 713148101459868317123909)
                ·
                  refine ⟨133715269023725309460733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 713148101459868317123909 133715269023725309460733)
                  ·
                    rfl

theorem cell22_1171843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 7, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 7, 1, 1, 3, 4].length) (baseStart_1171843 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1171843 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1171843 prefixEnd_1171843 := by exact prefixLift 1171843
  have htrace : WordTrace (prefixWord ++ tailWord_1171843) baseStart_1171843 baseEnd_1171843 := by
    simpa [prefixWord, tailWord_1171843, baseEnd_1171843] using wordTrace_append hprefix tailTrace_1171843
  have hstable : (prefixWord ++ tailWord_1171843).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1171843).length < 2 ^ (prefixWord ++ tailWord_1171843).sum := by decide
  have hdescent : baseEnd_1171843 < baseStart_1171843 := by decide
  rcases family_descends (prefixWord ++ tailWord_1171843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1171854 : List Nat := [4, 1, 1, 4, 1, 3, 8]
def baseStart_1171854 : Nat := 118140960795 + 1171854 * 2 ^ 59
def prefixEnd_1171854 : Nat := 4983230072969 + 3 ^ 40 * 1171854 * 2
def baseEnd_1171854 : Nat := 14857391577628724679895

theorem tailTrace_1171854 : CollatzResearch.WordTrace tailWord_1171854 prefixEnd_1171854 14857391577628724679895 := by
  unfold tailWord_1171854
  simp only [CollatzResearch.WordTrace]
  refine ⟨5342628337072571196826327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28494017797720379716407077 5342628337072571196826327)
  ·
    refine ⟨8013942505608856795239491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5342628337072571196826327 8013942505608856795239491)
    ·
      refine ⟨12020913758413285192859237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8013942505608856795239491 12020913758413285192859237)
      ·
        refine ⟨2253921329702490973661107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12020913758413285192859237 2253921329702490973661107)
        ·
          refine ⟨3380881994553736460491661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2253921329702490973661107 3380881994553736460491661)
          ·
            refine ⟨1267830747957651172684373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3380881994553736460491661 1267830747957651172684373)
            ·
              refine ⟨14857391577628724679895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1267830747957651172684373 14857391577628724679895)
              ·
                rfl

theorem cell22_1171854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 3, 8].length) (baseStart_1171854 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1171854 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1171854 prefixEnd_1171854 := by exact prefixLift 1171854
  have htrace : WordTrace (prefixWord ++ tailWord_1171854) baseStart_1171854 baseEnd_1171854 := by
    simpa [prefixWord, tailWord_1171854, baseEnd_1171854] using wordTrace_append hprefix tailTrace_1171854
  have hstable : (prefixWord ++ tailWord_1171854).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1171854).length < 2 ^ (prefixWord ++ tailWord_1171854).sum := by decide
  have hdescent : baseEnd_1171854 < baseStart_1171854 := by decide
  rcases family_descends (prefixWord ++ tailWord_1171854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1171916 : List Nat := [2, 2, 1, 4, 3, 1, 2, 2, 5]
def baseStart_1171916 : Nat := 118140960795 + 1171916 * 2 ^ 59
def prefixEnd_1171916 : Nat := 4983230072969 + 3 ^ 40 * 1171916 * 2
def baseEnd_1171916 : Nat := 133723598821009357102325

theorem tailTrace_1171916 : CollatzResearch.WordTrace tailWord_1171916 prefixEnd_1171916 133723598821009357102325 := by
  unfold tailWord_1171916
  simp only [CollatzResearch.WordTrace]
  refine ⟨21371644011177977081683801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28495525348237302775578401 21371644011177977081683801)
  ·
    refine ⟨16028733008383482811262851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21371644011177977081683801 16028733008383482811262851)
    ·
      refine ⟨24043099512575224216894277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16028733008383482811262851 24043099512575224216894277)
      ·
        refine ⟨4508081158607854540667677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24043099512575224216894277 4508081158607854540667677)
        ·
          refine ⟨1690530434477945452750379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4508081158607854540667677 1690530434477945452750379)
          ·
            refine ⟨2535795651716918179125569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1690530434477945452750379 2535795651716918179125569)
            ·
              refine ⟨1901846738787688634344177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2535795651716918179125569 1901846738787688634344177)
              ·
                refine ⟨1426385054090766475758133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1901846738787688634344177 1426385054090766475758133)
                ·
                  refine ⟨133723598821009357102325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1426385054090766475758133 133723598821009357102325)
                  ·
                    rfl

theorem cell22_1171916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 2, 2, 5].length) (baseStart_1171916 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1171916 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1171916 prefixEnd_1171916 := by exact prefixLift 1171916
  have htrace : WordTrace (prefixWord ++ tailWord_1171916) baseStart_1171916 baseEnd_1171916 := by
    simpa [prefixWord, tailWord_1171916, baseEnd_1171916] using wordTrace_append hprefix tailTrace_1171916
  have hstable : (prefixWord ++ tailWord_1171916).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1171916).length < 2 ^ (prefixWord ++ tailWord_1171916).sum := by decide
  have hdescent : baseEnd_1171916 < baseStart_1171916 := by decide
  rcases family_descends (prefixWord ++ tailWord_1171916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1171944 : List Nat := [2, 1, 4, 1, 1, 4, 1, 2, 6]
def baseStart_1171944 : Nat := 118140960795 + 1171944 * 2 ^ 59
def prefixEnd_1171944 : Nat := 4983230072969 + 3 ^ 40 * 1171944 * 2
def baseEnd_1171944 : Nat := 133726793811748443868963

theorem tailTrace_1171944 : CollatzResearch.WordTrace tailWord_1171944 prefixEnd_1171944 133726793811748443868963 := by
  unfold tailWord_1171944
  simp only [CollatzResearch.WordTrace]
  refine ⟨21372154633127257472693443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28496206177503009963591257 21372154633127257472693443)
  ·
    refine ⟨32058231949690886209040165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21372154633127257472693443 32058231949690886209040165)
    ·
      refine ⟨6010918490567041164195031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32058231949690886209040165 6010918490567041164195031)
      ·
        refine ⟨9016377735850561746292547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6010918490567041164195031 9016377735850561746292547)
        ·
          refine ⟨13524566603775842619438821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9016377735850561746292547 13524566603775842619438821)
          ·
            refine ⟨2535856238207970491144779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13524566603775842619438821 2535856238207970491144779)
            ·
              refine ⟨3803784357311955736717169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2535856238207970491144779 3803784357311955736717169)
              ·
                refine ⟨2852838267983966802537877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3803784357311955736717169 2852838267983966802537877)
                ·
                  refine ⟨133726793811748443868963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2852838267983966802537877 133726793811748443868963)
                  ·
                    rfl

theorem cell22_1171944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 1, 2, 6].length) (baseStart_1171944 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1171944 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1171944 prefixEnd_1171944 := by exact prefixLift 1171944
  have htrace : WordTrace (prefixWord ++ tailWord_1171944) baseStart_1171944 baseEnd_1171944 := by
    simpa [prefixWord, tailWord_1171944, baseEnd_1171944] using wordTrace_append hprefix tailTrace_1171944
  have hstable : (prefixWord ++ tailWord_1171944).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1171944).length < 2 ^ (prefixWord ++ tailWord_1171944).sum := by decide
  have hdescent : baseEnd_1171944 < baseStart_1171944 := by decide
  rcases family_descends (prefixWord ++ tailWord_1171944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1172141 : List Nat := [1, 5, 2, 1, 1, 3, 9]
def baseStart_1172141 : Nat := 118140960795 + 1172141 * 2 ^ 59
def prefixEnd_1172141 : Nat := 4983230072969 + 3 ^ 40 * 1172141 * 2
def baseEnd_1172141 : Nat := 14861030317081573497455

theorem tailTrace_1172141 : CollatzResearch.WordTrace tailWord_1172141 prefixEnd_1172141 14861030317081573497455 := by
  unfold tailWord_1172141
  simp only [CollatzResearch.WordTrace]
  refine ⟨42751494446540817590308277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28500996297693878393538851 42751494446540817590308277)
  ·
    refine ⟨4007952604363201649091401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 42751494446540817590308277 4007952604363201649091401)
    ·
      refine ⟨3005964453272401236818551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4007952604363201649091401 3005964453272401236818551)
      ·
        refine ⟨4508946679908601855227827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3005964453272401236818551 4508946679908601855227827)
        ·
          refine ⟨6763420019862902782841741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4508946679908601855227827 6763420019862902782841741)
          ·
            refine ⟨2536282507448588543565653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6763420019862902782841741 2536282507448588543565653)
            ·
              refine ⟨14861030317081573497455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2536282507448588543565653 14861030317081573497455)
              ·
                rfl

theorem cell22_1172141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 9].length) (baseStart_1172141 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1172141 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1172141 prefixEnd_1172141 := by exact prefixLift 1172141
  have htrace : WordTrace (prefixWord ++ tailWord_1172141) baseStart_1172141 baseEnd_1172141 := by
    simpa [prefixWord, tailWord_1172141, baseEnd_1172141] using wordTrace_append hprefix tailTrace_1172141
  have hstable : (prefixWord ++ tailWord_1172141).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1172141).length < 2 ^ (prefixWord ++ tailWord_1172141).sum := by decide
  have hdescent : baseEnd_1172141 < baseStart_1172141 := by decide
  rcases family_descends (prefixWord ++ tailWord_1172141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1172145 : List Nat := [1, 2, 2, 6, 1, 1, 1, 1, 4, 3]
def baseStart_1172145 : Nat := 118140960795 + 1172145 * 2 ^ 59
def prefixEnd_1172145 : Nat := 4983230072969 + 3 ^ 40 * 1172145 * 2
def baseEnd_1172145 : Nat := 401249187842947807331273

theorem tailTrace_1172145 : CollatzResearch.WordTrace tailWord_1172145 prefixEnd_1172145 401249187842947807331273 := by
  unfold tailWord_1172145
  simp only [CollatzResearch.WordTrace]
  refine ⟨42751640338526326273453889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28501093559017550848969259 42751640338526326273453889)
  ·
    refine ⟨32063730253894744705090417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42751640338526326273453889 32063730253894744705090417)
    ·
      refine ⟨24047797690421058528817813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32063730253894744705090417 24047797690421058528817813)
      ·
        refine ⟨1127240516738487118538335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 24047797690421058528817813 1127240516738487118538335)
        ·
          refine ⟨1690860775107730677807503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1127240516738487118538335 1690860775107730677807503)
          ·
            refine ⟨2536291162661596016711255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1690860775107730677807503 2536291162661596016711255)
            ·
              refine ⟨3804436743992394025066883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2536291162661596016711255 3804436743992394025066883)
              ·
                refine ⟨5706655115988591037600325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3804436743992394025066883 5706655115988591037600325)
                ·
                  refine ⟨1069997834247860819550061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5706655115988591037600325 1069997834247860819550061)
                  ·
                    refine ⟨401249187842947807331273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1069997834247860819550061 401249187842947807331273)
                    ·
                      rfl

theorem cell22_1172145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 1, 1, 4, 3].length) (baseStart_1172145 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1172145 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1172145 prefixEnd_1172145 := by exact prefixLift 1172145
  have htrace : WordTrace (prefixWord ++ tailWord_1172145) baseStart_1172145 baseEnd_1172145 := by
    simpa [prefixWord, tailWord_1172145, baseEnd_1172145] using wordTrace_append hprefix tailTrace_1172145
  have hstable : (prefixWord ++ tailWord_1172145).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1172145).length < 2 ^ (prefixWord ++ tailWord_1172145).sum := by decide
  have hdescent : baseEnd_1172145 < baseStart_1172145 := by decide
  rcases family_descends (prefixWord ++ tailWord_1172145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1172207 : List Nat := [1, 1, 2, 1, 5, 3, 3, 2, 1, 3]
def baseStart_1172207 : Nat := 118140960795 + 1172207 * 2 ^ 59
def prefixEnd_1172207 : Nat := 4983230072969 + 3 ^ 40 * 1172207 * 2
def baseEnd_1172207 : Nat := 401270411710000312281083

theorem tailTrace_1172207 : CollatzResearch.WordTrace tailWord_1172207 prefixEnd_1172207 401270411710000312281083 := by
  unfold tailWord_1172207
  simp only [CollatzResearch.WordTrace]
  refine ⟨42753901664301710862210875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28502601109534473908140583 42753901664301710862210875)
  ·
    refine ⟨64130852496452566293316313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42753901664301710862210875 64130852496452566293316313)
    ·
      refine ⟨48098139372339424719987235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64130852496452566293316313 48098139372339424719987235)
      ·
        refine ⟨72147209058509137079980853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48098139372339424719987235 72147209058509137079980853)
        ·
          refine ⟨6763800849235231601248205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 72147209058509137079980853 6763800849235231601248205)
          ·
            refine ⟨2536425318463211850468077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6763800849235231601248205 2536425318463211850468077)
            ·
              refine ⟨951159494423704443925529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2536425318463211850468077 951159494423704443925529)
              ·
                refine ⟨713369620817778332944147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 951159494423704443925529 713369620817778332944147)
                ·
                  refine ⟨1070054431226667499416221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 713369620817778332944147 1070054431226667499416221)
                  ·
                    refine ⟨401270411710000312281083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1070054431226667499416221 401270411710000312281083)
                    ·
                      rfl

theorem cell22_1172207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 3, 2, 1, 3].length) (baseStart_1172207 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1172207 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1172207 prefixEnd_1172207 := by exact prefixLift 1172207
  have htrace : WordTrace (prefixWord ++ tailWord_1172207) baseStart_1172207 baseEnd_1172207 := by
    simpa [prefixWord, tailWord_1172207, baseEnd_1172207] using wordTrace_append hprefix tailTrace_1172207
  have hstable : (prefixWord ++ tailWord_1172207).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1172207).length < 2 ^ (prefixWord ++ tailWord_1172207).sum := by decide
  have hdescent : baseEnd_1172207 < baseStart_1172207 := by decide
  rcases family_descends (prefixWord ++ tailWord_1172207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1172213 : List Nat := [1, 3, 6, 1, 2, 1, 2, 1, 2, 3]
def baseStart_1172213 : Nat := 118140960795 + 1172213 * 2 ^ 59
def prefixEnd_1172213 : Nat := 4983230072969 + 3 ^ 40 * 1172213 * 2
def baseEnd_1172213 : Nat := 401272465632618296631065

theorem tailTrace_1172213 : CollatzResearch.WordTrace tailWord_1172213 prefixEnd_1172213 401272465632618296631065 := by
  unfold tailWord_1172213
  simp only [CollatzResearch.WordTrace]
  refine ⟨42754120502279973886929293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28502747001519982591286195 42754120502279973886929293)
  ·
    refine ⟨16032795188354990207598485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42754120502279973886929293 16032795188354990207598485)
    ·
      refine ⟨751537274454140165981179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 16032795188354990207598485 751537274454140165981179)
      ·
        refine ⟨1127305911681210248971769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 751537274454140165981179 1127305911681210248971769)
        ·
          refine ⟨845479433760907686728827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1127305911681210248971769 845479433760907686728827)
          ·
            refine ⟨1268219150641361530093241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 845479433760907686728827 1268219150641361530093241)
            ·
              refine ⟨951164362981021147569931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1268219150641361530093241 951164362981021147569931)
              ·
                refine ⟨1426746544471531721354897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 951164362981021147569931 1426746544471531721354897)
                ·
                  refine ⟨1070059908353648791016173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1426746544471531721354897 1070059908353648791016173)
                  ·
                    refine ⟨401272465632618296631065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1070059908353648791016173 401272465632618296631065)
                    ·
                      rfl

theorem cell22_1172213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 2, 1, 2, 1, 2, 3].length) (baseStart_1172213 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1172213 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1172213 prefixEnd_1172213 := by exact prefixLift 1172213
  have htrace : WordTrace (prefixWord ++ tailWord_1172213) baseStart_1172213 baseEnd_1172213 := by
    simpa [prefixWord, tailWord_1172213, baseEnd_1172213] using wordTrace_append hprefix tailTrace_1172213
  have hstable : (prefixWord ++ tailWord_1172213).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1172213).length < 2 ^ (prefixWord ++ tailWord_1172213).sum := by decide
  have hdescent : baseEnd_1172213 < baseStart_1172213 := by decide
  rcases family_descends (prefixWord ++ tailWord_1172213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1172216 : List Nat := [2, 1, 2, 1, 1, 2, 4, 2, 3, 4]
def baseStart_1172216 : Nat := 118140960795 + 1172216 * 2 ^ 59
def prefixEnd_1172216 : Nat := 4983230072969 + 3 ^ 40 * 1172216 * 2
def baseEnd_1172216 : Nat := 401273492593927288806055

theorem tailTrace_1172216 : CollatzResearch.WordTrace tailWord_1172216 prefixEnd_1172216 401273492593927288806055 := by
  unfold tailWord_1172216
  simp only [CollatzResearch.WordTrace]
  refine ⟨21377114960634552699644251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28502819947512736932859001 21377114960634552699644251)
  ·
    refine ⟨32065672440951829049466377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21377114960634552699644251 32065672440951829049466377)
    ·
      refine ⟨24049254330713871787099783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32065672440951829049466377 24049254330713871787099783)
      ·
        refine ⟨36073881496070807680649675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24049254330713871787099783 36073881496070807680649675)
        ·
          refine ⟨54110822244106211520974513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36073881496070807680649675 54110822244106211520974513)
          ·
            refine ⟨40583116683079658640730885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54110822244106211520974513 40583116683079658640730885)
            ·
              refine ⟨7609334378077435995137041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40583116683079658640730885 7609334378077435995137041)
              ·
                refine ⟨5707000783558076996352781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7609334378077435995137041 5707000783558076996352781)
                ·
                  refine ⟨2140125293834278873632293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5707000783558076996352781 2140125293834278873632293)
                  ·
                    refine ⟨401273492593927288806055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2140125293834278873632293 401273492593927288806055)
                    ·
                      rfl

theorem cell22_1172216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 2, 3, 4].length) (baseStart_1172216 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1172216 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1172216 prefixEnd_1172216 := by exact prefixLift 1172216
  have htrace : WordTrace (prefixWord ++ tailWord_1172216) baseStart_1172216 baseEnd_1172216 := by
    simpa [prefixWord, tailWord_1172216, baseEnd_1172216] using wordTrace_append hprefix tailTrace_1172216
  have hstable : (prefixWord ++ tailWord_1172216).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1172216).length < 2 ^ (prefixWord ++ tailWord_1172216).sum := by decide
  have hdescent : baseEnd_1172216 < baseStart_1172216 := by decide
  rcases family_descends (prefixWord ++ tailWord_1172216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1172220 : List Nat := [2, 2, 2, 1, 3, 4, 2, 1, 5]
def baseStart_1172220 : Nat := 118140960795 + 1172220 * 2 ^ 59
def prefixEnd_1172220 : Nat := 4983230072969 + 3 ^ 40 * 1172220 * 2
def baseEnd_1172220 : Nat := 133758287291890870568681

theorem tailTrace_1172220 : CollatzResearch.WordTrace tailWord_1172220 prefixEnd_1172220 133758287291890870568681 := by
  unfold tailWord_1172220
  simp only [CollatzResearch.WordTrace]
  refine ⟨21377187906627307041217057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28502917208836409388289409 21377187906627307041217057)
  ·
    refine ⟨16032890929970480280912793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21377187906627307041217057 16032890929970480280912793)
    ·
      refine ⟨12024668197477860210684595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16032890929970480280912793 12024668197477860210684595)
      ·
        refine ⟨18037002296216790316026893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12024668197477860210684595 18037002296216790316026893)
        ·
          refine ⟨6763875861081296368510085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18037002296216790316026893 6763875861081296368510085)
          ·
            refine ⟨1268226723952743069095641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6763875861081296368510085 1268226723952743069095641)
            ·
              refine ⟨951170042964557301821731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1268226723952743069095641 951170042964557301821731)
              ·
                refine ⟨1426755064446835952732597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 951170042964557301821731 1426755064446835952732597)
                ·
                  refine ⟨133758287291890870568681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1426755064446835952732597 133758287291890870568681)
                  ·
                    rfl

theorem cell22_1172220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 4, 2, 1, 5].length) (baseStart_1172220 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1172220 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1172220 prefixEnd_1172220 := by exact prefixLift 1172220
  have htrace : WordTrace (prefixWord ++ tailWord_1172220) baseStart_1172220 baseEnd_1172220 := by
    simpa [prefixWord, tailWord_1172220, baseEnd_1172220] using wordTrace_append hprefix tailTrace_1172220
  have hstable : (prefixWord ++ tailWord_1172220).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1172220).length < 2 ^ (prefixWord ++ tailWord_1172220).sum := by decide
  have hdescent : baseEnd_1172220 < baseStart_1172220 := by decide
  rcases family_descends (prefixWord ++ tailWord_1172220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1172233 : List Nat := [1, 2, 1, 1, 3, 2, 5, 2, 1, 4]
def baseStart_1172233 : Nat := 118140960795 + 1172233 * 2 ^ 59
def prefixEnd_1172233 : Nat := 4983230072969 + 3 ^ 40 * 1172233 * 2
def baseEnd_1172233 : Nat := 401279312041344911131003

theorem tailTrace_1172233 : CollatzResearch.WordTrace tailWord_1172233 prefixEnd_1172233 401279312041344911131003 := by
  unfold tailWord_1172233
  simp only [CollatzResearch.WordTrace]
  refine ⟨42754849962207517302657353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28503233308138344868438235 42754849962207517302657353)
  ·
    refine ⟨32066137471655637976993015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42754849962207517302657353 32066137471655637976993015)
    ·
      refine ⟨48099206207483456965489523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32066137471655637976993015 48099206207483456965489523)
      ·
        refine ⟨72148809311225185448234285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48099206207483456965489523 72148809311225185448234285)
        ·
          refine ⟨27055803491709444543087857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 72148809311225185448234285 27055803491709444543087857)
          ·
            refine ⟨20291852618782083407315893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27055803491709444543087857 20291852618782083407315893)
            ·
              refine ⟨1902361183010820319435865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 20291852618782083407315893 1902361183010820319435865)
              ·
                refine ⟨1426770887258115239576899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1902361183010820319435865 1426770887258115239576899)
                ·
                  refine ⟨2140156330887172859365349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1426770887258115239576899 2140156330887172859365349)
                  ·
                    refine ⟨401279312041344911131003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2140156330887172859365349 401279312041344911131003)
                    ·
                      rfl

theorem cell22_1172233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 5, 2, 1, 4].length) (baseStart_1172233 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1172233 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1172233 prefixEnd_1172233 := by exact prefixLift 1172233
  have htrace : WordTrace (prefixWord ++ tailWord_1172233) baseStart_1172233 baseEnd_1172233 := by
    simpa [prefixWord, tailWord_1172233, baseEnd_1172233] using wordTrace_append hprefix tailTrace_1172233
  have hstable : (prefixWord ++ tailWord_1172233).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1172233).length < 2 ^ (prefixWord ++ tailWord_1172233).sum := by decide
  have hdescent : baseEnd_1172233 < baseStart_1172233 := by decide
  rcases family_descends (prefixWord ++ tailWord_1172233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1172248 : List Nat := [2, 1, 2, 3, 1, 1, 1, 7, 4]
def baseStart_1172248 : Nat := 118140960795 + 1172248 * 2 ^ 59
def prefixEnd_1172248 : Nat := 4983230072969 + 3 ^ 40 * 1172248 * 2
def baseEnd_1172248 : Nat := 133761482282629957335319

theorem tailTrace_1172248 : CollatzResearch.WordTrace tailWord_1172248 prefixEnd_1172248 133761482282629957335319 := by
  unfold tailWord_1172248
  simp only [CollatzResearch.WordTrace]
  refine ⟨21377698528576587432226699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28503598038102116576302265 21377698528576587432226699)
  ·
    refine ⟨32066547792864881148340049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21377698528576587432226699 32066547792864881148340049)
    ·
      refine ⟨24049910844648660861255037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32066547792864881148340049 24049910844648660861255037)
      ·
        refine ⟨9018716566743247822970639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24049910844648660861255037 9018716566743247822970639)
        ·
          refine ⟨13528074850114871734455959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9018716566743247822970639 13528074850114871734455959)
          ·
            refine ⟨20292112275172307601683939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13528074850114871734455959 20292112275172307601683939)
            ·
              refine ⟨30438168412758461402525909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20292112275172307601683939 30438168412758461402525909)
              ·
                refine ⟨713394572174026439121701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 30438168412758461402525909 713394572174026439121701)
                ·
                  refine ⟨133761482282629957335319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 713394572174026439121701 133761482282629957335319)
                  ·
                    rfl

theorem cell22_1172248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 7, 4].length) (baseStart_1172248 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1172248 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1172248 prefixEnd_1172248 := by exact prefixLift 1172248
  have htrace : WordTrace (prefixWord ++ tailWord_1172248) baseStart_1172248 baseEnd_1172248 := by
    simpa [prefixWord, tailWord_1172248, baseEnd_1172248] using wordTrace_append hprefix tailTrace_1172248
  have hstable : (prefixWord ++ tailWord_1172248).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1172248).length < 2 ^ (prefixWord ++ tailWord_1172248).sum := by decide
  have hdescent : baseEnd_1172248 < baseStart_1172248 := by decide
  rcases family_descends (prefixWord ++ tailWord_1172248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1172250 : List Nat := [3, 1, 1, 3, 2, 1, 5, 1, 1, 4]
def baseStart_1172250 : Nat := 118140960795 + 1172250 * 2 ^ 59
def prefixEnd_1172250 : Nat := 4983230072969 + 3 ^ 40 * 1172250 * 2
def baseEnd_1172250 : Nat := 401285131488762533455951

theorem tailTrace_1172250 : CollatzResearch.WordTrace tailWord_1172250 prefixEnd_1172250 401285131488762533455951 := by
  unfold tailWord_1172250
  simp only [CollatzResearch.WordTrace]
  refine ⟨10688867500786482301506551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28503646668763952804017469 10688867500786482301506551)
  ·
    refine ⟨16033301251179723452259827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10688867500786482301506551 16033301251179723452259827)
    ·
      refine ⟨24049951876769585178389741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16033301251179723452259827 24049951876769585178389741)
      ·
        refine ⟨9018731953788594441896153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24049951876769585178389741 9018731953788594441896153)
        ·
          refine ⟨6764048965341445831422115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9018731953788594441896153 6764048965341445831422115)
          ·
            refine ⟨10146073448012168747133173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6764048965341445831422115 10146073448012168747133173)
            ·
              refine ⟨951194385751140820043735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10146073448012168747133173 951194385751140820043735)
              ·
                refine ⟨1426791578626711230065603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 951194385751140820043735 1426791578626711230065603)
                ·
                  refine ⟨2140187367940066845098405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1426791578626711230065603 2140187367940066845098405)
                  ·
                    refine ⟨401285131488762533455951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2140187367940066845098405 401285131488762533455951)
                    ·
                      rfl

theorem cell22_1172250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 5, 1, 1, 4].length) (baseStart_1172250 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1172250 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1172250 prefixEnd_1172250 := by exact prefixLift 1172250
  have htrace : WordTrace (prefixWord ++ tailWord_1172250) baseStart_1172250 baseEnd_1172250 := by
    simpa [prefixWord, tailWord_1172250, baseEnd_1172250] using wordTrace_append hprefix tailTrace_1172250
  have hstable : (prefixWord ++ tailWord_1172250).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1172250).length < 2 ^ (prefixWord ++ tailWord_1172250).sum := by decide
  have hdescent : baseEnd_1172250 < baseStart_1172250 := by decide
  rcases family_descends (prefixWord ++ tailWord_1172250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1172301 : List Nat := [1, 6, 1, 2, 3, 1, 2, 1, 1, 4]
def baseStart_1172301 : Nat := 118140960795 + 1172301 * 2 ^ 59
def prefixEnd_1172301 : Nat := 4983230072969 + 3 ^ 40 * 1172301 * 2
def baseEnd_1172301 : Nat := 401302589831015400430795

theorem tailTrace_1172301 : CollatzResearch.WordTrace tailWord_1172301 prefixEnd_1172301 401302589831015400430795 := by
  unfold tailWord_1172301
  simp only [CollatzResearch.WordTrace]
  refine ⟨42757330125961164916132757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28504886750640776610755171 42757330125961164916132757)
  ·
    refine ⟨2004249849654429605443723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 42757330125961164916132757 2004249849654429605443723)
    ·
      refine ⟨3006374774481644408165585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2004249849654429605443723 3006374774481644408165585)
      ·
        refine ⟨2254781080861233306124189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3006374774481644408165585 2254781080861233306124189)
        ·
          refine ⟨845542905322962489796571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2254781080861233306124189 845542905322962489796571)
          ·
            refine ⟨1268314357984443734694857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 845542905322962489796571 1268314357984443734694857)
            ·
              refine ⟨951235768488332801021143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1268314357984443734694857 951235768488332801021143)
              ·
                refine ⟨1426853652732499201531715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 951235768488332801021143 1426853652732499201531715)
                ·
                  refine ⟨2140280479098748802297573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1426853652732499201531715 2140280479098748802297573)
                  ·
                    refine ⟨401302589831015400430795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2140280479098748802297573 401302589831015400430795)
                    ·
                      rfl

theorem cell22_1172301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 3, 1, 2, 1, 1, 4].length) (baseStart_1172301 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1172301 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1172301 prefixEnd_1172301 := by exact prefixLift 1172301
  have htrace : WordTrace (prefixWord ++ tailWord_1172301) baseStart_1172301 baseEnd_1172301 := by
    simpa [prefixWord, tailWord_1172301, baseEnd_1172301] using wordTrace_append hprefix tailTrace_1172301
  have hstable : (prefixWord ++ tailWord_1172301).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1172301).length < 2 ^ (prefixWord ++ tailWord_1172301).sum := by decide
  have hdescent : baseEnd_1172301 < baseStart_1172301 := by decide
  rcases family_descends (prefixWord ++ tailWord_1172301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1172338 : List Nat := [3, 2, 1, 2, 1, 1, 2, 5, 5]
def baseStart_1172338 : Nat := 118140960795 + 1172338 * 2 ^ 59
def prefixEnd_1172338 : Nat := 4983230072969 + 3 ^ 40 * 1172338 * 2
def baseEnd_1172338 : Nat := 133771751895719879085227

theorem tailTrace_1172338 : CollatzResearch.WordTrace tailWord_1172338 prefixEnd_1172338 133771751895719879085227 := by
  unfold tailWord_1172338
  simp only [CollatzResearch.WordTrace]
  refine ⟨10689669906706780058807417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28505786417884746823486445 10689669906706780058807417)
  ·
    refine ⟨8017252430030085044105563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10689669906706780058807417 8017252430030085044105563)
    ·
      refine ⟨12025878645045127566158345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8017252430030085044105563 12025878645045127566158345)
      ·
        refine ⟨9019408983783845674618759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12025878645045127566158345 9019408983783845674618759)
        ·
          refine ⟨13529113475675768511928139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9019408983783845674618759 13529113475675768511928139)
          ·
            refine ⟨20293670213513652767892209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13529113475675768511928139 20293670213513652767892209)
            ·
              refine ⟨15220252660135239575919157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20293670213513652767892209 15220252660135239575919157)
              ·
                refine ⟨1426898686887678710242421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15220252660135239575919157 1426898686887678710242421)
                ·
                  refine ⟨133771751895719879085227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1426898686887678710242421 133771751895719879085227)
                  ·
                    rfl

theorem cell22_1172338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 5, 5].length) (baseStart_1172338 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1172338 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1172338 prefixEnd_1172338 := by exact prefixLift 1172338
  have htrace : WordTrace (prefixWord ++ tailWord_1172338) baseStart_1172338 baseEnd_1172338 := by
    simpa [prefixWord, tailWord_1172338, baseEnd_1172338] using wordTrace_append hprefix tailTrace_1172338
  have hstable : (prefixWord ++ tailWord_1172338).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1172338).length < 2 ^ (prefixWord ++ tailWord_1172338).sum := by decide
  have hdescent : baseEnd_1172338 < baseStart_1172338 := by decide
  rcases family_descends (prefixWord ++ tailWord_1172338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1172342 : List Nat := [5, 1, 1, 3, 1, 1, 2, 2, 3, 3]
def baseStart_1172342 : Nat := 118140960795 + 1172342 * 2 ^ 59
def prefixEnd_1172342 : Nat := 4983230072969 + 3 ^ 40 * 1172342 * 2
def baseEnd_1172342 : Nat := 401316624968904960155669

theorem tailTrace_1172342 : CollatzResearch.WordTrace tailWord_1172342 prefixEnd_1172342 401316624968904960155669 := by
  unfold tailWord_1172342
  simp only [CollatzResearch.WordTrace]
  refine ⟨2672426594925789307398455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 28505883679208419278916853 2672426594925789307398455)
  ·
    refine ⟨4008639892388683961097683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2672426594925789307398455 4008639892388683961097683)
    ·
      refine ⟨6012959838583025941646525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4008639892388683961097683 6012959838583025941646525)
      ·
        refine ⟨2254859939468634728117447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6012959838583025941646525 2254859939468634728117447)
        ·
          refine ⟨3382289909202952092176171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2254859939468634728117447 3382289909202952092176171)
          ·
            refine ⟨5073434863804428138264257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3382289909202952092176171 5073434863804428138264257)
            ·
              refine ⟨3805076147853321103698193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5073434863804428138264257 3805076147853321103698193)
              ·
                refine ⟨2853807110889990827773645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3805076147853321103698193 2853807110889990827773645)
                ·
                  refine ⟨1070177666583746560415117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2853807110889990827773645 1070177666583746560415117)
                  ·
                    refine ⟨401316624968904960155669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1070177666583746560415117 401316624968904960155669)
                    ·
                      rfl

theorem cell22_1172342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 2, 2, 3, 3].length) (baseStart_1172342 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1172342 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1172342 prefixEnd_1172342 := by exact prefixLift 1172342
  have htrace : WordTrace (prefixWord ++ tailWord_1172342) baseStart_1172342 baseEnd_1172342 := by
    simpa [prefixWord, tailWord_1172342, baseEnd_1172342] using wordTrace_append hprefix tailTrace_1172342
  have hstable : (prefixWord ++ tailWord_1172342).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1172342).length < 2 ^ (prefixWord ++ tailWord_1172342).sum := by decide
  have hdescent : baseEnd_1172342 < baseStart_1172342 := by decide
  rcases family_descends (prefixWord ++ tailWord_1172342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1172359 : List Nat := [1, 1, 4, 2, 3, 3, 1, 3, 1, 3]
def baseStart_1172359 : Nat := 118140960795 + 1172359 * 2 ^ 59
def prefixEnd_1172359 : Nat := 4983230072969 + 3 ^ 40 * 1172359 * 2
def baseEnd_1172359 : Nat := 401322444416322582480617

theorem tailTrace_1172359 : CollatzResearch.WordTrace tailWord_1172359 prefixEnd_1172359 401322444416322582480617 := by
  unfold tailWord_1172359
  simp only [CollatzResearch.WordTrace]
  refine ⟨42759445559751040821744131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28506297039834027214496087 42759445559751040821744131)
  ·
    refine ⟨64139168339626561232616197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42759445559751040821744131 64139168339626561232616197)
    ·
      refine ⟨12026094063679980231115537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 64139168339626561232616197 12026094063679980231115537)
      ·
        refine ⟨9019570547759985173336653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12026094063679980231115537 9019570547759985173336653)
        ·
          refine ⟨3382338955409994440001245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9019570547759985173336653 3382338955409994440001245)
          ·
            refine ⟨1268377108278747915000467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3382338955409994440001245 1268377108278747915000467)
            ·
              refine ⟨1902565662418121872500701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1268377108278747915000467 1902565662418121872500701)
              ·
                refine ⟨713462123406795702187763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1902565662418121872500701 713462123406795702187763)
                ·
                  refine ⟨1070193185110193553281645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 713462123406795702187763 1070193185110193553281645)
                  ·
                    refine ⟨401322444416322582480617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1070193185110193553281645 401322444416322582480617)
                    ·
                      rfl

theorem cell22_1172359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 3, 1, 3, 1, 3].length) (baseStart_1172359 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1172359 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1172359 prefixEnd_1172359 := by exact prefixLift 1172359
  have htrace : WordTrace (prefixWord ++ tailWord_1172359) baseStart_1172359 baseEnd_1172359 := by
    simpa [prefixWord, tailWord_1172359, baseEnd_1172359] using wordTrace_append hprefix tailTrace_1172359
  have hstable : (prefixWord ++ tailWord_1172359).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1172359).length < 2 ^ (prefixWord ++ tailWord_1172359).sum := by decide
  have hdescent : baseEnd_1172359 < baseStart_1172359 := by decide
  rcases family_descends (prefixWord ++ tailWord_1172359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1172430 : List Nat := [4, 1, 1, 1, 2, 3, 2, 2, 2, 4]
def baseStart_1172430 : Nat := 118140960795 + 1172430 * 2 ^ 59
def prefixEnd_1172430 : Nat := 4983230072969 + 3 ^ 40 * 1172430 * 2
def baseEnd_1172430 : Nat := 401346749167302063955399

theorem tailTrace_1172430 : CollatzResearch.WordTrace tailWord_1172430 prefixEnd_1172430 401346749167302063955399 := by
  unfold tailWord_1172430
  simp only [CollatzResearch.WordTrace]
  refine ⟨5345254392811727493447343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28508023428329213298385829 5345254392811727493447343)
  ·
    refine ⟨8017881589217591240171015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5345254392811727493447343 8017881589217591240171015)
    ·
      refine ⟨12026822383826386860256523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8017881589217591240171015 12026822383826386860256523)
      ·
        refine ⟨18040233575739580290384785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12026822383826386860256523 18040233575739580290384785)
        ·
          refine ⟨13530175181804685217788589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18040233575739580290384785 13530175181804685217788589)
          ·
            refine ⟨5073815693176756956670721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13530175181804685217788589 5073815693176756956670721)
            ·
              refine ⟨3805361769882567717503041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5073815693176756956670721 3805361769882567717503041)
              ·
                refine ⟨2854021327411925788127281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3805361769882567717503041 2854021327411925788127281)
                ·
                  refine ⟨2140515995558944341095461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2854021327411925788127281 2140515995558944341095461)
                  ·
                    refine ⟨401346749167302063955399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2140515995558944341095461 401346749167302063955399)
                    ·
                      rfl

theorem cell22_1172430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 2, 2, 2, 4].length) (baseStart_1172430 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1172430 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1172430 prefixEnd_1172430 := by exact prefixLift 1172430
  have htrace : WordTrace (prefixWord ++ tailWord_1172430) baseStart_1172430 baseEnd_1172430 := by
    simpa [prefixWord, tailWord_1172430, baseEnd_1172430] using wordTrace_append hprefix tailTrace_1172430
  have hstable : (prefixWord ++ tailWord_1172430).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1172430).length < 2 ^ (prefixWord ++ tailWord_1172430).sum := by decide
  have hdescent : baseEnd_1172430 < baseStart_1172430 := by decide
  rcases family_descends (prefixWord ++ tailWord_1172430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1172434 : List Nat := [3, 2, 2, 3, 1, 1, 4, 2, 4]
def baseStart_1172434 : Nat := 118140960795 + 1172434 * 2 ^ 59
def prefixEnd_1172434 : Nat := 4983230072969 + 3 ^ 40 * 1172434 * 2
def baseEnd_1172434 : Nat := 133782706149682462285129

theorem tailTrace_1172434 : CollatzResearch.WordTrace tailWord_1172434 prefixEnd_1172434 133782706149682462285129 := by
  unfold tailWord_1172434
  simp only [CollatzResearch.WordTrace]
  refine ⟨10690545258619832157681089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28508120689652885753816237 10690545258619832157681089)
  ·
    refine ⟨8017908943964874118260817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10690545258619832157681089 8017908943964874118260817)
    ·
      refine ⟨6013431707973655588695613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8017908943964874118260817 6013431707973655588695613)
      ·
        refine ⟨2255036890490120845760855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6013431707973655588695613 2255036890490120845760855)
        ·
          refine ⟨3382555335735181268641283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2255036890490120845760855 3382555335735181268641283)
          ·
            refine ⟨5073833003602771902961925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3382555335735181268641283 5073833003602771902961925)
            ·
              refine ⟨951343688175519731805361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5073833003602771902961925 951343688175519731805361)
              ·
                refine ⟨713507766131639798854021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 951343688175519731805361 713507766131639798854021)
                ·
                  refine ⟨133782706149682462285129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 713507766131639798854021 133782706149682462285129)
                  ·
                    rfl

theorem cell22_1172434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 4, 2, 4].length) (baseStart_1172434 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1172434 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1172434 prefixEnd_1172434 := by exact prefixLift 1172434
  have htrace : WordTrace (prefixWord ++ tailWord_1172434) baseStart_1172434 baseEnd_1172434 := by
    simpa [prefixWord, tailWord_1172434, baseEnd_1172434] using wordTrace_append hprefix tailTrace_1172434
  have hstable : (prefixWord ++ tailWord_1172434).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1172434).length < 2 ^ (prefixWord ++ tailWord_1172434).sum := by decide
  have hdescent : baseEnd_1172434 < baseStart_1172434 := by decide
  rcases family_descends (prefixWord ++ tailWord_1172434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1172445 : List Nat := [1, 4, 3, 1, 2, 1, 3, 7]
def baseStart_1172445 : Nat := 118140960795 + 1172445 * 2 ^ 59
def prefixEnd_1172445 : Nat := 4983230072969 + 3 ^ 40 * 1172445 * 2
def baseEnd_1172445 : Nat := 44594653774871891647817

theorem tailTrace_1172445 : CollatzResearch.WordTrace tailWord_1172445 prefixEnd_1172445 44594653774871891647817 := by
  unfold tailWord_1172445
  simp only [CollatzResearch.WordTrace]
  refine ⟨42762582237439477509374789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28508388158292985006249859 42762582237439477509374789)
  ·
    refine ⟨8017984169519902033007773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 42762582237439477509374789 8017984169519902033007773)
    ·
      refine ⟨3006744063569963262377915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8017984169519902033007773 3006744063569963262377915)
      ·
        refine ⟨4510116095354944893566873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3006744063569963262377915 4510116095354944893566873)
        ·
          refine ⟨3382587071516208670175155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4510116095354944893566873 3382587071516208670175155)
          ·
            refine ⟨5073880607274313005262733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3382587071516208670175155 5073880607274313005262733)
            ·
              refine ⟨1902705227727867376973525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5073880607274313005262733 1902705227727867376973525)
              ·
                refine ⟨44594653774871891647817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1902705227727867376973525 44594653774871891647817)
                ·
                  rfl

theorem cell22_1172445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 3, 7].length) (baseStart_1172445 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1172445 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1172445 prefixEnd_1172445 := by exact prefixLift 1172445
  have htrace : WordTrace (prefixWord ++ tailWord_1172445) baseStart_1172445 baseEnd_1172445 := by
    simpa [prefixWord, tailWord_1172445, baseEnd_1172445] using wordTrace_append hprefix tailTrace_1172445
  have hstable : (prefixWord ++ tailWord_1172445).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1172445).length < 2 ^ (prefixWord ++ tailWord_1172445).sum := by decide
  have hdescent : baseEnd_1172445 < baseStart_1172445 := by decide
  rcases family_descends (prefixWord ++ tailWord_1172445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1172462 : List Nat := [4, 1, 2, 1, 4, 1, 3, 6]
def baseStart_1172462 : Nat := 118140960795 + 1172462 * 2 ^ 59
def prefixEnd_1172462 : Nat := 4983230072969 + 3 ^ 40 * 1172462 * 2
def baseEnd_1172462 : Nat := 44595300380140516350589

theorem tailTrace_1172462 : CollatzResearch.WordTrace tailWord_1172462 prefixEnd_1172462 44595300380140516350589 := by
  unfold tailWord_1172462
  simp only [CollatzResearch.WordTrace]
  refine ⟨5345400284797236176592955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28508801518918592941829093 5345400284797236176592955)
  ·
    refine ⟨8018100427195854264889433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5345400284797236176592955 8018100427195854264889433)
    ·
      refine ⟨6013575320396890698667075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8018100427195854264889433 6013575320396890698667075)
      ·
        refine ⟨9020362980595336048000613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6013575320396890698667075 9020362980595336048000613)
        ·
          refine ⟨1691318058861625509000115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9020362980595336048000613 1691318058861625509000115)
          ·
            refine ⟨2536977088292438263500173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1691318058861625509000115 2536977088292438263500173)
            ·
              refine ⟨951366408109664348812565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2536977088292438263500173 951366408109664348812565)
              ·
                refine ⟨44595300380140516350589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 951366408109664348812565 44595300380140516350589)
                ·
                  rfl

theorem cell22_1172462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 3, 6].length) (baseStart_1172462 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1172462 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1172462 prefixEnd_1172462 := by exact prefixLift 1172462
  have htrace : WordTrace (prefixWord ++ tailWord_1172462) baseStart_1172462 baseEnd_1172462 := by
    simpa [prefixWord, tailWord_1172462, baseEnd_1172462] using wordTrace_append hprefix tailTrace_1172462
  have hstable : (prefixWord ++ tailWord_1172462).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1172462).length < 2 ^ (prefixWord ++ tailWord_1172462).sum := by decide
  have hdescent : baseEnd_1172462 < baseStart_1172462 := by decide
  rcases family_descends (prefixWord ++ tailWord_1172462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1172473 : List Nat := [1, 2, 1, 3, 1, 3, 2, 2, 7]
def baseStart_1172473 : Nat := 118140960795 + 1172473 * 2 ^ 59
def prefixEnd_1172473 : Nat := 4983230072969 + 3 ^ 40 * 1172473 * 2
def baseEnd_1172473 : Nat := 133787156315354761710089

theorem tailTrace_1172473 : CollatzResearch.WordTrace tailWord_1172473 prefixEnd_1172473 133787156315354761710089 := by
  unfold tailWord_1172473
  simp only [CollatzResearch.WordTrace]
  refine ⟨42763603481338038291394073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28509068987558692194262715 42763603481338038291394073)
  ·
    refine ⟨32072702611003528718545555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42763603481338038291394073 32072702611003528718545555)
    ·
      refine ⟨48109053916505293077818333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32072702611003528718545555 48109053916505293077818333)
      ·
        refine ⟨18040895218689484904181875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48109053916505293077818333 18040895218689484904181875)
        ·
          refine ⟨27061342828034227356272813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18040895218689484904181875 27061342828034227356272813)
          ·
            refine ⟨10148003560512835258602305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27061342828034227356272813 10148003560512835258602305)
            ·
              refine ⟨7611002670384626443951729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10148003560512835258602305 7611002670384626443951729)
              ·
                refine ⟨5708252002788469832963797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7611002670384626443951729 5708252002788469832963797)
                ·
                  refine ⟨133787156315354761710089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5708252002788469832963797 133787156315354761710089)
                  ·
                    rfl

theorem cell22_1172473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 2, 7].length) (baseStart_1172473 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1172473 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1172473 prefixEnd_1172473 := by exact prefixLift 1172473
  have htrace : WordTrace (prefixWord ++ tailWord_1172473) baseStart_1172473 baseEnd_1172473 := by
    simpa [prefixWord, tailWord_1172473, baseEnd_1172473] using wordTrace_append hprefix tailTrace_1172473
  have hstable : (prefixWord ++ tailWord_1172473).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1172473).length < 2 ^ (prefixWord ++ tailWord_1172473).sum := by decide
  have hdescent : baseEnd_1172473 < baseStart_1172473 := by decide
  rcases family_descends (prefixWord ++ tailWord_1172473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1172490 : List Nat := [3, 1, 2, 2, 3, 2, 1, 1, 7]
def baseStart_1172490 : Nat := 118140960795 + 1172490 * 2 ^ 59
def prefixEnd_1172490 : Nat := 4983230072969 + 3 ^ 40 * 1172490 * 2
def baseEnd_1172490 : Nat := 133789096131160635818405

theorem tailTrace_1172490 : CollatzResearch.WordTrace tailWord_1172490 prefixEnd_1172490 133789096131160635818405 := by
  unfold tailWord_1172490
  simp only [CollatzResearch.WordTrace]
  refine ⟨10691055880569112548690731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28509482348184300129841949 10691055880569112548690731)
  ·
    refine ⟨16036583820853668823036097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10691055880569112548690731 16036583820853668823036097)
    ·
      refine ⟨12027437865640251617277073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16036583820853668823036097 12027437865640251617277073)
      ·
        refine ⟨9020578399230188712957805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12027437865640251617277073 9020578399230188712957805)
        ·
          refine ⟨3382716899711320767359177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9020578399230188712957805 3382716899711320767359177)
          ·
            refine ⟨2537037674783490575519383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3382716899711320767359177 2537037674783490575519383)
            ·
              refine ⟨3805556512175235863279075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2537037674783490575519383 3805556512175235863279075)
              ·
                refine ⟨5708334768262853794918613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3805556512175235863279075 5708334768262853794918613)
                ·
                  refine ⟨133789096131160635818405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5708334768262853794918613 133789096131160635818405)
                  ·
                    rfl

theorem cell22_1172490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 1, 1, 7].length) (baseStart_1172490 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1172490 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1172490 prefixEnd_1172490 := by exact prefixLift 1172490
  have htrace : WordTrace (prefixWord ++ tailWord_1172490) baseStart_1172490 baseEnd_1172490 := by
    simpa [prefixWord, tailWord_1172490, baseEnd_1172490] using wordTrace_append hprefix tailTrace_1172490
  have hstable : (prefixWord ++ tailWord_1172490).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1172490).length < 2 ^ (prefixWord ++ tailWord_1172490).sum := by decide
  have hdescent : baseEnd_1172490 < baseStart_1172490 := by decide
  rcases family_descends (prefixWord ++ tailWord_1172490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1172494 : List Nat := [4, 1, 1, 2, 2, 2, 2, 4, 1, 3]
def baseStart_1172494 : Nat := 118140960795 + 1172494 * 2 ^ 59
def prefixEnd_1172494 : Nat := 4983230072969 + 3 ^ 40 * 1172494 * 2
def baseEnd_1172494 : Nat := 401368657675227230355203

theorem tailTrace_1172494 : CollatzResearch.WordTrace tailWord_1172494 prefixEnd_1172494 401368657675227230355203 := by
  unfold tailWord_1172494
  simp only [CollatzResearch.WordTrace]
  refine ⟨5345546176782744859738567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28509579609507972585272357 5345546176782744859738567)
  ·
    refine ⟨8018319265174117289607851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5345546176782744859738567 8018319265174117289607851)
    ·
      refine ⟨12027478897761175934411777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8018319265174117289607851 12027478897761175934411777)
      ·
        refine ⟨9020609173320881950808833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12027478897761175934411777 9020609173320881950808833)
        ·
          refine ⟨6765456879990661463106625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9020609173320881950808833 6765456879990661463106625)
          ·
            refine ⟨5074092659992996097329969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6765456879990661463106625 5074092659992996097329969)
            ·
              refine ⟨3805569494994747072997477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5074092659992996097329969 3805569494994747072997477)
              ·
                refine ⟨713544280311515076187027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3805569494994747072997477 713544280311515076187027)
                ·
                  refine ⟨1070316420467272614280541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 713544280311515076187027 1070316420467272614280541)
                  ·
                    refine ⟨401368657675227230355203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1070316420467272614280541 401368657675227230355203)
                    ·
                      rfl

theorem cell22_1172494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 2, 4, 1, 3].length) (baseStart_1172494 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1172494 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1172494 prefixEnd_1172494 := by exact prefixLift 1172494
  have htrace : WordTrace (prefixWord ++ tailWord_1172494) baseStart_1172494 baseEnd_1172494 := by
    simpa [prefixWord, tailWord_1172494, baseEnd_1172494] using wordTrace_append hprefix tailTrace_1172494
  have hstable : (prefixWord ++ tailWord_1172494).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1172494).length < 2 ^ (prefixWord ++ tailWord_1172494).sum := by decide
  have hdescent : baseEnd_1172494 < baseStart_1172494 := by decide
  rcases family_descends (prefixWord ++ tailWord_1172494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1172537 : List Nat := [1, 2, 1, 5, 2, 1, 2, 3, 1, 4]
def baseStart_1172537 : Nat := 118140960795 + 1172537 * 2 ^ 59
def prefixEnd_1172537 : Nat := 4983230072969 + 3 ^ 40 * 1172537 * 2
def baseEnd_1172537 : Nat := 401383377453989451530071

theorem tailTrace_1172537 : CollatzResearch.WordTrace tailWord_1172537 prefixEnd_1172537 401383377453989451530071 := by
  unfold tailWord_1172537
  simp only [CollatzResearch.WordTrace]
  refine ⟨42765937753106177221723865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28510625168737451481149243 42765937753106177221723865)
  ·
    refine ⟨32074453314829632916292899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42765937753106177221723865 32074453314829632916292899)
    ·
      refine ⟨48111679972244449374439349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32074453314829632916292899 48111679972244449374439349)
      ·
        refine ⟨4510469997397917128853689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 48111679972244449374439349 4510469997397917128853689)
        ·
          refine ⟨3382852498048437846640267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4510469997397917128853689 3382852498048437846640267)
          ·
            refine ⟨5074278747072656769960401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3382852498048437846640267 5074278747072656769960401)
            ·
              refine ⟨3805709060304492577470301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5074278747072656769960401 3805709060304492577470301)
              ·
                refine ⟨1427140897614184716551363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3805709060304492577470301 1427140897614184716551363)
                ·
                  refine ⟨2140711346421277074827045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1427140897614184716551363 2140711346421277074827045)
                  ·
                    refine ⟨401383377453989451530071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2140711346421277074827045 401383377453989451530071)
                    ·
                      rfl

theorem cell22_1172537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 2, 3, 1, 4].length) (baseStart_1172537 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1172537 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1172537 prefixEnd_1172537 := by exact prefixLift 1172537
  have htrace : WordTrace (prefixWord ++ tailWord_1172537) baseStart_1172537 baseEnd_1172537 := by
    simpa [prefixWord, tailWord_1172537, baseEnd_1172537] using wordTrace_append hprefix tailTrace_1172537
  have hstable : (prefixWord ++ tailWord_1172537).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1172537).length < 2 ^ (prefixWord ++ tailWord_1172537).sum := by decide
  have hdescent : baseEnd_1172537 < baseStart_1172537 := by decide
  rcases family_descends (prefixWord ++ tailWord_1172537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1172563 : List Nat := [1, 1, 1, 2, 1, 1, 2, 13]
def baseStart_1172563 : Nat := 118140960795 + 1172563 * 2 ^ 59
def prefixEnd_1172563 : Nat := 4983230072969 + 3 ^ 40 * 1172563 * 2
def baseEnd_1172563 : Nat := 44599141976148227819999

theorem tailTrace_1172563 : CollatzResearch.WordTrace tailWord_1172563 prefixEnd_1172563 44599141976148227819999 := by
  unfold tailWord_1172563
  simp only [CollatzResearch.WordTrace]
  refine ⟨42766886051011983662170343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28511257367341322441446895 42766886051011983662170343)
  ·
    refine ⟨64150329076517975493255515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42766886051011983662170343 64150329076517975493255515)
    ·
      refine ⟨96225493614776963239883273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64150329076517975493255515 96225493614776963239883273)
      ·
        refine ⟨72169120211082722429912455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96225493614776963239883273 72169120211082722429912455)
        ·
          refine ⟨108253680316624083644868683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72169120211082722429912455 108253680316624083644868683)
          ·
            refine ⟨162380520474936125467303025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108253680316624083644868683 162380520474936125467303025)
            ·
              refine ⟨121785390356202094100477269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 162380520474936125467303025 121785390356202094100477269)
              ·
                refine ⟨44599141976148227819999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 13 121785390356202094100477269 44599141976148227819999)
                ·
                  rfl

theorem cell22_1172563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 13].length) (baseStart_1172563 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1172563 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1172563 prefixEnd_1172563 := by exact prefixLift 1172563
  have htrace : WordTrace (prefixWord ++ tailWord_1172563) baseStart_1172563 baseEnd_1172563 := by
    simpa [prefixWord, tailWord_1172563, baseEnd_1172563] using wordTrace_append hprefix tailTrace_1172563
  have hstable : (prefixWord ++ tailWord_1172563).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1172563).length < 2 ^ (prefixWord ++ tailWord_1172563).sum := by decide
  have hdescent : baseEnd_1172563 < baseStart_1172563 := by decide
  rcases family_descends (prefixWord ++ tailWord_1172563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1172565 : List Nat := [1, 3, 2, 2, 1, 2, 1, 2, 4, 4]
def baseStart_1172565 : Nat := 118140960795 + 1172565 * 2 ^ 59
def prefixEnd_1172565 : Nat := 4983230072969 + 3 ^ 40 * 1172565 * 2
def baseEnd_1172565 : Nat := 401392962426206711829985

theorem tailTrace_1172565 : CollatzResearch.WordTrace tailWord_1172565 prefixEnd_1172565 401392962426206711829985 := by
  unfold tailWord_1172565
  simp only [CollatzResearch.WordTrace]
  refine ⟨42766958997004738003743149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28511305998003158669162099 42766958997004738003743149)
  ·
    refine ⟨16037609623876776751403681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42766958997004738003743149 16037609623876776751403681)
    ·
      refine ⟨12028207217907582563552761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16037609623876776751403681 12028207217907582563552761)
      ·
        refine ⟨9021155413430686922664571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12028207217907582563552761 9021155413430686922664571)
        ·
          refine ⟨13531733120146030383996857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9021155413430686922664571 13531733120146030383996857)
          ·
            refine ⟨10148799840109522787997643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13531733120146030383996857 10148799840109522787997643)
            ·
              refine ⟨15223199760164284181996465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10148799840109522787997643 15223199760164284181996465)
              ·
                refine ⟨11417399820123213136497349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15223199760164284181996465 11417399820123213136497349)
                ·
                  refine ⟨2140762466273102463093253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11417399820123213136497349 2140762466273102463093253)
                  ·
                    refine ⟨401392962426206711829985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2140762466273102463093253 401392962426206711829985)
                    ·
                      rfl

theorem cell22_1172565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 2, 4, 4].length) (baseStart_1172565 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1172565 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1172565 prefixEnd_1172565 := by exact prefixLift 1172565
  have htrace : WordTrace (prefixWord ++ tailWord_1172565) baseStart_1172565 baseEnd_1172565 := by
    simpa [prefixWord, tailWord_1172565, baseEnd_1172565] using wordTrace_append hprefix tailTrace_1172565
  have hstable : (prefixWord ++ tailWord_1172565).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1172565).length < 2 ^ (prefixWord ++ tailWord_1172565).sum := by decide
  have hdescent : baseEnd_1172565 < baseStart_1172565 := by decide
  rcases family_descends (prefixWord ++ tailWord_1172565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1172584 : List Nat := [2, 1, 4, 4, 1, 1, 1, 2, 1, 5]
def baseStart_1172584 : Nat := 118140960795 + 1172584 * 2 ^ 59
def prefixEnd_1172584 : Nat := 4983230072969 + 3 ^ 40 * 1172584 * 2
def baseEnd_1172584 : Nat := 401399466514496995604927

theorem tailTrace_1172584 : CollatzResearch.WordTrace tailWord_1172584 prefixEnd_1172584 401399466514496995604927 := by
  unfold tailWord_1172584
  simp only [CollatzResearch.WordTrace]
  refine ⟨21383825991967952124342403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28511767989290602832456537 21383825991967952124342403)
  ·
    refine ⟨32075738987951928186513605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21383825991967952124342403 32075738987951928186513605)
    ·
      refine ⟨6014201060240986534971301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32075738987951928186513605 6014201060240986534971301)
      ·
        refine ⟨1127662698795184975307119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6014201060240986534971301 1127662698795184975307119)
        ·
          refine ⟨1691494048192777462960679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1127662698795184975307119 1691494048192777462960679)
          ·
            refine ⟨2537241072289166194441019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1691494048192777462960679 2537241072289166194441019)
            ·
              refine ⟨3805861608433749291661529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2537241072289166194441019 3805861608433749291661529)
              ·
                refine ⟨2854396206325311968746147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3805861608433749291661529 2854396206325311968746147)
                ·
                  refine ⟨4281594309487967953119221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2854396206325311968746147 4281594309487967953119221)
                  ·
                    refine ⟨401399466514496995604927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4281594309487967953119221 401399466514496995604927)
                    ·
                      rfl

theorem cell22_1172584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 1, 2, 1, 5].length) (baseStart_1172584 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1172584 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1172584 prefixEnd_1172584 := by exact prefixLift 1172584
  have htrace : WordTrace (prefixWord ++ tailWord_1172584) baseStart_1172584 baseEnd_1172584 := by
    simpa [prefixWord, tailWord_1172584, baseEnd_1172584] using wordTrace_append hprefix tailTrace_1172584
  have hstable : (prefixWord ++ tailWord_1172584).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1172584).length < 2 ^ (prefixWord ++ tailWord_1172584).sum := by decide
  have hdescent : baseEnd_1172584 < baseStart_1172584 := by decide
  rcases family_descends (prefixWord ++ tailWord_1172584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1172597 : List Nat := [1, 3, 4, 3, 1, 10]
def baseStart_1172597 : Nat := 118140960795 + 1172597 * 2 ^ 59
def prefixEnd_1172597 : Nat := 4983230072969 + 3 ^ 40 * 1172597 * 2
def baseEnd_1172597 : Nat := 4955603909631719691727

theorem tailTrace_1172597 : CollatzResearch.WordTrace tailWord_1172597 prefixEnd_1172597 4955603909631719691727 := by
  unfold tailWord_1172597
  simp only [CollatzResearch.WordTrace]
  refine ⟨42768126132888807468908045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28512084088592538312605363 42768126132888807468908045)
  ·
    refine ⟨16038047299833302800840517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42768126132888807468908045 16038047299833302800840517)
    ·
      refine ⟨3007133868718744275157597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16038047299833302800840517 3007133868718744275157597)
      ·
        refine ⟨1127675200769529103184099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3007133868718744275157597 1127675200769529103184099)
        ·
          refine ⟨1691512801154293654776149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1127675200769529103184099 1691512801154293654776149)
          ·
            refine ⟨4955603909631719691727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 1691512801154293654776149 4955603909631719691727)
            ·
              rfl

theorem cell22_1172597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 10].length) (baseStart_1172597 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1172597 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1172597 prefixEnd_1172597 := by exact prefixLift 1172597
  have htrace : WordTrace (prefixWord ++ tailWord_1172597) baseStart_1172597 baseEnd_1172597 := by
    simpa [prefixWord, tailWord_1172597, baseEnd_1172597] using wordTrace_append hprefix tailTrace_1172597
  have hstable : (prefixWord ++ tailWord_1172597).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1172597).length < 2 ^ (prefixWord ++ tailWord_1172597).sum := by decide
  have hdescent : baseEnd_1172597 < baseStart_1172597 := by decide
  rcases family_descends (prefixWord ++ tailWord_1172597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1172640 : List Nat := [2, 1, 1, 4, 2, 1, 1, 2, 1, 7]
def baseStart_1172640 : Nat := 118140960795 + 1172640 * 2 ^ 59
def prefixEnd_1172640 : Nat := 4983230072969 + 3 ^ 40 * 1172640 * 2
def baseEnd_1172640 : Nat := 401418636458931516204755

theorem tailTrace_1172640 : CollatzResearch.WordTrace tailWord_1172640 prefixEnd_1172640 401418636458931516204755 := by
  unfold tailWord_1172640
  simp only [CollatzResearch.WordTrace]
  refine ⟨21384847235866512906361687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28513129647822017208482249 21384847235866512906361687)
  ·
    refine ⟨32077270853799769359542531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21384847235866512906361687 32077270853799769359542531)
    ·
      refine ⟨48115906280699654039313797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32077270853799769359542531 48115906280699654039313797)
      ·
        refine ⟨9021732427631185132371337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 48115906280699654039313797 9021732427631185132371337)
        ·
          refine ⟨6766299320723388849278503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9021732427631185132371337 6766299320723388849278503)
          ·
            refine ⟨10149448981085083273917755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6766299320723388849278503 10149448981085083273917755)
            ·
              refine ⟨15224173471627624910876633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10149448981085083273917755 15224173471627624910876633)
              ·
                refine ⟨11418130103720718683157475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15224173471627624910876633 11418130103720718683157475)
                ·
                  refine ⟨17127195155581078024736213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11418130103720718683157475 17127195155581078024736213)
                  ·
                    refine ⟨401418636458931516204755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 17127195155581078024736213 401418636458931516204755)
                    ·
                      rfl

theorem cell22_1172640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 2, 1, 7].length) (baseStart_1172640 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1172640 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1172640 prefixEnd_1172640 := by exact prefixLift 1172640
  have htrace : WordTrace (prefixWord ++ tailWord_1172640) baseStart_1172640 baseEnd_1172640 := by
    simpa [prefixWord, tailWord_1172640, baseEnd_1172640] using wordTrace_append hprefix tailTrace_1172640
  have hstable : (prefixWord ++ tailWord_1172640).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1172640).length < 2 ^ (prefixWord ++ tailWord_1172640).sum := by decide
  have hdescent : baseEnd_1172640 < baseStart_1172640 := by decide
  rcases family_descends (prefixWord ++ tailWord_1172640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1172657 : List Nat := [1, 2, 2, 5, 1, 1, 1, 2, 2, 5]
def baseStart_1172657 : Nat := 118140960795 + 1172657 * 2 ^ 59
def prefixEnd_1172657 : Nat := 4983230072969 + 3 ^ 40 * 1172657 * 2
def baseEnd_1172657 : Nat := 401424455906349138529703

theorem tailTrace_1172657 : CollatzResearch.WordTrace tailWord_1172657 prefixEnd_1172657 401424455906349138529703 := by
  unfold tailWord_1172657
  simp only [CollatzResearch.WordTrace]
  refine ⟨42770314512671437716092225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28513543008447625144061483 42770314512671437716092225)
  ·
    refine ⟨32077735884503578287069169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42770314512671437716092225 32077735884503578287069169)
    ·
      refine ⟨24058301913377683715301877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32077735884503578287069169 24058301913377683715301877)
      ·
        refine ⟨2255465804379157848309551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 24058301913377683715301877 2255465804379157848309551)
        ·
          refine ⟨3383198706568736772464327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2255465804379157848309551 3383198706568736772464327)
          ·
            refine ⟨5074798059853105158696491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3383198706568736772464327 5074798059853105158696491)
            ·
              refine ⟨7612197089779657738044737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5074798059853105158696491 7612197089779657738044737)
              ·
                refine ⟨5709147817334743303533553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7612197089779657738044737 5709147817334743303533553)
                ·
                  refine ⟨4281860863001057477650165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5709147817334743303533553 4281860863001057477650165)
                  ·
                    refine ⟨401424455906349138529703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4281860863001057477650165 401424455906349138529703)
                    ·
                      rfl

theorem cell22_1172657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 2, 2, 5].length) (baseStart_1172657 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1172657 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1172657 prefixEnd_1172657 := by exact prefixLift 1172657
  have htrace : WordTrace (prefixWord ++ tailWord_1172657) baseStart_1172657 baseEnd_1172657 := by
    simpa [prefixWord, tailWord_1172657, baseEnd_1172657] using wordTrace_append hprefix tailTrace_1172657
  have hstable : (prefixWord ++ tailWord_1172657).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1172657).length < 2 ^ (prefixWord ++ tailWord_1172657).sum := by decide
  have hdescent : baseEnd_1172657 < baseStart_1172657 := by decide
  rcases family_descends (prefixWord ++ tailWord_1172657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1172676 : List Nat := [2, 3, 3, 1, 3, 1, 3, 1, 5]
def baseStart_1172676 : Nat := 118140960795 + 1172676 * 2 ^ 59
def prefixEnd_1172676 : Nat := 4983230072969 + 3 ^ 40 * 1172676 * 2
def baseEnd_1172676 : Nat := 133810319998213140768215

theorem tailTrace_1172676 : CollatzResearch.WordTrace tailWord_1172676 prefixEnd_1172676 133810319998213140768215 := by
  unfold tailWord_1172676
  simp only [CollatzResearch.WordTrace]
  refine ⟨21385503749801301980516941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28514004999735069307355921 21385503749801301980516941)
  ·
    refine ⟨8019563906175488242693853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21385503749801301980516941 8019563906175488242693853)
    ·
      refine ⟨3007336464815808091010195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8019563906175488242693853 3007336464815808091010195)
      ·
        refine ⟨4511004697223712136515293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3007336464815808091010195 4511004697223712136515293)
        ·
          refine ⟨1691626761458892051193235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4511004697223712136515293 1691626761458892051193235)
          ·
            refine ⟨2537440142188338076789853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1691626761458892051193235 2537440142188338076789853)
            ·
              refine ⟨951540053320626778796195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2537440142188338076789853 951540053320626778796195)
              ·
                refine ⟨1427310079980940168194293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 951540053320626778796195 1427310079980940168194293)
                ·
                  refine ⟨133810319998213140768215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1427310079980940168194293 133810319998213140768215)
                  ·
                    rfl

theorem cell22_1172676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 3, 1, 5].length) (baseStart_1172676 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1172676 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1172676 prefixEnd_1172676 := by exact prefixLift 1172676
  have htrace : WordTrace (prefixWord ++ tailWord_1172676) baseStart_1172676 baseEnd_1172676 := by
    simpa [prefixWord, tailWord_1172676, baseEnd_1172676] using wordTrace_append hprefix tailTrace_1172676
  have hstable : (prefixWord ++ tailWord_1172676).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1172676).length < 2 ^ (prefixWord ++ tailWord_1172676).sum := by decide
  have hdescent : baseEnd_1172676 < baseStart_1172676 := by decide
  rcases family_descends (prefixWord ++ tailWord_1172676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1172704 : List Nat := [2, 1, 1, 3, 1, 4, 3, 3, 4]
def baseStart_1172704 : Nat := 118140960795 + 1172704 * 2 ^ 59
def prefixEnd_1172704 : Nat := 4983230072969 + 3 ^ 40 * 1172704 * 2
def baseEnd_1172704 : Nat := 133813514988952227534853

theorem tailTrace_1172704 : CollatzResearch.WordTrace tailWord_1172704 prefixEnd_1172704 133813514988952227534853 := by
  unfold tailWord_1172704
  simp only [CollatzResearch.WordTrace]
  refine ⟨21386014371750582371526583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28514685829000776495368777 21386014371750582371526583)
  ·
    refine ⟨32079021557625873557289875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21386014371750582371526583 32079021557625873557289875)
    ·
      refine ⟨48118532336438810335934813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32079021557625873557289875 48118532336438810335934813)
      ·
        refine ⟨18044449626164553875975555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48118532336438810335934813 18044449626164553875975555)
        ·
          refine ⟨27066674439246830813963333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18044449626164553875975555 27066674439246830813963333)
          ·
            refine ⟨5075001457358780777618125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27066674439246830813963333 5075001457358780777618125)
            ·
              refine ⟨1903125546509542791606797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5075001457358780777618125 1903125546509542791606797)
              ·
                refine ⟨713672079941078546852549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1903125546509542791606797 713672079941078546852549)
                ·
                  refine ⟨133813514988952227534853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 713672079941078546852549 133813514988952227534853)
                  ·
                    rfl

theorem cell22_1172704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 3, 3, 4].length) (baseStart_1172704 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1172704 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1172704 prefixEnd_1172704 := by exact prefixLift 1172704
  have htrace : WordTrace (prefixWord ++ tailWord_1172704) baseStart_1172704 baseEnd_1172704 := by
    simpa [prefixWord, tailWord_1172704, baseEnd_1172704] using wordTrace_append hprefix tailTrace_1172704
  have hstable : (prefixWord ++ tailWord_1172704).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1172704).length < 2 ^ (prefixWord ++ tailWord_1172704).sum := by decide
  have hdescent : baseEnd_1172704 < baseStart_1172704 := by decide
  rcases family_descends (prefixWord ++ tailWord_1172704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1172715 : List Nat := [1, 1, 1, 1, 2, 6, 10]
def baseStart_1172715 : Nat := 118140960795 + 1172715 * 2 ^ 59
def prefixEnd_1172715 : Nat := 4983230072969 + 3 ^ 40 * 1172715 * 2
def baseEnd_1172715 : Nat := 14868307795987271132575

theorem tailTrace_1172715 : CollatzResearch.WordTrace tailWord_1172715 prefixEnd_1172715 14868307795987271132575 := by
  unfold tailWord_1172715
  simp only [CollatzResearch.WordTrace]
  refine ⟨42772429946461313621703599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28514953297640875747802399 42772429946461313621703599)
  ·
    refine ⟨64158644919691970432555399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42772429946461313621703599 64158644919691970432555399)
    ·
      refine ⟨96237967379537955648833099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64158644919691970432555399 96237967379537955648833099)
      ·
        refine ⟨144356951069306933473249649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96237967379537955648833099 144356951069306933473249649)
        ·
          refine ⟨108267713301980200104937237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 144356951069306933473249649 108267713301980200104937237)
          ·
            refine ⟨5075049061030321879918933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 108267713301980200104937237 5075049061030321879918933)
            ·
              refine ⟨14868307795987271132575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 5075049061030321879918933 14868307795987271132575)
              ·
                rfl

theorem cell22_1172715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 10].length) (baseStart_1172715 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1172715 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1172715 prefixEnd_1172715 := by exact prefixLift 1172715
  have htrace : WordTrace (prefixWord ++ tailWord_1172715) baseStart_1172715 baseEnd_1172715 := by
    simpa [prefixWord, tailWord_1172715, baseEnd_1172715] using wordTrace_append hprefix tailTrace_1172715
  have hstable : (prefixWord ++ tailWord_1172715).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1172715).length < 2 ^ (prefixWord ++ tailWord_1172715).sum := by decide
  have hdescent : baseEnd_1172715 < baseStart_1172715 := by decide
  rcases family_descends (prefixWord ++ tailWord_1172715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1172766 : List Nat := [4, 3, 2, 1, 3, 9]
def baseStart_1172766 : Nat := 118140960795 + 1172766 * 2 ^ 59
def prefixEnd_1172766 : Nat := 4983230072969 + 3 ^ 40 * 1172766 * 2
def baseEnd_1172766 : Nat := 4956318133751965278449

theorem tailTrace_1172766 : CollatzResearch.WordTrace tailWord_1172766 prefixEnd_1172766 4956318133751965278449 := by
  unfold tailWord_1172766
  simp only [CollatzResearch.WordTrace]
  refine ⟨5346786258659568666476269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28516193379517699554540101 5346786258659568666476269)
  ·
    refine ⟨2005044846997338249928601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5346786258659568666476269 2005044846997338249928601)
    ·
      refine ⟨1503783635248003687446451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2005044846997338249928601 1503783635248003687446451)
      ·
        refine ⟨2255675452872005531169677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1503783635248003687446451 2255675452872005531169677)
        ·
          refine ⟨845878294827002074188629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2255675452872005531169677 845878294827002074188629)
          ·
            refine ⟨4956318133751965278449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 845878294827002074188629 4956318133751965278449)
            ·
              rfl

theorem cell22_1172766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 3, 9].length) (baseStart_1172766 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1172766 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1172766 prefixEnd_1172766 := by exact prefixLift 1172766
  have htrace : WordTrace (prefixWord ++ tailWord_1172766) baseStart_1172766 baseEnd_1172766 := by
    simpa [prefixWord, tailWord_1172766, baseEnd_1172766] using wordTrace_append hprefix tailTrace_1172766
  have hstable : (prefixWord ++ tailWord_1172766).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1172766).length < 2 ^ (prefixWord ++ tailWord_1172766).sum := by decide
  have hdescent : baseEnd_1172766 < baseStart_1172766 := by decide
  rcases family_descends (prefixWord ++ tailWord_1172766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1172824 : List Nat := [2, 1, 2, 2, 1, 1, 5, 3, 1, 4]
def baseStart_1172824 : Nat := 118140960795 + 1172824 * 2 ^ 59
def prefixEnd_1172824 : Nat := 4983230072969 + 3 ^ 40 * 1172824 * 2
def baseEnd_1172824 : Nat := 401481623419216369604191

theorem tailTrace_1172824 : CollatzResearch.WordTrace tailWord_1172824 prefixEnd_1172824 401481623419216369604191 := by
  unfold tailWord_1172824
  simp only [CollatzResearch.WordTrace]
  refine ⟨21388202751533212618710763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28517603668710950158281017 21388202751533212618710763)
  ·
    refine ⟨32082304127299818928066145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21388202751533212618710763 32082304127299818928066145)
    ·
      refine ⟨24061728095474864196049609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32082304127299818928066145 24061728095474864196049609)
      ·
        refine ⟨18046296071606148147037207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24061728095474864196049609 18046296071606148147037207)
        ·
          refine ⟨27069444107409222220555811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18046296071606148147037207 27069444107409222220555811)
          ·
            refine ⟨40604166161113833330833717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27069444107409222220555811 40604166161113833330833717)
            ·
              refine ⟨3806640577604421874765661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 40604166161113833330833717 3806640577604421874765661)
              ·
                refine ⟨1427490216601658203037123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3806640577604421874765661 1427490216601658203037123)
                ·
                  refine ⟨2141235324902487304555685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1427490216601658203037123 2141235324902487304555685)
                  ·
                    refine ⟨401481623419216369604191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2141235324902487304555685 401481623419216369604191)
                    ·
                      rfl

theorem cell22_1172824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 5, 3, 1, 4].length) (baseStart_1172824 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1172824 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1172824 prefixEnd_1172824 := by exact prefixLift 1172824
  have htrace : WordTrace (prefixWord ++ tailWord_1172824) baseStart_1172824 baseEnd_1172824 := by
    simpa [prefixWord, tailWord_1172824, baseEnd_1172824] using wordTrace_append hprefix tailTrace_1172824
  have hstable : (prefixWord ++ tailWord_1172824).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1172824).length < 2 ^ (prefixWord ++ tailWord_1172824).sum := by decide
  have hdescent : baseEnd_1172824 < baseStart_1172824 := by decide
  rcases family_descends (prefixWord ++ tailWord_1172824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1172873 : List Nat := [1, 2, 1, 1, 7, 2, 1, 3, 4]
def baseStart_1172873 : Nat := 118140960795 + 1172873 * 2 ^ 59
def prefixEnd_1172873 : Nat := 4983230072969 + 3 ^ 40 * 1172873 * 2
def baseEnd_1172873 : Nat := 133832799040198858376347

theorem tailTrace_1172873 : CollatzResearch.WordTrace tailWord_1172873 prefixEnd_1172873 133832799040198858376347 := by
  unfold tailWord_1172873
  simp only [CollatzResearch.WordTrace]
  refine ⟨42778192679888906605955273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28518795119925937737303515 42778192679888906605955273)
  ·
    refine ⟨32083644509916679954466455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42778192679888906605955273 32083644509916679954466455)
    ·
      refine ⟨48125466764875019931699683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32083644509916679954466455 48125466764875019931699683)
      ·
        refine ⟨72188200147312529897549525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48125466764875019931699683 72188200147312529897549525)
        ·
          refine ⟨1691910940952637419473817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 72188200147312529897549525 1691910940952637419473817)
          ·
            refine ⟨1268933205714478064605363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1691910940952637419473817 1268933205714478064605363)
            ·
              refine ⟨1903399808571717096908045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1268933205714478064605363 1903399808571717096908045)
              ·
                refine ⟨713774928214393911340517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1903399808571717096908045 713774928214393911340517)
                ·
                  refine ⟨133832799040198858376347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 713774928214393911340517 133832799040198858376347)
                  ·
                    rfl

theorem cell22_1172873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 2, 1, 3, 4].length) (baseStart_1172873 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1172873 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1172873 prefixEnd_1172873 := by exact prefixLift 1172873
  have htrace : WordTrace (prefixWord ++ tailWord_1172873) baseStart_1172873 baseEnd_1172873 := by
    simpa [prefixWord, tailWord_1172873, baseEnd_1172873] using wordTrace_append hprefix tailTrace_1172873
  have hstable : (prefixWord ++ tailWord_1172873).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1172873).length < 2 ^ (prefixWord ++ tailWord_1172873).sum := by decide
  have hdescent : baseEnd_1172873 < baseStart_1172873 := by decide
  rcases family_descends (prefixWord ++ tailWord_1172873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1172884 : List Nat := [2, 4, 2, 1, 2, 1, 10]
def baseStart_1172884 : Nat := 118140960795 + 1172884 * 2 ^ 59
def prefixEnd_1172884 : Nat := 4983230072969 + 3 ^ 40 * 1172884 * 2
def baseEnd_1172884 : Nat := 14870450468348007892741

theorem tailTrace_1172884 : CollatzResearch.WordTrace tailWord_1172884 prefixEnd_1172884 14870450468348007892741 := by
  unfold tailWord_1172884
  simp only [CollatzResearch.WordTrace]
  refine ⟨21389296941424527742302853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28519062588566036989737137 21389296941424527742302853)
  ·
    refine ⟨4010493176517098951681785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21389296941424527742302853 4010493176517098951681785)
    ·
      refine ⟨3007869882387824213761339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4010493176517098951681785 3007869882387824213761339)
      ·
        refine ⟨4511804823581736320642009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3007869882387824213761339 4511804823581736320642009)
        ·
          refine ⟨3383853617686302240481507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4511804823581736320642009 3383853617686302240481507)
          ·
            refine ⟨5075780426529453360722261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3383853617686302240481507 5075780426529453360722261)
            ·
              refine ⟨14870450468348007892741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 5075780426529453360722261 14870450468348007892741)
              ·
                rfl

theorem cell22_1172884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 10].length) (baseStart_1172884 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1172884 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1172884 prefixEnd_1172884 := by exact prefixLift 1172884
  have htrace : WordTrace (prefixWord ++ tailWord_1172884) baseStart_1172884 baseEnd_1172884 := by
    simpa [prefixWord, tailWord_1172884, baseEnd_1172884] using wordTrace_append hprefix tailTrace_1172884
  have hstable : (prefixWord ++ tailWord_1172884).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1172884).length < 2 ^ (prefixWord ++ tailWord_1172884).sum := by decide
  have hdescent : baseEnd_1172884 < baseStart_1172884 := by decide
  rcases family_descends (prefixWord ++ tailWord_1172884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1172912 : List Nat := [2, 1, 1, 1, 2, 1, 1, 4, 9]
def baseStart_1172912 : Nat := 118140960795 + 1172912 * 2 ^ 59
def prefixEnd_1172912 : Nat := 4983230072969 + 3 ^ 40 * 1172912 * 2
def baseEnd_1172912 : Nat := 133837249205871157801307

theorem tailTrace_1172912 : CollatzResearch.WordTrace tailWord_1172912 prefixEnd_1172912 133837249205871157801307 := by
  unfold tailWord_1172912
  simp only [CollatzResearch.WordTrace]
  refine ⟨21389807563373808133312495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28519743417831744177749993 21389807563373808133312495)
  ·
    refine ⟨32084711345060712199968743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21389807563373808133312495 32084711345060712199968743)
    ·
      refine ⟨48127067017591068299953115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32084711345060712199968743 48127067017591068299953115)
      ·
        refine ⟨72190600526386602449929673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48127067017591068299953115 72190600526386602449929673)
        ·
          refine ⟨54142950394789951837447255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72190600526386602449929673 54142950394789951837447255)
          ·
            refine ⟨81214425592184927756170883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54142950394789951837447255 81214425592184927756170883)
            ·
              refine ⟨121821638388277391634256325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81214425592184927756170883 121821638388277391634256325)
              ·
                refine ⟨22841557197802010931423061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 121821638388277391634256325 22841557197802010931423061)
                ·
                  refine ⟨133837249205871157801307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 22841557197802010931423061 133837249205871157801307)
                  ·
                    rfl

theorem cell22_1172912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 4, 9].length) (baseStart_1172912 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1172912 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1172912 prefixEnd_1172912 := by exact prefixLift 1172912
  have htrace : WordTrace (prefixWord ++ tailWord_1172912) baseStart_1172912 baseEnd_1172912 := by
    simpa [prefixWord, tailWord_1172912, baseEnd_1172912] using wordTrace_append hprefix tailTrace_1172912
  have hstable : (prefixWord ++ tailWord_1172912).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1172912).length < 2 ^ (prefixWord ++ tailWord_1172912).sum := by decide
  have hdescent : baseEnd_1172912 < baseStart_1172912 := by decide
  rcases family_descends (prefixWord ++ tailWord_1172912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1172959 : List Nat := [1, 1, 2, 3, 3, 1, 1, 1, 5, 4]
def baseStart_1172959 : Nat := 118140960795 + 1172959 * 2 ^ 59
def prefixEnd_1172959 : Nat := 4983230072969 + 3 ^ 40 * 1172959 * 2
def baseEnd_1172959 : Nat := 401527836678121017478777

theorem tailTrace_1172959 : CollatzResearch.WordTrace tailWord_1172959 prefixEnd_1172959 401527836678121017478777 := by
  unfold tailWord_1172959
  simp only [CollatzResearch.WordTrace]
  refine ⟨42781329357577343293585931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28520886238384895529057287 42781329357577343293585931)
  ·
    refine ⟨64171994036366014940378897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42781329357577343293585931 64171994036366014940378897)
    ·
      refine ⟨48128995527274511205284173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64171994036366014940378897 48128995527274511205284173)
      ·
        refine ⟨18048373322727941701981565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48128995527274511205284173 18048373322727941701981565)
        ·
          refine ⟨6768139996022978138243087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18048373322727941701981565 6768139996022978138243087)
          ·
            refine ⟨10152209994034467207364631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6768139996022978138243087 10152209994034467207364631)
            ·
              refine ⟨15228314991051700811046947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10152209994034467207364631 15228314991051700811046947)
              ·
                refine ⟨22842472486577551216570421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15228314991051700811046947 22842472486577551216570421)
                ·
                  refine ⟨2141481795616645426553477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 22842472486577551216570421 2141481795616645426553477)
                  ·
                    refine ⟨401527836678121017478777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2141481795616645426553477 401527836678121017478777)
                    ·
                      rfl

theorem cell22_1172959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 1, 5, 4].length) (baseStart_1172959 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1172959 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1172959 prefixEnd_1172959 := by exact prefixLift 1172959
  have htrace : WordTrace (prefixWord ++ tailWord_1172959) baseStart_1172959 baseEnd_1172959 := by
    simpa [prefixWord, tailWord_1172959, baseEnd_1172959] using wordTrace_append hprefix tailTrace_1172959
  have hstable : (prefixWord ++ tailWord_1172959).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1172959).length < 2 ^ (prefixWord ++ tailWord_1172959).sum := by decide
  have hdescent : baseEnd_1172959 < baseStart_1172959 := by decide
  rcases family_descends (prefixWord ++ tailWord_1172959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1172993 : List Nat := [1, 2, 4, 1, 4, 1, 1, 3, 1, 4]
def baseStart_1172993 : Nat := 118140960795 + 1172993 * 2 ^ 59
def prefixEnd_1172993 : Nat := 4983230072969 + 3 ^ 40 * 1172993 * 2
def baseEnd_1172993 : Nat := 401539475572956262128673

theorem tailTrace_1172993 : CollatzResearch.WordTrace tailWord_1172993 prefixEnd_1172993 401539475572956262128673 := by
  unfold tailWord_1172993
  simp only [CollatzResearch.WordTrace]
  refine ⟨42782569439454167100323633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28521712959636111400215755 42782569439454167100323633)
  ·
    refine ⟨32086927079590625325242725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42782569439454167100323633 32086927079590625325242725)
    ·
      refine ⟨6016298827423242248483011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32086927079590625325242725 6016298827423242248483011)
      ·
        refine ⟨9024448241134863372724517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6016298827423242248483011 9024448241134863372724517)
        ·
          refine ⟨1692084045212786882385847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9024448241134863372724517 1692084045212786882385847)
          ·
            refine ⟨2538126067819180323578771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1692084045212786882385847 2538126067819180323578771)
            ·
              refine ⟨3807189101728770485368157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2538126067819180323578771 3807189101728770485368157)
              ·
                refine ⟨1427695913148288932013059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3807189101728770485368157 1427695913148288932013059)
                ·
                  refine ⟨2141543869722433398019589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1427695913148288932013059 2141543869722433398019589)
                  ·
                    refine ⟨401539475572956262128673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2141543869722433398019589 401539475572956262128673)
                    ·
                      rfl

theorem cell22_1172993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 1, 3, 1, 4].length) (baseStart_1172993 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1172993 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1172993 prefixEnd_1172993 := by exact prefixLift 1172993
  have htrace : WordTrace (prefixWord ++ tailWord_1172993) baseStart_1172993 baseEnd_1172993 := by
    simpa [prefixWord, tailWord_1172993, baseEnd_1172993] using wordTrace_append hprefix tailTrace_1172993
  have hstable : (prefixWord ++ tailWord_1172993).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1172993).length < 2 ^ (prefixWord ++ tailWord_1172993).sum := by decide
  have hdescent : baseEnd_1172993 < baseStart_1172993 := by decide
  rcases family_descends (prefixWord ++ tailWord_1172993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1173053 : List Nat := [1, 4, 1, 3, 4, 1, 8]
def baseStart_1173053 : Nat := 118140960795 + 1173053 * 2 ^ 59
def prefixEnd_1173053 : Nat := 4983230072969 + 3 ^ 40 * 1173053 * 2
def baseEnd_1173053 : Nat := 14872593140708744652907

theorem tailTrace_1173053 : CollatzResearch.WordTrace tailWord_1173053 prefixEnd_1173053 14872593140708744652907 := by
  unfold tailWord_1173053
  simp only [CollatzResearch.WordTrace]
  refine ⟨42784757819236797347507813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28523171879491198231671875 42784757819236797347507813)
  ·
    refine ⟨8022142091106899502657715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 42784757819236797347507813 8022142091106899502657715)
    ·
      refine ⟨12033213136660349253986573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8022142091106899502657715 12033213136660349253986573)
      ·
        refine ⟨4512454926247630970244965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12033213136660349253986573 4512454926247630970244965)
        ·
          refine ⟨846085298671430806920931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4512454926247630970244965 846085298671430806920931)
          ·
            refine ⟨1269127948007146210381397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 846085298671430806920931 1269127948007146210381397)
            ·
              refine ⟨14872593140708744652907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1269127948007146210381397 14872593140708744652907)
              ·
                rfl

theorem cell22_1173053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 4, 1, 8].length) (baseStart_1173053 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1173053 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1173053 prefixEnd_1173053 := by exact prefixLift 1173053
  have htrace : WordTrace (prefixWord ++ tailWord_1173053) baseStart_1173053 baseEnd_1173053 := by
    simpa [prefixWord, tailWord_1173053, baseEnd_1173053] using wordTrace_append hprefix tailTrace_1173053
  have hstable : (prefixWord ++ tailWord_1173053).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1173053).length < 2 ^ (prefixWord ++ tailWord_1173053).sum := by decide
  have hdescent : baseEnd_1173053 < baseStart_1173053 := by decide
  rcases family_descends (prefixWord ++ tailWord_1173053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1173068 : List Nat := [2, 2, 1, 3, 1, 3, 3, 1, 3, 3]
def baseStart_1173068 : Nat := 118140960795 + 1173068 * 2 ^ 59
def prefixEnd_1173068 : Nat := 4983230072969 + 3 ^ 40 * 1173068 * 2
def baseEnd_1173068 : Nat := 401565149605681066503443

theorem tailTrace_1173068 : CollatzResearch.WordTrace tailWord_1173068 prefixEnd_1173068 401565149605681066503443 := by
  unfold tailWord_1173068
  simp only [CollatzResearch.WordTrace]
  refine ⟨21392652457091227454651929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28523536609454969939535905 21392652457091227454651929)
  ·
    refine ⟨16044489342818420590988947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21392652457091227454651929 16044489342818420590988947)
    ·
      refine ⟨24066734014227630886483421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16044489342818420590988947 24066734014227630886483421)
      ·
        refine ⟨9025025255335361582431283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24066734014227630886483421 9025025255335361582431283)
        ·
          refine ⟨13537537883003042373646925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9025025255335361582431283 13537537883003042373646925)
          ·
            refine ⟨5076576706126140890117597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13537537883003042373646925 5076576706126140890117597)
            ·
              refine ⟨1903716264797302833794099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5076576706126140890117597 1903716264797302833794099)
              ·
                refine ⟨2855574397195954250691149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1903716264797302833794099 2855574397195954250691149)
                ·
                  refine ⟨1070840398948482844009181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2855574397195954250691149 1070840398948482844009181)
                  ·
                    refine ⟨401565149605681066503443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1070840398948482844009181 401565149605681066503443)
                    ·
                      rfl

theorem cell22_1173068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 3, 1, 3, 3].length) (baseStart_1173068 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1173068 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1173068 prefixEnd_1173068 := by exact prefixLift 1173068
  have htrace : WordTrace (prefixWord ++ tailWord_1173068) baseStart_1173068 baseEnd_1173068 := by
    simpa [prefixWord, tailWord_1173068, baseEnd_1173068] using wordTrace_append hprefix tailTrace_1173068
  have hstable : (prefixWord ++ tailWord_1173068).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1173068).length < 2 ^ (prefixWord ++ tailWord_1173068).sum := by decide
  have hdescent : baseEnd_1173068 < baseStart_1173068 := by decide
  rcases family_descends (prefixWord ++ tailWord_1173068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1173175 : List Nat := [1, 1, 3, 1, 5, 1, 3, 2, 2, 3]
def baseStart_1173175 : Nat := 118140960795 + 1173175 * 2 ^ 59
def prefixEnd_1173175 : Nat := 4983230072969 + 3 ^ 40 * 1173175 * 2
def baseEnd_1173175 : Nat := 401601777892368454078115

theorem tailTrace_1173175 : CollatzResearch.WordTrace tailWord_1173175 prefixEnd_1173175 401601777892368454078115 := by
  unfold tailWord_1173175
  simp only [CollatzResearch.WordTrace]
  refine ⟨42789207524794812183448979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28526138349863208122299319 42789207524794812183448979)
  ·
    refine ⟨64183811287192218275173469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42789207524794812183448979 64183811287192218275173469)
    ·
      refine ⟨24068929232697081853190051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64183811287192218275173469 24068929232697081853190051)
      ·
        refine ⟨36103393849045622779785077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24068929232697081853190051 36103393849045622779785077)
        ·
          refine ⟨3384693173348027135604851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 36103393849045622779785077 3384693173348027135604851)
          ·
            refine ⟨5077039760022040703407277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3384693173348027135604851 5077039760022040703407277)
            ·
              refine ⟨1903889910008265263777729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5077039760022040703407277 1903889910008265263777729)
              ·
                refine ⟨1427917432506198947833297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1903889910008265263777729 1427917432506198947833297)
                ·
                  refine ⟨1070938074379649210874973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1427917432506198947833297 1070938074379649210874973)
                  ·
                    refine ⟨401601777892368454078115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1070938074379649210874973 401601777892368454078115)
                    ·
                      rfl

theorem cell22_1173175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 3, 2, 2, 3].length) (baseStart_1173175 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1173175 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1173175 prefixEnd_1173175 := by exact prefixLift 1173175
  have htrace : WordTrace (prefixWord ++ tailWord_1173175) baseStart_1173175 baseEnd_1173175 := by
    simpa [prefixWord, tailWord_1173175, baseEnd_1173175] using wordTrace_append hprefix tailTrace_1173175
  have hstable : (prefixWord ++ tailWord_1173175).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1173175).length < 2 ^ (prefixWord ++ tailWord_1173175).sum := by decide
  have hdescent : baseEnd_1173175 < baseStart_1173175 := by decide
  rcases family_descends (prefixWord ++ tailWord_1173175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1173216 : List Nat := [2, 1, 1, 3, 1, 2, 3, 2, 7]
def baseStart_1173216 : Nat := 118140960795 + 1173216 * 2 ^ 59
def prefixEnd_1173216 : Nat := 4983230072969 + 3 ^ 40 * 1173216 * 2
def baseEnd_1173216 : Nat := 133871937676752671267663

theorem tailTrace_1173216 : CollatzResearch.WordTrace tailWord_1173216 prefixEnd_1173216 133871937676752671267663 := by
  unfold tailWord_1173216
  simp only [CollatzResearch.WordTrace]
  refine ⟨21395351458823138092845751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28527135278430850790461001 21395351458823138092845751)
  ·
    refine ⟨32093027188234707139268627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21395351458823138092845751 32093027188234707139268627)
    ·
      refine ⟨48139540782352060708902941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32093027188234707139268627 48139540782352060708902941)
      ·
        refine ⟨18052327793382022765838603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48139540782352060708902941 18052327793382022765838603)
        ·
          refine ⟨27078491690073034148757905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18052327793382022765838603 27078491690073034148757905)
          ·
            refine ⟨20308868767554775611568429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27078491690073034148757905 20308868767554775611568429)
            ·
              refine ⟨7615825787833040854338161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20308868767554775611568429 7615825787833040854338161)
              ·
                refine ⟨5711869340874780640753621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7615825787833040854338161 5711869340874780640753621)
                ·
                  refine ⟨133871937676752671267663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5711869340874780640753621 133871937676752671267663)
                  ·
                    rfl

theorem cell22_1173216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 2, 7].length) (baseStart_1173216 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1173216 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1173216 prefixEnd_1173216 := by exact prefixLift 1173216
  have htrace : WordTrace (prefixWord ++ tailWord_1173216) baseStart_1173216 baseEnd_1173216 := by
    simpa [prefixWord, tailWord_1173216, baseEnd_1173216] using wordTrace_append hprefix tailTrace_1173216
  have hstable : (prefixWord ++ tailWord_1173216).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1173216).length < 2 ^ (prefixWord ++ tailWord_1173216).sum := by decide
  have hdescent : baseEnd_1173216 < baseStart_1173216 := by decide
  rcases family_descends (prefixWord ++ tailWord_1173216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1173250 : List Nat := [3, 4, 1, 1, 1, 1, 3, 3, 5]
def baseStart_1173250 : Nat := 118140960795 + 1173250 * 2 ^ 59
def prefixEnd_1173250 : Nat := 4983230072969 + 3 ^ 40 * 1173250 * 2
def baseEnd_1173250 : Nat := 133875817308364419484295

theorem tailTrace_1173250 : CollatzResearch.WordTrace tailWord_1173250 prefixEnd_1173250 133875817308364419484295 := by
  unfold tailWord_1173250
  simp only [CollatzResearch.WordTrace]
  refine ⟨10697985749880774998107301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28527961999682066661619469 10697985749880774998107301)
  ·
    refine ⟨2005872328102645312145119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10697985749880774998107301 2005872328102645312145119)
    ·
      refine ⟨3008808492153967968217679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2005872328102645312145119 3008808492153967968217679)
      ·
        refine ⟨4513212738230951952326519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3008808492153967968217679 4513212738230951952326519)
        ·
          refine ⟨6769819107346427928489779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4513212738230951952326519 6769819107346427928489779)
          ·
            refine ⟨10154728661019641892734669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6769819107346427928489779 10154728661019641892734669)
            ·
              refine ⟨3808023247882365709775501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10154728661019641892734669 3808023247882365709775501)
              ·
                refine ⟨1428008717955887141165813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3808023247882365709775501 1428008717955887141165813)
                ·
                  refine ⟨133875817308364419484295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1428008717955887141165813 133875817308364419484295)
                  ·
                    rfl

theorem cell22_1173250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 3, 3, 5].length) (baseStart_1173250 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1173250 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1173250 prefixEnd_1173250 := by exact prefixLift 1173250
  have htrace : WordTrace (prefixWord ++ tailWord_1173250) baseStart_1173250 baseEnd_1173250 := by
    simpa [prefixWord, tailWord_1173250, baseEnd_1173250] using wordTrace_append hprefix tailTrace_1173250
  have hstable : (prefixWord ++ tailWord_1173250).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1173250).length < 2 ^ (prefixWord ++ tailWord_1173250).sum := by decide
  have hdescent : baseEnd_1173250 < baseStart_1173250 := by decide
  rcases family_descends (prefixWord ++ tailWord_1173250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1173263 : List Nat := [1, 1, 2, 1, 1, 1, 4, 6, 1, 4]
def baseStart_1173263 : Nat := 118140960795 + 1173263 * 2 ^ 59
def prefixEnd_1173263 : Nat := 4983230072969 + 3 ^ 40 * 1173263 * 2
def baseEnd_1173263 : Nat := 401631902090765557877845

theorem tailTrace_1173263 : CollatzResearch.WordTrace tailWord_1173263 prefixEnd_1173263 401631902090765557877845 := by
  unfold tailWord_1173263
  simp only [CollatzResearch.WordTrace]
  refine ⟨42792417148476003212652443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28528278098984002141768295 42792417148476003212652443)
  ·
    refine ⟨64188625722714004818978665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42792417148476003212652443 64188625722714004818978665)
    ·
      refine ⟨48141469292035503614233999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64188625722714004818978665 48141469292035503614233999)
      ·
        refine ⟨72212203938053255421350999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48141469292035503614233999 72212203938053255421350999)
        ·
          refine ⟨108318305907079883132026499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72212203938053255421350999 108318305907079883132026499)
          ·
            refine ⟨162477458860619824698039749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108318305907079883132026499 162477458860619824698039749)
            ·
              refine ⟨30464523536366217130882453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 162477458860619824698039749 30464523536366217130882453)
              ·
                refine ⟨1428024540767166428010115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 30464523536366217130882453 1428024540767166428010115)
                ·
                  refine ⟨2142036811150749642015173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1428024540767166428010115 2142036811150749642015173)
                  ·
                    refine ⟨401631902090765557877845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2142036811150749642015173 401631902090765557877845)
                    ·
                      rfl

theorem cell22_1173263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 6, 1, 4].length) (baseStart_1173263 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1173263 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1173263 prefixEnd_1173263 := by exact prefixLift 1173263
  have htrace : WordTrace (prefixWord ++ tailWord_1173263) baseStart_1173263 baseEnd_1173263 := by
    simpa [prefixWord, tailWord_1173263, baseEnd_1173263] using wordTrace_append hprefix tailTrace_1173263
  have hstable : (prefixWord ++ tailWord_1173263).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1173263).length < 2 ^ (prefixWord ++ tailWord_1173263).sum := by decide
  have hdescent : baseEnd_1173263 < baseStart_1173263 := by decide
  rcases family_descends (prefixWord ++ tailWord_1173263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1173308 : List Nat := [2, 2, 2, 2, 1, 1, 2, 2, 4, 4]
def baseStart_1173308 : Nat := 118140960795 + 1173308 * 2 ^ 59
def prefixEnd_1173308 : Nat := 4983230072969 + 3 ^ 40 * 1173308 * 2
def baseEnd_1173308 : Nat := 401647306510400440502707

theorem tailTrace_1173308 : CollatzResearch.WordTrace tailWord_1173308 prefixEnd_1173308 401647306510400440502707 := by
  unfold tailWord_1173308
  simp only [CollatzResearch.WordTrace]
  refine ⟨21397029216656487949020289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28529372288875317265360385 21397029216656487949020289)
  ·
    refine ⟨16047771912492365961765217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21397029216656487949020289 16047771912492365961765217)
    ·
      refine ⟨12035828934369274471323913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16047771912492365961765217 12035828934369274471323913)
      ·
        refine ⟨9026871700776955853492935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12035828934369274471323913 9026871700776955853492935)
        ·
          refine ⟨13540307551165433780239403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9026871700776955853492935 13540307551165433780239403)
          ·
            refine ⟨20310461326748150670359105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13540307551165433780239403 20310461326748150670359105)
            ·
              refine ⟨15232845995061113002769329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20310461326748150670359105 15232845995061113002769329)
              ·
                refine ⟨11424634496295834752076997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15232845995061113002769329 11424634496295834752076997)
                ·
                  refine ⟨2142118968055469016014437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11424634496295834752076997 2142118968055469016014437)
                  ·
                    refine ⟨401647306510400440502707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2142118968055469016014437 401647306510400440502707)
                    ·
                      rfl

theorem cell22_1173308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 2, 4, 4].length) (baseStart_1173308 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1173308 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1173308 prefixEnd_1173308 := by exact prefixLift 1173308
  have htrace : WordTrace (prefixWord ++ tailWord_1173308) baseStart_1173308 baseEnd_1173308 := by
    simpa [prefixWord, tailWord_1173308, baseEnd_1173308] using wordTrace_append hprefix tailTrace_1173308
  have hstable : (prefixWord ++ tailWord_1173308).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1173308).length < 2 ^ (prefixWord ++ tailWord_1173308).sum := by decide
  have hdescent : baseEnd_1173308 < baseStart_1173308 := by decide
  rcases family_descends (prefixWord ++ tailWord_1173308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1173310 : List Nat := [4, 2, 1, 2, 2, 1, 1, 3, 1, 5]
def baseStart_1173310 : Nat := 118140960795 + 1173310 * 2 ^ 59
def prefixEnd_1173310 : Nat := 4983230072969 + 3 ^ 40 * 1173310 * 2
def baseEnd_1173310 : Nat := 401647991151273101952701

theorem tailTrace_1173310 : CollatzResearch.WordTrace tailWord_1173310 prefixEnd_1173310 401647991151273101952701 := by
  unfold tailWord_1173310
  simp only [CollatzResearch.WordTrace]
  refine ⟨5349266422413216279951673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28529420919537153493075589 5349266422413216279951673)
  ·
    refine ⟨4011949816809912209963755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5349266422413216279951673 4011949816809912209963755)
    ·
      refine ⟨6017924725214868314945633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4011949816809912209963755 6017924725214868314945633)
      ·
        refine ⟨4513443543911151236209225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6017924725214868314945633 4513443543911151236209225)
        ·
          refine ⟨3385082657933363427156919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4513443543911151236209225 3385082657933363427156919)
          ·
            refine ⟨5077623986900045140735379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3385082657933363427156919 5077623986900045140735379)
            ·
              refine ⟨7616435980350067711103069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5077623986900045140735379 7616435980350067711103069)
              ·
                refine ⟨2856163492631275391663651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7616435980350067711103069 2856163492631275391663651)
                ·
                  refine ⟨4284245238946913087495477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2856163492631275391663651 4284245238946913087495477)
                  ·
                    refine ⟨401647991151273101952701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4284245238946913087495477 401647991151273101952701)
                    ·
                      rfl

theorem cell22_1173310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 3, 1, 5].length) (baseStart_1173310 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1173310 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1173310 prefixEnd_1173310 := by exact prefixLift 1173310
  have htrace : WordTrace (prefixWord ++ tailWord_1173310) baseStart_1173310 baseEnd_1173310 := by
    simpa [prefixWord, tailWord_1173310, baseEnd_1173310] using wordTrace_append hprefix tailTrace_1173310
  have hstable : (prefixWord ++ tailWord_1173310).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1173310).length < 2 ^ (prefixWord ++ tailWord_1173310).sum := by decide
  have hdescent : baseEnd_1173310 < baseStart_1173310 := by decide
  rcases family_descends (prefixWord ++ tailWord_1173310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1173340 : List Nat := [2, 2, 4, 2, 2, 1, 9]
def baseStart_1173340 : Nat := 118140960795 + 1173340 * 2 ^ 59
def prefixEnd_1173340 : Nat := 4983230072969 + 3 ^ 40 * 1173340 * 2
def baseEnd_1173340 : Nat := 14876231880161593470467

theorem tailTrace_1173340 : CollatzResearch.WordTrace tailWord_1173340 prefixEnd_1173340 14876231880161593470467 := by
  unfold tailWord_1173340
  simp only [CollatzResearch.WordTrace]
  refine ⟨21397612784598522681602737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28530150379464696908803649 21397612784598522681602737)
  ·
    refine ⟨16048209588448892011202053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21397612784598522681602737 16048209588448892011202053)
    ·
      refine ⟨3009039297834167252100385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16048209588448892011202053 3009039297834167252100385)
      ·
        refine ⟨2256779473375625439075289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3009039297834167252100385 2256779473375625439075289)
        ·
          refine ⟨1692584605031719079306467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2256779473375625439075289 1692584605031719079306467)
          ·
            refine ⟨2538876907547578618959701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1692584605031719079306467 2538876907547578618959701)
            ·
              refine ⟨14876231880161593470467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2538876907547578618959701 14876231880161593470467)
              ·
                rfl

theorem cell22_1173340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 9].length) (baseStart_1173340 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1173340 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1173340 prefixEnd_1173340 := by exact prefixLift 1173340
  have htrace : WordTrace (prefixWord ++ tailWord_1173340) baseStart_1173340 baseEnd_1173340 := by
    simpa [prefixWord, tailWord_1173340, baseEnd_1173340] using wordTrace_append hprefix tailTrace_1173340
  have hstable : (prefixWord ++ tailWord_1173340).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1173340).length < 2 ^ (prefixWord ++ tailWord_1173340).sum := by decide
  have hdescent : baseEnd_1173340 < baseStart_1173340 := by decide
  rcases family_descends (prefixWord ++ tailWord_1173340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1173374 : List Nat := [4, 2, 3, 1, 1, 3, 2, 6]
def baseStart_1173374 : Nat := 118140960795 + 1173374 * 2 ^ 59
def prefixEnd_1173374 : Nat := 4983230072969 + 3 ^ 40 * 1173374 * 2
def baseEnd_1173374 : Nat := 44629988851022029816945

theorem tailTrace_1173374 : CollatzResearch.WordTrace tailWord_1173374 prefixEnd_1173374 44629988851022029816945 := by
  unfold tailWord_1173374
  simp only [CollatzResearch.WordTrace]
  refine ⟨5349558206384233646242897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28530977100715912779962117 5349558206384233646242897)
  ·
    refine ⟨4012168654788175234682173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5349558206384233646242897 4012168654788175234682173)
    ·
      refine ⟨1504563245545565713005815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4012168654788175234682173 1504563245545565713005815)
      ·
        refine ⟨2256844868318348569508723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1504563245545565713005815 2256844868318348569508723)
        ·
          refine ⟨3385267302477522854263085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2256844868318348569508723 3385267302477522854263085)
          ·
            refine ⟨1269475238429071070348657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3385267302477522854263085 1269475238429071070348657)
            ·
              refine ⟨952106428821803302761493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1269475238429071070348657 952106428821803302761493)
              ·
                refine ⟨44629988851022029816945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 952106428821803302761493 44629988851022029816945)
                ·
                  rfl

theorem cell22_1173374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 3, 2, 6].length) (baseStart_1173374 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1173374 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1173374 prefixEnd_1173374 := by exact prefixLift 1173374
  have htrace : WordTrace (prefixWord ++ tailWord_1173374) baseStart_1173374 baseEnd_1173374 := by
    simpa [prefixWord, tailWord_1173374, baseEnd_1173374] using wordTrace_append hprefix tailTrace_1173374
  have hstable : (prefixWord ++ tailWord_1173374).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1173374).length < 2 ^ (prefixWord ++ tailWord_1173374).sum := by decide
  have hdescent : baseEnd_1173374 < baseStart_1173374 := by decide
  rcases family_descends (prefixWord ++ tailWord_1173374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1173445 : List Nat := [1, 3, 1, 1, 1, 1, 1, 6, 4, 3]
def baseStart_1173445 : Nat := 118140960795 + 1173445 * 2 ^ 59
def prefixEnd_1173445 : Nat := 4983230072969 + 3 ^ 40 * 1173445 * 2
def baseEnd_1173445 : Nat := 401694204410177749827287

theorem tailTrace_1173445 : CollatzResearch.WordTrace tailWord_1173445 prefixEnd_1173445 401694204410177749827287 := by
  unfold tailWord_1173445
  simp only [CollatzResearch.WordTrace]
  refine ⟨42799055233816648295777789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28532703489211098863851859 42799055233816648295777789)
  ·
    refine ⟨16049645712681243110916671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42799055233816648295777789 16049645712681243110916671)
    ·
      refine ⟨24074468569021864666375007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16049645712681243110916671 24074468569021864666375007)
      ·
        refine ⟨36111702853532796999562511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24074468569021864666375007 36111702853532796999562511)
        ·
          refine ⟨54167554280299195499343767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36111702853532796999562511 54167554280299195499343767)
          ·
            refine ⟨81251331420448793249015651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54167554280299195499343767 81251331420448793249015651)
            ·
              refine ⟨121876997130673189873523477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81251331420448793249015651 121876997130673189873523477)
              ·
                refine ⟨5712984240500305775321413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 121876997130673189873523477 5712984240500305775321413)
                ·
                  refine ⟨1071184545093807332872765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5712984240500305775321413 1071184545093807332872765)
                  ·
                    refine ⟨401694204410177749827287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1071184545093807332872765 401694204410177749827287)
                    ·
                      rfl

theorem cell22_1173445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 6, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 6, 4, 3].length) (baseStart_1173445 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1173445 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1173445 prefixEnd_1173445 := by exact prefixLift 1173445
  have htrace : WordTrace (prefixWord ++ tailWord_1173445) baseStart_1173445 baseEnd_1173445 := by
    simpa [prefixWord, tailWord_1173445, baseEnd_1173445] using wordTrace_append hprefix tailTrace_1173445
  have hstable : (prefixWord ++ tailWord_1173445).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1173445).length < 2 ^ (prefixWord ++ tailWord_1173445).sum := by decide
  have hdescent : baseEnd_1173445 < baseStart_1173445 := by decide
  rcases family_descends (prefixWord ++ tailWord_1173445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1173475 : List Nat := [1, 1, 1, 6, 1, 2, 3, 7]
def baseStart_1173475 : Nat := 118140960795 + 1173475 * 2 ^ 59
def prefixEnd_1173475 : Nat := 4983230072969 + 3 ^ 40 * 1173475 * 2
def baseEnd_1173475 : Nat := 44633830447029741286355

theorem tailTrace_1173475 : CollatzResearch.WordTrace tailWord_1173475 prefixEnd_1173475 44633830447029741286355 := by
  unfold tailWord_1173475
  simp only [CollatzResearch.WordTrace]
  refine ⟨42800149423707963419369879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28533432949138642279579919 42800149423707963419369879)
  ·
    refine ⟨64200224135561945129054819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42800149423707963419369879 64200224135561945129054819)
    ·
      refine ⟨96300336203342917693582229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64200224135561945129054819 96300336203342917693582229)
      ·
        refine ⟨4514078259531699266886667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 96300336203342917693582229 4514078259531699266886667)
        ·
          refine ⟨6771117389297548900330001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4514078259531699266886667 6771117389297548900330001)
          ·
            refine ⟨5078338041973161675247501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6771117389297548900330001 5078338041973161675247501)
            ·
              refine ⟨1904376765739935628217813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5078338041973161675247501 1904376765739935628217813)
              ·
                refine ⟨44633830447029741286355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1904376765739935628217813 44633830447029741286355)
                ·
                  rfl

theorem cell22_1173475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 3, 7].length) (baseStart_1173475 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1173475 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1173475 prefixEnd_1173475 := by exact prefixLift 1173475
  have htrace : WordTrace (prefixWord ++ tailWord_1173475) baseStart_1173475 baseEnd_1173475 := by
    simpa [prefixWord, tailWord_1173475, baseEnd_1173475] using wordTrace_append hprefix tailTrace_1173475
  have hstable : (prefixWord ++ tailWord_1173475).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1173475).length < 2 ^ (prefixWord ++ tailWord_1173475).sum := by decide
  have hdescent : baseEnd_1173475 < baseStart_1173475 := by decide
  rcases family_descends (prefixWord ++ tailWord_1173475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1173535 : List Nat := [1, 1, 2, 4, 1, 2, 1, 3, 2, 5]
def baseStart_1173535 : Nat := 118140960795 + 1173535 * 2 ^ 59
def prefixEnd_1173535 : Nat := 4983230072969 + 3 ^ 40 * 1173535 * 2
def baseEnd_1173535 : Nat := 401725013249447515077011

theorem tailTrace_1173535 : CollatzResearch.WordTrace tailWord_1173535 prefixEnd_1173535 401725013249447515077011 := by
  unfold tailWord_1173535
  simp only [CollatzResearch.WordTrace]
  refine ⟨42802337803490593666554059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28534891868993729111036039 42802337803490593666554059)
  ·
    refine ⟨64203506705235890499831089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42802337803490593666554059 64203506705235890499831089)
    ·
      refine ⟨48152630028926917874873317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64203506705235890499831089 48152630028926917874873317)
      ·
        refine ⟨9028618130423797101538747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 48152630028926917874873317 9028618130423797101538747)
        ·
          refine ⟨13542927195635695652308121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9028618130423797101538747 13542927195635695652308121)
          ·
            refine ⟨10157195396726771739231091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13542927195635695652308121 10157195396726771739231091)
            ·
              refine ⟨15235793095090157608846637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10157195396726771739231091 15235793095090157608846637)
              ·
                refine ⟨5713422410658809103317489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15235793095090157608846637 5713422410658809103317489)
                ·
                  refine ⟨4285066807994106827488117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5713422410658809103317489 4285066807994106827488117)
                  ·
                    refine ⟨401725013249447515077011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4285066807994106827488117 401725013249447515077011)
                    ·
                      rfl

theorem cell22_1173535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 3, 2, 5].length) (baseStart_1173535 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1173535 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1173535 prefixEnd_1173535 := by exact prefixLift 1173535
  have htrace : WordTrace (prefixWord ++ tailWord_1173535) baseStart_1173535 baseEnd_1173535 := by
    simpa [prefixWord, tailWord_1173535, baseEnd_1173535] using wordTrace_append hprefix tailTrace_1173535
  have hstable : (prefixWord ++ tailWord_1173535).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1173535).length < 2 ^ (prefixWord ++ tailWord_1173535).sum := by decide
  have hdescent : baseEnd_1173535 < baseStart_1173535 := by decide
  rcases family_descends (prefixWord ++ tailWord_1173535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1173567 : List Nat := [1, 1, 2, 2, 3, 1, 4, 3, 1, 4]
def baseStart_1173567 : Nat := 118140960795 + 1173567 * 2 ^ 59
def prefixEnd_1173567 : Nat := 4983230072969 + 3 ^ 40 * 1173567 * 2
def baseEnd_1173567 : Nat := 401735967503410098276913

theorem tailTrace_1173567 : CollatzResearch.WordTrace tailWord_1173567 prefixEnd_1173567 401735967503410098276913 := by
  unfold tailWord_1173567
  simp only [CollatzResearch.WordTrace]
  refine ⟨42803504939374663131718955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28535669959583108754479303 42803504939374663131718955)
  ·
    refine ⟨64205257409061994697578433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42803504939374663131718955 64205257409061994697578433)
    ·
      refine ⟨48153943056796496023183825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64205257409061994697578433 48153943056796496023183825)
      ·
        refine ⟨36115457292597372017387869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48153943056796496023183825 36115457292597372017387869)
        ·
          refine ⟨13543296484724014506520451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36115457292597372017387869 13543296484724014506520451)
          ·
            refine ⟨20314944727086021759780677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13543296484724014506520451 20314944727086021759780677)
            ·
              refine ⟨3809052136328629079958877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20314944727086021759780677 3809052136328629079958877)
              ·
                refine ⟨1428394551123235904984579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3809052136328629079958877 1428394551123235904984579)
                ·
                  refine ⟨2142591826684853857476869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1428394551123235904984579 2142591826684853857476869)
                  ·
                    refine ⟨401735967503410098276913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2142591826684853857476869 401735967503410098276913)
                    ·
                      rfl

theorem cell22_1173567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 4, 3, 1, 4].length) (baseStart_1173567 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1173567 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1173567 prefixEnd_1173567 := by exact prefixLift 1173567
  have htrace : WordTrace (prefixWord ++ tailWord_1173567) baseStart_1173567 baseEnd_1173567 := by
    simpa [prefixWord, tailWord_1173567, baseEnd_1173567] using wordTrace_append hprefix tailTrace_1173567
  have hstable : (prefixWord ++ tailWord_1173567).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1173567).length < 2 ^ (prefixWord ++ tailWord_1173567).sum := by decide
  have hdescent : baseEnd_1173567 < baseStart_1173567 := by decide
  rcases family_descends (prefixWord ++ tailWord_1173567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1173582 : List Nat := [4, 1, 1, 1, 1, 4, 3, 1, 6]
def baseStart_1173582 : Nat := 118140960795 + 1173582 * 2 ^ 59
def prefixEnd_1173582 : Nat := 4983230072969 + 3 ^ 40 * 1173582 * 2
def baseEnd_1173582 : Nat := 133913700769985019717289

theorem tailTrace_1173582 : CollatzResearch.WordTrace tailWord_1173582 prefixEnd_1173582 133913700769985019717289 := by
  unfold tailWord_1173582
  simp only [CollatzResearch.WordTrace]
  refine ⟨5350506504290040086689375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28536034689546880462343333 5350506504290040086689375)
  ·
    refine ⟨8025759756435060130034063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5350506504290040086689375 8025759756435060130034063)
    ·
      refine ⟨12038639634652590195051095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8025759756435060130034063 12038639634652590195051095)
      ·
        refine ⟨18057959451978885292576643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12038639634652590195051095 18057959451978885292576643)
        ·
          refine ⟨27086939177968327938864965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18057959451978885292576643 27086939177968327938864965)
          ·
            refine ⟨5078801095869061488537181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27086939177968327938864965 5078801095869061488537181)
            ·
              refine ⟨1904550410950898058201443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5078801095869061488537181 1904550410950898058201443)
              ·
                refine ⟨2856825616426347087302165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1904550410950898058201443 2856825616426347087302165)
                ·
                  refine ⟨133913700769985019717289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2856825616426347087302165 133913700769985019717289)
                  ·
                    rfl

theorem cell22_1173582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 3, 1, 6].length) (baseStart_1173582 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1173582 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1173582 prefixEnd_1173582 := by exact prefixLift 1173582
  have htrace : WordTrace (prefixWord ++ tailWord_1173582) baseStart_1173582 baseEnd_1173582 := by
    simpa [prefixWord, tailWord_1173582, baseEnd_1173582] using wordTrace_append hprefix tailTrace_1173582
  have hstable : (prefixWord ++ tailWord_1173582).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1173582).length < 2 ^ (prefixWord ++ tailWord_1173582).sum := by decide
  have hdescent : baseEnd_1173582 < baseStart_1173582 := by decide
  rcases family_descends (prefixWord ++ tailWord_1173582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1173612 : List Nat := [2, 2, 1, 1, 3, 3, 1, 3, 2, 4]
def baseStart_1173612 : Nat := 118140960795 + 1173612 * 2 ^ 59
def prefixEnd_1173612 : Nat := 4983230072969 + 3 ^ 40 * 1173612 * 2
def baseEnd_1173612 : Nat := 401751371923044980901775

theorem tailTrace_1173612 : CollatzResearch.WordTrace tailWord_1173612 prefixEnd_1173612 401751371923044980901775 := by
  unfold tailWord_1173612
  simp only [CollatzResearch.WordTrace]
  refine ⟨21402573112105817908553545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28536764149474423878071393 21402573112105817908553545)
  ·
    refine ⟨16051929834079363431415159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21402573112105817908553545 16051929834079363431415159)
    ·
      refine ⟨24077894751119045147122739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16051929834079363431415159 24077894751119045147122739)
      ·
        refine ⟨36116842126678567720684109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24077894751119045147122739 36116842126678567720684109)
        ·
          refine ⟨13543815797504462895256541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36116842126678567720684109 13543815797504462895256541)
          ·
            refine ⟨5078930924064173585721203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13543815797504462895256541 5078930924064173585721203)
            ·
              refine ⟨7618396386096260378581805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5078930924064173585721203 7618396386096260378581805)
              ·
                refine ⟨2856898644786097641968177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7618396386096260378581805 2856898644786097641968177)
                ·
                  refine ⟨2142673983589573231476133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2856898644786097641968177 2142673983589573231476133)
                  ·
                    refine ⟨401751371923044980901775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2142673983589573231476133 401751371923044980901775)
                    ·
                      rfl

theorem cell22_1173612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 4].length) (baseStart_1173612 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1173612 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1173612 prefixEnd_1173612 := by exact prefixLift 1173612
  have htrace : WordTrace (prefixWord ++ tailWord_1173612) baseStart_1173612 baseEnd_1173612 := by
    simpa [prefixWord, tailWord_1173612, baseEnd_1173612] using wordTrace_append hprefix tailTrace_1173612
  have hstable : (prefixWord ++ tailWord_1173612).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1173612).length < 2 ^ (prefixWord ++ tailWord_1173612).sum := by decide
  have hdescent : baseEnd_1173612 < baseStart_1173612 := by decide
  rcases family_descends (prefixWord ++ tailWord_1173612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1173633 : List Nat := [1, 2, 4, 2, 3, 2, 2, 2, 4]
def baseStart_1173633 : Nat := 118140960795 + 1173633 * 2 ^ 59
def prefixEnd_1173633 : Nat := 4983230072969 + 3 ^ 40 * 1173633 * 2
def baseEnd_1173633 : Nat := 133919520217402642042237

theorem tailTrace_1173633 : CollatzResearch.WordTrace tailWord_1173633 prefixEnd_1173633 133919520217402642042237 := by
  unfold tailWord_1173633
  simp only [CollatzResearch.WordTrace]
  refine ⟨42805912157135556403621553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28537274771423704269081035 42805912157135556403621553)
  ·
    refine ⟨32104434117851667302716165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42805912157135556403621553 32104434117851667302716165)
    ·
      refine ⟨6019581397097187619259281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32104434117851667302716165 6019581397097187619259281)
      ·
        refine ⟨4514686047822890714444461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6019581397097187619259281 4514686047822890714444461)
        ·
          refine ⟨1693007267933584017916673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4514686047822890714444461 1693007267933584017916673)
          ·
            refine ⟨1269755450950188013437505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1693007267933584017916673 1269755450950188013437505)
            ·
              refine ⟨952316588212641010078129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1269755450950188013437505 952316588212641010078129)
              ·
                refine ⟨714237441159480757558597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 952316588212641010078129 714237441159480757558597)
                ·
                  refine ⟨133919520217402642042237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 714237441159480757558597 133919520217402642042237)
                  ·
                    rfl

theorem cell22_1173633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 2, 2, 2, 4].length) (baseStart_1173633 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1173633 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1173633 prefixEnd_1173633 := by exact prefixLift 1173633
  have htrace : WordTrace (prefixWord ++ tailWord_1173633) baseStart_1173633 baseEnd_1173633 := by
    simpa [prefixWord, tailWord_1173633, baseEnd_1173633] using wordTrace_append hprefix tailTrace_1173633
  have hstable : (prefixWord ++ tailWord_1173633).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1173633).length < 2 ^ (prefixWord ++ tailWord_1173633).sum := by decide
  have hdescent : baseEnd_1173633 < baseStart_1173633 := by decide
  rcases family_descends (prefixWord ++ tailWord_1173633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1173687 : List Nat := [1, 1, 3, 1, 4, 2, 1, 2, 2, 5]
def baseStart_1173687 : Nat := 118140960795 + 1173687 * 2 ^ 59
def prefixEnd_1173687 : Nat := 4983230072969 + 3 ^ 40 * 1173687 * 2
def baseEnd_1173687 : Nat := 401777045955769785276545

theorem tailTrace_1173687 : CollatzResearch.WordTrace tailWord_1173687 prefixEnd_1173687 401777045955769785276545 := by
  unfold tailWord_1173687
  simp only [CollatzResearch.WordTrace]
  refine ⟨42807881698939923626087315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28538587799293282417391543 42807881698939923626087315)
  ·
    refine ⟨64211822548409885439130973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42807881698939923626087315 64211822548409885439130973)
    ·
      refine ⟨24079433455653707039674115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64211822548409885439130973 24079433455653707039674115)
      ·
        refine ⟨36119150183480560559511173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24079433455653707039674115 36119150183480560559511173)
        ·
          refine ⟨6772340659402605104908345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 36119150183480560559511173 6772340659402605104908345)
          ·
            refine ⟨5079255494551953828681259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6772340659402605104908345 5079255494551953828681259)
            ·
              refine ⟨7618883241827930743021889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5079255494551953828681259 7618883241827930743021889)
              ·
                refine ⟨5714162431370948057266417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7618883241827930743021889 5714162431370948057266417)
                ·
                  refine ⟨4285621823528211042949813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5714162431370948057266417 4285621823528211042949813)
                  ·
                    refine ⟨401777045955769785276545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4285621823528211042949813 401777045955769785276545)
                    ·
                      rfl

theorem cell22_1173687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 2, 2, 5].length) (baseStart_1173687 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1173687 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1173687 prefixEnd_1173687 := by exact prefixLift 1173687
  have htrace : WordTrace (prefixWord ++ tailWord_1173687) baseStart_1173687 baseEnd_1173687 := by
    simpa [prefixWord, tailWord_1173687, baseEnd_1173687] using wordTrace_append hprefix tailTrace_1173687
  have hstable : (prefixWord ++ tailWord_1173687).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1173687).length < 2 ^ (prefixWord ++ tailWord_1173687).sum := by decide
  have hdescent : baseEnd_1173687 < baseStart_1173687 := by decide
  rcases family_descends (prefixWord ++ tailWord_1173687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1173732 : List Nat := [2, 3, 1, 1, 1, 2, 1, 3, 3, 5]
def baseStart_1173732 : Nat := 118140960795 + 1173732 * 2 ^ 59
def prefixEnd_1173732 : Nat := 4983230072969 + 3 ^ 40 * 1173732 * 2
def baseEnd_1173732 : Nat := 401792450375404667901407

theorem tailTrace_1173732 : CollatzResearch.WordTrace tailWord_1173732 prefixEnd_1173732 401792450375404667901407 := by
  unfold tailWord_1173732
  simp only [CollatzResearch.WordTrace]
  refine ⟨21404761491888448155737725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28539681989184597540983633 21404761491888448155737725)
  ·
    refine ⟨8026785559458168058401647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21404761491888448155737725 8026785559458168058401647)
    ·
      refine ⟨12040178339187252087602471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8026785559458168058401647 12040178339187252087602471)
      ·
        refine ⟨18060267508780878131403707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12040178339187252087602471 18060267508780878131403707)
        ·
          refine ⟨27090401263171317197105561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18060267508780878131403707 27090401263171317197105561)
          ·
            refine ⟨20317800947378487897829171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27090401263171317197105561 20317800947378487897829171)
            ·
              refine ⟨30476701421067731846743757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20317800947378487897829171 30476701421067731846743757)
              ·
                refine ⟨11428763032900399442528909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30476701421067731846743757 11428763032900399442528909)
                ·
                  refine ⟨4285786137337649790948341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11428763032900399442528909 4285786137337649790948341)
                  ·
                    refine ⟨401792450375404667901407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4285786137337649790948341 401792450375404667901407)
                    ·
                      rfl

theorem cell22_1173732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 3, 3, 5].length) (baseStart_1173732 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1173732 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1173732 prefixEnd_1173732 := by exact prefixLift 1173732
  have htrace : WordTrace (prefixWord ++ tailWord_1173732) baseStart_1173732 baseEnd_1173732 := by
    simpa [prefixWord, tailWord_1173732, baseEnd_1173732] using wordTrace_append hprefix tailTrace_1173732
  have hstable : (prefixWord ++ tailWord_1173732).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1173732).length < 2 ^ (prefixWord ++ tailWord_1173732).sum := by decide
  have hdescent : baseEnd_1173732 < baseStart_1173732 := by decide
  rcases family_descends (prefixWord ++ tailWord_1173732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1173802 : List Nat := [3, 1, 4, 2, 3, 1, 2, 2, 4]
def baseStart_1173802 : Nat := 118140960795 + 1173802 * 2 ^ 59
def prefixEnd_1173802 : Nat := 4983230072969 + 3 ^ 40 * 1173802 * 2
def baseEnd_1173802 : Nat := 133938804268649272883731

theorem tailTrace_1173802 : CollatzResearch.WordTrace tailWord_1173802 prefixEnd_1173802 133938804268649272883731 := by
  unfold tailWord_1173802
  simp only [CollatzResearch.WordTrace]
  refine ⟨10703019023380824566630915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28541384062348865511015773 10703019023380824566630915)
  ·
    refine ⟨16054528535071236849946373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10703019023380824566630915 16054528535071236849946373)
    ·
      refine ⟨3010224100325856909364945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16054528535071236849946373 3010224100325856909364945)
      ·
        refine ⟨2257668075244392682023709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3010224100325856909364945 2257668075244392682023709)
        ·
          refine ⟨846625528216647255758891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2257668075244392682023709 846625528216647255758891)
          ·
            refine ⟨1269938292324970883638337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 846625528216647255758891 1269938292324970883638337)
            ·
              refine ⟨952453719243728162728753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1269938292324970883638337 952453719243728162728753)
              ·
                refine ⟨714340289432796122046565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 952453719243728162728753 714340289432796122046565)
                ·
                  refine ⟨133938804268649272883731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 714340289432796122046565 133938804268649272883731)
                  ·
                    rfl

theorem cell22_1173802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 3, 1, 2, 2, 4].length) (baseStart_1173802 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1173802 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1173802 prefixEnd_1173802 := by exact prefixLift 1173802
  have htrace : WordTrace (prefixWord ++ tailWord_1173802) baseStart_1173802 baseEnd_1173802 := by
    simpa [prefixWord, tailWord_1173802, baseEnd_1173802] using wordTrace_append hprefix tailTrace_1173802
  have hstable : (prefixWord ++ tailWord_1173802).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1173802).length < 2 ^ (prefixWord ++ tailWord_1173802).sum := by decide
  have hdescent : baseEnd_1173802 < baseStart_1173802 := by decide
  rcases family_descends (prefixWord ++ tailWord_1173802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1173807 : List Nat := [1, 1, 2, 1, 2, 1, 4, 3, 7]
def baseStart_1173807 : Nat := 118140960795 + 1173807 * 2 ^ 59
def prefixEnd_1173807 : Nat := 4983230072969 + 3 ^ 40 * 1173807 * 2
def baseEnd_1173807 : Nat := 133939374802709824092059

theorem tailTrace_1173807 : CollatzResearch.WordTrace tailWord_1173807 prefixEnd_1173807 133939374802709824092059 := by
  unfold tailWord_1173807
  simp only [CollatzResearch.WordTrace]
  refine ⟨42812258458505184120455675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28541505639003456080303783 42812258458505184120455675)
  ·
    refine ⟨64218387687757776180683513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42812258458505184120455675 64218387687757776180683513)
    ·
      refine ⟨48163790765818332135512635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64218387687757776180683513 48163790765818332135512635)
      ·
        refine ⟨72245686148727498203268953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48163790765818332135512635 72245686148727498203268953)
        ·
          refine ⟨54184264611545623652451715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72245686148727498203268953 54184264611545623652451715)
          ·
            refine ⟨81276396917318435478677573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54184264611545623652451715 81276396917318435478677573)
            ·
              refine ⟨15239324421997206652252045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 81276396917318435478677573 15239324421997206652252045)
              ·
                refine ⟨5714746658248952494594517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15239324421997206652252045 5714746658248952494594517)
                ·
                  refine ⟨133939374802709824092059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5714746658248952494594517 133939374802709824092059)
                  ·
                    rfl

theorem cell22_1173807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 3, 7].length) (baseStart_1173807 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1173807 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1173807 prefixEnd_1173807 := by exact prefixLift 1173807
  have htrace : WordTrace (prefixWord ++ tailWord_1173807) baseStart_1173807 baseEnd_1173807 := by
    simpa [prefixWord, tailWord_1173807, baseEnd_1173807] using wordTrace_append hprefix tailTrace_1173807
  have hstable : (prefixWord ++ tailWord_1173807).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1173807).length < 2 ^ (prefixWord ++ tailWord_1173807).sum := by decide
  have hdescent : baseEnd_1173807 < baseStart_1173807 := by decide
  rcases family_descends (prefixWord ++ tailWord_1173807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1173845 : List Nat := [1, 3, 2, 2, 4, 1, 2, 3, 1, 3]
def baseStart_1173845 : Nat := 118140960795 + 1173845 * 2 ^ 59
def prefixEnd_1173845 : Nat := 4983230072969 + 3 ^ 40 * 1173845 * 2
def baseEnd_1173845 : Nat := 401831132584710039826061

theorem tailTrace_1173845 : CollatzResearch.WordTrace tailWord_1173845 prefixEnd_1173845 401831132584710039826061 := by
  unfold tailWord_1173845
  simp only [CollatzResearch.WordTrace]
  refine ⟨42813644432367516610338989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28542429621578344406892659 42813644432367516610338989)
  ·
    refine ⟨16055116662137818728877121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42813644432367516610338989 16055116662137818728877121)
    ·
      refine ⟨12041337496603364046657841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16055116662137818728877121 12041337496603364046657841)
      ·
        refine ⟨9031003122452523034993381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12041337496603364046657841 9031003122452523034993381)
        ·
          refine ⟨1693313085459848069061259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9031003122452523034993381 1693313085459848069061259)
          ·
            refine ⟨2539969628189772103591889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1693313085459848069061259 2539969628189772103591889)
            ·
              refine ⟨1904977221142329077693917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2539969628189772103591889 1904977221142329077693917)
              ·
                refine ⟨714366457928373404135219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1904977221142329077693917 714366457928373404135219)
                ·
                  refine ⟨1071549686892560106202829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 714366457928373404135219 1071549686892560106202829)
                  ·
                    refine ⟨401831132584710039826061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1071549686892560106202829 401831132584710039826061)
                    ·
                      rfl

theorem cell22_1173845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 2, 3, 1, 3].length) (baseStart_1173845 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1173845 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1173845 prefixEnd_1173845 := by exact prefixLift 1173845
  have htrace : WordTrace (prefixWord ++ tailWord_1173845) baseStart_1173845 baseEnd_1173845 := by
    simpa [prefixWord, tailWord_1173845, baseEnd_1173845] using wordTrace_append hprefix tailTrace_1173845
  have hstable : (prefixWord ++ tailWord_1173845).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1173845).length < 2 ^ (prefixWord ++ tailWord_1173845).sum := by decide
  have hdescent : baseEnd_1173845 < baseStart_1173845 := by decide
  rcases family_descends (prefixWord ++ tailWord_1173845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1173858 : List Nat := [3, 3, 2, 1, 1, 4, 1, 2, 5]
def baseStart_1173858 : Nat := 118140960795 + 1173858 * 2 ^ 59
def prefixEnd_1173858 : Nat := 4983230072969 + 3 ^ 40 * 1173858 * 2
def baseEnd_1173858 : Nat := 133945194250127446417007

theorem tailTrace_1173858 : CollatzResearch.WordTrace tailWord_1173858 prefixEnd_1173858 133945194250127446417007 := by
  unfold tailWord_1173858
  simp only [CollatzResearch.WordTrace]
  refine ⟨10703529645330104957640557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28542745720880279887041485 10703529645330104957640557)
  ·
    refine ⟨4013823616998789359115209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10703529645330104957640557 4013823616998789359115209)
    ·
      refine ⟨3010367712749092019336407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4013823616998789359115209 3010367712749092019336407)
      ·
        refine ⟨4515551569123638029004611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3010367712749092019336407 4515551569123638029004611)
        ·
          refine ⟨6773327353685457043506917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4515551569123638029004611 6773327353685457043506917)
          ·
            refine ⟨1269998878816023195657547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6773327353685457043506917 1269998878816023195657547)
            ·
              refine ⟨1904998318224034793486321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1269998878816023195657547 1904998318224034793486321)
              ·
                refine ⟨1428748738668026095114741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1904998318224034793486321 1428748738668026095114741)
                ·
                  refine ⟨133945194250127446417007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1428748738668026095114741 133945194250127446417007)
                  ·
                    rfl

theorem cell22_1173858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 4, 1, 2, 5].length) (baseStart_1173858 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1173858 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1173858 prefixEnd_1173858 := by exact prefixLift 1173858
  have htrace : WordTrace (prefixWord ++ tailWord_1173858) baseStart_1173858 baseEnd_1173858 := by
    simpa [prefixWord, tailWord_1173858, baseEnd_1173858] using wordTrace_append hprefix tailTrace_1173858
  have hstable : (prefixWord ++ tailWord_1173858).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1173858).length < 2 ^ (prefixWord ++ tailWord_1173858).sum := by decide
  have hdescent : baseEnd_1173858 < baseStart_1173858 := by decide
  rcases family_descends (prefixWord ++ tailWord_1173858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1173884 : List Nat := [2, 2, 2, 1, 1, 1, 2, 5, 1, 5]
def baseStart_1173884 : Nat := 118140960795 + 1173884 * 2 ^ 59
def prefixEnd_1173884 : Nat := 4983230072969 + 3 ^ 40 * 1173884 * 2
def baseEnd_1173884 : Nat := 401844483081726938100941

theorem tailTrace_1173884 : CollatzResearch.WordTrace tailWord_1173884 prefixEnd_1173884 401844483081726938100941 := by
  unfold tailWord_1173884
  simp only [CollatzResearch.WordTrace]
  refine ⟨21407533439613113135504353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28543377919484150847339137 21407533439613113135504353)
  ·
    refine ⟨16055650079709834851628265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21407533439613113135504353 16055650079709834851628265)
    ·
      refine ⟨12041737559782376138721199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16055650079709834851628265 12041737559782376138721199)
      ·
        refine ⟨18062606339673564208081799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12041737559782376138721199 18062606339673564208081799)
        ·
          refine ⟨27093909509510346312122699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18062606339673564208081799 27093909509510346312122699)
          ·
            refine ⟨40640864264265519468184049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27093909509510346312122699 40640864264265519468184049)
            ·
              refine ⟨30480648198199139601138037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40640864264265519468184049 30480648198199139601138037)
              ·
                refine ⟨2857560768581169337606691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 30480648198199139601138037 2857560768581169337606691)
                ·
                  refine ⟨4286341152871754006410037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2857560768581169337606691 4286341152871754006410037)
                  ·
                    refine ⟨401844483081726938100941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4286341152871754006410037 401844483081726938100941)
                    ·
                      rfl

theorem cell22_1173884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 5, 1, 5].length) (baseStart_1173884 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1173884 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1173884 prefixEnd_1173884 := by exact prefixLift 1173884
  have htrace : WordTrace (prefixWord ++ tailWord_1173884) baseStart_1173884 baseEnd_1173884 := by
    simpa [prefixWord, tailWord_1173884, baseEnd_1173884] using wordTrace_append hprefix tailTrace_1173884
  have hstable : (prefixWord ++ tailWord_1173884).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1173884).length < 2 ^ (prefixWord ++ tailWord_1173884).sum := by decide
  have hdescent : baseEnd_1173884 < baseStart_1173884 := by decide
  rcases family_descends (prefixWord ++ tailWord_1173884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1173899 : List Nat := [1, 1, 1, 1, 4, 4, 2, 1, 1, 6]
def baseStart_1173899 : Nat := 118140960795 + 1173899 * 2 ^ 59
def prefixEnd_1173899 : Nat := 4983230072969 + 3 ^ 40 * 1173899 * 2
def baseEnd_1173899 : Nat := 401849617888271898975895

theorem tailTrace_1173899 : CollatzResearch.WordTrace tailWord_1173899 prefixEnd_1173899 401849617888271898975895 := by
  unfold tailWord_1173899
  simp only [CollatzResearch.WordTrace]
  refine ⟨42815613974171883832804751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28543742649447922555203167 42815613974171883832804751)
  ·
    refine ⟨64223420961257825749207127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42815613974171883832804751 64223420961257825749207127)
    ·
      refine ⟨96335131441886738623810691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64223420961257825749207127 96335131441886738623810691)
      ·
        refine ⟨144502697162830107935716037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96335131441886738623810691 144502697162830107935716037)
        ·
          refine ⟨27094255718030645237946757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 144502697162830107935716037 27094255718030645237946757)
          ·
            refine ⟨5080172947130745982115017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27094255718030645237946757 5080172947130745982115017)
            ·
              refine ⟨3810129710348059486586263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5080172947130745982115017 3810129710348059486586263)
              ·
                refine ⟨5715194565522089229879395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3810129710348059486586263 5715194565522089229879395)
                ·
                  refine ⟨8572791848283133844819093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5715194565522089229879395 8572791848283133844819093)
                  ·
                    refine ⟨401849617888271898975895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8572791848283133844819093 401849617888271898975895)
                    ·
                      rfl

theorem cell22_1173899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 2, 1, 1, 6].length) (baseStart_1173899 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1173899 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1173899 prefixEnd_1173899 := by exact prefixLift 1173899
  have htrace : WordTrace (prefixWord ++ tailWord_1173899) baseStart_1173899 baseEnd_1173899 := by
    simpa [prefixWord, tailWord_1173899, baseEnd_1173899] using wordTrace_append hprefix tailTrace_1173899
  have hstable : (prefixWord ++ tailWord_1173899).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1173899).length < 2 ^ (prefixWord ++ tailWord_1173899).sum := by decide
  have hdescent : baseEnd_1173899 < baseStart_1173899 := by decide
  rcases family_descends (prefixWord ++ tailWord_1173899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1173914 : List Nat := [3, 1, 1, 4, 1, 2, 10]
def baseStart_1173914 : Nat := 118140960795 + 1173914 * 2 ^ 59
def prefixEnd_1173914 : Nat := 4983230072969 + 3 ^ 40 * 1173914 * 2
def baseEnd_1173914 : Nat := 14883509359067291105587

theorem tailTrace_1173914 : CollatzResearch.WordTrace tailWord_1173914 prefixEnd_1173914 14883509359067291105587 := by
  unfold tailWord_1173914
  simp only [CollatzResearch.WordTrace]
  refine ⟨10704040267279385348650199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28544107379411694263067197 10704040267279385348650199)
  ·
    refine ⟨16056060400919078022975299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10704040267279385348650199 16056060400919078022975299)
    ·
      refine ⟨24084090601378617034462949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16056060400919078022975299 24084090601378617034462949)
      ·
        refine ⟨4515766987758490693961803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24084090601378617034462949 4515766987758490693961803)
        ·
          refine ⟨6773650481637736040942705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4515766987758490693961803 6773650481637736040942705)
          ·
            refine ⟨5080237861228302030707029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6773650481637736040942705 5080237861228302030707029)
            ·
              refine ⟨14883509359067291105587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 5080237861228302030707029 14883509359067291105587)
              ·
                rfl

theorem cell22_1173914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 10].length) (baseStart_1173914 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1173914 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1173914 prefixEnd_1173914 := by exact prefixLift 1173914
  have htrace : WordTrace (prefixWord ++ tailWord_1173914) baseStart_1173914 baseEnd_1173914 := by
    simpa [prefixWord, tailWord_1173914, baseEnd_1173914] using wordTrace_append hprefix tailTrace_1173914
  have hstable : (prefixWord ++ tailWord_1173914).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1173914).length < 2 ^ (prefixWord ++ tailWord_1173914).sum := by decide
  have hdescent : baseEnd_1173914 < baseStart_1173914 := by decide
  rcases family_descends (prefixWord ++ tailWord_1173914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1173946 : List Nat := [3, 1, 1, 1, 2, 1, 1, 6, 3, 3]
def baseStart_1173946 : Nat := 118140960795 + 1173946 * 2 ^ 59
def prefixEnd_1173946 : Nat := 4983230072969 + 3 ^ 40 * 1173946 * 2
def baseEnd_1173946 : Nat := 401865706948779443050751

theorem tailTrace_1173946 : CollatzResearch.WordTrace tailWord_1173946 prefixEnd_1173946 401865706948779443050751 := by
  unfold tailWord_1173946
  simp only [CollatzResearch.WordTrace]
  refine ⟨10704332051250402714941423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28544885470001073906510461 10704332051250402714941423)
  ·
    refine ⟨16056498076875604072412135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10704332051250402714941423 16056498076875604072412135)
    ·
      refine ⟨24084747115313406108618203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16056498076875604072412135 24084747115313406108618203)
      ·
        refine ⟨36127120672970109162927305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24084747115313406108618203 36127120672970109162927305)
        ·
          refine ⟨27095340504727581872195479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36127120672970109162927305 27095340504727581872195479)
          ·
            refine ⟨40643010757091372808293219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27095340504727581872195479 40643010757091372808293219)
            ·
              refine ⟨60964516135637059212439829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40643010757091372808293219 60964516135637059212439829)
              ·
                refine ⟨2857711693857987150583117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 60964516135637059212439829 2857711693857987150583117)
                ·
                  refine ⟨1071641885196745181468669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2857711693857987150583117 1071641885196745181468669)
                  ·
                    refine ⟨401865706948779443050751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1071641885196745181468669 401865706948779443050751)
                    ·
                      rfl

theorem cell22_1173946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 6, 3, 3].length) (baseStart_1173946 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1173946 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1173946 prefixEnd_1173946 := by exact prefixLift 1173946
  have htrace : WordTrace (prefixWord ++ tailWord_1173946) baseStart_1173946 baseEnd_1173946 := by
    simpa [prefixWord, tailWord_1173946, baseEnd_1173946] using wordTrace_append hprefix tailTrace_1173946
  have hstable : (prefixWord ++ tailWord_1173946).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1173946).length < 2 ^ (prefixWord ++ tailWord_1173946).sum := by decide
  have hdescent : baseEnd_1173946 < baseStart_1173946 := by decide
  rcases family_descends (prefixWord ++ tailWord_1173946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1173963 : List Nat := [1, 1, 1, 1, 3, 3, 1, 7, 1, 3]
def baseStart_1173963 : Nat := 118140960795 + 1173963 * 2 ^ 59
def prefixEnd_1173963 : Nat := 4983230072969 + 3 ^ 40 * 1173963 * 2
def baseEnd_1173963 : Nat := 401871526396197065375699

theorem tailTrace_1173963 : CollatzResearch.WordTrace tailWord_1173963 prefixEnd_1173963 401871526396197065375699 := by
  unfold tailWord_1173963
  simp only [CollatzResearch.WordTrace]
  refine ⟨42817948245940022763134543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28545298830626681842089695 42817948245940022763134543)
  ·
    refine ⟨64226922368910034144701815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42817948245940022763134543 64226922368910034144701815)
    ·
      refine ⟨96340383553365051217052723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64226922368910034144701815 96340383553365051217052723)
      ·
        refine ⟨144510575330047576825579085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96340383553365051217052723 144510575330047576825579085)
        ·
          refine ⟨54191465748767841309592157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 144510575330047576825579085 54191465748767841309592157)
          ·
            refine ⟨20321799655787940491097059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54191465748767841309592157 20321799655787940491097059)
            ·
              refine ⟨30482699483681910736645589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20321799655787940491097059 30482699483681910736645589)
              ·
                refine ⟨714438269148794782890131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 30482699483681910736645589 714438269148794782890131)
                ·
                  refine ⟨1071657403723192174335197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 714438269148794782890131 1071657403723192174335197)
                  ·
                    refine ⟨401871526396197065375699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1071657403723192174335197 401871526396197065375699)
                    ·
                      rfl

theorem cell22_1173963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 7, 1, 3].length) (baseStart_1173963 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1173963 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1173963 prefixEnd_1173963 := by exact prefixLift 1173963
  have htrace : WordTrace (prefixWord ++ tailWord_1173963) baseStart_1173963 baseEnd_1173963 := by
    simpa [prefixWord, tailWord_1173963, baseEnd_1173963] using wordTrace_append hprefix tailTrace_1173963
  have hstable : (prefixWord ++ tailWord_1173963).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1173963).length < 2 ^ (prefixWord ++ tailWord_1173963).sum := by decide
  have hdescent : baseEnd_1173963 < baseStart_1173963 := by decide
  rcases family_descends (prefixWord ++ tailWord_1173963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1173991 : List Nat := [1, 1, 5, 2, 1, 1, 3, 1, 2, 5]
def baseStart_1173991 : Nat := 118140960795 + 1173991 * 2 ^ 59
def prefixEnd_1173991 : Nat := 4983230072969 + 3 ^ 40 * 1173991 * 2
def baseEnd_1173991 : Nat := 401881111368414325675613

theorem tailTrace_1173991 : CollatzResearch.WordTrace tailWord_1173991 prefixEnd_1173991 401881111368414325675613 := by
  unfold tailWord_1173991
  simp only [CollatzResearch.WordTrace]
  refine ⟨42818969489838583545153827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28545979659892389030102551 42818969489838583545153827)
  ·
    refine ⟨64228454234757875317730741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42818969489838583545153827 64228454234757875317730741)
    ·
      refine ⟨6021417584508550811037257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 64228454234757875317730741 6021417584508550811037257)
      ·
        refine ⟨4516063188381413108277943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6021417584508550811037257 4516063188381413108277943)
        ·
          refine ⟨6774094782572119662416915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4516063188381413108277943 6774094782572119662416915)
          ·
            refine ⟨10161142173858179493625373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6774094782572119662416915 10161142173858179493625373)
            ·
              refine ⟨3810428315196817310109515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10161142173858179493625373 3810428315196817310109515)
              ·
                refine ⟨5715642472795225965164273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3810428315196817310109515 5715642472795225965164273)
                ·
                  refine ⟨4286731854596419473873205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5715642472795225965164273 4286731854596419473873205)
                  ·
                    refine ⟨401881111368414325675613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4286731854596419473873205 401881111368414325675613)
                    ·
                      rfl

theorem cell22_1173991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 3, 1, 2, 5].length) (baseStart_1173991 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1173991 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1173991 prefixEnd_1173991 := by exact prefixLift 1173991
  have htrace : WordTrace (prefixWord ++ tailWord_1173991) baseStart_1173991 baseEnd_1173991 := by
    simpa [prefixWord, tailWord_1173991, baseEnd_1173991] using wordTrace_append hprefix tailTrace_1173991
  have hstable : (prefixWord ++ tailWord_1173991).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1173991).length < 2 ^ (prefixWord ++ tailWord_1173991).sum := by decide
  have hdescent : baseEnd_1173991 < baseStart_1173991 := by decide
  rcases family_descends (prefixWord ++ tailWord_1173991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1174051 : List Nat := [1, 1, 1, 4, 4, 1, 1, 2, 1, 6]
def baseStart_1174051 : Nat := 118140960795 + 1174051 * 2 ^ 59
def prefixEnd_1174051 : Nat := 4983230072969 + 3 ^ 40 * 1174051 * 2
def baseEnd_1174051 : Nat := 401901650594594169175429

theorem tailTrace_1174051 : CollatzResearch.WordTrace tailWord_1174051 prefixEnd_1174051 401901650594594169175429 := by
  unfold tailWord_1174051
  simp only [CollatzResearch.WordTrace]
  refine ⟨42821157869621213792338007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28547438579747475861558671 42821157869621213792338007)
  ·
    refine ⟨64231736804431820688507011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42821157869621213792338007 64231736804431820688507011)
    ·
      refine ⟨96347605206647731032760517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64231736804431820688507011 96347605206647731032760517)
      ·
        refine ⟨18065175976246449568642597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 96347605206647731032760517 18065175976246449568642597)
        ·
          refine ⟨3387220495546209294120487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18065175976246449568642597 3387220495546209294120487)
          ·
            refine ⟨5080830743319313941180731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3387220495546209294120487 5080830743319313941180731)
            ·
              refine ⟨7621246114978970911771097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5080830743319313941180731 7621246114978970911771097)
              ·
                refine ⟨5715934586234228183828323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7621246114978970911771097 5715934586234228183828323)
                ·
                  refine ⟨8573901879351342275742485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5715934586234228183828323 8573901879351342275742485)
                  ·
                    refine ⟨401901650594594169175429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8573901879351342275742485 401901650594594169175429)
                    ·
                      rfl

theorem cell22_1174051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 2, 1, 6].length) (baseStart_1174051 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1174051 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1174051 prefixEnd_1174051 := by exact prefixLift 1174051
  have htrace : WordTrace (prefixWord ++ tailWord_1174051) baseStart_1174051 baseEnd_1174051 := by
    simpa [prefixWord, tailWord_1174051, baseEnd_1174051] using wordTrace_append hprefix tailTrace_1174051
  have hstable : (prefixWord ++ tailWord_1174051).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1174051).length < 2 ^ (prefixWord ++ tailWord_1174051).sum := by decide
  have hdescent : baseEnd_1174051 < baseStart_1174051 := by decide
  rcases family_descends (prefixWord ++ tailWord_1174051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1174053 : List Nat := [1, 3, 1, 2, 2, 1, 2, 5, 2, 3]
def baseStart_1174053 : Nat := 118140960795 + 1174053 * 2 ^ 59
def prefixEnd_1174053 : Nat := 4983230072969 + 3 ^ 40 * 1174053 * 2
def baseEnd_1174053 : Nat := 401902335235466830625423

theorem tailTrace_1174053 : CollatzResearch.WordTrace tailWord_1174053 prefixEnd_1174053 401902335235466830625423 := by
  unfold tailWord_1174053
  simp only [CollatzResearch.WordTrace]
  refine ⟨42821230815613968133910813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28547487210409312089273875 42821230815613968133910813)
  ·
    refine ⟨16057961555855238050216555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42821230815613968133910813 16057961555855238050216555)
    ·
      refine ⟨24086942333782857075324833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16057961555855238050216555 24086942333782857075324833)
      ·
        refine ⟨18065206750337142806493625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24086942333782857075324833 18065206750337142806493625)
        ·
          refine ⟨13548905062752857104870219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18065206750337142806493625 13548905062752857104870219)
          ·
            refine ⟨20323357594129285657305329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13548905062752857104870219 20323357594129285657305329)
            ·
              refine ⟨15242518195596964242978997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20323357594129285657305329 15242518195596964242978997)
              ·
                refine ⟨1428986080837215397779281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15242518195596964242978997 1428986080837215397779281)
                ·
                  refine ⟨1071739560627911548334461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1428986080837215397779281 1071739560627911548334461)
                  ·
                    refine ⟨401902335235466830625423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1071739560627911548334461 401902335235466830625423)
                    ·
                      rfl

theorem cell22_1174053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 5, 2, 3].length) (baseStart_1174053 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1174053 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1174053 prefixEnd_1174053 := by exact prefixLift 1174053
  have htrace : WordTrace (prefixWord ++ tailWord_1174053) baseStart_1174053 baseEnd_1174053 := by
    simpa [prefixWord, tailWord_1174053, baseEnd_1174053] using wordTrace_append hprefix tailTrace_1174053
  have hstable : (prefixWord ++ tailWord_1174053).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1174053).length < 2 ^ (prefixWord ++ tailWord_1174053).sum := by decide
  have hdescent : baseEnd_1174053 < baseStart_1174053 := by decide
  rcases family_descends (prefixWord ++ tailWord_1174053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1174070 : List Nat := [5, 1, 2, 1, 2, 1, 1, 2, 4, 3]
def baseStart_1174070 : Nat := 118140960795 + 1174070 * 2 ^ 59
def prefixEnd_1174070 : Nat := 4983230072969 + 3 ^ 40 * 1174070 * 2
def baseEnd_1174070 : Nat := 401908154682884452950371

theorem tailTrace_1174070 : CollatzResearch.WordTrace tailWord_1174070 prefixEnd_1174070 401908154682884452950371 := by
  unfold tailWord_1174070
  simp only [CollatzResearch.WordTrace]
  refine ⟨2676365678534523752329979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 28547900571034920024853109 2676365678534523752329979)
  ·
    refine ⟨4014548517801785628494969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2676365678534523752329979 4014548517801785628494969)
    ·
      refine ⟨3010911388351339221371227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4014548517801785628494969 3010911388351339221371227)
      ·
        refine ⟨4516367082527008832056841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3010911388351339221371227 4516367082527008832056841)
        ·
          refine ⟨3387275311895256624042631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4516367082527008832056841 3387275311895256624042631)
          ·
            refine ⟨5080912967842884936063947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3387275311895256624042631 5080912967842884936063947)
            ·
              refine ⟨7621369451764327404095921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5080912967842884936063947 7621369451764327404095921)
              ·
                refine ⟨5716027088823245553071941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7621369451764327404095921 5716027088823245553071941)
                ·
                  refine ⟨1071755079154358541200989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5716027088823245553071941 1071755079154358541200989)
                  ·
                    refine ⟨401908154682884452950371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1071755079154358541200989 401908154682884452950371)
                    ·
                      rfl

theorem cell22_1174070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 2, 4, 3].length) (baseStart_1174070 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1174070 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1174070 prefixEnd_1174070 := by exact prefixLift 1174070
  have htrace : WordTrace (prefixWord ++ tailWord_1174070) baseStart_1174070 baseEnd_1174070 := by
    simpa [prefixWord, tailWord_1174070, baseEnd_1174070] using wordTrace_append hprefix tailTrace_1174070
  have hstable : (prefixWord ++ tailWord_1174070).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1174070).length < 2 ^ (prefixWord ++ tailWord_1174070).sum := by decide
  have hdescent : baseEnd_1174070 < baseStart_1174070 := by decide
  rcases family_descends (prefixWord ++ tailWord_1174070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1174149 : List Nat := [1, 3, 1, 1, 4, 4, 2, 2, 1, 3]
def baseStart_1174149 : Nat := 118140960795 + 1174149 * 2 ^ 59
def prefixEnd_1174149 : Nat := 4983230072969 + 3 ^ 40 * 1174149 * 2
def baseEnd_1174149 : Nat := 401935197997354580225129

theorem tailTrace_1174149 : CollatzResearch.WordTrace tailWord_1174149 prefixEnd_1174149 401935197997354580225129 := by
  unfold tailWord_1174149
  simp only [CollatzResearch.WordTrace]
  refine ⟨42824732223266176529405501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28549821482177451019603667 42824732223266176529405501)
  ·
    refine ⟨16059274583724816198527063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42824732223266176529405501 16059274583724816198527063)
    ·
      refine ⟨24088911875587224297790595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16059274583724816198527063 24088911875587224297790595)
      ·
        refine ⟨36133367813380836446685893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24088911875587224297790595 36133367813380836446685893)
        ·
          refine ⟨6775006465008906833753605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 36133367813380836446685893 6775006465008906833753605)
          ·
            refine ⟨1270313712189170031328801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6775006465008906833753605 1270313712189170031328801)
            ·
              refine ⟨952735284141877523496601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1270313712189170031328801 952735284141877523496601)
              ·
                refine ⟨714551463106408142622451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 952735284141877523496601 714551463106408142622451)
                ·
                  refine ⟨1071827194659612213933677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 714551463106408142622451 1071827194659612213933677)
                  ·
                    refine ⟨401935197997354580225129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1071827194659612213933677 401935197997354580225129)
                    ·
                      rfl

theorem cell22_1174149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 4, 2, 2, 1, 3].length) (baseStart_1174149 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1174149 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1174149 prefixEnd_1174149 := by exact prefixLift 1174149
  have htrace : WordTrace (prefixWord ++ tailWord_1174149) baseStart_1174149 baseEnd_1174149 := by
    simpa [prefixWord, tailWord_1174149, baseEnd_1174149] using wordTrace_append hprefix tailTrace_1174149
  have hstable : (prefixWord ++ tailWord_1174149).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1174149).length < 2 ^ (prefixWord ++ tailWord_1174149).sum := by decide
  have hdescent : baseEnd_1174149 < baseStart_1174149 := by decide
  rcases family_descends (prefixWord ++ tailWord_1174149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1174158 : List Nat := [4, 1, 1, 3, 1, 1, 1, 1, 5, 4]
def baseStart_1174158 : Nat := 118140960795 + 1174158 * 2 ^ 59
def prefixEnd_1174158 : Nat := 4983230072969 + 3 ^ 40 * 1174158 * 2
def baseEnd_1174158 : Nat := 401938278881281556750101

theorem tailTrace_1174158 : CollatzResearch.WordTrace tailWord_1174158 prefixEnd_1174158 401938278881281556750101 := by
  unfold tailWord_1174158
  simp only [CollatzResearch.WordTrace]
  refine ⟨5353132560029196383310391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28550040320155714044322085 5353132560029196383310391)
  ·
    refine ⟨8029698840043794574965587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5353132560029196383310391 8029698840043794574965587)
    ·
      refine ⟨12044548260065691862448381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8029698840043794574965587 12044548260065691862448381)
      ·
        refine ⟨4516705597524634448418143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12044548260065691862448381 4516705597524634448418143)
        ·
          refine ⟨6775058396286951672627215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4516705597524634448418143 6775058396286951672627215)
          ·
            refine ⟨10162587594430427508940823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6775058396286951672627215 10162587594430427508940823)
            ·
              refine ⟨15243881391645641263411235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10162587594430427508940823 15243881391645641263411235)
              ·
                refine ⟨22865822087468461895116853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15243881391645641263411235 22865822087468461895116853)
                ·
                  refine ⟨2143670820700168302667205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 22865822087468461895116853 2143670820700168302667205)
                  ·
                    refine ⟨401938278881281556750101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2143670820700168302667205 401938278881281556750101)
                    ·
                      rfl

theorem cell22_1174158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 1, 5, 4].length) (baseStart_1174158 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1174158 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1174158 prefixEnd_1174158 := by exact prefixLift 1174158
  have htrace : WordTrace (prefixWord ++ tailWord_1174158) baseStart_1174158 baseEnd_1174158 := by
    simpa [prefixWord, tailWord_1174158, baseEnd_1174158] using wordTrace_append hprefix tailTrace_1174158
  have hstable : (prefixWord ++ tailWord_1174158).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1174158).length < 2 ^ (prefixWord ++ tailWord_1174158).sum := by decide
  have hdescent : baseEnd_1174158 < baseStart_1174158 := by decide
  rcases family_descends (prefixWord ++ tailWord_1174158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1174205 : List Nat := [1, 4, 1, 2, 1, 4, 1, 1, 4, 3]
def baseStart_1174205 : Nat := 118140960795 + 1174205 * 2 ^ 59
def prefixEnd_1174205 : Nat := 4983230072969 + 3 ^ 40 * 1174205 * 2
def baseEnd_1174205 : Nat := 401954367941789100824957

theorem tailTrace_1174205 : CollatzResearch.WordTrace tailWord_1174205 prefixEnd_1174205 401954367941789100824957 := by
  unfold tailWord_1174205
  simp only [CollatzResearch.WordTrace]
  refine ⟨42826774711063298093444069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28551183140708865395629379 42826774711063298093444069)
  ·
    refine ⟨8030020258324368392520763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 42826774711063298093444069 8030020258324368392520763)
    ·
      refine ⟨12045030387486552588781145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8030020258324368392520763 12045030387486552588781145)
      ·
        refine ⟨9033772790614914441585859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12045030387486552588781145 9033772790614914441585859)
        ·
          refine ⟨13550659185922371662378789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9033772790614914441585859 13550659185922371662378789)
          ·
            refine ⟨2540748597360444686696023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13550659185922371662378789 2540748597360444686696023)
            ·
              refine ⟨3811122896040667030044035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2540748597360444686696023 3811122896040667030044035)
              ·
                refine ⟨5716684344061000545066053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3811122896040667030044035 5716684344061000545066053)
                ·
                  refine ⟨1071878314511437602199885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5716684344061000545066053 1071878314511437602199885)
                  ·
                    refine ⟨401954367941789100824957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1071878314511437602199885 401954367941789100824957)
                    ·
                      rfl

theorem cell22_1174205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 1, 1, 4, 3].length) (baseStart_1174205 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1174205 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1174205 prefixEnd_1174205 := by exact prefixLift 1174205
  have htrace : WordTrace (prefixWord ++ tailWord_1174205) baseStart_1174205 baseEnd_1174205 := by
    simpa [prefixWord, tailWord_1174205, baseEnd_1174205] using wordTrace_append hprefix tailTrace_1174205
  have hstable : (prefixWord ++ tailWord_1174205).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1174205).length < 2 ^ (prefixWord ++ tailWord_1174205).sum := by decide
  have hdescent : baseEnd_1174205 < baseStart_1174205 := by decide
  rcases family_descends (prefixWord ++ tailWord_1174205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1174263 : List Nat := [1, 1, 3, 1, 1, 1, 3, 6, 5]
def baseStart_1174263 : Nat := 118140960795 + 1174263 * 2 ^ 59
def prefixEnd_1174263 : Nat := 4983230072969 + 3 ^ 40 * 1174263 * 2
def baseEnd_1174263 : Nat := 133991407509032094291593

theorem tailTrace_1174263 : CollatzResearch.WordTrace tailWord_1174263 prefixEnd_1174263 133991407509032094291593 := by
  unfold tailWord_1174263
  simp only [CollatzResearch.WordTrace]
  refine ⟨42828890144853173999055443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28552593429902115999370295 42828890144853173999055443)
  ·
    refine ⟨64243335217279760998583165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42828890144853173999055443 64243335217279760998583165)
    ·
      refine ⟨24091250706479910374468687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64243335217279760998583165 24091250706479910374468687)
      ·
        refine ⟨36136876059719865561703031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24091250706479910374468687 36136876059719865561703031)
        ·
          refine ⟨54205314089579798342554547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36136876059719865561703031 54205314089579798342554547)
          ·
            refine ⟨81307971134369697513831821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54205314089579798342554547 81307971134369697513831821)
            ·
              refine ⟨30490489175388636567686933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 81307971134369697513831821 30490489175388636567686933)
              ·
                refine ⟨1429241680096342339110325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 30490489175388636567686933 1429241680096342339110325)
                ·
                  refine ⟨133991407509032094291593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1429241680096342339110325 133991407509032094291593)
                  ·
                    rfl

theorem cell22_1174263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 6, 5].length) (baseStart_1174263 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1174263 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1174263 prefixEnd_1174263 := by exact prefixLift 1174263
  have htrace : WordTrace (prefixWord ++ tailWord_1174263) baseStart_1174263 baseEnd_1174263 := by
    simpa [prefixWord, tailWord_1174263, baseEnd_1174263] using wordTrace_append hprefix tailTrace_1174263
  have hstable : (prefixWord ++ tailWord_1174263).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1174263).length < 2 ^ (prefixWord ++ tailWord_1174263).sum := by decide
  have hdescent : baseEnd_1174263 < baseStart_1174263 := by decide
  rcases family_descends (prefixWord ++ tailWord_1174263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1174280 : List Nat := [2, 1, 3, 2, 2, 3, 1, 3, 5]
def baseStart_1174280 : Nat := 118140960795 + 1174280 * 2 ^ 59
def prefixEnd_1174280 : Nat := 4983230072969 + 3 ^ 40 * 1174280 * 2
def baseEnd_1174280 : Nat := 133993347324837968399909

theorem tailTrace_1174280 : CollatzResearch.WordTrace tailWord_1174280 prefixEnd_1174280 133993347324837968399909 := by
  unfold tailWord_1174280
  simp only [CollatzResearch.WordTrace]
  refine ⟨21414755092895792951212147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28553006790527723934949529 21414755092895792951212147)
  ·
    refine ⟨32122132639343689426818221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21414755092895792951212147 32122132639343689426818221)
    ·
      refine ⟨12045799739753883535056833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32122132639343689426818221 12045799739753883535056833)
      ·
        refine ⟨9034349804815412651292625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12045799739753883535056833 9034349804815412651292625)
        ·
          refine ⟨6775762353611559488469469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9034349804815412651292625 6775762353611559488469469)
          ·
            refine ⟨2540910882604334808176051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6775762353611559488469469 2540910882604334808176051)
            ·
              refine ⟨3811366323906502212264077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2540910882604334808176051 3811366323906502212264077)
              ·
                refine ⟨1429262371464938329599029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3811366323906502212264077 1429262371464938329599029)
                ·
                  refine ⟨133993347324837968399909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1429262371464938329599029 133993347324837968399909)
                  ·
                    rfl

theorem cell22_1174280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 1, 3, 5].length) (baseStart_1174280 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1174280 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1174280 prefixEnd_1174280 := by exact prefixLift 1174280
  have htrace : WordTrace (prefixWord ++ tailWord_1174280) baseStart_1174280 baseEnd_1174280 := by
    simpa [prefixWord, tailWord_1174280, baseEnd_1174280] using wordTrace_append hprefix tailTrace_1174280
  have hstable : (prefixWord ++ tailWord_1174280).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1174280).length < 2 ^ (prefixWord ++ tailWord_1174280).sum := by decide
  have hdescent : baseEnd_1174280 < baseStart_1174280 := by decide
  rcases family_descends (prefixWord ++ tailWord_1174280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1174314 : List Nat := [3, 1, 4, 3, 1, 1, 2, 2, 5]
def baseStart_1174314 : Nat := 118140960795 + 1174314 * 2 ^ 59
def prefixEnd_1174314 : Nat := 4983230072969 + 3 ^ 40 * 1174314 * 2
def baseEnd_1174314 : Nat := 133997226956449716616541

theorem tailTrace_1174314 : CollatzResearch.WordTrace tailWord_1174314 prefixEnd_1174314 133997226956449716616541 := by
  unfold tailWord_1174314
  simp only [CollatzResearch.WordTrace]
  refine ⟨10707687566917102427290499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28553833511778939806107997 10707687566917102427290499)
  ·
    refine ⟨16061531350375653640935749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10707687566917102427290499 16061531350375653640935749)
    ·
      refine ⟨3011537128195435057675453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16061531350375653640935749 3011537128195435057675453)
      ·
        refine ⟨1129326423073288146628295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3011537128195435057675453 1129326423073288146628295)
        ·
          refine ⟨1693989634609932219942443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1129326423073288146628295 1693989634609932219942443)
          ·
            refine ⟨2540984451914898329913665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1693989634609932219942443 2540984451914898329913665)
            ·
              refine ⟨1905738338936173747435249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2540984451914898329913665 1905738338936173747435249)
              ·
                refine ⟨1429303754202130310576437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1905738338936173747435249 1429303754202130310576437)
                ·
                  refine ⟨133997226956449716616541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1429303754202130310576437 133997226956449716616541)
                  ·
                    rfl

theorem cell22_1174314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 2, 2, 5].length) (baseStart_1174314 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1174314 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1174314 prefixEnd_1174314 := by exact prefixLift 1174314
  have htrace : WordTrace (prefixWord ++ tailWord_1174314) baseStart_1174314 baseEnd_1174314 := by
    simpa [prefixWord, tailWord_1174314, baseEnd_1174314] using wordTrace_append hprefix tailTrace_1174314
  have hstable : (prefixWord ++ tailWord_1174314).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1174314).length < 2 ^ (prefixWord ++ tailWord_1174314).sum := by decide
  have hdescent : baseEnd_1174314 < baseStart_1174314 := by decide
  rcases family_descends (prefixWord ++ tailWord_1174314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1174318 : List Nat := [4, 1, 3, 2, 1, 3, 2, 2, 1, 3]
def baseStart_1174318 : Nat := 118140960795 + 1174318 * 2 ^ 59
def prefixEnd_1174318 : Nat := 4983230072969 + 3 ^ 40 * 1174318 * 2
def baseEnd_1174318 : Nat := 401993050151094472749611

theorem tailTrace_1174318 : CollatzResearch.WordTrace tailWord_1174318 prefixEnd_1174318 401993050151094472749611 := by
  unfold tailWord_1174318
  simp only [CollatzResearch.WordTrace]
  refine ⟨5353862019956739799038451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28553930773102612261538405 5353862019956739799038451)
  ·
    refine ⟨8030793029935109698557677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5353862019956739799038451 8030793029935109698557677)
    ·
      refine ⟨3011547386225666136959129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8030793029935109698557677 3011547386225666136959129)
      ·
        refine ⟨2258660539669249602719347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3011547386225666136959129 2258660539669249602719347)
        ·
          refine ⟨3387990809503874404079021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2258660539669249602719347 3387990809503874404079021)
          ·
            refine ⟨1270496553563952901529633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3387990809503874404079021 1270496553563952901529633)
            ·
              refine ⟨952872415172964676147225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1270496553563952901529633 952872415172964676147225)
              ·
                refine ⟨714654311379723507110419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 952872415172964676147225 714654311379723507110419)
                ·
                  refine ⟨1071981467069585260665629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 714654311379723507110419 1071981467069585260665629)
                  ·
                    refine ⟨401993050151094472749611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1071981467069585260665629 401993050151094472749611)
                    ·
                      rfl

theorem cell22_1174318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 3, 2, 2, 1, 3].length) (baseStart_1174318 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1174318 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1174318 prefixEnd_1174318 := by exact prefixLift 1174318
  have htrace : WordTrace (prefixWord ++ tailWord_1174318) baseStart_1174318 baseEnd_1174318 := by
    simpa [prefixWord, tailWord_1174318, baseEnd_1174318] using wordTrace_append hprefix tailTrace_1174318
  have hstable : (prefixWord ++ tailWord_1174318).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1174318).length < 2 ^ (prefixWord ++ tailWord_1174318).sum := by decide
  have hdescent : baseEnd_1174318 < baseStart_1174318 := by decide
  rcases family_descends (prefixWord ++ tailWord_1174318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1174383 : List Nat := [1, 1, 2, 1, 3, 1, 1, 3, 1, 8]
def baseStart_1174383 : Nat := 118140960795 + 1174383 * 2 ^ 59
def prefixEnd_1174383 : Nat := 4983230072969 + 3 ^ 40 * 1174383 * 2
def baseEnd_1174383 : Nat := 402015300979455969874411

theorem tailTrace_1174383 : CollatzResearch.WordTrace tailWord_1174383 prefixEnd_1174383 402015300979455969874411 := by
  unfold tailWord_1174383
  simp only [CollatzResearch.WordTrace]
  refine ⟨42833266904418434493423803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28555511269612289662282535 42833266904418434493423803)
  ·
    refine ⟨64249900356627651740135705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42833266904418434493423803 64249900356627651740135705)
    ·
      refine ⟨48187425267470738805101779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64249900356627651740135705 48187425267470738805101779)
      ·
        refine ⟨72281137901206108207652669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48187425267470738805101779 72281137901206108207652669)
        ·
          refine ⟨27105426712952290577869751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 72281137901206108207652669 27105426712952290577869751)
          ·
            refine ⟨40658140069428435866804627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27105426712952290577869751 40658140069428435866804627)
            ·
              refine ⟨60987210104142653800206941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40658140069428435866804627 60987210104142653800206941)
              ·
                refine ⟨22870203789053495175077603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 60987210104142653800206941 22870203789053495175077603)
                ·
                  refine ⟨34305305683580242762616405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22870203789053495175077603 34305305683580242762616405)
                  ·
                    refine ⟨402015300979455969874411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 34305305683580242762616405 402015300979455969874411)
                    ·
                      rfl

theorem cell22_1174383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 3, 1, 8].length) (baseStart_1174383 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1174383 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1174383 prefixEnd_1174383 := by exact prefixLift 1174383
  have htrace : WordTrace (prefixWord ++ tailWord_1174383) baseStart_1174383 baseEnd_1174383 := by
    simpa [prefixWord, tailWord_1174383, baseEnd_1174383] using wordTrace_append hprefix tailTrace_1174383
  have hstable : (prefixWord ++ tailWord_1174383).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1174383).length < 2 ^ (prefixWord ++ tailWord_1174383).sum := by decide
  have hdescent : baseEnd_1174383 < baseStart_1174383 := by decide
  rcases family_descends (prefixWord ++ tailWord_1174383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1174436 : List Nat := [2, 3, 1, 2, 1, 2, 5, 2, 1, 3]
def baseStart_1174436 : Nat := 118140960795 + 1174436 * 2 ^ 59
def prefixEnd_1174436 : Nat := 4983230072969 + 3 ^ 40 * 1174436 * 2
def baseEnd_1174436 : Nat := 402033443962581498299249

theorem tailTrace_1174436 : CollatzResearch.WordTrace tailWord_1174436 prefixEnd_1174436 402033443962581498299249 := by
  unfold tailWord_1174436
  simp only [CollatzResearch.WordTrace]
  refine ⟨21417599986613212272551581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28556799982150949696735441 21417599986613212272551581)
  ·
    refine ⟨8031599994979954602206843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21417599986613212272551581 8031599994979954602206843)
    ·
      refine ⟨12047399992469931903310265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8031599994979954602206843 12047399992469931903310265)
      ·
        refine ⟨9035549994352448927482699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12047399992469931903310265 9035549994352448927482699)
        ·
          refine ⟨13553324991528673391224049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9035549994352448927482699 13553324991528673391224049)
          ·
            refine ⟨10164993743646505043418037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13553324991528673391224049 10164993743646505043418037)
            ·
              refine ⟨952968163466859847820441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10164993743646505043418037 952968163466859847820441)
              ·
                refine ⟨714726122600144885865331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 952968163466859847820441 714726122600144885865331)
                ·
                  refine ⟨1072089183900217328797997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 714726122600144885865331 1072089183900217328797997)
                  ·
                    refine ⟨402033443962581498299249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1072089183900217328797997 402033443962581498299249)
                    ·
                      rfl

theorem cell22_1174436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 5, 2, 1, 3].length) (baseStart_1174436 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1174436 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1174436 prefixEnd_1174436 := by exact prefixLift 1174436
  have htrace : WordTrace (prefixWord ++ tailWord_1174436) baseStart_1174436 baseEnd_1174436 := by
    simpa [prefixWord, tailWord_1174436, baseEnd_1174436] using wordTrace_append hprefix tailTrace_1174436
  have hstable : (prefixWord ++ tailWord_1174436).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1174436).length < 2 ^ (prefixWord ++ tailWord_1174436).sum := by decide
  have hdescent : baseEnd_1174436 < baseStart_1174436 := by decide
  rcases family_descends (prefixWord ++ tailWord_1174436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1174462 : List Nat := [4, 2, 1, 1, 1, 2, 3, 1, 3, 4]
def baseStart_1174462 : Nat := 118140960795 + 1174462 * 2 ^ 59
def prefixEnd_1174462 : Nat := 4983230072969 + 3 ^ 40 * 1174462 * 2
def baseEnd_1174462 : Nat := 402042344293926097149169

theorem tailTrace_1174462 : CollatzResearch.WordTrace tailWord_1174462 prefixEnd_1174462 402042344293926097149169 := by
  unfold tailWord_1174462
  simp only [CollatzResearch.WordTrace]
  refine ⟨5354518533891528873193705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28557432180754820657033093 5354518533891528873193705)
  ·
    refine ⟨4015888900418646654895279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5354518533891528873193705 4015888900418646654895279)
    ·
      refine ⟨6023833350627969982342919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4015888900418646654895279 6023833350627969982342919)
      ·
        refine ⟨9035750025941954973514379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6023833350627969982342919 9035750025941954973514379)
        ·
          refine ⟨13553625038912932460271569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9035750025941954973514379 13553625038912932460271569)
          ·
            refine ⟨10165218779184699345203677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13553625038912932460271569 10165218779184699345203677)
            ·
              refine ⟨3811957042194262254451379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10165218779184699345203677 3811957042194262254451379)
              ·
                refine ⟨5717935563291393381677069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3811957042194262254451379 5717935563291393381677069)
                ·
                  refine ⟨2144225836234272518128901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5717935563291393381677069 2144225836234272518128901)
                  ·
                    refine ⟨402042344293926097149169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2144225836234272518128901 402042344293926097149169)
                    ·
                      rfl

theorem cell22_1174462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 3, 1, 3, 4].length) (baseStart_1174462 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1174462 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1174462 prefixEnd_1174462 := by exact prefixLift 1174462
  have htrace : WordTrace (prefixWord ++ tailWord_1174462) baseStart_1174462 baseEnd_1174462 := by
    simpa [prefixWord, tailWord_1174462, baseEnd_1174462] using wordTrace_append hprefix tailTrace_1174462
  have hstable : (prefixWord ++ tailWord_1174462).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1174462).length < 2 ^ (prefixWord ++ tailWord_1174462).sum := by decide
  have hdescent : baseEnd_1174462 < baseStart_1174462 := by decide
  rcases family_descends (prefixWord ++ tailWord_1174462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1174475 : List Nat := [1, 1, 1, 1, 3, 5, 1, 1, 3, 5]
def baseStart_1174475 : Nat := 118140960795 + 1174475 * 2 ^ 59
def prefixEnd_1174475 : Nat := 4983230072969 + 3 ^ 40 * 1174475 * 2
def baseEnd_1174475 : Nat := 402046794459598396574129

theorem tailTrace_1174475 : CollatzResearch.WordTrace tailWord_1174475 prefixEnd_1174475 402046794459598396574129 := by
  unfold tailWord_1174475
  simp only [CollatzResearch.WordTrace]
  refine ⟨42836622420085134205772879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28557748280056756137181919 42836622420085134205772879)
  ·
    refine ⟨64254933630127701308659319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42836622420085134205772879 64254933630127701308659319)
    ·
      refine ⟨96382400445191551962988979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64254933630127701308659319 96382400445191551962988979)
      ·
        refine ⟨144573600667787327944483469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96382400445191551962988979 144573600667787327944483469)
        ·
          refine ⟨54215100250420247979181301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 144573600667787327944483469 54215100250420247979181301)
          ·
            refine ⟨5082665648476898248048247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 54215100250420247979181301 5082665648476898248048247)
            ·
              refine ⟨7623998472715347372072371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5082665648476898248048247 7623998472715347372072371)
              ·
                refine ⟨11435997709073021058108557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7623998472715347372072371 11435997709073021058108557)
                ·
                  refine ⟨4288499140902382896790709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11435997709073021058108557 4288499140902382896790709)
                  ·
                    refine ⟨402046794459598396574129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4288499140902382896790709 402046794459598396574129)
                    ·
                      rfl

theorem cell22_1174475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 1, 3, 5].length) (baseStart_1174475 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1174475 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1174475 prefixEnd_1174475 := by exact prefixLift 1174475
  have htrace : WordTrace (prefixWord ++ tailWord_1174475) baseStart_1174475 baseEnd_1174475 := by
    simpa [prefixWord, tailWord_1174475, baseEnd_1174475] using wordTrace_append hprefix tailTrace_1174475
  have hstable : (prefixWord ++ tailWord_1174475).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1174475).length < 2 ^ (prefixWord ++ tailWord_1174475).sum := by decide
  have hdescent : baseEnd_1174475 < baseStart_1174475 := by decide
  rcases family_descends (prefixWord ++ tailWord_1174475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1174479 : List Nat := [1, 1, 2, 1, 1, 7, 3, 1, 1, 4]
def baseStart_1174479 : Nat := 118140960795 + 1174479 * 2 ^ 59
def prefixEnd_1174479 : Nat := 4983230072969 + 3 ^ 40 * 1174479 * 2
def baseEnd_1174479 : Nat := 402048163741343719474117

theorem tailTrace_1174479 : CollatzResearch.WordTrace tailWord_1174479 prefixEnd_1174479 402048163741343719474117 := by
  unfold tailWord_1174479
  simp only [CollatzResearch.WordTrace]
  refine ⟨42836768312070642888918491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28557845541380428592612327 42836768312070642888918491)
  ·
    refine ⟨64255152468105964333377737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42836768312070642888918491 64255152468105964333377737)
    ·
      refine ⟨48191364351079473250033303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64255152468105964333377737 48191364351079473250033303)
      ·
        refine ⟨72287046526619209875049955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48191364351079473250033303 72287046526619209875049955)
        ·
          refine ⟨108430569789928814812574933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72287046526619209875049955 108430569789928814812574933)
          ·
            refine ⟨2541341479451456597169725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 108430569789928814812574933 2541341479451456597169725)
            ·
              refine ⟨953003054794296223938647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2541341479451456597169725 953003054794296223938647)
              ·
                refine ⟨1429504582191444335907971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 953003054794296223938647 1429504582191444335907971)
                ·
                  refine ⟨2144256873287166503861957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1429504582191444335907971 2144256873287166503861957)
                  ·
                    refine ⟨402048163741343719474117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2144256873287166503861957 402048163741343719474117)
                    ·
                      rfl

theorem cell22_1174479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 3, 1, 1, 4].length) (baseStart_1174479 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1174479 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1174479 prefixEnd_1174479 := by exact prefixLift 1174479
  have htrace : WordTrace (prefixWord ++ tailWord_1174479) baseStart_1174479 baseEnd_1174479 := by
    simpa [prefixWord, tailWord_1174479, baseEnd_1174479] using wordTrace_append hprefix tailTrace_1174479
  have hstable : (prefixWord ++ tailWord_1174479).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1174479).length < 2 ^ (prefixWord ++ tailWord_1174479).sum := by decide
  have hdescent : baseEnd_1174479 < baseStart_1174479 := by decide
  rcases family_descends (prefixWord ++ tailWord_1174479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1174524 : List Nat := [2, 2, 2, 1, 2, 5, 1, 1, 2, 4]
def baseStart_1174524 : Nat := 118140960795 + 1174524 * 2 ^ 59
def prefixEnd_1174524 : Nat := 4983230072969 + 3 ^ 40 * 1174524 * 2
def baseEnd_1174524 : Nat := 402063568160978602098979

theorem tailTrace_1174524 : CollatzResearch.WordTrace tailWord_1174524 prefixEnd_1174524 402063568160978602098979 := by
  unfold tailWord_1174524
  simp only [CollatzResearch.WordTrace]
  refine ⟨21419204798453807787153313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28558939731271743716204417 21419204798453807787153313)
  ·
    refine ⟨16064403598840355840364985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21419204798453807787153313 16064403598840355840364985)
    ·
      refine ⟨12048302699130266880273739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16064403598840355840364985 12048302699130266880273739)
      ·
        refine ⟨18072454048695400320410609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12048302699130266880273739 18072454048695400320410609)
        ·
          refine ⟨13554340536521550240307957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18072454048695400320410609 13554340536521550240307957)
          ·
            refine ⟨1270719425298895335028871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 13554340536521550240307957 1270719425298895335028871)
            ·
              refine ⟨1906079137948343002543307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1270719425298895335028871 1906079137948343002543307)
              ·
                refine ⟨2859118706922514503814961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1906079137948343002543307 2859118706922514503814961)
                ·
                  refine ⟨2144339030191885877861221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2859118706922514503814961 2144339030191885877861221)
                  ·
                    refine ⟨402063568160978602098979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2144339030191885877861221 402063568160978602098979)
                    ·
                      rfl

theorem cell22_1174524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 5, 1, 1, 2, 4].length) (baseStart_1174524 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1174524 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1174524 prefixEnd_1174524 := by exact prefixLift 1174524
  have htrace : WordTrace (prefixWord ++ tailWord_1174524) baseStart_1174524 baseEnd_1174524 := by
    simpa [prefixWord, tailWord_1174524, baseEnd_1174524] using wordTrace_append hprefix tailTrace_1174524
  have hstable : (prefixWord ++ tailWord_1174524).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1174524).length < 2 ^ (prefixWord ++ tailWord_1174524).sum := by decide
  have hdescent : baseEnd_1174524 < baseStart_1174524 := by decide
  rcases family_descends (prefixWord ++ tailWord_1174524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1174530 : List Nat := [3, 4, 1, 3, 1, 2, 2, 1, 1, 4]
def baseStart_1174530 : Nat := 118140960795 + 1174530 * 2 ^ 59
def prefixEnd_1174530 : Nat := 4983230072969 + 3 ^ 40 * 1174530 * 2
def baseEnd_1174530 : Nat := 402065622083596586448961

theorem tailTrace_1174530 : CollatzResearch.WordTrace tailWord_1174530 prefixEnd_1174530 402065622083596586448961 := by
  unfold tailWord_1174530
  simp only [CollatzResearch.WordTrace]
  refine ⟨10709657108721469649756261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28559085623257252399350029 10709657108721469649756261)
  ·
    refine ⟨2008060707885275559329299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10709657108721469649756261 2008060707885275559329299)
    ·
      refine ⟨3012091061827913338993949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2008060707885275559329299 3012091061827913338993949)
      ·
        refine ⟨1129534148185467502122731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3012091061827913338993949 1129534148185467502122731)
        ·
          refine ⟨1694301222278201253184097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1129534148185467502122731 1694301222278201253184097)
          ·
            refine ⟨1270725916708650939888073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1694301222278201253184097 1270725916708650939888073)
            ·
              refine ⟨953044437531488204916055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1270725916708650939888073 953044437531488204916055)
              ·
                refine ⟨1429566656297232307374083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 953044437531488204916055 1429566656297232307374083)
                ·
                  refine ⟨2144349984445848461061125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1429566656297232307374083 2144349984445848461061125)
                  ·
                    refine ⟨402065622083596586448961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2144349984445848461061125 402065622083596586448961)
                    ·
                      rfl

theorem cell22_1174530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 2, 2, 1, 1, 4].length) (baseStart_1174530 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1174530 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1174530 prefixEnd_1174530 := by exact prefixLift 1174530
  have htrace : WordTrace (prefixWord ++ tailWord_1174530) baseStart_1174530 baseEnd_1174530 := by
    simpa [prefixWord, tailWord_1174530, baseEnd_1174530] using wordTrace_append hprefix tailTrace_1174530
  have hstable : (prefixWord ++ tailWord_1174530).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1174530).length < 2 ^ (prefixWord ++ tailWord_1174530).sum := by decide
  have hdescent : baseEnd_1174530 < baseStart_1174530 := by decide
  rcases family_descends (prefixWord ++ tailWord_1174530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1174554 : List Nat := [3, 1, 1, 3, 1, 2, 4, 1, 3, 3]
def baseStart_1174554 : Nat := 118140960795 + 1174554 * 2 ^ 59
def prefixEnd_1174554 : Nat := 4983230072969 + 3 ^ 40 * 1174554 * 2
def baseEnd_1174554 : Nat := 402073837774068523848887

theorem tailTrace_1174554 : CollatzResearch.WordTrace tailWord_1174554 prefixEnd_1174554 402073837774068523848887 := by
  unfold tailWord_1174554
  simp only [CollatzResearch.WordTrace]
  refine ⟨10709875946699732674474679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28559669191199287131932477 10709875946699732674474679)
  ·
    refine ⟨16064813920049599011712019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10709875946699732674474679 16064813920049599011712019)
    ·
      refine ⟨24097220880074398517568029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16064813920049599011712019 24097220880074398517568029)
      ·
        refine ⟨9036457830027899444088011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24097220880074398517568029 9036457830027899444088011)
        ·
          refine ⟨13554686745041849166132017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9036457830027899444088011 13554686745041849166132017)
          ·
            refine ⟨10166015058781386874599013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13554686745041849166132017 10166015058781386874599013)
            ·
              refine ⟨1906127823521510038987315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10166015058781386874599013 1906127823521510038987315)
              ·
                refine ⟨2859191735282265058480973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1906127823521510038987315 2859191735282265058480973)
                ·
                  refine ⟨1072196900730849396930365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2859191735282265058480973 1072196900730849396930365)
                  ·
                    refine ⟨402073837774068523848887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1072196900730849396930365 402073837774068523848887)
                    ·
                      rfl

theorem cell22_1174554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 4, 1, 3, 3].length) (baseStart_1174554 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1174554 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1174554 prefixEnd_1174554 := by exact prefixLift 1174554
  have htrace : WordTrace (prefixWord ++ tailWord_1174554) baseStart_1174554 baseEnd_1174554 := by
    simpa [prefixWord, tailWord_1174554, baseEnd_1174554] using wordTrace_append hprefix tailTrace_1174554
  have hstable : (prefixWord ++ tailWord_1174554).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1174554).length < 2 ^ (prefixWord ++ tailWord_1174554).sum := by decide
  have hdescent : baseEnd_1174554 < baseStart_1174554 := by decide
  rcases family_descends (prefixWord ++ tailWord_1174554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1174588 : List Nat := [2, 2, 2, 2, 2, 4, 1, 3, 1, 3]
def baseStart_1174588 : Nat := 118140960795 + 1174588 * 2 ^ 59
def prefixEnd_1174588 : Nat := 4983230072969 + 3 ^ 40 * 1174588 * 2
def baseEnd_1174588 : Nat := 402085476668903768498783

theorem tailTrace_1174588 : CollatzResearch.WordTrace tailWord_1174588 prefixEnd_1174588 402085476668903768498783 := by
  unfold tailWord_1174588
  simp only [CollatzResearch.WordTrace]
  refine ⟨21420371934337877252318209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28560495912450503003090945 21420371934337877252318209)
  ·
    refine ⟨16065278950753407939238657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21420371934337877252318209 16065278950753407939238657)
    ·
      refine ⟨12048959213065055954428993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16065278950753407939238657 12048959213065055954428993)
      ·
        refine ⟨9036719409798791965821745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12048959213065055954428993 9036719409798791965821745)
        ·
          refine ⟨6777539557349093974366309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9036719409798791965821745 6777539557349093974366309)
          ·
            refine ⟨1270788667002955120193683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6777539557349093974366309 1270788667002955120193683)
            ·
              refine ⟨1906183000504432680290525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1270788667002955120193683 1906183000504432680290525)
              ·
                refine ⟨714818625189162255108947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1906183000504432680290525 714818625189162255108947)
                ·
                  refine ⟨1072227937783743382663421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 714818625189162255108947 1072227937783743382663421)
                  ·
                    refine ⟨402085476668903768498783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1072227937783743382663421 402085476668903768498783)
                    ·
                      rfl

theorem cell22_1174588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 4, 1, 3, 1, 3].length) (baseStart_1174588 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1174588 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1174588 prefixEnd_1174588 := by exact prefixLift 1174588
  have htrace : WordTrace (prefixWord ++ tailWord_1174588) baseStart_1174588 baseEnd_1174588 := by
    simpa [prefixWord, tailWord_1174588, baseEnd_1174588] using wordTrace_append hprefix tailTrace_1174588
  have hstable : (prefixWord ++ tailWord_1174588).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1174588).length < 2 ^ (prefixWord ++ tailWord_1174588).sum := by decide
  have hdescent : baseEnd_1174588 < baseStart_1174588 := by decide
  rcases family_descends (prefixWord ++ tailWord_1174588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1174605 : List Nat := [1, 6, 1, 1, 1, 3, 3, 2, 1, 3]
def baseStart_1174605 : Nat := 118140960795 + 1174605 * 2 ^ 59
def prefixEnd_1174605 : Nat := 4983230072969 + 3 ^ 40 * 1174605 * 2
def baseEnd_1174605 : Nat := 402091296116321390823731

theorem tailTrace_1174605 : CollatzResearch.WordTrace tailWord_1174605 prefixEnd_1174605 402091296116321390823731 := by
  unfold tailWord_1174605
  simp only [CollatzResearch.WordTrace]
  refine ⟨42841363909614166408005269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28560909273076110938670179 42841363909614166408005269)
  ·
    refine ⟨2008188933263164050375247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 42841363909614166408005269 2008188933263164050375247)
    ·
      refine ⟨3012283399894746075562871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2008188933263164050375247 3012283399894746075562871)
      ·
        refine ⟨4518425099842119113344307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3012283399894746075562871 4518425099842119113344307)
        ·
          refine ⟨6777637649763178670016461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4518425099842119113344307 6777637649763178670016461)
          ·
            refine ⟨2541614118661192001256173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6777637649763178670016461 2541614118661192001256173)
            ·
              refine ⟨953105294497947000471065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2541614118661192001256173 953105294497947000471065)
              ·
                refine ⟨714828970873460250353299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 953105294497947000471065 714828970873460250353299)
                ·
                  refine ⟨1072243456310190375529949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 714828970873460250353299 1072243456310190375529949)
                  ·
                    refine ⟨402091296116321390823731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1072243456310190375529949 402091296116321390823731)
                    ·
                      rfl

theorem cell22_1174605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 3, 2, 1, 3].length) (baseStart_1174605 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1174605 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1174605 prefixEnd_1174605 := by exact prefixLift 1174605
  have htrace : WordTrace (prefixWord ++ tailWord_1174605) baseStart_1174605 baseEnd_1174605 := by
    simpa [prefixWord, tailWord_1174605, baseEnd_1174605] using wordTrace_append hprefix tailTrace_1174605
  have hstable : (prefixWord ++ tailWord_1174605).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1174605).length < 2 ^ (prefixWord ++ tailWord_1174605).sum := by decide
  have hdescent : baseEnd_1174605 < baseStart_1174605 := by decide
  rcases family_descends (prefixWord ++ tailWord_1174605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1174627 : List Nat := [1, 1, 1, 5, 1, 1, 1, 5, 1, 5]
def baseStart_1174627 : Nat := 118140960795 + 1174627 * 2 ^ 59
def prefixEnd_1174627 : Nat := 4983230072969 + 3 ^ 40 * 1174627 * 2
def baseEnd_1174627 : Nat := 402098827165920666773663

theorem tailTrace_1174627 : CollatzResearch.WordTrace tailWord_1174627 prefixEnd_1174627 402098827165920666773663 := by
  unfold tailWord_1174627
  simp only [CollatzResearch.WordTrace]
  refine ⟨42842166315534464165306135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28561444210356309443537423 42842166315534464165306135)
  ·
    refine ⟨64263249473301696247959203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42842166315534464165306135 64263249473301696247959203)
    ·
      refine ⟨96394874209952544371938805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64263249473301696247959203 96394874209952544371938805)
      ·
        refine ⟨9037019457183051034869263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 96394874209952544371938805 9037019457183051034869263)
        ·
          refine ⟨13555529185774576552303895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9037019457183051034869263 13555529185774576552303895)
          ·
            refine ⟨20333293778661864828455843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13555529185774576552303895 20333293778661864828455843)
            ·
              refine ⟨30499940667992797242683765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20333293778661864828455843 30499940667992797242683765)
              ·
                refine ⟨2859369437624324741501603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 30499940667992797242683765 2859369437624324741501603)
                ·
                  refine ⟨4289054156436487112252405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2859369437624324741501603 4289054156436487112252405)
                  ·
                    refine ⟨402098827165920666773663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4289054156436487112252405 402098827165920666773663)
                    ·
                      rfl

theorem cell22_1174627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 5, 1, 5].length) (baseStart_1174627 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1174627 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1174627 prefixEnd_1174627 := by exact prefixLift 1174627
  have htrace : WordTrace (prefixWord ++ tailWord_1174627) baseStart_1174627 baseEnd_1174627 := by
    simpa [prefixWord, tailWord_1174627, baseEnd_1174627] using wordTrace_append hprefix tailTrace_1174627
  have hstable : (prefixWord ++ tailWord_1174627).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1174627).length < 2 ^ (prefixWord ++ tailWord_1174627).sum := by decide
  have hdescent : baseEnd_1174627 < baseStart_1174627 := by decide
  rcases family_descends (prefixWord ++ tailWord_1174627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1174631 : List Nat := [1, 1, 5, 1, 1, 5, 1, 2, 1, 4]
def baseStart_1174631 : Nat := 118140960795 + 1174631 * 2 ^ 59
def prefixEnd_1174631 : Nat := 4983230072969 + 3 ^ 40 * 1174631 * 2
def baseEnd_1174631 : Nat := 402100196447665989673651

theorem tailTrace_1174631 : CollatzResearch.WordTrace tailWord_1174631 prefixEnd_1174631 402100196447665989673651 := by
  unfold tailWord_1174631
  simp only [CollatzResearch.WordTrace]
  refine ⟨42842312207519972848451747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28561541471679981898967831 42842312207519972848451747)
  ·
    refine ⟨64263468311279959272677621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42842312207519972848451747 64263468311279959272677621)
    ·
      refine ⟨6024700154182496181813527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 64263468311279959272677621 6024700154182496181813527)
      ·
        refine ⟨9037050231273744272720291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6024700154182496181813527 9037050231273744272720291)
        ·
          refine ⟨13555575346910616409080437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9037050231273744272720291 13555575346910616409080437)
          ·
            refine ⟨1270835188772870288351291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 13555575346910616409080437 1270835188772870288351291)
            ·
              refine ⟨1906252783159305432526937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1270835188772870288351291 1906252783159305432526937)
              ·
                refine ⟨1429689587369479074395203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1906252783159305432526937 1429689587369479074395203)
                ·
                  refine ⟨2144534381054218611592805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1429689587369479074395203 2144534381054218611592805)
                  ·
                    refine ⟨402100196447665989673651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2144534381054218611592805 402100196447665989673651)
                    ·
                      rfl

theorem cell22_1174631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 5, 1, 2, 1, 4].length) (baseStart_1174631 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1174631 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1174631 prefixEnd_1174631 := by exact prefixLift 1174631
  have htrace : WordTrace (prefixWord ++ tailWord_1174631) baseStart_1174631 baseEnd_1174631 := by
    simpa [prefixWord, tailWord_1174631, baseEnd_1174631] using wordTrace_append hprefix tailTrace_1174631
  have hstable : (prefixWord ++ tailWord_1174631).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1174631).length < 2 ^ (prefixWord ++ tailWord_1174631).sum := by decide
  have hdescent : baseEnd_1174631 < baseStart_1174631 := by decide
  rcases family_descends (prefixWord ++ tailWord_1174631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1174646 : List Nat := [5, 1, 1, 2, 1, 1, 2, 5, 4]
def baseStart_1174646 : Nat := 118140960795 + 1174646 * 2 ^ 59
def prefixEnd_1174646 : Nat := 4983230072969 + 3 ^ 40 * 1174646 * 2
def baseEnd_1174646 : Nat := 134035110418070316849535

theorem tailTrace_1174646 : CollatzResearch.WordTrace tailWord_1174646 prefixEnd_1174646 134035110418070316849535 := by
  unfold tailWord_1174646
  simp only [CollatzResearch.WordTrace]
  refine ⟨2677678706404101900640487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 28561906201643753606831861 2677678706404101900640487)
  ·
    refine ⟨4016518059606152850960731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2677678706404101900640487 4016518059606152850960731)
    ·
      refine ⟨6024777089409229276441097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4016518059606152850960731 6024777089409229276441097)
      ·
        refine ⟨4518582817056921957330823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6024777089409229276441097 4518582817056921957330823)
        ·
          refine ⟨6777874225585382935996235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4518582817056921957330823 6777874225585382935996235)
          ·
            refine ⟨10166811338378074403994353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6777874225585382935996235 10166811338378074403994353)
            ·
              refine ⟨7625108503783555802995765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10166811338378074403994353 7625108503783555802995765)
              ·
                refine ⟨714853922229708356530853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7625108503783555802995765 714853922229708356530853)
                ·
                  refine ⟨134035110418070316849535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 714853922229708356530853 134035110418070316849535)
                  ·
                    rfl

theorem cell22_1174646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 5, 4].length) (baseStart_1174646 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1174646 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1174646 prefixEnd_1174646 := by exact prefixLift 1174646
  have htrace : WordTrace (prefixWord ++ tailWord_1174646) baseStart_1174646 baseEnd_1174646 := by
    simpa [prefixWord, tailWord_1174646, baseEnd_1174646] using wordTrace_append hprefix tailTrace_1174646
  have hstable : (prefixWord ++ tailWord_1174646).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1174646).length < 2 ^ (prefixWord ++ tailWord_1174646).sum := by decide
  have hdescent : baseEnd_1174646 < baseStart_1174646 := by decide
  rcases family_descends (prefixWord ++ tailWord_1174646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1174657 : List Nat := [1, 2, 4, 2, 2, 11]
def baseStart_1174657 : Nat := 118140960795 + 1174657 * 2 ^ 59
def prefixEnd_1174657 : Nat := 4983230072969 + 3 ^ 40 * 1174657 * 2
def baseEnd_1174657 : Nat := 4964309836777908500291

theorem tailTrace_1174657 : CollatzResearch.WordTrace tailWord_1174657 prefixEnd_1174657 4964309836777908500291 := by
  unfold tailWord_1174657
  simp only [CollatzResearch.WordTrace]
  refine ⟨42843260505425779288898225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28562173670283852859265483 42843260505425779288898225)
  ·
    refine ⟨32132445379069334466673669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42843260505425779288898225 32132445379069334466673669)
    ·
      refine ⟨6024833508575500212501313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32132445379069334466673669 6024833508575500212501313)
      ·
        refine ⟨4518625131431625159375985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6024833508575500212501313 4518625131431625159375985)
        ·
          refine ⟨3388968848573718869531989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4518625131431625159375985 3388968848573718869531989)
          ·
            refine ⟨4964309836777908500291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 3388968848573718869531989 4964309836777908500291)
            ·
              rfl

theorem cell22_1174657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 11].length) (baseStart_1174657 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1174657 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1174657 prefixEnd_1174657 := by exact prefixLift 1174657
  have htrace : WordTrace (prefixWord ++ tailWord_1174657) baseStart_1174657 baseEnd_1174657 := by
    simpa [prefixWord, tailWord_1174657, baseEnd_1174657] using wordTrace_append hprefix tailTrace_1174657
  have hstable : (prefixWord ++ tailWord_1174657).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1174657).length < 2 ^ (prefixWord ++ tailWord_1174657).sum := by decide
  have hdescent : baseEnd_1174657 < baseStart_1174657 := by decide
  rcases family_descends (prefixWord ++ tailWord_1174657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1174674 : List Nat := [3, 2, 3, 1, 1, 2, 3, 7]
def baseStart_1174674 : Nat := 118140960795 + 1174674 * 2 ^ 59
def prefixEnd_1174674 : Nat := 4983230072969 + 3 ^ 40 * 1174674 * 2
def baseEnd_1174674 : Nat := 44679435136269801205391

theorem tailTrace_1174674 : CollatzResearch.WordTrace tailWord_1174674 prefixEnd_1174674 44679435136269801205391 := by
  unfold tailWord_1174674
  simp only [CollatzResearch.WordTrace]
  refine ⟨10710970136591047798066769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28562587030909460794844717 10710970136591047798066769)
  ·
    refine ⟨8033227602443285848550077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10710970136591047798066769 8033227602443285848550077)
    ·
      refine ⟨3012460350916232193206279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8033227602443285848550077 3012460350916232193206279)
      ·
        refine ⟨4518690526374348289809419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3012460350916232193206279 4518690526374348289809419)
        ·
          refine ⟨6778035789561522434714129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4518690526374348289809419 6778035789561522434714129)
          ·
            refine ⟨5083526842171141826035597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6778035789561522434714129 5083526842171141826035597)
            ·
              refine ⟨1906322565814178184763349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5083526842171141826035597 1906322565814178184763349)
              ·
                refine ⟨44679435136269801205391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1906322565814178184763349 44679435136269801205391)
                ·
                  rfl

theorem cell22_1174674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 3, 7].length) (baseStart_1174674 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1174674 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1174674 prefixEnd_1174674 := by exact prefixLift 1174674
  have htrace : WordTrace (prefixWord ++ tailWord_1174674) baseStart_1174674 baseEnd_1174674 := by
    simpa [prefixWord, tailWord_1174674, baseEnd_1174674] using wordTrace_append hprefix tailTrace_1174674
  have hstable : (prefixWord ++ tailWord_1174674).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1174674).length < 2 ^ (prefixWord ++ tailWord_1174674).sum := by decide
  have hdescent : baseEnd_1174674 < baseStart_1174674 := by decide
  rcases family_descends (prefixWord ++ tailWord_1174674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1174719 : List Nat := [1, 1, 2, 2, 2, 2, 5, 2, 5]
def baseStart_1174719 : Nat := 118140960795 + 1174719 * 2 ^ 59
def prefixEnd_1174719 : Nat := 4983230072969 + 3 ^ 40 * 1174719 * 2
def baseEnd_1174719 : Nat := 134043440215354364491127

theorem tailTrace_1174719 : CollatzResearch.WordTrace tailWord_1174719 prefixEnd_1174719 134043440215354364491127 := by
  unfold tailWord_1174719
  simp only [CollatzResearch.WordTrace]
  refine ⟨42845521831201163877655211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28563681220800775918436807 42845521831201163877655211)
  ·
    refine ⟨64268282746801745816482817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42845521831201163877655211 64268282746801745816482817)
    ·
      refine ⟨48201212060101309362362113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64268282746801745816482817 48201212060101309362362113)
      ·
        refine ⟨36150909045075982021771585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48201212060101309362362113 36150909045075982021771585)
        ·
          refine ⟨27113181783806986516328689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36150909045075982021771585 27113181783806986516328689)
          ·
            refine ⟨20334886337855239887246517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27113181783806986516328689 20334886337855239887246517)
            ·
              refine ⟨1906395594173928739429361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 20334886337855239887246517 1906395594173928739429361)
              ·
                refine ⟨1429796695630446554572021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1906395594173928739429361 1429796695630446554572021)
                ·
                  refine ⟨134043440215354364491127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1429796695630446554572021 134043440215354364491127)
                  ·
                    rfl

theorem cell22_1174719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 5, 2, 5].length) (baseStart_1174719 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1174719 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1174719 prefixEnd_1174719 := by exact prefixLift 1174719
  have htrace : WordTrace (prefixWord ++ tailWord_1174719) baseStart_1174719 baseEnd_1174719 := by
    simpa [prefixWord, tailWord_1174719, baseEnd_1174719] using wordTrace_append hprefix tailTrace_1174719
  have hstable : (prefixWord ++ tailWord_1174719).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1174719).length < 2 ^ (prefixWord ++ tailWord_1174719).sum := by decide
  have hdescent : baseEnd_1174719 < baseStart_1174719 := by decide
  rcases family_descends (prefixWord ++ tailWord_1174719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1174757 : List Nat := [1, 3, 1, 4, 4, 1, 1, 3, 1, 3]
def baseStart_1174757 : Nat := 118140960795 + 1174757 * 2 ^ 59
def prefixEnd_1174757 : Nat := 4983230072969 + 3 ^ 40 * 1174757 * 2
def baseEnd_1174757 : Nat := 402143328822643661023265

theorem tailTrace_1174757 : CollatzResearch.WordTrace tailWord_1174757 prefixEnd_1174757 402143328822643661023265 := by
  unfold tailWord_1174757
  simp only [CollatzResearch.WordTrace]
  refine ⟨42846907805063496367538525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28564605203375664245025683 42846907805063496367538525)
  ·
    refine ⟨16067590426898811137826947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42846907805063496367538525 16067590426898811137826947)
    ·
      refine ⟨24101385640348216706740421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16067590426898811137826947 24101385640348216706740421)
      ·
        refine ⟨4519009807565290632513829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24101385640348216706740421 4519009807565290632513829)
        ·
          refine ⟨847314338918491993596343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4519009807565290632513829 847314338918491993596343)
          ·
            refine ⟨1270971508377737990394515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 847314338918491993596343 1270971508377737990394515)
            ·
              refine ⟨1906457262566606985591773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1270971508377737990394515 1906457262566606985591773)
              ·
                refine ⟨714921473462477619596915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1906457262566606985591773 714921473462477619596915)
                ·
                  refine ⟨1072382210193716429395373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 714921473462477619596915 1072382210193716429395373)
                  ·
                    refine ⟨402143328822643661023265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1072382210193716429395373 402143328822643661023265)
                    ·
                      rfl

theorem cell22_1174757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 4, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 4, 1, 1, 3, 1, 3].length) (baseStart_1174757 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1174757 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1174757 prefixEnd_1174757 := by exact prefixLift 1174757
  have htrace : WordTrace (prefixWord ++ tailWord_1174757) baseStart_1174757 baseEnd_1174757 := by
    simpa [prefixWord, tailWord_1174757, baseEnd_1174757] using wordTrace_append hprefix tailTrace_1174757
  have hstable : (prefixWord ++ tailWord_1174757).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1174757).length < 2 ^ (prefixWord ++ tailWord_1174757).sum := by decide
  have hdescent : baseEnd_1174757 < baseStart_1174757 := by decide
  rcases family_descends (prefixWord ++ tailWord_1174757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1174766 : List Nat := [4, 1, 2, 1, 1, 1, 4, 3, 1, 4]
def baseStart_1174766 : Nat := 118140960795 + 1174766 * 2 ^ 59
def prefixEnd_1174766 : Nat := 4983230072969 + 3 ^ 40 * 1174766 * 2
def baseEnd_1174766 : Nat := 402146409706570637548237

theorem tailTrace_1174766 : CollatzResearch.WordTrace tailWord_1174766 prefixEnd_1174766 402146409706570637548237 := by
  unfold tailWord_1174766
  simp only [CollatzResearch.WordTrace]
  refine ⟨5355904507753861363077019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28564824041353927269744101 5355904507753861363077019)
  ·
    refine ⟨8033856761630792044615529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5355904507753861363077019 8033856761630792044615529)
    ·
      refine ⟨6025392571223094033461647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8033856761630792044615529 6025392571223094033461647)
      ·
        refine ⟨9038088856834641050192471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6025392571223094033461647 9038088856834641050192471)
        ·
          refine ⟨13557133285251961575288707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9038088856834641050192471 13557133285251961575288707)
          ·
            refine ⟨20335699927877942362933061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13557133285251961575288707 20335699927877942362933061)
            ·
              refine ⟨3812943736477114193049949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20335699927877942362933061 3812943736477114193049949)
              ·
                refine ⟨1429853901178917822393731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3812943736477114193049949 1429853901178917822393731)
                ·
                  refine ⟨2144780851768376733590597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1429853901178917822393731 2144780851768376733590597)
                  ·
                    refine ⟨402146409706570637548237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2144780851768376733590597 402146409706570637548237)
                    ·
                      rfl

theorem cell22_1174766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 4, 3, 1, 4].length) (baseStart_1174766 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1174766 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1174766 prefixEnd_1174766 := by exact prefixLift 1174766
  have htrace : WordTrace (prefixWord ++ tailWord_1174766) baseStart_1174766 baseEnd_1174766 := by
    simpa [prefixWord, tailWord_1174766, baseEnd_1174766] using wordTrace_append hprefix tailTrace_1174766
  have hstable : (prefixWord ++ tailWord_1174766).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1174766).length < 2 ^ (prefixWord ++ tailWord_1174766).sum := by decide
  have hdescent : baseEnd_1174766 < baseStart_1174766 := by decide
  rcases family_descends (prefixWord ++ tailWord_1174766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1174794 : List Nat := [3, 1, 2, 2, 1, 1, 1, 1, 6, 4]
def baseStart_1174794 : Nat := 118140960795 + 1174794 * 2 ^ 59
def prefixEnd_1174794 : Nat := 4983230072969 + 3 ^ 40 * 1174794 * 2
def baseEnd_1174794 : Nat := 402155994678787897848151

theorem tailTrace_1174794 : CollatzResearch.WordTrace tailWord_1174794 prefixEnd_1174794 402155994678787897848151 := by
  unfold tailWord_1174794
  simp only [CollatzResearch.WordTrace]
  refine ⟨10712064326482362921658859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28565504870619634457756957 10712064326482362921658859)
  ·
    refine ⟨16068096489723544382488289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10712064326482362921658859 16068096489723544382488289)
    ·
      refine ⟨12051072367292658286866217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16068096489723544382488289 12051072367292658286866217)
      ·
        refine ⟨9038304275469493715149663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12051072367292658286866217 9038304275469493715149663)
        ·
          refine ⟨13557456413204240572724495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9038304275469493715149663 13557456413204240572724495)
          ·
            refine ⟨20336184619806360859086743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13557456413204240572724495 20336184619806360859086743)
            ·
              refine ⟨30504276929709541288630115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20336184619806360859086743 30504276929709541288630115)
              ·
                refine ⟨45756415394564311932945173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30504276929709541288630115 45756415394564311932945173)
                ·
                  refine ⟨2144831971620202121856805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 45756415394564311932945173 2144831971620202121856805)
                  ·
                    refine ⟨402155994678787897848151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2144831971620202121856805 402155994678787897848151)
                    ·
                      rfl

theorem cell22_1174794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 1, 6, 4].length) (baseStart_1174794 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1174794 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1174794 prefixEnd_1174794 := by exact prefixLift 1174794
  have htrace : WordTrace (prefixWord ++ tailWord_1174794) baseStart_1174794 baseEnd_1174794 := by
    simpa [prefixWord, tailWord_1174794, baseEnd_1174794] using wordTrace_append hprefix tailTrace_1174794
  have hstable : (prefixWord ++ tailWord_1174794).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1174794).length < 2 ^ (prefixWord ++ tailWord_1174794).sum := by decide
  have hdescent : baseEnd_1174794 < baseStart_1174794 := by decide
  rcases family_descends (prefixWord ++ tailWord_1174794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1174916 : List Nat := [2, 3, 2, 1, 1, 3, 2, 2, 6]
def baseStart_1174916 : Nat := 118140960795 + 1174916 * 2 ^ 59
def prefixEnd_1174916 : Nat := 4983230072969 + 3 ^ 40 * 1174916 * 2
def baseEnd_1174916 : Nat := 134065919257340082099259

theorem tailTrace_1174916 : CollatzResearch.WordTrace tailWord_1174916 prefixEnd_1174916 134065919257340082099259 := by
  unfold tailWord_1174916
  simp only [CollatzResearch.WordTrace]
  refine ⟨21426353505743733261288301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28568471340991644348384401 21426353505743733261288301)
  ·
    refine ⟨8034882564653899972983113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21426353505743733261288301 8034882564653899972983113)
    ·
      refine ⟨6026161923490424979737335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8034882564653899972983113 6026161923490424979737335)
      ·
        refine ⟨9039242885235637469606003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6026161923490424979737335 9039242885235637469606003)
        ·
          refine ⟨13558864327853456204409005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9039242885235637469606003 13558864327853456204409005)
          ·
            refine ⟨5084574122945046076653377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13558864327853456204409005 5084574122945046076653377)
            ·
              refine ⟨3813430592208784557490033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5084574122945046076653377 3813430592208784557490033)
              ·
                refine ⟨2860072944156588418117525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3813430592208784557490033 2860072944156588418117525)
                ·
                  refine ⟨134065919257340082099259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2860072944156588418117525 134065919257340082099259)
                  ·
                    rfl

theorem cell22_1174916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 2, 2, 6].length) (baseStart_1174916 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1174916 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1174916 prefixEnd_1174916 := by exact prefixLift 1174916
  have htrace : WordTrace (prefixWord ++ tailWord_1174916) baseStart_1174916 baseEnd_1174916 := by
    simpa [prefixWord, tailWord_1174916, baseEnd_1174916] using wordTrace_append hprefix tailTrace_1174916
  have hstable : (prefixWord ++ tailWord_1174916).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1174916).length < 2 ^ (prefixWord ++ tailWord_1174916).sum := by decide
  have hdescent : baseEnd_1174916 < baseStart_1174916 := by decide
  rcases family_descends (prefixWord ++ tailWord_1174916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1174933 : List Nat := [1, 3, 2, 1, 1, 2, 5, 3, 4]
def baseStart_1174933 : Nat := 118140960795 + 1174933 * 2 ^ 59
def prefixEnd_1174933 : Nat := 4983230072969 + 3 ^ 40 * 1174933 * 2
def baseEnd_1174933 : Nat := 134067859073145956207575

theorem tailTrace_1174933 : CollatzResearch.WordTrace tailWord_1174933 prefixEnd_1174933 134067859073145956207575 := by
  unfold tailWord_1174933
  simp only [CollatzResearch.WordTrace]
  refine ⟨42853327052425878425945453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28568884701617252283963635 42853327052425878425945453)
  ·
    refine ⟨16069997644659704409729545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42853327052425878425945453 16069997644659704409729545)
    ·
      refine ⟨12052498233494778307297159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16069997644659704409729545 12052498233494778307297159)
      ·
        refine ⟨18078747350242167460945739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12052498233494778307297159 18078747350242167460945739)
        ·
          refine ⟨27118121025363251191418609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18078747350242167460945739 27118121025363251191418609)
          ·
            refine ⟨20338590769022438393563957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27118121025363251191418609 20338590769022438393563957)
            ·
              refine ⟨1906742884595853599396621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 20338590769022438393563957 1906742884595853599396621)
              ·
                refine ⟨715028581723445099773733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1906742884595853599396621 715028581723445099773733)
                ·
                  refine ⟨134067859073145956207575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 715028581723445099773733 134067859073145956207575)
                  ·
                    rfl

theorem cell22_1174933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 5, 3, 4].length) (baseStart_1174933 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1174933 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1174933 prefixEnd_1174933 := by exact prefixLift 1174933
  have htrace : WordTrace (prefixWord ++ tailWord_1174933) baseStart_1174933 baseEnd_1174933 := by
    simpa [prefixWord, tailWord_1174933, baseEnd_1174933] using wordTrace_append hprefix tailTrace_1174933
  have hstable : (prefixWord ++ tailWord_1174933).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1174933).length < 2 ^ (prefixWord ++ tailWord_1174933).sum := by decide
  have hdescent : baseEnd_1174933 < baseStart_1174933 := by decide
  rcases family_descends (prefixWord ++ tailWord_1174933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1174948 : List Nat := [2, 3, 1, 2, 1, 1, 1, 6, 2, 3]
def baseStart_1174948 : Nat := 118140960795 + 1174948 * 2 ^ 59
def prefixEnd_1174948 : Nat := 4983230072969 + 3 ^ 40 * 1174948 * 2
def baseEnd_1174948 : Nat := 402208712025982829497679

theorem tailTrace_1174948 : CollatzResearch.WordTrace tailWord_1174948 prefixEnd_1174948 402208712025982829497679 := by
  unfold tailWord_1174948
  simp only [CollatzResearch.WordTrace]
  refine ⟨21426937073685767993870749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28569249431581023991827665 21426937073685767993870749)
  ·
    refine ⟨8035101402632162997701531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21426937073685767993870749 8035101402632162997701531)
    ·
      refine ⟨12052652103948244496552297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8035101402632162997701531 12052652103948244496552297)
      ·
        refine ⟨9039489077961183372414223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12052652103948244496552297 9039489077961183372414223)
        ·
          refine ⟨13559233616941775058621335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9039489077961183372414223 13559233616941775058621335)
          ·
            refine ⟨20338850425412662587932003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13559233616941775058621335 20338850425412662587932003)
            ·
              refine ⟨30508275638118993881898005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20338850425412662587932003 30508275638118993881898005)
              ·
                refine ⟨1430075420536827838213969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 30508275638118993881898005 1430075420536827838213969)
                ·
                  refine ⟨1072556565402620878660477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1430075420536827838213969 1072556565402620878660477)
                  ·
                    refine ⟨402208712025982829497679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1072556565402620878660477 402208712025982829497679)
                    ·
                      rfl

theorem cell22_1174948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 6, 2, 3].length) (baseStart_1174948 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1174948 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1174948 prefixEnd_1174948 := by exact prefixLift 1174948
  have htrace : WordTrace (prefixWord ++ tailWord_1174948) baseStart_1174948 baseEnd_1174948 := by
    simpa [prefixWord, tailWord_1174948, baseEnd_1174948] using wordTrace_append hprefix tailTrace_1174948
  have hstable : (prefixWord ++ tailWord_1174948).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1174948).length < 2 ^ (prefixWord ++ tailWord_1174948).sum := by decide
  have hdescent : baseEnd_1174948 < baseStart_1174948 := by decide
  rcases family_descends (prefixWord ++ tailWord_1174948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1174961 : List Nat := [1, 2, 2, 4, 1, 1, 4, 7]
def baseStart_1174961 : Nat := 118140960795 + 1174961 * 2 ^ 59
def prefixEnd_1174961 : Nat := 4983230072969 + 3 ^ 40 * 1174961 * 2
def baseEnd_1174961 : Nat := 44690351354628347658071

theorem tailTrace_1174961 : CollatzResearch.WordTrace tailWord_1174961 prefixEnd_1174961 44690351354628347658071 := by
  unfold tailWord_1174961
  simp only [CollatzResearch.WordTrace]
  refine ⟨42854348296324439207964737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28569565530882959471976491 42854348296324439207964737)
  ·
    refine ⟨32140761222243329405973553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42854348296324439207964737 32140761222243329405973553)
    ·
      refine ⟨24105570916682497054480165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32140761222243329405973553 24105570916682497054480165)
      ·
        refine ⟨4519794546877968197715031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24105570916682497054480165 4519794546877968197715031)
        ·
          refine ⟨6779691820316952296572547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4519794546877968197715031 6779691820316952296572547)
          ·
            refine ⟨10169537730475428444858821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6779691820316952296572547 10169537730475428444858821)
            ·
              refine ⟨1906788324464142833411029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10169537730475428444858821 1906788324464142833411029)
              ·
                refine ⟨44690351354628347658071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1906788324464142833411029 44690351354628347658071)
                ·
                  rfl

theorem cell22_1174961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 4, 7].length) (baseStart_1174961 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1174961 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1174961 prefixEnd_1174961 := by exact prefixLift 1174961
  have htrace : WordTrace (prefixWord ++ tailWord_1174961) baseStart_1174961 baseEnd_1174961 := by
    simpa [prefixWord, tailWord_1174961, baseEnd_1174961] using wordTrace_append hprefix tailTrace_1174961
  have hstable : (prefixWord ++ tailWord_1174961).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1174961).length < 2 ^ (prefixWord ++ tailWord_1174961).sum := by decide
  have hdescent : baseEnd_1174961 < baseStart_1174961 := by decide
  rcases family_descends (prefixWord ++ tailWord_1174961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1174965 : List Nat := [1, 3, 3, 2, 2, 2, 1, 3, 2, 3]
def baseStart_1174965 : Nat := 118140960795 + 1174965 * 2 ^ 59
def prefixEnd_1174965 : Nat := 4983230072969 + 3 ^ 40 * 1174965 * 2
def baseEnd_1174965 : Nat := 402214531473400451822627

theorem tailTrace_1174965 : CollatzResearch.WordTrace tailWord_1174965 prefixEnd_1174965 402214531473400451822627 := by
  unfold tailWord_1174965
  simp only [CollatzResearch.WordTrace]
  refine ⟨42854494188309947891110349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28569662792206631927406899 42854494188309947891110349)
  ·
    refine ⟨16070435320616230459166381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42854494188309947891110349 16070435320616230459166381)
    ·
      refine ⟨6026413245231086422187393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16070435320616230459166381 6026413245231086422187393)
      ·
        refine ⟨4519809933923314816640545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6026413245231086422187393 4519809933923314816640545)
        ·
          refine ⟨3389857450442486112480409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4519809933923314816640545 3389857450442486112480409)
          ·
            refine ⟨2542393087831864584360307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3389857450442486112480409 2542393087831864584360307)
            ·
              refine ⟨3813589631747796876540461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2542393087831864584360307 3813589631747796876540461)
              ·
                refine ⟨1430096111905423828702673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3813589631747796876540461 1430096111905423828702673)
                ·
                  refine ⟨1072572083929067871527005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1430096111905423828702673 1072572083929067871527005)
                  ·
                    refine ⟨402214531473400451822627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1072572083929067871527005 402214531473400451822627)
                    ·
                      rfl

theorem cell22_1174965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 1, 3, 2, 3].length) (baseStart_1174965 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1174965 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1174965 prefixEnd_1174965 := by exact prefixLift 1174965
  have htrace : WordTrace (prefixWord ++ tailWord_1174965) baseStart_1174965 baseEnd_1174965 := by
    simpa [prefixWord, tailWord_1174965, baseEnd_1174965] using wordTrace_append hprefix tailTrace_1174965
  have hstable : (prefixWord ++ tailWord_1174965).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1174965).length < 2 ^ (prefixWord ++ tailWord_1174965).sum := by decide
  have hdescent : baseEnd_1174965 < baseStart_1174965 := by decide
  rcases family_descends (prefixWord ++ tailWord_1174965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1174980 : List Nat := [2, 3, 3, 2, 1, 2, 2, 1, 2, 4]
def baseStart_1174980 : Nat := 118140960795 + 1174980 * 2 ^ 59
def prefixEnd_1174980 : Nat := 4983230072969 + 3 ^ 40 * 1174980 * 2
def baseEnd_1174980 : Nat := 402219666279945412697581

theorem tailTrace_1174980 : CollatzResearch.WordTrace tailWord_1174980 prefixEnd_1174980 402219666279945412697581 := by
  unfold tailWord_1174980
  simp only [CollatzResearch.WordTrace]
  refine ⟨21427520641627802726453197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28570027522170403635270929 21427520641627802726453197)
  ·
    refine ⟨8035320240610426022419949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21427520641627802726453197 8035320240610426022419949)
    ·
      refine ⟨3013245090228909758407481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8035320240610426022419949 3013245090228909758407481)
      ·
        refine ⟨2259933817671682318805611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3013245090228909758407481 2259933817671682318805611)
        ·
          refine ⟨3389900726507523478208417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2259933817671682318805611 3389900726507523478208417)
          ·
            refine ⟨2542425544880642608656313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3389900726507523478208417 2542425544880642608656313)
            ·
              refine ⟨1906819158660481956492235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2542425544880642608656313 1906819158660481956492235)
              ·
                refine ⟨2860228737990722934738353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1906819158660481956492235 2860228737990722934738353)
                ·
                  refine ⟨2145171553493042201053765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2860228737990722934738353 2145171553493042201053765)
                  ·
                    refine ⟨402219666279945412697581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2145171553493042201053765 402219666279945412697581)
                    ·
                      rfl

theorem cell22_1174980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 2, 1, 2, 4].length) (baseStart_1174980 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1174980 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1174980 prefixEnd_1174980 := by exact prefixLift 1174980
  have htrace : WordTrace (prefixWord ++ tailWord_1174980) baseStart_1174980 baseEnd_1174980 := by
    simpa [prefixWord, tailWord_1174980, baseEnd_1174980] using wordTrace_append hprefix tailTrace_1174980
  have hstable : (prefixWord ++ tailWord_1174980).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1174980).length < 2 ^ (prefixWord ++ tailWord_1174980).sum := by decide
  have hdescent : baseEnd_1174980 < baseStart_1174980 := by decide
  rcases family_descends (prefixWord ++ tailWord_1174980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1175044 : List Nat := [2, 3, 2, 3, 2, 1, 2, 3, 1, 3]
def baseStart_1175044 : Nat := 118140960795 + 1175044 * 2 ^ 59
def prefixEnd_1175044 : Nat := 4983230072969 + 3 ^ 40 * 1175044 * 2
def baseEnd_1175044 : Nat := 402241574787870579097385

theorem tailTrace_1175044 : CollatzResearch.WordTrace tailWord_1175044 prefixEnd_1175044 402241574787870579097385 := by
  unfold tailWord_1175044
  simp only [CollatzResearch.WordTrace]
  refine ⟨21428687777511872191618093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28571583703349162922157457 21428687777511872191618093)
  ·
    refine ⟨8035757916566952071856785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21428687777511872191618093 8035757916566952071856785)
    ·
      refine ⟨6026818437425214053892589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8035757916566952071856785 6026818437425214053892589)
      ·
        refine ⟨2260056914034455270209721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6026818437425214053892589 2260056914034455270209721)
        ·
          refine ⟨1695042685525841452657291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2260056914034455270209721 1695042685525841452657291)
          ·
            refine ⟨2542564028288762178985937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1695042685525841452657291 2542564028288762178985937)
            ·
              refine ⟨1906923021216571634239453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2542564028288762178985937 1906923021216571634239453)
              ·
                refine ⟨715096132956214362839795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1906923021216571634239453 715096132956214362839795)
                ·
                  refine ⟨1072644199434321544259693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 715096132956214362839795 1072644199434321544259693)
                  ·
                    refine ⟨402241574787870579097385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1072644199434321544259693 402241574787870579097385)
                    ·
                      rfl

theorem cell22_1175044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 2, 3, 1, 3].length) (baseStart_1175044 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1175044 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1175044 prefixEnd_1175044 := by exact prefixLift 1175044
  have htrace : WordTrace (prefixWord ++ tailWord_1175044) baseStart_1175044 baseEnd_1175044 := by
    simpa [prefixWord, tailWord_1175044, baseEnd_1175044] using wordTrace_append hprefix tailTrace_1175044
  have hstable : (prefixWord ++ tailWord_1175044).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1175044).length < 2 ^ (prefixWord ++ tailWord_1175044).sum := by decide
  have hdescent : baseEnd_1175044 < baseStart_1175044 := by decide
  rcases family_descends (prefixWord ++ tailWord_1175044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1175068 : List Nat := [2, 2, 3, 1, 2, 1, 4, 1, 6]
def baseStart_1175068 : Nat := 118140960795 + 1175068 * 2 ^ 59
def prefixEnd_1175068 : Nat := 4983230072969 + 3 ^ 40 * 1175068 * 2
def baseEnd_1175068 : Nat := 134083263492780838832437

theorem tailTrace_1175068 : CollatzResearch.WordTrace tailWord_1175068 prefixEnd_1175068 134083263492780838832437 := by
  unfold tailWord_1175068
  simp only [CollatzResearch.WordTrace]
  refine ⟨21429125453468398241054929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28572167271291197654739905 21429125453468398241054929)
  ·
    refine ⟨16071844090101298680791197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21429125453468398241054929 16071844090101298680791197)
    ·
      refine ⟨6026941533787987005296699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16071844090101298680791197 6026941533787987005296699)
      ·
        refine ⟨9040412300681980507945049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6026941533787987005296699 9040412300681980507945049)
        ·
          refine ⟨6780309225511485380958787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9040412300681980507945049 6780309225511485380958787)
          ·
            refine ⟨10170463838267228071438181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6780309225511485380958787 10170463838267228071438181)
            ·
              refine ⟨1906961969675105263394659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10170463838267228071438181 1906961969675105263394659)
              ·
                refine ⟨2860442954512657895091989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1906961969675105263394659 2860442954512657895091989)
                ·
                  refine ⟨134083263492780838832437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2860442954512657895091989 134083263492780838832437)
                  ·
                    rfl

theorem cell22_1175068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 4, 1, 6].length) (baseStart_1175068 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1175068 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1175068 prefixEnd_1175068 := by exact prefixLift 1175068
  have htrace : WordTrace (prefixWord ++ tailWord_1175068) baseStart_1175068 baseEnd_1175068 := by
    simpa [prefixWord, tailWord_1175068, baseEnd_1175068] using wordTrace_append hprefix tailTrace_1175068
  have hstable : (prefixWord ++ tailWord_1175068).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1175068).length < 2 ^ (prefixWord ++ tailWord_1175068).sum := by decide
  have hdescent : baseEnd_1175068 < baseStart_1175068 := by decide
  rcases family_descends (prefixWord ++ tailWord_1175068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1175098 : List Nat := [3, 1, 1, 1, 3, 2, 2, 3, 2, 4]
def baseStart_1175098 : Nat := 118140960795 + 1175098 * 2 ^ 59
def prefixEnd_1175098 : Nat := 4983230072969 + 3 ^ 40 * 1175098 * 2
def baseEnd_1175098 : Nat := 402260060091432438247219

theorem tailTrace_1175098 : CollatzResearch.WordTrace tailWord_1175098 prefixEnd_1175098 402260060091432438247219 := by
  unfold tailWord_1175098
  simp only [CollatzResearch.WordTrace]
  refine ⟨10714836274207027901425487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28572896731218741070467965 10714836274207027901425487)
  ·
    refine ⟨16072254411310541852138231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10714836274207027901425487 16072254411310541852138231)
    ·
      refine ⟨24108381616965812778207347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16072254411310541852138231 24108381616965812778207347)
      ·
        refine ⟨36162572425448719167311021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24108381616965812778207347 36162572425448719167311021)
        ·
          refine ⟨13560964659543269687741633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36162572425448719167311021 13560964659543269687741633)
          ·
            refine ⟨10170723494657452265806225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13560964659543269687741633 10170723494657452265806225)
            ·
              refine ⟨7628042620993089199354669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10170723494657452265806225 7628042620993089199354669)
              ·
                refine ⟨2860515982872408449758001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7628042620993089199354669 2860515982872408449758001)
                ·
                  refine ⟨2145386987154306337318501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2860515982872408449758001 2145386987154306337318501)
                  ·
                    refine ⟨402260060091432438247219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2145386987154306337318501 402260060091432438247219)
                    ·
                      rfl

theorem cell22_1175098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 3, 2, 4].length) (baseStart_1175098 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1175098 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1175098 prefixEnd_1175098 := by exact prefixLift 1175098
  have htrace : WordTrace (prefixWord ++ tailWord_1175098) baseStart_1175098 baseEnd_1175098 := by
    simpa [prefixWord, tailWord_1175098, baseEnd_1175098] using wordTrace_append hprefix tailTrace_1175098
  have hstable : (prefixWord ++ tailWord_1175098).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1175098).length < 2 ^ (prefixWord ++ tailWord_1175098).sum := by decide
  have hdescent : baseEnd_1175098 < baseStart_1175098 := by decide
  rcases family_descends (prefixWord ++ tailWord_1175098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1175173 : List Nat := [1, 3, 1, 1, 4, 1, 2, 2, 2, 5]
def baseStart_1175173 : Nat := 118140960795 + 1175173 * 2 ^ 59
def prefixEnd_1175173 : Nat := 4983230072969 + 3 ^ 40 * 1175173 * 2
def baseEnd_1175173 : Nat := 402285734124157242621989

theorem tailTrace_1175173 : CollatzResearch.WordTrace tailWord_1175173 prefixEnd_1175173 402285734124157242621989 := by
  unfold tailWord_1175173
  simp only [CollatzResearch.WordTrace]
  refine ⟨42862080571556399414682173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28574720381037599609788115 42862080571556399414682173)
  ·
    refine ⟨16073280214333649780505815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42862080571556399414682173 16073280214333649780505815)
    ·
      refine ⟨24109920321500474670758723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16073280214333649780505815 24109920321500474670758723)
      ·
        refine ⟨36164880482250712006138085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24109920321500474670758723 36164880482250712006138085)
        ·
          refine ⟨6780915090422008501150891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 36164880482250712006138085 6780915090422008501150891)
          ·
            refine ⟨10171372635633012751726337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6780915090422008501150891 10171372635633012751726337)
            ·
              refine ⟨7628529476724759563794753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10171372635633012751726337 7628529476724759563794753)
              ·
                refine ⟨5721397107543569672846065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7628529476724759563794753 5721397107543569672846065)
                ·
                  refine ⟨4291047830657677254634549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5721397107543569672846065 4291047830657677254634549)
                  ·
                    refine ⟨402285734124157242621989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4291047830657677254634549 402285734124157242621989)
                    ·
                      rfl

theorem cell22_1175173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 2, 2, 5].length) (baseStart_1175173 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1175173 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1175173 prefixEnd_1175173 := by exact prefixLift 1175173
  have htrace : WordTrace (prefixWord ++ tailWord_1175173) baseStart_1175173 baseEnd_1175173 := by
    simpa [prefixWord, tailWord_1175173, baseEnd_1175173] using wordTrace_append hprefix tailTrace_1175173
  have hstable : (prefixWord ++ tailWord_1175173).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1175173).length < 2 ^ (prefixWord ++ tailWord_1175173).sum := by decide
  have hdescent : baseEnd_1175173 < baseStart_1175173 := by decide
  rcases family_descends (prefixWord ++ tailWord_1175173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1175175 : List Nat := [1, 1, 4, 2, 1, 4, 2, 2, 5]
def baseStart_1175175 : Nat := 118140960795 + 1175175 * 2 ^ 59
def prefixEnd_1175175 : Nat := 4983230072969 + 3 ^ 40 * 1175175 * 2
def baseEnd_1175175 : Nat := 134095472921676634690661

theorem tailTrace_1175175 : CollatzResearch.WordTrace tailWord_1175175 prefixEnd_1175175 134095472921676634690661 := by
  unfold tailWord_1175175
  simp only [CollatzResearch.WordTrace]
  refine ⟨42862153517549153756254979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28574769011699435837503319 42862153517549153756254979)
  ·
    refine ⟨64293230276323730634382469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42862153517549153756254979 64293230276323730634382469)
    ·
      refine ⟨12054980676810699493946713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 64293230276323730634382469 12054980676810699493946713)
      ·
        refine ⟨9041235507608024620460035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12054980676810699493946713 9041235507608024620460035)
        ·
          refine ⟨13561853261412036930690053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9041235507608024620460035 13561853261412036930690053)
          ·
            refine ⟨2542847486514756924504385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13561853261412036930690053 2542847486514756924504385)
            ·
              refine ⟨1907135614886067693378289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2542847486514756924504385 1907135614886067693378289)
              ·
                refine ⟨1430351711164550770033717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1907135614886067693378289 1430351711164550770033717)
                ·
                  refine ⟨134095472921676634690661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1430351711164550770033717 134095472921676634690661)
                  ·
                    rfl

theorem cell22_1175175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 2, 2, 5].length) (baseStart_1175175 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1175175 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1175175 prefixEnd_1175175 := by exact prefixLift 1175175
  have htrace : WordTrace (prefixWord ++ tailWord_1175175) baseStart_1175175 baseEnd_1175175 := by
    simpa [prefixWord, tailWord_1175175, baseEnd_1175175] using wordTrace_append hprefix tailTrace_1175175
  have hstable : (prefixWord ++ tailWord_1175175).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1175175).length < 2 ^ (prefixWord ++ tailWord_1175175).sum := by decide
  have hdescent : baseEnd_1175175 < baseStart_1175175 := by decide
  rcases family_descends (prefixWord ++ tailWord_1175175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1175203 : List Nat := [1, 1, 1, 4, 1, 1, 5, 2, 6]
def baseStart_1175203 : Nat := 118140960795 + 1175203 * 2 ^ 59
def prefixEnd_1175203 : Nat := 4983230072969 + 3 ^ 40 * 1175203 * 2
def baseEnd_1175203 : Nat := 134098667912415721457299

theorem tailTrace_1175203 : CollatzResearch.WordTrace tailWord_1175203 prefixEnd_1175203 134098667912415721457299 := by
  unfold tailWord_1175203
  simp only [CollatzResearch.WordTrace]
  refine ⟨42863174761447714538274263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28575449840965143025516175 42863174761447714538274263)
  ·
    refine ⟨64294762142171571807411395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42863174761447714538274263 64294762142171571807411395)
    ·
      refine ⟨96442143213257357711117093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64294762142171571807411395 96442143213257357711117093)
      ·
        refine ⟨18082901852485754570834455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 96442143213257357711117093 18082901852485754570834455)
        ·
          refine ⟨27124352778728631856251683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18082901852485754570834455 27124352778728631856251683)
          ·
            refine ⟨40686529168092947784377525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27124352778728631856251683 40686529168092947784377525)
            ·
              refine ⟨3814362109508713854785393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 40686529168092947784377525 3814362109508713854785393)
              ·
                refine ⟨2860771582131535391089045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3814362109508713854785393 2860771582131535391089045)
                ·
                  refine ⟨134098667912415721457299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2860771582131535391089045 134098667912415721457299)
                  ·
                    rfl

theorem cell22_1175203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 5, 2, 6].length) (baseStart_1175203 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1175203 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1175203 prefixEnd_1175203 := by exact prefixLift 1175203
  have htrace : WordTrace (prefixWord ++ tailWord_1175203) baseStart_1175203 baseEnd_1175203 := by
    simpa [prefixWord, tailWord_1175203, baseEnd_1175203] using wordTrace_append hprefix tailTrace_1175203
  have hstable : (prefixWord ++ tailWord_1175203).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1175203).length < 2 ^ (prefixWord ++ tailWord_1175203).sum := by decide
  have hdescent : baseEnd_1175203 < baseStart_1175203 := by decide
  rcases family_descends (prefixWord ++ tailWord_1175203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1175250 : List Nat := [3, 2, 2, 2, 2, 1, 1, 2, 1, 6]
def baseStart_1175250 : Nat := 118140960795 + 1175250 * 2 ^ 59
def prefixEnd_1175250 : Nat := 4983230072969 + 3 ^ 40 * 1175250 * 2
def baseEnd_1175250 : Nat := 402312092797754708446753

theorem tailTrace_1175250 : CollatzResearch.WordTrace tailWord_1175250 prefixEnd_1175250 402312092797754708446753 := by
  unfold tailWord_1175250
  simp only [CollatzResearch.WordTrace]
  refine ⟨10716222248069360391308801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28576592661518294376823469 10716222248069360391308801)
  ·
    refine ⟨8037166686052020293481601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10716222248069360391308801 8037166686052020293481601)
    ·
      refine ⟨6027875014539015220111201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8037166686052020293481601 6027875014539015220111201)
      ·
        refine ⟨4520906260904261415083401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6027875014539015220111201 4520906260904261415083401)
        ·
          refine ⟨3390679695678196061312551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4520906260904261415083401 3390679695678196061312551)
          ·
            refine ⟨5086019543517294091968827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3390679695678196061312551 5086019543517294091968827)
            ·
              refine ⟨7629029315275941137953241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5086019543517294091968827 7629029315275941137953241)
              ·
                refine ⟨5721771986456955853464931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7629029315275941137953241 5721771986456955853464931)
                ·
                  refine ⟨8582657979685433780197397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5721771986456955853464931 8582657979685433780197397)
                  ·
                    refine ⟨402312092797754708446753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8582657979685433780197397 402312092797754708446753)
                    ·
                      rfl

theorem cell22_1175250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 2, 1, 6].length) (baseStart_1175250 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1175250 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1175250 prefixEnd_1175250 := by exact prefixLift 1175250
  have htrace : WordTrace (prefixWord ++ tailWord_1175250) baseStart_1175250 baseEnd_1175250 := by
    simpa [prefixWord, tailWord_1175250, baseEnd_1175250] using wordTrace_append hprefix tailTrace_1175250
  have hstable : (prefixWord ++ tailWord_1175250).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1175250).length < 2 ^ (prefixWord ++ tailWord_1175250).sum := by decide
  have hdescent : baseEnd_1175250 < baseStart_1175250 := by decide
  rcases family_descends (prefixWord ++ tailWord_1175250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1175252 : List Nat := [2, 4, 1, 3, 1, 1, 3, 1, 1, 5]
def baseStart_1175252 : Nat := 118140960795 + 1175252 * 2 ^ 59
def prefixEnd_1175252 : Nat := 4983230072969 + 3 ^ 40 * 1175252 * 2
def baseEnd_1175252 : Nat := 402312777438627369896747

theorem tailTrace_1175252 : CollatzResearch.WordTrace tailWord_1175252 prefixEnd_1175252 402312777438627369896747 := by
  unfold tailWord_1175252
  simp only [CollatzResearch.WordTrace]
  refine ⟨21432480969135097953404005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28576641292180130604538673 21432480969135097953404005)
  ·
    refine ⟨4018590181712830866263251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21432480969135097953404005 4018590181712830866263251)
    ·
      refine ⟨6027885272569246299394877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4018590181712830866263251 6027885272569246299394877)
      ·
        refine ⟨2260456977213467362273079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6027885272569246299394877 2260456977213467362273079)
        ·
          refine ⟨3390685465820201043409619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2260456977213467362273079 3390685465820201043409619)
          ·
            refine ⟨5086028198730301565114429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3390685465820201043409619 5086028198730301565114429)
            ·
              refine ⟨1907260574523863086917911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5086028198730301565114429 1907260574523863086917911)
              ·
                refine ⟨2860890861785794630376867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1907260574523863086917911 2860890861785794630376867)
                ·
                  refine ⟨4291336292678691945565301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2860890861785794630376867 4291336292678691945565301)
                  ·
                    refine ⟨402312777438627369896747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4291336292678691945565301 402312777438627369896747)
                    ·
                      rfl

theorem cell22_1175252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 3, 1, 1, 5].length) (baseStart_1175252 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1175252 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1175252 prefixEnd_1175252 := by exact prefixLift 1175252
  have htrace : WordTrace (prefixWord ++ tailWord_1175252) baseStart_1175252 baseEnd_1175252 := by
    simpa [prefixWord, tailWord_1175252, baseEnd_1175252] using wordTrace_append hprefix tailTrace_1175252
  have hstable : (prefixWord ++ tailWord_1175252).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1175252).length < 2 ^ (prefixWord ++ tailWord_1175252).sum := by decide
  have hdescent : baseEnd_1175252 < baseStart_1175252 := by decide
  rcases family_descends (prefixWord ++ tailWord_1175252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1175263 : List Nat := [1, 1, 2, 3, 2, 2, 1, 1, 2, 7]
def baseStart_1175263 : Nat := 118140960795 + 1175263 * 2 ^ 59
def prefixEnd_1175263 : Nat := 4983230072969 + 3 ^ 40 * 1175263 * 2
def baseEnd_1175263 : Nat := 402316542963427007871713

theorem tailTrace_1175263 : CollatzResearch.WordTrace tailWord_1175263 prefixEnd_1175263 402316542963427007871713 := by
  unfold tailWord_1175263
  simp only [CollatzResearch.WordTrace]
  refine ⟨42865363141230344785458443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28576908760820229856972295 42865363141230344785458443)
  ·
    refine ⟨64298044711845517178187665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42865363141230344785458443 64298044711845517178187665)
    ·
      refine ⟨48223533533884137883640749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64298044711845517178187665 48223533533884137883640749)
      ·
        refine ⟨18083825075206551706365281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48223533533884137883640749 18083825075206551706365281)
        ·
          refine ⟨13562868806404913779773961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18083825075206551706365281 13562868806404913779773961)
          ·
            refine ⟨10172151604803685334830471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13562868806404913779773961 10172151604803685334830471)
            ·
              refine ⟨15258227407205528002245707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10172151604803685334830471 15258227407205528002245707)
              ·
                refine ⟨22887341110808292003368561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15258227407205528002245707 22887341110808292003368561)
                ·
                  refine ⟨17165505833106219002526421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22887341110808292003368561 17165505833106219002526421)
                  ·
                    refine ⟨402316542963427007871713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 17165505833106219002526421 402316542963427007871713)
                    ·
                      rfl

theorem cell22_1175263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 1, 2, 7].length) (baseStart_1175263 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1175263 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1175263 prefixEnd_1175263 := by exact prefixLift 1175263
  have htrace : WordTrace (prefixWord ++ tailWord_1175263) baseStart_1175263 baseEnd_1175263 := by
    simpa [prefixWord, tailWord_1175263, baseEnd_1175263] using wordTrace_append hprefix tailTrace_1175263
  have hstable : (prefixWord ++ tailWord_1175263).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1175263).length < 2 ^ (prefixWord ++ tailWord_1175263).sum := by decide
  have hdescent : baseEnd_1175263 < baseStart_1175263 := by decide
  rcases family_descends (prefixWord ++ tailWord_1175263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1175265 : List Nat := [1, 2, 3, 1, 5, 1, 1, 8]
def baseStart_1175265 : Nat := 118140960795 + 1175265 * 2 ^ 59
def prefixEnd_1175265 : Nat := 4983230072969 + 3 ^ 40 * 1175265 * 2
def baseEnd_1175265 : Nat := 44701914178255518813523

theorem tailTrace_1175265 : CollatzResearch.WordTrace tailWord_1175265 prefixEnd_1175265 44701914178255518813523 := by
  unfold tailWord_1175265
  simp only [CollatzResearch.WordTrace]
  refine ⟨42865436087223099127031249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28576957391482066084687499 42865436087223099127031249)
  ·
    refine ⟨32149077065417324345273437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42865436087223099127031249 32149077065417324345273437)
    ·
      refine ⟨12055903899531496629477539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32149077065417324345273437 12055903899531496629477539)
      ·
        refine ⟨18083855849297244944216309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12055903899531496629477539 18083855849297244944216309)
        ·
          refine ⟨1695361485871616713520279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 18083855849297244944216309 1695361485871616713520279)
          ·
            refine ⟨2543042228807425070280419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1695361485871616713520279 2543042228807425070280419)
            ·
              refine ⟨3814563343211137605420629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2543042228807425070280419 3814563343211137605420629)
              ·
                refine ⟨44701914178255518813523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3814563343211137605420629 44701914178255518813523)
                ·
                  rfl

theorem cell22_1175265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 1, 8].length) (baseStart_1175265 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1175265 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1175265 prefixEnd_1175265 := by exact prefixLift 1175265
  have htrace : WordTrace (prefixWord ++ tailWord_1175265) baseStart_1175265 baseEnd_1175265 := by
    simpa [prefixWord, tailWord_1175265, baseEnd_1175265] using wordTrace_append hprefix tailTrace_1175265
  have hstable : (prefixWord ++ tailWord_1175265).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1175265).length < 2 ^ (prefixWord ++ tailWord_1175265).sum := by decide
  have hdescent : baseEnd_1175265 < baseStart_1175265 := by decide
  rcases family_descends (prefixWord ++ tailWord_1175265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1175271 : List Nat := [1, 1, 5, 4, 1, 2, 1, 3, 4]
def baseStart_1175271 : Nat := 118140960795 + 1175271 * 2 ^ 59
def prefixEnd_1175271 : Nat := 4983230072969 + 3 ^ 40 * 1175271 * 2
def baseEnd_1175271 : Nat := 134106427175639217890563

theorem tailTrace_1175271 : CollatzResearch.WordTrace tailWord_1175271 prefixEnd_1175271 134106427175639217890563 := by
  unfold tailWord_1175271
  simp only [CollatzResearch.WordTrace]
  refine ⟨42865654925201362151749667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28577103283467574767833111 42865654925201362151749667)
  ·
    refine ⟨64298482387802043227624501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42865654925201362151749667 64298482387802043227624501)
    ·
      refine ⟨6027982723856441552589797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 64298482387802043227624501 6027982723856441552589797)
      ·
        refine ⟨1130246760723082791110587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6027982723856441552589797 1130246760723082791110587)
        ·
          refine ⟨1695370141084624186665881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1130246760723082791110587 1695370141084624186665881)
          ·
            refine ⟨1271527605813468139999411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1695370141084624186665881 1271527605813468139999411)
            ·
              refine ⟨1907291408720202209999117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1271527605813468139999411 1907291408720202209999117)
              ·
                refine ⟨715234278270075828749669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1907291408720202209999117 715234278270075828749669)
                ·
                  refine ⟨134106427175639217890563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 715234278270075828749669 134106427175639217890563)
                  ·
                    rfl

theorem cell22_1175271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 2, 1, 3, 4].length) (baseStart_1175271 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1175271 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1175271 prefixEnd_1175271 := by exact prefixLift 1175271
  have htrace : WordTrace (prefixWord ++ tailWord_1175271) baseStart_1175271 baseEnd_1175271 := by
    simpa [prefixWord, tailWord_1175271, baseEnd_1175271] using wordTrace_append hprefix tailTrace_1175271
  have hstable : (prefixWord ++ tailWord_1175271).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1175271).length < 2 ^ (prefixWord ++ tailWord_1175271).sum := by decide
  have hdescent : baseEnd_1175271 < baseStart_1175271 := by decide
  rcases family_descends (prefixWord ++ tailWord_1175271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1175284 : List Nat := [2, 6, 1, 1, 1, 1, 1, 1, 4, 4]
def baseStart_1175284 : Nat := 118140960795 + 1175284 * 2 ^ 59
def prefixEnd_1175284 : Nat := 4983230072969 + 3 ^ 40 * 1175284 * 2
def baseEnd_1175284 : Nat := 402323731692589953096649

theorem tailTrace_1175284 : CollatzResearch.WordTrace tailWord_1175284 prefixEnd_1175284 402323731692589953096649 := by
  unfold tailWord_1175284
  simp only [CollatzResearch.WordTrace]
  refine ⟨21433064537077132685986453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28577419382769510247981937 21433064537077132685986453)
  ·
    refine ⟨1004674900175490594655615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 21433064537077132685986453 1004674900175490594655615)
    ·
      refine ⟨1507012350263235891983423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1004674900175490594655615 1507012350263235891983423)
      ·
        refine ⟨2260518525394853837975135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1507012350263235891983423 2260518525394853837975135)
        ·
          refine ⟨3390777788092280756962703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2260518525394853837975135 3390777788092280756962703)
          ·
            refine ⟨5086166682138421135444055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3390777788092280756962703 5086166682138421135444055)
            ·
              refine ⟨7629250023207631703166083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5086166682138421135444055 7629250023207631703166083)
              ·
                refine ⟨11443875034811447554749125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7629250023207631703166083 11443875034811447554749125)
                ·
                  refine ⟨2145726569027146416515461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11443875034811447554749125 2145726569027146416515461)
                  ·
                    refine ⟨402323731692589953096649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2145726569027146416515461 402323731692589953096649)
                    ·
                      rfl

theorem cell22_1175284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 1, 4, 4].length) (baseStart_1175284 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1175284 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1175284 prefixEnd_1175284 := by exact prefixLift 1175284
  have htrace : WordTrace (prefixWord ++ tailWord_1175284) baseStart_1175284 baseEnd_1175284 := by
    simpa [prefixWord, tailWord_1175284, baseEnd_1175284] using wordTrace_append hprefix tailTrace_1175284
  have hstable : (prefixWord ++ tailWord_1175284).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1175284).length < 2 ^ (prefixWord ++ tailWord_1175284).sum := by decide
  have hdescent : baseEnd_1175284 < baseStart_1175284 := by decide
  rcases family_descends (prefixWord ++ tailWord_1175284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1175297 : List Nat := [1, 2, 4, 1, 1, 1, 5, 1, 3, 3]
def baseStart_1175297 : Nat := 118140960795 + 1175297 * 2 ^ 59
def prefixEnd_1175297 : Nat := 4983230072969 + 3 ^ 40 * 1175297 * 2
def baseEnd_1175297 : Nat := 402328181858262252521609

theorem tailTrace_1175297 : CollatzResearch.WordTrace tailWord_1175297 prefixEnd_1175297 402328181858262252521609 := by
  unfold tailWord_1175297
  simp only [CollatzResearch.WordTrace]
  refine ⟨42866603223107168592196145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28577735482071445728130763 42866603223107168592196145)
  ·
    refine ⟨32149952417330376444147109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42866603223107168592196145 32149952417330376444147109)
    ·
      refine ⟨6028116078249445583277583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32149952417330376444147109 6028116078249445583277583)
      ·
        refine ⟨9042174117374168374916375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6028116078249445583277583 9042174117374168374916375)
        ·
          refine ⟨13563261176061252562374563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9042174117374168374916375 13563261176061252562374563)
          ·
            refine ⟨20344891764091878843561845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13563261176061252562374563 20344891764091878843561845)
            ·
              refine ⟨1907333602883613641583923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 20344891764091878843561845 1907333602883613641583923)
              ·
                refine ⟨2861000404325420462375885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1907333602883613641583923 2861000404325420462375885)
                ·
                  refine ⟨1072875151622032673390957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2861000404325420462375885 1072875151622032673390957)
                  ·
                    refine ⟨402328181858262252521609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1072875151622032673390957 402328181858262252521609)
                    ·
                      rfl

theorem cell22_1175297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 5, 1, 3, 3].length) (baseStart_1175297 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1175297 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1175297 prefixEnd_1175297 := by exact prefixLift 1175297
  have htrace : WordTrace (prefixWord ++ tailWord_1175297) baseStart_1175297 baseEnd_1175297 := by
    simpa [prefixWord, tailWord_1175297, baseEnd_1175297] using wordTrace_append hprefix tailTrace_1175297
  have hstable : (prefixWord ++ tailWord_1175297).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1175297).length < 2 ^ (prefixWord ++ tailWord_1175297).sum := by decide
  have hdescent : baseEnd_1175297 < baseStart_1175297 := by decide
  rcases family_descends (prefixWord ++ tailWord_1175297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1175303 : List Nat := [1, 1, 4, 4, 3, 1, 2, 1, 2, 3]
def baseStart_1175303 : Nat := 118140960795 + 1175303 * 2 ^ 59
def prefixEnd_1175303 : Nat := 4983230072969 + 3 ^ 40 * 1175303 * 2
def baseEnd_1175303 : Nat := 402330235780880236871591

theorem tailTrace_1175303 : CollatzResearch.WordTrace tailWord_1175303 prefixEnd_1175303 402330235780880236871591 := by
  unfold tailWord_1175303
  simp only [CollatzResearch.WordTrace]
  refine ⟨42866822061085431616914563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28577881374056954411276375 42866822061085431616914563)
  ·
    refine ⟨64300233091628147425371845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42866822061085431616914563 64300233091628147425371845)
    ·
      refine ⟨12056293704680277642257221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 64300233091628147425371845 12056293704680277642257221)
      ·
        refine ⟨2260555069627552057923229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12056293704680277642257221 2260555069627552057923229)
        ·
          refine ⟨847708151110332021721211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2260555069627552057923229 847708151110332021721211)
          ·
            refine ⟨1271562226665498032581817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 847708151110332021721211 1271562226665498032581817)
            ·
              refine ⟨953671669999123524436363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1271562226665498032581817 953671669999123524436363)
              ·
                refine ⟨1430507504998685286654545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 953671669999123524436363 1430507504998685286654545)
                ·
                  refine ⟨1072880628749013964990909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1430507504998685286654545 1072880628749013964990909)
                  ·
                    refine ⟨402330235780880236871591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1072880628749013964990909 402330235780880236871591)
                    ·
                      rfl

theorem cell22_1175303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 3, 1, 2, 1, 2, 3].length) (baseStart_1175303 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1175303 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1175303 prefixEnd_1175303 := by exact prefixLift 1175303
  have htrace : WordTrace (prefixWord ++ tailWord_1175303) baseStart_1175303 baseEnd_1175303 := by
    simpa [prefixWord, tailWord_1175303, baseEnd_1175303] using wordTrace_append hprefix tailTrace_1175303
  have hstable : (prefixWord ++ tailWord_1175303).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1175303).length < 2 ^ (prefixWord ++ tailWord_1175303).sum := by decide
  have hdescent : baseEnd_1175303 < baseStart_1175303 := by decide
  rcases family_descends (prefixWord ++ tailWord_1175303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1175323 : List Nat := [1, 1, 1, 1, 1, 1, 4, 2, 2, 8]
def baseStart_1175323 : Nat := 118140960795 + 1175323 * 2 ^ 59
def prefixEnd_1175323 : Nat := 4983230072969 + 3 ^ 40 * 1175323 * 2
def baseEnd_1175323 : Nat := 402337082189606851371529

theorem tailTrace_1175323 : CollatzResearch.WordTrace tailWord_1175323 prefixEnd_1175323 402337082189606851371529 := by
  unfold tailWord_1175323
  simp only [CollatzResearch.WordTrace]
  refine ⟨42867551521012975032642623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28578367680675316688428415 42867551521012975032642623)
  ·
    refine ⟨64301327281519462548963935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42867551521012975032642623 64301327281519462548963935)
    ·
      refine ⟨96451990922279193823445903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64301327281519462548963935 96451990922279193823445903)
      ·
        refine ⟨144677986383418790735168855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96451990922279193823445903 144677986383418790735168855)
        ·
          refine ⟨217016979575128186102753283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 144677986383418790735168855 217016979575128186102753283)
          ·
            refine ⟨325525469362692279154129925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 217016979575128186102753283 325525469362692279154129925)
            ·
              refine ⟨61036025505504802341399361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 325525469362692279154129925 61036025505504802341399361)
              ·
                refine ⟨45777019129128601756049521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 61036025505504802341399361 45777019129128601756049521)
                ·
                  refine ⟨34332764346846451317037141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 45777019129128601756049521 34332764346846451317037141)
                  ·
                    refine ⟨402337082189606851371529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 34332764346846451317037141 402337082189606851371529)
                    ·
                      rfl

theorem cell22_1175323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 2, 2, 8].length) (baseStart_1175323 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1175323 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1175323 prefixEnd_1175323 := by exact prefixLift 1175323
  have htrace : WordTrace (prefixWord ++ tailWord_1175323) baseStart_1175323 baseEnd_1175323 := by
    simpa [prefixWord, tailWord_1175323, baseEnd_1175323] using wordTrace_append hprefix tailTrace_1175323
  have hstable : (prefixWord ++ tailWord_1175323).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1175323).length < 2 ^ (prefixWord ++ tailWord_1175323).sum := by decide
  have hdescent : baseEnd_1175323 < baseStart_1175323 := by decide
  rcases family_descends (prefixWord ++ tailWord_1175323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1175348 : List Nat := [2, 5, 1, 1, 2, 1, 4, 2, 1, 3]
def baseStart_1175348 : Nat := 118140960795 + 1175348 * 2 ^ 59
def prefixEnd_1175348 : Nat := 4983230072969 + 3 ^ 40 * 1175348 * 2
def baseEnd_1175348 : Nat := 402345640200515119496453

theorem tailTrace_1175348 : CollatzResearch.WordTrace tailWord_1175348 prefixEnd_1175348 402345640200515119496453 := by
  unfold tailWord_1175348
  simp only [CollatzResearch.WordTrace]
  refine ⟨21434231672961202151151349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28578975563948269534868465 21434231672961202151151349)
  ·
    refine ⟨2009459219340112701670439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 21434231672961202151151349 2009459219340112701670439)
    ·
      refine ⟨3014188829010169052505659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2009459219340112701670439 3014188829010169052505659)
      ·
        refine ⟨4521283243515253578758489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3014188829010169052505659 4521283243515253578758489)
        ·
          refine ⟨3390962432636440184068867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4521283243515253578758489 3390962432636440184068867)
          ·
            refine ⟨5086443648954660276103301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3390962432636440184068867 5086443648954660276103301)
            ·
              refine ⟨953708184178998801769369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5086443648954660276103301 953708184178998801769369)
              ·
                refine ⟨715281138134249101327027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 953708184178998801769369 715281138134249101327027)
                ·
                  refine ⟨1072921707201373651990541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 715281138134249101327027 1072921707201373651990541)
                  ·
                    refine ⟨402345640200515119496453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1072921707201373651990541 402345640200515119496453)
                    ·
                      rfl

theorem cell22_1175348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 4, 2, 1, 3].length) (baseStart_1175348 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1175348 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1175348 prefixEnd_1175348 := by exact prefixLift 1175348
  have htrace : WordTrace (prefixWord ++ tailWord_1175348) baseStart_1175348 baseEnd_1175348 := by
    simpa [prefixWord, tailWord_1175348, baseEnd_1175348] using wordTrace_append hprefix tailTrace_1175348
  have hstable : (prefixWord ++ tailWord_1175348).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1175348).length < 2 ^ (prefixWord ++ tailWord_1175348).sum := by decide
  have hdescent : baseEnd_1175348 < baseStart_1175348 := by decide
  rcases family_descends (prefixWord ++ tailWord_1175348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1175357 : List Nat := [1, 4, 1, 4, 1, 1, 1, 2, 3, 4]
def baseStart_1175357 : Nat := 118140960795 + 1175357 * 2 ^ 59
def prefixEnd_1175357 : Nat := 4983230072969 + 3 ^ 40 * 1175357 * 2
def baseEnd_1175357 : Nat := 402348721084442096021425

theorem tailTrace_1175357 : CollatzResearch.WordTrace tailWord_1175357 prefixEnd_1175357 402348721084442096021425 := by
  unfold tailWord_1175357
  simp only [CollatzResearch.WordTrace]
  refine ⟨42868791602889798839380325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28579194401926532559586883 42868791602889798839380325)
  ·
    refine ⟨8037898425541837282383811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 42868791602889798839380325 8037898425541837282383811)
    ·
      refine ⟨12056847638312755923575717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8037898425541837282383811 12056847638312755923575717)
      ·
        refine ⟨2260658932183641735670447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12056847638312755923575717 2260658932183641735670447)
        ·
          refine ⟨3390988398275462603505671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2260658932183641735670447 3390988398275462603505671)
          ·
            refine ⟨5086482597413193905258507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3390988398275462603505671 5086482597413193905258507)
            ·
              refine ⟨7629723896119790857887761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5086482597413193905258507 7629723896119790857887761)
              ·
                refine ⟨5722292922089843143415821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7629723896119790857887761 5722292922089843143415821)
                ·
                  refine ⟨2145859845783691178780933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5722292922089843143415821 2145859845783691178780933)
                  ·
                    refine ⟨402348721084442096021425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2145859845783691178780933 402348721084442096021425)
                    ·
                      rfl

theorem cell22_1175357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 2, 3, 4].length) (baseStart_1175357 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1175357 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1175357 prefixEnd_1175357 := by exact prefixLift 1175357
  have htrace : WordTrace (prefixWord ++ tailWord_1175357) baseStart_1175357 baseEnd_1175357 := by
    simpa [prefixWord, tailWord_1175357, baseEnd_1175357] using wordTrace_append hprefix tailTrace_1175357
  have hstable : (prefixWord ++ tailWord_1175357).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1175357).length < 2 ^ (prefixWord ++ tailWord_1175357).sum := by decide
  have hdescent : baseEnd_1175357 < baseStart_1175357 := by decide
  rcases family_descends (prefixWord ++ tailWord_1175357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1175372 : List Nat := [2, 2, 1, 3, 4, 1, 1, 2, 6]
def baseStart_1175372 : Nat := 118140960795 + 1175372 * 2 ^ 59
def prefixEnd_1175372 : Nat := 4983230072969 + 3 ^ 40 * 1175372 * 2
def baseEnd_1175372 : Nat := 134117951963662352298793

theorem tailTrace_1175372 : CollatzResearch.WordTrace tailWord_1175372 prefixEnd_1175372 134117951963662352298793 := by
  unfold tailWord_1175372
  simp only [CollatzResearch.WordTrace]
  refine ⟨21434669348917728200588185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28579559131890304267450913 21434669348917728200588185)
  ·
    refine ⟨16076002011688296150441139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21434669348917728200588185 16076002011688296150441139)
    ·
      refine ⟨24114003017532444225661709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16076002011688296150441139 24114003017532444225661709)
      ·
        refine ⟨9042751131574666584623141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24114003017532444225661709 9042751131574666584623141)
        ·
          refine ⟨1695515837170249984616839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9042751131574666584623141 1695515837170249984616839)
          ·
            refine ⟨2543273755755374976925259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1695515837170249984616839 2543273755755374976925259)
            ·
              refine ⟨3814910633633062465387889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2543273755755374976925259 3814910633633062465387889)
              ·
                refine ⟨2861182975224796849040917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3814910633633062465387889 2861182975224796849040917)
                ·
                  refine ⟨134117951963662352298793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2861182975224796849040917 134117951963662352298793)
                  ·
                    rfl

theorem cell22_1175372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 1, 2, 6].length) (baseStart_1175372 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1175372 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1175372 prefixEnd_1175372 := by exact prefixLift 1175372
  have htrace : WordTrace (prefixWord ++ tailWord_1175372) baseStart_1175372 baseEnd_1175372 := by
    simpa [prefixWord, tailWord_1175372, baseEnd_1175372] using wordTrace_append hprefix tailTrace_1175372
  have hstable : (prefixWord ++ tailWord_1175372).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1175372).length < 2 ^ (prefixWord ++ tailWord_1175372).sum := by decide
  have hdescent : baseEnd_1175372 < baseStart_1175372 := by decide
  rcases family_descends (prefixWord ++ tailWord_1175372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1175385 : List Nat := [1, 2, 1, 2, 2, 3, 3, 1, 1, 6]
def baseStart_1175385 : Nat := 118140960795 + 1175385 * 2 ^ 59
def prefixEnd_1175385 : Nat := 4983230072969 + 3 ^ 40 * 1175385 * 2
def baseEnd_1175385 : Nat := 402358306056659356321339

theorem tailTrace_1175385 : CollatzResearch.WordTrace tailWord_1175385 prefixEnd_1175385 402358306056659356321339 := by
  unfold tailWord_1175385
  simp only [CollatzResearch.WordTrace]
  refine ⟨42869812846788359621399609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28579875231192239747599739 42869812846788359621399609)
  ·
    refine ⟨32152359635091269716049707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42869812846788359621399609 32152359635091269716049707)
    ·
      refine ⟨48228539452636904574074561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32152359635091269716049707 48228539452636904574074561)
      ·
        refine ⟨36171404589477678430555921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48228539452636904574074561 36171404589477678430555921)
        ·
          refine ⟨27128553442108258822916941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36171404589477678430555921 27128553442108258822916941)
          ·
            refine ⟨10173207540790597058593853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27128553442108258822916941 10173207540790597058593853)
            ·
              refine ⟨3814952827796473896972695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10173207540790597058593853 3814952827796473896972695)
              ·
                refine ⟨5722429241694710845459043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3814952827796473896972695 5722429241694710845459043)
                ·
                  refine ⟨8583643862542066268188565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5722429241694710845459043 8583643862542066268188565)
                  ·
                    refine ⟨402358306056659356321339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8583643862542066268188565 402358306056659356321339)
                    ·
                      rfl

theorem cell22_1175385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 3, 1, 1, 6].length) (baseStart_1175385 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1175385 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1175385 prefixEnd_1175385 := by exact prefixLift 1175385
  have htrace : WordTrace (prefixWord ++ tailWord_1175385) baseStart_1175385 baseEnd_1175385 := by
    simpa [prefixWord, tailWord_1175385, baseEnd_1175385] using wordTrace_append hprefix tailTrace_1175385
  have hstable : (prefixWord ++ tailWord_1175385).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1175385).length < 2 ^ (prefixWord ++ tailWord_1175385).sum := by decide
  have hdescent : baseEnd_1175385 < baseStart_1175385 := by decide
  rcases family_descends (prefixWord ++ tailWord_1175385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1175400 : List Nat := [2, 1, 4, 2, 1, 1, 11]
def baseStart_1175400 : Nat := 118140960795 + 1175400 * 2 ^ 59
def prefixEnd_1175400 : Nat := 4983230072969 + 3 ^ 40 * 1175400 * 2
def baseEnd_1175400 : Nat := 14902349661600159896159

theorem tailTrace_1175400 : CollatzResearch.WordTrace tailWord_1175400 prefixEnd_1175400 14902349661600159896159 := by
  unfold tailWord_1175400
  simp only [CollatzResearch.WordTrace]
  refine ⟨21435179970867008591597827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28580239961156011455463769 21435179970867008591597827)
  ·
    refine ⟨32152769956300512887396741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21435179970867008591597827 32152769956300512887396741)
    ·
      refine ⟨6028644366806346166386889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32152769956300512887396741 6028644366806346166386889)
      ·
        refine ⟨4521483275104759624790167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6028644366806346166386889 4521483275104759624790167)
        ·
          refine ⟨6782224912657139437185251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4521483275104759624790167 6782224912657139437185251)
          ·
            refine ⟨10173337368985709155777877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6782224912657139437185251 10173337368985709155777877)
            ·
              refine ⟨14902349661600159896159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 10173337368985709155777877 14902349661600159896159)
              ·
                rfl

theorem cell22_1175400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 11].length) (baseStart_1175400 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1175400 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1175400 prefixEnd_1175400 := by exact prefixLift 1175400
  have htrace : WordTrace (prefixWord ++ tailWord_1175400) baseStart_1175400 baseEnd_1175400 := by
    simpa [prefixWord, tailWord_1175400, baseEnd_1175400] using wordTrace_append hprefix tailTrace_1175400
  have hstable : (prefixWord ++ tailWord_1175400).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1175400).length < 2 ^ (prefixWord ++ tailWord_1175400).sum := by decide
  have hdescent : baseEnd_1175400 < baseStart_1175400 := by decide
  rcases family_descends (prefixWord ++ tailWord_1175400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1175404 : List Nat := [2, 2, 1, 1, 4, 2, 3, 2, 2, 3]
def baseStart_1175404 : Nat := 118140960795 + 1175404 * 2 ^ 59
def prefixEnd_1175404 : Nat := 4983230072969 + 3 ^ 40 * 1175404 * 2
def baseEnd_1175404 : Nat := 402364810144949640096281

theorem tailTrace_1175404 : CollatzResearch.WordTrace tailWord_1175404 prefixEnd_1175404 402364810144949640096281 := by
  unfold tailWord_1175404
  simp only [CollatzResearch.WordTrace]
  refine ⟨21435252916859762933170633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28580337222479683910894177 21435252916859762933170633)
  ·
    refine ⟨16076439687644822199877975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21435252916859762933170633 16076439687644822199877975)
    ·
      refine ⟨24114659531467233299816963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16076439687644822199877975 24114659531467233299816963)
      ·
        refine ⟨36171989297200849949725445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24114659531467233299816963 36171989297200849949725445)
        ·
          refine ⟨6782247993225159365573521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 36171989297200849949725445 6782247993225159365573521)
          ·
            refine ⟨5086685994918869524180141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6782247993225159365573521 5086685994918869524180141)
            ·
              refine ⟨1907507248094576071567553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5086685994918869524180141 1907507248094576071567553)
              ·
                refine ⟨1430630436070932053675665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1907507248094576071567553 1430630436070932053675665)
                ·
                  refine ⟨1072972827053199040256749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1430630436070932053675665 1072972827053199040256749)
                  ·
                    refine ⟨402364810144949640096281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1072972827053199040256749 402364810144949640096281)
                    ·
                      rfl

theorem cell22_1175404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 2, 3].length) (baseStart_1175404 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1175404 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1175404 prefixEnd_1175404 := by exact prefixLift 1175404
  have htrace : WordTrace (prefixWord ++ tailWord_1175404) baseStart_1175404 baseEnd_1175404 := by
    simpa [prefixWord, tailWord_1175404, baseEnd_1175404] using wordTrace_append hprefix tailTrace_1175404
  have hstable : (prefixWord ++ tailWord_1175404).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1175404).length < 2 ^ (prefixWord ++ tailWord_1175404).sum := by decide
  have hdescent : baseEnd_1175404 < baseStart_1175404 := by decide
  rcases family_descends (prefixWord ++ tailWord_1175404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1175445 : List Nat := [1, 3, 2, 1, 1, 3, 1, 1, 9]
def baseStart_1175445 : Nat := 118140960795 + 1175445 * 2 ^ 59
def prefixEnd_1175445 : Nat := 4983230072969 + 3 ^ 40 * 1175445 * 2
def baseEnd_1175445 : Nat := 134126281760946399940385

theorem tailTrace_1175445 : CollatzResearch.WordTrace tailWord_1175445 prefixEnd_1175445 134126281760946399940385 := by
  unfold tailWord_1175445
  simp only [CollatzResearch.WordTrace]
  refine ⟨42872001226570989868583789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28581334151047326579055859 42872001226570989868583789)
  ·
    refine ⟨16077000459964121200718921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42872001226570989868583789 16077000459964121200718921)
    ·
      refine ⟨12057750344973090900539191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16077000459964121200718921 12057750344973090900539191)
      ·
        refine ⟨18086625517459636350808787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12057750344973090900539191 18086625517459636350808787)
        ·
          refine ⟨27129938276189454526213181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18086625517459636350808787 27129938276189454526213181)
          ·
            refine ⟨10173726853571045447329943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27129938276189454526213181 10173726853571045447329943)
            ·
              refine ⟨15260590280356568170994915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10173726853571045447329943 15260590280356568170994915)
              ·
                refine ⟨22890885420534852256492373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15260590280356568170994915 22890885420534852256492373)
                ·
                  refine ⟨134126281760946399940385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 22890885420534852256492373 134126281760946399940385)
                  ·
                    rfl

theorem cell22_1175445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 1, 9].length) (baseStart_1175445 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1175445 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1175445 prefixEnd_1175445 := by exact prefixLift 1175445
  have htrace : WordTrace (prefixWord ++ tailWord_1175445) baseStart_1175445 baseEnd_1175445 := by
    simpa [prefixWord, tailWord_1175445, baseEnd_1175445] using wordTrace_append hprefix tailTrace_1175445
  have hstable : (prefixWord ++ tailWord_1175445).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1175445).length < 2 ^ (prefixWord ++ tailWord_1175445).sum := by decide
  have hdescent : baseEnd_1175445 < baseStart_1175445 := by decide
  rcases family_descends (prefixWord ++ tailWord_1175445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1175517 : List Nat := [1, 4, 3, 1, 4, 1, 2, 2, 1, 3]
def baseStart_1175517 : Nat := 118140960795 + 1175517 * 2 ^ 59
def prefixEnd_1175517 : Nat := 4983230072969 + 3 ^ 40 * 1175517 * 2
def baseEnd_1175517 : Nat := 402403492354255012020935

theorem tailTrace_1175517 : CollatzResearch.WordTrace tailWord_1175517 prefixEnd_1175517 402403492354255012020935 := by
  unfold tailWord_1175517
  simp only [CollatzResearch.WordTrace]
  refine ⟨42874627282310146165204805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28583084854873430776803203 42874627282310146165204805)
  ·
    refine ⟨8038992615433152405975901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 42874627282310146165204805 8038992615433152405975901)
    ·
      refine ⟨3014622230787432152240963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8038992615433152405975901 3014622230787432152240963)
      ·
        refine ⟨4521933346181148228361445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3014622230787432152240963 4521933346181148228361445)
        ·
          refine ⟨847862502408965292817771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4521933346181148228361445 847862502408965292817771)
          ·
            refine ⟨1271793753613447939226657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 847862502408965292817771 1271793753613447939226657)
            ·
              refine ⟨953845315210085954419993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1271793753613447939226657 953845315210085954419993)
              ·
                refine ⟨715383986407564465814995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 953845315210085954419993 715383986407564465814995)
                ·
                  refine ⟨1073075979611346698722493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 715383986407564465814995 1073075979611346698722493)
                  ·
                    refine ⟨402403492354255012020935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1073075979611346698722493 402403492354255012020935)
                    ·
                      rfl

theorem cell22_1175517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 4, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 4, 1, 2, 2, 1, 3].length) (baseStart_1175517 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1175517 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1175517 prefixEnd_1175517 := by exact prefixLift 1175517
  have htrace : WordTrace (prefixWord ++ tailWord_1175517) baseStart_1175517 baseEnd_1175517 := by
    simpa [prefixWord, tailWord_1175517, baseEnd_1175517] using wordTrace_append hprefix tailTrace_1175517
  have hstable : (prefixWord ++ tailWord_1175517).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1175517).length < 2 ^ (prefixWord ++ tailWord_1175517).sum := by decide
  have hdescent : baseEnd_1175517 < baseStart_1175517 := by decide
  rcases family_descends (prefixWord ++ tailWord_1175517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1175524 : List Nat := [2, 3, 1, 1, 1, 1, 5, 4, 4]
def baseStart_1175524 : Nat := 118140960795 + 1175524 * 2 ^ 59
def prefixEnd_1175524 : Nat := 4983230072969 + 3 ^ 40 * 1175524 * 2
def baseEnd_1175524 : Nat := 134135296199103109031971

theorem tailTrace_1175524 : CollatzResearch.WordTrace tailWord_1175524 prefixEnd_1175524 134135296199103109031971 := by
  unfold tailWord_1175524
  simp only [CollatzResearch.WordTrace]
  refine ⟨21437441296642393180354813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28583255062189857573806417 21437441296642393180354813)
  ·
    refine ⟨8039040486240897442633055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21437441296642393180354813 8039040486240897442633055)
    ·
      refine ⟨12058560729361346163949583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8039040486240897442633055 12058560729361346163949583)
      ·
        refine ⟨18087841094042019245924375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12058560729361346163949583 18087841094042019245924375)
        ·
          refine ⟨27131761641063028868886563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18087841094042019245924375 27131761641063028868886563)
          ·
            refine ⟨40697642461594543303329845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27131761641063028868886563 40697642461594543303329845)
            ·
              refine ⟨3815403980774488434687173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 40697642461594543303329845 3815403980774488434687173)
              ·
                refine ⟨715388246395216581503845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3815403980774488434687173 715388246395216581503845)
                ·
                  refine ⟨134135296199103109031971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 715388246395216581503845 134135296199103109031971)
                  ·
                    rfl

theorem cell22_1175524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 5, 4, 4].length) (baseStart_1175524 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1175524 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1175524 prefixEnd_1175524 := by exact prefixLift 1175524
  have htrace : WordTrace (prefixWord ++ tailWord_1175524) baseStart_1175524 baseEnd_1175524 := by
    simpa [prefixWord, tailWord_1175524, baseEnd_1175524] using wordTrace_append hprefix tailTrace_1175524
  have hstable : (prefixWord ++ tailWord_1175524).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1175524).length < 2 ^ (prefixWord ++ tailWord_1175524).sum := by decide
  have hdescent : baseEnd_1175524 < baseStart_1175524 := by decide
  rcases family_descends (prefixWord ++ tailWord_1175524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1175573 : List Nat := [1, 3, 2, 1, 5, 2, 1, 2, 2, 3]
def baseStart_1175573 : Nat := 118140960795 + 1175573 * 2 ^ 59
def prefixEnd_1175573 : Nat := 4983230072969 + 3 ^ 40 * 1175573 * 2
def baseEnd_1175573 : Nat := 402422662298689532620763

theorem tailTrace_1175573 : CollatzResearch.WordTrace tailWord_1175573 prefixEnd_1175573 402422662298689532620763 := by
  unfold tailWord_1175573
  simp only [CollatzResearch.WordTrace]
  refine ⟨42876669770107267729243373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28584446513404845152828915 42876669770107267729243373)
  ·
    refine ⟨16078751163790225398466265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42876669770107267729243373 16078751163790225398466265)
    ·
      refine ⟨12059063372842669048849699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16078751163790225398466265 12059063372842669048849699)
      ·
        refine ⟨18088595059264003573274549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12059063372842669048849699 18088595059264003573274549)
        ·
          refine ⟨1695805786806000334994489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 18088595059264003573274549 1695805786806000334994489)
          ·
            refine ⟨1271854340104500251245867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1695805786806000334994489 1271854340104500251245867)
            ·
              refine ⟨1907781510156750376868801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1271854340104500251245867 1907781510156750376868801)
              ·
                refine ⟨1430836132617562782651601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1907781510156750376868801 1430836132617562782651601)
                ·
                  refine ⟨1073127099463172086988701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1430836132617562782651601 1073127099463172086988701)
                  ·
                    refine ⟨402422662298689532620763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1073127099463172086988701 402422662298689532620763)
                    ·
                      rfl

theorem cell22_1175573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 2, 1, 2, 2, 3].length) (baseStart_1175573 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1175573 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1175573 prefixEnd_1175573 := by exact prefixLift 1175573
  have htrace : WordTrace (prefixWord ++ tailWord_1175573) baseStart_1175573 baseEnd_1175573 := by
    simpa [prefixWord, tailWord_1175573, baseEnd_1175573] using wordTrace_append hprefix tailTrace_1175573
  have hstable : (prefixWord ++ tailWord_1175573).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1175573).length < 2 ^ (prefixWord ++ tailWord_1175573).sum := by decide
  have hdescent : baseEnd_1175573 < baseStart_1175573 := by decide
  rcases family_descends (prefixWord ++ tailWord_1175573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1175689 : List Nat := [1, 2, 1, 1, 4, 2, 1, 4, 2, 4]
def baseStart_1175689 : Nat := 118140960795 + 1175689 * 2 ^ 59
def prefixEnd_1175689 : Nat := 4983230072969 + 3 ^ 40 * 1175689 * 2
def baseEnd_1175689 : Nat := 402462371469303896720407

theorem tailTrace_1175689 : CollatzResearch.WordTrace tailWord_1175689 prefixEnd_1175689 402462371469303896720407 := by
  unfold tailWord_1175689
  simp only [CollatzResearch.WordTrace]
  refine ⟨42880900637687019540466121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28587267091791346360310747 42880900637687019540466121)
  ·
    refine ⟨32160675478265264655349591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42880900637687019540466121 32160675478265264655349591)
    ·
      refine ⟨48241013217397896983024387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32160675478265264655349591 48241013217397896983024387)
      ·
        refine ⟨72361519826096845474536581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48241013217397896983024387 72361519826096845474536581)
        ·
          refine ⟨13567784967393158526475609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 72361519826096845474536581 13567784967393158526475609)
          ·
            refine ⟨10175838725544868894856707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13567784967393158526475609 10175838725544868894856707)
            ·
              refine ⟨15263758088317303342285061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10175838725544868894856707 15263758088317303342285061)
              ·
                refine ⟨2861954641559494376678449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15263758088317303342285061 2861954641559494376678449)
                ·
                  refine ⟨2146465981169620782508837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2861954641559494376678449 2146465981169620782508837)
                  ·
                    refine ⟨402462371469303896720407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2146465981169620782508837 402462371469303896720407)
                    ·
                      rfl

theorem cell22_1175689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 4, 2, 4].length) (baseStart_1175689 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1175689 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1175689 prefixEnd_1175689 := by exact prefixLift 1175689
  have htrace : WordTrace (prefixWord ++ tailWord_1175689) baseStart_1175689 baseEnd_1175689 := by
    simpa [prefixWord, tailWord_1175689, baseEnd_1175689] using wordTrace_append hprefix tailTrace_1175689
  have hstable : (prefixWord ++ tailWord_1175689).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1175689).length < 2 ^ (prefixWord ++ tailWord_1175689).sum := by decide
  have hdescent : baseEnd_1175689 < baseStart_1175689 := by decide
  rcases family_descends (prefixWord ++ tailWord_1175689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1175742 : List Nat := [4, 2, 1, 1, 5, 1, 1, 2, 2, 3]
def baseStart_1175742 : Nat := 118140960795 + 1175742 * 2 ^ 59
def prefixEnd_1175742 : Nat := 4983230072969 + 3 ^ 40 * 1175742 * 2
def baseEnd_1175742 : Nat := 402480514452429425145245

theorem tailTrace_1175742 : CollatzResearch.WordTrace tailWord_1175742 prefixEnd_1175742 402480514452429425145245 := by
  unfold tailWord_1175742
  simp only [CollatzResearch.WordTrace]
  refine ⟨5360354213311876199018185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28588555804330006394763653 5360354213311876199018185)
  ·
    refine ⟨4020265659983907149263639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5360354213311876199018185 4020265659983907149263639)
    ·
      refine ⟨6030398489975860723895459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4020265659983907149263639 6030398489975860723895459)
      ·
        refine ⟨9045597734963791085843189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6030398489975860723895459 9045597734963791085843189)
        ·
          refine ⟨848024787652855414297799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 9045597734963791085843189 848024787652855414297799)
          ·
            refine ⟨1272037181479283121446699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 848024787652855414297799 1272037181479283121446699)
            ·
              refine ⟨1908055772218924682170049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1272037181479283121446699 1908055772218924682170049)
              ·
                refine ⟨1431041829164193511627537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1908055772218924682170049 1431041829164193511627537)
                ·
                  refine ⟨1073281371873145133720653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1431041829164193511627537 1073281371873145133720653)
                  ·
                    refine ⟨402480514452429425145245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1073281371873145133720653 402480514452429425145245)
                    ·
                      rfl

theorem cell22_1175742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 5, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 5, 1, 1, 2, 2, 3].length) (baseStart_1175742 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1175742 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1175742 prefixEnd_1175742 := by exact prefixLift 1175742
  have htrace : WordTrace (prefixWord ++ tailWord_1175742) baseStart_1175742 baseEnd_1175742 := by
    simpa [prefixWord, tailWord_1175742, baseEnd_1175742] using wordTrace_append hprefix tailTrace_1175742
  have hstable : (prefixWord ++ tailWord_1175742).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1175742).length < 2 ^ (prefixWord ++ tailWord_1175742).sum := by decide
  have hdescent : baseEnd_1175742 < baseStart_1175742 := by decide
  rcases family_descends (prefixWord ++ tailWord_1175742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1175772 : List Nat := [2, 2, 5, 2, 2, 1, 2, 6]
def baseStart_1175772 : Nat := 118140960795 + 1175772 * 2 ^ 59
def prefixEnd_1175772 : Nat := 4983230072969 + 3 ^ 40 * 1175772 * 2
def baseEnd_1175772 : Nat := 44721198229502149655017

theorem tailTrace_1175772 : CollatzResearch.WordTrace tailWord_1175772 prefixEnd_1175772 44721198229502149655017 := by
  unfold tailWord_1175772
  simp only [CollatzResearch.WordTrace]
  refine ⟨21441963948193162357868785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28589285264257549810491713 21441963948193162357868785)
  ·
    refine ⟨16081472961144871768401589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21441963948193162357868785 16081472961144871768401589)
    ·
      refine ⟨1507638090107331728287649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 16081472961144871768401589 1507638090107331728287649)
      ·
        refine ⟨1130728567580498796215737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1507638090107331728287649 1130728567580498796215737)
        ·
          refine ⟨848046425685374097161803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1130728567580498796215737 848046425685374097161803)
          ·
            refine ⟨1272069638528061145742705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 848046425685374097161803 1272069638528061145742705)
            ·
              refine ⟨954052228896045859307029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1272069638528061145742705 954052228896045859307029)
              ·
                refine ⟨44721198229502149655017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 954052228896045859307029 44721198229502149655017)
                ·
                  rfl

theorem cell22_1175772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 2, 1, 2, 6].length) (baseStart_1175772 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1175772 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1175772 prefixEnd_1175772 := by exact prefixLift 1175772
  have htrace : WordTrace (prefixWord ++ tailWord_1175772) baseStart_1175772 baseEnd_1175772 := by
    simpa [prefixWord, tailWord_1175772, baseEnd_1175772] using wordTrace_append hprefix tailTrace_1175772
  have hstable : (prefixWord ++ tailWord_1175772).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1175772).length < 2 ^ (prefixWord ++ tailWord_1175772).sum := by decide
  have hdescent : baseEnd_1175772 < baseStart_1175772 := by decide
  rcases family_descends (prefixWord ++ tailWord_1175772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1175841 : List Nat := [1, 2, 3, 2, 1, 1, 3, 3, 2, 4]
def baseStart_1175841 : Nat := 118140960795 + 1175841 * 2 ^ 59
def prefixEnd_1175841 : Nat := 4983230072969 + 3 ^ 40 * 1175841 * 2
def baseEnd_1175841 : Nat := 402514404175626166919941

theorem tailTrace_1175841 : CollatzResearch.WordTrace tailWord_1175841 prefixEnd_1175841 402514404175626166919941 := by
  unfold tailWord_1175841
  simp only [CollatzResearch.WordTrace]
  refine ⟨42886444533136349499999377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28590963022090899666666251 42886444533136349499999377)
  ·
    refine ⟨32164833399852262124999533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42886444533136349499999377 32164833399852262124999533)
    ·
      refine ⟨12061812524944598296874825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32164833399852262124999533 12061812524944598296874825)
      ·
        refine ⟨9046359393708448722656119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12061812524944598296874825 9046359393708448722656119)
        ·
          refine ⟨13569539090562673083984179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9046359393708448722656119 13569539090562673083984179)
          ·
            refine ⟨20354308635844009625976269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13569539090562673083984179 20354308635844009625976269)
            ·
              refine ⟨7632865738441503609741101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20354308635844009625976269 7632865738441503609741101)
              ·
                refine ⟨2862324651915563853652913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7632865738441503609741101 2862324651915563853652913)
                ·
                  refine ⟨2146743488936672890239685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2862324651915563853652913 2146743488936672890239685)
                  ·
                    refine ⟨402514404175626166919941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2146743488936672890239685 402514404175626166919941)
                    ·
                      rfl

theorem cell22_1175841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 3, 2, 4].length) (baseStart_1175841 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1175841 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1175841 prefixEnd_1175841 := by exact prefixLift 1175841
  have htrace : WordTrace (prefixWord ++ tailWord_1175841) baseStart_1175841 baseEnd_1175841 := by
    simpa [prefixWord, tailWord_1175841, baseEnd_1175841] using wordTrace_append hprefix tailTrace_1175841
  have hstable : (prefixWord ++ tailWord_1175841).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1175841).length < 2 ^ (prefixWord ++ tailWord_1175841).sum := by decide
  have hdescent : baseEnd_1175841 < baseStart_1175841 := by decide
  rcases family_descends (prefixWord ++ tailWord_1175841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1175860 : List Nat := [2, 5, 1, 1, 1, 2, 1, 4, 2, 3]
def baseStart_1175860 : Nat := 118140960795 + 1175860 * 2 ^ 59
def prefixEnd_1175860 : Nat := 4983230072969 + 3 ^ 40 * 1175860 * 2
def baseEnd_1175860 : Nat := 402520908263916450694883

theorem tailTrace_1175860 : CollatzResearch.WordTrace tailWord_1175860 prefixEnd_1175860 402520908263916450694883 := by
  unfold tailWord_1175860
  simp only [CollatzResearch.WordTrace]
  refine ⟨21443568760033757872470517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28591425013378343829960689 21443568760033757872470517)
  ·
    refine ⟨2010334571253164800544111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 21443568760033757872470517 2010334571253164800544111)
    ·
      refine ⟨3015501856879747200816167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2010334571253164800544111 3015501856879747200816167)
      ·
        refine ⟨4523252785319620801224251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3015501856879747200816167 4523252785319620801224251)
        ·
          refine ⟨6784879177979431201836377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4523252785319620801224251 6784879177979431201836377)
          ·
            refine ⟨5088659383484573401377283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6784879177979431201836377 5088659383484573401377283)
            ·
              refine ⟨7632989075226860102065925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5088659383484573401377283 7632989075226860102065925)
              ·
                refine ⟨1431185451605036269137361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7632989075226860102065925 1431185451605036269137361)
                ·
                  refine ⟨1073389088703777201853021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1431185451605036269137361 1073389088703777201853021)
                  ·
                    refine ⟨402520908263916450694883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1073389088703777201853021 402520908263916450694883)
                    ·
                      rfl

theorem cell22_1175860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 4, 2, 3].length) (baseStart_1175860 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1175860 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1175860 prefixEnd_1175860 := by exact prefixLift 1175860
  have htrace : WordTrace (prefixWord ++ tailWord_1175860) baseStart_1175860 baseEnd_1175860 := by
    simpa [prefixWord, tailWord_1175860, baseEnd_1175860] using wordTrace_append hprefix tailTrace_1175860
  have hstable : (prefixWord ++ tailWord_1175860).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1175860).length < 2 ^ (prefixWord ++ tailWord_1175860).sum := by decide
  have hdescent : baseEnd_1175860 < baseStart_1175860 := by decide
  rcases family_descends (prefixWord ++ tailWord_1175860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1175888 : List Nat := [2, 1, 1, 1, 1, 7, 1, 2, 3, 3]
def baseStart_1175888 : Nat := 118140960795 + 1175888 * 2 ^ 59
def prefixEnd_1175888 : Nat := 4983230072969 + 3 ^ 40 * 1175888 * 2
def baseEnd_1175888 : Nat := 402530493236133710994797

theorem tailTrace_1175888 : CollatzResearch.WordTrace tailWord_1175888 prefixEnd_1175888 402530493236133710994797 := by
  unfold tailWord_1175888
  simp only [CollatzResearch.WordTrace]
  refine ⟨21444079381983038263480159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28592105842644051017973545 21444079381983038263480159)
  ·
    refine ⟨32166119072974557395220239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21444079381983038263480159 32166119072974557395220239)
    ·
      refine ⟨48249178609461836092830359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32166119072974557395220239 48249178609461836092830359)
      ·
        refine ⟨72373767914192754139245539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48249178609461836092830359 72373767914192754139245539)
        ·
          refine ⟨108560651871289131208868309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72373767914192754139245539 108560651871289131208868309)
          ·
            refine ⟨2544390278233339012707851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 108560651871289131208868309 2544390278233339012707851)
            ·
              refine ⟨3816585417350008519061777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2544390278233339012707851 3816585417350008519061777)
              ·
                refine ⟨2862439063012506389296333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3816585417350008519061777 2862439063012506389296333)
                ·
                  refine ⟨1073414648629689895986125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2862439063012506389296333 1073414648629689895986125)
                  ·
                    refine ⟨402530493236133710994797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1073414648629689895986125 402530493236133710994797)
                    ·
                      rfl

theorem cell22_1175888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 1, 2, 3, 3].length) (baseStart_1175888 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1175888 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1175888 prefixEnd_1175888 := by exact prefixLift 1175888
  have htrace : WordTrace (prefixWord ++ tailWord_1175888) baseStart_1175888 baseEnd_1175888 := by
    simpa [prefixWord, tailWord_1175888, baseEnd_1175888] using wordTrace_append hprefix tailTrace_1175888
  have hstable : (prefixWord ++ tailWord_1175888).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1175888).length < 2 ^ (prefixWord ++ tailWord_1175888).sum := by decide
  have hdescent : baseEnd_1175888 < baseStart_1175888 := by decide
  rcases family_descends (prefixWord ++ tailWord_1175888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1175948 : List Nat := [2, 2, 1, 2, 1, 4, 1, 4, 1, 4]
def baseStart_1175948 : Nat := 118140960795 + 1175948 * 2 ^ 59
def prefixEnd_1175948 : Nat := 4983230072969 + 3 ^ 40 * 1175948 * 2
def baseEnd_1175948 : Nat := 402551032462313554494613

theorem tailTrace_1175948 : CollatzResearch.WordTrace tailWord_1175948 prefixEnd_1175948 402551032462313554494613 := by
  unfold tailWord_1175948
  simp only [CollatzResearch.WordTrace]
  refine ⟨21445173571874353387072249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28593564762499137849429665 21445173571874353387072249)
  ·
    refine ⟨16083880178905765040304187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21445173571874353387072249 16083880178905765040304187)
    ·
      refine ⟨24125820268358647560456281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16083880178905765040304187 24125820268358647560456281)
      ·
        refine ⟨18094365201268985670342211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24125820268358647560456281 18094365201268985670342211)
        ·
          refine ⟨27141547801903478505513317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18094365201268985670342211 27141547801903478505513317)
          ·
            refine ⟨5089040212856902219783747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27141547801903478505513317 5089040212856902219783747)
            ·
              refine ⟨7633560319285353329675621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5089040212856902219783747 7633560319285353329675621)
              ·
                refine ⟨1431292559866003749314179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7633560319285353329675621 1431292559866003749314179)
                ·
                  refine ⟨2146938839799005623971269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1431292559866003749314179 2146938839799005623971269)
                  ·
                    refine ⟨402551032462313554494613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2146938839799005623971269 402551032462313554494613)
                    ·
                      rfl

theorem cell22_1175948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 4, 1, 4].length) (baseStart_1175948 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1175948 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1175948 prefixEnd_1175948 := by exact prefixLift 1175948
  have htrace : WordTrace (prefixWord ++ tailWord_1175948) baseStart_1175948 baseEnd_1175948 := by
    simpa [prefixWord, tailWord_1175948, baseEnd_1175948] using wordTrace_append hprefix tailTrace_1175948
  have hstable : (prefixWord ++ tailWord_1175948).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1175948).length < 2 ^ (prefixWord ++ tailWord_1175948).sum := by decide
  have hdescent : baseEnd_1175948 < baseStart_1175948 := by decide
  rcases family_descends (prefixWord ++ tailWord_1175948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1175956 : List Nat := [2, 4, 2, 1, 4, 1, 1, 3, 1, 3]
def baseStart_1175956 : Nat := 118140960795 + 1175956 * 2 ^ 59
def prefixEnd_1175956 : Nat := 4983230072969 + 3 ^ 40 * 1175956 * 2
def baseEnd_1175956 : Nat := 402553771025804200294589

theorem tailTrace_1175956 : CollatzResearch.WordTrace tailWord_1175956 prefixEnd_1175956 402553771025804200294589 := by
  unfold tailWord_1175956
  simp only [CollatzResearch.WordTrace]
  refine ⟨21445319463859862070217861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28593759285146482760290481 21445319463859862070217861)
  ·
    refine ⟨4020997399473724138165849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21445319463859862070217861 4020997399473724138165849)
    ·
      refine ⟨3015748049605293103624387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4020997399473724138165849 3015748049605293103624387)
      ·
        refine ⟨4523622074407939655436581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3015748049605293103624387 4523622074407939655436581)
        ·
          refine ⟨848179138951488685394359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4523622074407939655436581 848179138951488685394359)
          ·
            refine ⟨1272268708427233028091539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 848179138951488685394359 1272268708427233028091539)
            ·
              refine ⟨1908403062640849542137309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1272268708427233028091539 1908403062640849542137309)
              ·
                refine ⟨715651148490318578301491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1908403062640849542137309 715651148490318578301491)
                ·
                  refine ⟨1073476722735477867452237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 715651148490318578301491 1073476722735477867452237)
                  ·
                    refine ⟨402553771025804200294589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1073476722735477867452237 402553771025804200294589)
                    ·
                      rfl

theorem cell22_1175956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 4, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 4, 1, 1, 3, 1, 3].length) (baseStart_1175956 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1175956 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1175956 prefixEnd_1175956 := by exact prefixLift 1175956
  have htrace : WordTrace (prefixWord ++ tailWord_1175956) baseStart_1175956 baseEnd_1175956 := by
    simpa [prefixWord, tailWord_1175956, baseEnd_1175956] using wordTrace_append hprefix tailTrace_1175956
  have hstable : (prefixWord ++ tailWord_1175956).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1175956).length < 2 ^ (prefixWord ++ tailWord_1175956).sum := by decide
  have hdescent : baseEnd_1175956 < baseStart_1175956 := by decide
  rcases family_descends (prefixWord ++ tailWord_1175956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1175961 : List Nat := [1, 2, 1, 2, 1, 4, 2, 1, 3, 5]
def baseStart_1175961 : Nat := 118140960795 + 1175961 * 2 ^ 59
def prefixEnd_1175961 : Nat := 4983230072969 + 3 ^ 40 * 1175961 * 2
def baseEnd_1175961 : Nat := 402555482627985853919573

theorem tailTrace_1175961 : CollatzResearch.WordTrace tailWord_1175961 prefixEnd_1175961 402555482627985853919573 := by
  unfold tailWord_1175961
  simp only [CollatzResearch.WordTrace]
  refine ⟨42890821292701609994367737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28593880861801073329578491 42890821292701609994367737)
  ·
    refine ⟨32168115969526207495775803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42890821292701609994367737 32168115969526207495775803)
    ·
      refine ⟨48252173954289311243663705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32168115969526207495775803 48252173954289311243663705)
      ·
        refine ⟨36189130465716983432747779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48252173954289311243663705 36189130465716983432747779)
        ·
          refine ⟨54283695698575475149121669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36189130465716983432747779 54283695698575475149121669)
          ·
            refine ⟨10178192943482901590460313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 54283695698575475149121669 10178192943482901590460313)
            ·
              refine ⟨7633644707612176192845235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10178192943482901590460313 7633644707612176192845235)
              ·
                refine ⟨11450467061418264289267853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7633644707612176192845235 11450467061418264289267853)
                ·
                  refine ⟨4293925148031849108475445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11450467061418264289267853 4293925148031849108475445)
                  ·
                    refine ⟨402555482627985853919573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4293925148031849108475445 402555482627985853919573)
                    ·
                      rfl

theorem cell22_1175961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 1, 3, 5].length) (baseStart_1175961 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1175961 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1175961 prefixEnd_1175961 := by exact prefixLift 1175961
  have htrace : WordTrace (prefixWord ++ tailWord_1175961) baseStart_1175961 baseEnd_1175961 := by
    simpa [prefixWord, tailWord_1175961, baseEnd_1175961] using wordTrace_append hprefix tailTrace_1175961
  have hstable : (prefixWord ++ tailWord_1175961).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1175961).length < 2 ^ (prefixWord ++ tailWord_1175961).sum := by decide
  have hdescent : baseEnd_1175961 < baseStart_1175961 := by decide
  rcases family_descends (prefixWord ++ tailWord_1175961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1175991 : List Nat := [1, 1, 3, 1, 3, 3, 1, 9]
def baseStart_1175991 : Nat := 118140960795 + 1175991 * 2 ^ 59
def prefixEnd_1175991 : Nat := 4983230072969 + 3 ^ 40 * 1175991 * 2
def baseEnd_1175991 : Nat := 44729528026786197296609

theorem tailTrace_1175991 : CollatzResearch.WordTrace tailWord_1175991 prefixEnd_1175991 44729528026786197296609 := by
  unfold tailWord_1175991
  simp only [CollatzResearch.WordTrace]
  refine ⟨42891915482592925117959827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28594610321728616745306551 42891915482592925117959827)
  ·
    refine ⟨64337873223889387676939741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42891915482592925117959827 64337873223889387676939741)
    ·
      refine ⟨24126702458958520378852403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64337873223889387676939741 24126702458958520378852403)
      ·
        refine ⟨36190053688437780568278605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24126702458958520378852403 36190053688437780568278605)
        ·
          refine ⟨13571270133164167713104477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36190053688437780568278605 13571270133164167713104477)
          ·
            refine ⟨5089226299936562892414179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13571270133164167713104477 5089226299936562892414179)
            ·
              refine ⟨7633839449904844338621269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5089226299936562892414179 7633839449904844338621269)
              ·
                refine ⟨44729528026786197296609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 7633839449904844338621269 44729528026786197296609)
                ·
                  rfl

theorem cell22_1175991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 9].length) (baseStart_1175991 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1175991 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1175991 prefixEnd_1175991 := by exact prefixLift 1175991
  have htrace : WordTrace (prefixWord ++ tailWord_1175991) baseStart_1175991 baseEnd_1175991 := by
    simpa [prefixWord, tailWord_1175991, baseEnd_1175991] using wordTrace_append hprefix tailTrace_1175991
  have hstable : (prefixWord ++ tailWord_1175991).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1175991).length < 2 ^ (prefixWord ++ tailWord_1175991).sum := by decide
  have hdescent : baseEnd_1175991 < baseStart_1175991 := by decide
  rcases family_descends (prefixWord ++ tailWord_1175991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1176128 : List Nat := [2, 1, 1, 2, 2, 2, 4, 1, 1, 6]
def baseStart_1176128 : Nat := 118140960795 + 1176128 * 2 ^ 59
def prefixEnd_1176128 : Nat := 4983230072969 + 3 ^ 40 * 1176128 * 2
def baseEnd_1176128 : Nat := 402612650140853084994061

theorem tailTrace_1176128 : CollatzResearch.WordTrace tailWord_1176128 prefixEnd_1176128 402612650140853084994061 := by
  unfold tailWord_1176128
  simp only [CollatzResearch.WordTrace]
  refine ⟨21448456141548298757848519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28597941522064398343798025 21448456141548298757848519)
  ·
    refine ⟨32172684212322448136772779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21448456141548298757848519 32172684212322448136772779)
    ·
      refine ⟨48259026318483672205159169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32172684212322448136772779 48259026318483672205159169)
      ·
        refine ⟨36194269738862754153869377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48259026318483672205159169 36194269738862754153869377)
        ·
          refine ⟨27145702304147065615402033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36194269738862754153869377 27145702304147065615402033)
          ·
            refine ⟨20359276728110299211551525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27145702304147065615402033 20359276728110299211551525)
            ·
              refine ⟨3817364386520681102165911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20359276728110299211551525 3817364386520681102165911)
              ·
                refine ⟨5726046579781021653248867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3817364386520681102165911 5726046579781021653248867)
                ·
                  refine ⟨8589069869671532479873301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5726046579781021653248867 8589069869671532479873301)
                  ·
                    refine ⟨402612650140853084994061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8589069869671532479873301 402612650140853084994061)
                    ·
                      rfl

theorem cell22_1176128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 4, 1, 1, 6].length) (baseStart_1176128 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1176128 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1176128 prefixEnd_1176128 := by exact prefixLift 1176128
  have htrace : WordTrace (prefixWord ++ tailWord_1176128) baseStart_1176128 baseEnd_1176128 := by
    simpa [prefixWord, tailWord_1176128, baseEnd_1176128] using wordTrace_append hprefix tailTrace_1176128
  have hstable : (prefixWord ++ tailWord_1176128).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1176128).length < 2 ^ (prefixWord ++ tailWord_1176128).sum := by decide
  have hdescent : baseEnd_1176128 < baseStart_1176128 := by decide
  rcases family_descends (prefixWord ++ tailWord_1176128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1176134 : List Nat := [6, 1, 1, 1, 2, 1, 2, 3, 1, 4]
def baseStart_1176134 : Nat := 118140960795 + 1176134 * 2 ^ 59
def prefixEnd_1176134 : Nat := 4983230072969 + 3 ^ 40 * 1176134 * 2
def baseEnd_1176134 : Nat := 402614704063471069344043

theorem tailTrace_1176134 : CollatzResearch.WordTrace tailWord_1176134 prefixEnd_1176134 402614704063471069344043 := by
  unfold tailWord_1176134
  simp only [CollatzResearch.WordTrace]
  refine ⟨1340535347533589391887983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 28598087414049907026943637 1340535347533589391887983)
  ·
    refine ⟨2010803021300384087831975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1340535347533589391887983 2010803021300384087831975)
    ·
      refine ⟨3016204531950576131747963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2010803021300384087831975 3016204531950576131747963)
      ·
        refine ⟨4524306797925864197621945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3016204531950576131747963 4524306797925864197621945)
        ·
          refine ⟨3393230098444398148216459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4524306797925864197621945 3393230098444398148216459)
          ·
            refine ⟨5089845147666597222324689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3393230098444398148216459 5089845147666597222324689)
            ·
              refine ⟨3817383860749947916743517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5089845147666597222324689 3817383860749947916743517)
              ·
                refine ⟨1431518947781230468778819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3817383860749947916743517 1431518947781230468778819)
                ·
                  refine ⟨2147278421671845703168229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1431518947781230468778819 2147278421671845703168229)
                  ·
                    refine ⟨402614704063471069344043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2147278421671845703168229 402614704063471069344043)
                    ·
                      rfl

theorem cell22_1176134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 2, 3, 1, 4].length) (baseStart_1176134 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1176134 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1176134 prefixEnd_1176134 := by exact prefixLift 1176134
  have htrace : WordTrace (prefixWord ++ tailWord_1176134) baseStart_1176134 baseEnd_1176134 := by
    simpa [prefixWord, tailWord_1176134, baseEnd_1176134] using wordTrace_append hprefix tailTrace_1176134
  have hstable : (prefixWord ++ tailWord_1176134).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1176134).length < 2 ^ (prefixWord ++ tailWord_1176134).sum := by decide
  have hdescent : baseEnd_1176134 < baseStart_1176134 := by decide
  rcases family_descends (prefixWord ++ tailWord_1176134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1176145 : List Nat := [1, 2, 2, 1, 3, 4, 1, 2, 2, 4]
def baseStart_1176145 : Nat := 118140960795 + 1176145 * 2 ^ 59
def prefixEnd_1176145 : Nat := 4983230072969 + 3 ^ 40 * 1176145 * 2
def baseEnd_1176145 : Nat := 402618469588270707319009

theorem tailTrace_1176145 : CollatzResearch.WordTrace tailWord_1176145 prefixEnd_1176145 402618469588270707319009 := by
  unfold tailWord_1176145
  simp only [CollatzResearch.WordTrace]
  refine ⟨42897532324035009419065889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28598354882690006279377259 42897532324035009419065889)
  ·
    refine ⟨32173149243026257064299417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42897532324035009419065889 32173149243026257064299417)
    ·
      refine ⟨24129861932269692798224563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32173149243026257064299417 24129861932269692798224563)
      ·
        refine ⟨36194792898404539197336845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24129861932269692798224563 36194792898404539197336845)
        ·
          refine ⟨13573047336901702199001317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36194792898404539197336845 13573047336901702199001317)
          ·
            refine ⟨2544946375669069162312747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13573047336901702199001317 2544946375669069162312747)
            ·
              refine ⟨3817419563503603743469121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2544946375669069162312747 3817419563503603743469121)
              ·
                refine ⟨2863064672627702807601841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3817419563503603743469121 2863064672627702807601841)
                ·
                  refine ⟨2147298504470777105701381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2863064672627702807601841 2147298504470777105701381)
                  ·
                    refine ⟨402618469588270707319009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2147298504470777105701381 402618469588270707319009)
                    ·
                      rfl

theorem cell22_1176145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 1, 2, 2, 4].length) (baseStart_1176145 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1176145 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1176145 prefixEnd_1176145 := by exact prefixLift 1176145
  have htrace : WordTrace (prefixWord ++ tailWord_1176145) baseStart_1176145 baseEnd_1176145 := by
    simpa [prefixWord, tailWord_1176145, baseEnd_1176145] using wordTrace_append hprefix tailTrace_1176145
  have hstable : (prefixWord ++ tailWord_1176145).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1176145).length < 2 ^ (prefixWord ++ tailWord_1176145).sum := by decide
  have hdescent : baseEnd_1176145 < baseStart_1176145 := by decide
  rcases family_descends (prefixWord ++ tailWord_1176145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1176175 : List Nat := [1, 1, 2, 1, 3, 2, 2, 4, 3, 3]
def baseStart_1176175 : Nat := 118140960795 + 1176175 * 2 ^ 59
def prefixEnd_1176175 : Nat := 4983230072969 + 3 ^ 40 * 1176175 * 2
def baseEnd_1176175 : Nat := 402628739201360629068917

theorem tailTrace_1176175 : CollatzResearch.WordTrace tailWord_1176175 prefixEnd_1176175 402628739201360629068917 := by
  unfold tailWord_1176175
  simp only [CollatzResearch.WordTrace]
  refine ⟨42898626513926324542657979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28599084342617549695105319 42898626513926324542657979)
  ·
    refine ⟨64347939770889486813986969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42898626513926324542657979 64347939770889486813986969)
    ·
      refine ⟨48260954828167115110490227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64347939770889486813986969 48260954828167115110490227)
      ·
        refine ⟨72391432242250672665735341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48260954828167115110490227 72391432242250672665735341)
        ·
          refine ⟨27146787090844002249650753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 72391432242250672665735341 27146787090844002249650753)
          ·
            refine ⟨20360090318133001687238065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27146787090844002249650753 20360090318133001687238065)
            ·
              refine ⟨15270067738599751265428549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20360090318133001687238065 15270067738599751265428549)
              ·
                refine ⟨2863137700987453362267853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15270067738599751265428549 2863137700987453362267853)
                ·
                  refine ⟨1073676637870295010850445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2863137700987453362267853 1073676637870295010850445)
                  ·
                    refine ⟨402628739201360629068917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1073676637870295010850445 402628739201360629068917)
                    ·
                      rfl

theorem cell22_1176175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 4, 3, 3].length) (baseStart_1176175 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1176175 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1176175 prefixEnd_1176175 := by exact prefixLift 1176175
  have htrace : WordTrace (prefixWord ++ tailWord_1176175) baseStart_1176175 baseEnd_1176175 := by
    simpa [prefixWord, tailWord_1176175, baseEnd_1176175] using wordTrace_append hprefix tailTrace_1176175
  have hstable : (prefixWord ++ tailWord_1176175).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1176175).length < 2 ^ (prefixWord ++ tailWord_1176175).sum := by decide
  have hdescent : baseEnd_1176175 < baseStart_1176175 := by decide
  rcases family_descends (prefixWord ++ tailWord_1176175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1176188 : List Nat := [2, 2, 2, 1, 1, 2, 2, 1, 9]
def baseStart_1176188 : Nat := 118140960795 + 1176188 * 2 ^ 59
def prefixEnd_1176188 : Nat := 4983230072969 + 3 ^ 40 * 1176188 * 2
def baseEnd_1176188 : Nat := 134211063122344309497959

theorem tailTrace_1176188 : CollatzResearch.WordTrace tailWord_1176188 prefixEnd_1176188 134211063122344309497959 := by
  unfold tailWord_1176188
  simp only [CollatzResearch.WordTrace]
  refine ⟨21449550331439613881440609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28599400441919485175254145 21449550331439613881440609)
  ·
    refine ⟨16087162748579710411080457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21449550331439613881440609 16087162748579710411080457)
    ·
      refine ⟨12065372061434782808310343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16087162748579710411080457 12065372061434782808310343)
      ·
        refine ⟨18098058092152174212465515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12065372061434782808310343 18098058092152174212465515)
        ·
          refine ⟨27147087138228261318698273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18098058092152174212465515 27147087138228261318698273)
          ·
            refine ⟨20360315353671195989023705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27147087138228261318698273 20360315353671195989023705)
            ·
              refine ⟨15270236515253396991767779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20360315353671195989023705 15270236515253396991767779)
              ·
                refine ⟨22905354772880095487651669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15270236515253396991767779 22905354772880095487651669)
                ·
                  refine ⟨134211063122344309497959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 22905354772880095487651669 134211063122344309497959)
                  ·
                    rfl

theorem cell22_1176188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 1, 9].length) (baseStart_1176188 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1176188 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1176188 prefixEnd_1176188 := by exact prefixLift 1176188
  have htrace : WordTrace (prefixWord ++ tailWord_1176188) baseStart_1176188 baseEnd_1176188 := by
    simpa [prefixWord, tailWord_1176188, baseEnd_1176188] using wordTrace_append hprefix tailTrace_1176188
  have hstable : (prefixWord ++ tailWord_1176188).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1176188).length < 2 ^ (prefixWord ++ tailWord_1176188).sum := by decide
  have hdescent : baseEnd_1176188 < baseStart_1176188 := by decide
  rcases family_descends (prefixWord ++ tailWord_1176188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1176194 : List Nat := [3, 4, 3, 1, 1, 10]
def baseStart_1176194 : Nat := 118140960795 + 1176194 * 2 ^ 59
def prefixEnd_1176194 : Nat := 4983230072969 + 3 ^ 40 * 1176194 * 2
def baseEnd_1176194 : Nat := 4970805472711739664739

theorem tailTrace_1176194 : CollatzResearch.WordTrace tailWord_1176194 prefixEnd_1176194 4970805472711739664739 := by
  unfold tailWord_1176194
  simp only [CollatzResearch.WordTrace]
  refine ⟨10724829875214372696899909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28599546333904993858399757 10724829875214372696899909)
  ·
    refine ⟨2010905601602694880668733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10724829875214372696899909 2010905601602694880668733)
    ·
      refine ⟨754089600601010580250775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2010905601602694880668733 754089600601010580250775)
      ·
        refine ⟨1131134400901515870376163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 754089600601010580250775 1131134400901515870376163)
        ·
          refine ⟨1696701601352273805564245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1131134400901515870376163 1696701601352273805564245)
          ·
            refine ⟨4970805472711739664739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 1696701601352273805564245 4970805472711739664739)
            ·
              rfl

theorem cell22_1176194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 10].length) (baseStart_1176194 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1176194 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1176194 prefixEnd_1176194 := by exact prefixLift 1176194
  have htrace : WordTrace (prefixWord ++ tailWord_1176194) baseStart_1176194 baseEnd_1176194 := by
    simpa [prefixWord, tailWord_1176194, baseEnd_1176194] using wordTrace_append hprefix tailTrace_1176194
  have hstable : (prefixWord ++ tailWord_1176194).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1176194).length < 2 ^ (prefixWord ++ tailWord_1176194).sum := by decide
  have hdescent : baseEnd_1176194 < baseStart_1176194 := by decide
  rcases family_descends (prefixWord ++ tailWord_1176194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1176220 : List Nat := [2, 2, 3, 2, 2, 1, 1, 1, 1, 7]
def baseStart_1176220 : Nat := 118140960795 + 1176220 * 2 ^ 59
def prefixEnd_1176220 : Nat := 4983230072969 + 3 ^ 40 * 1176220 * 2
def baseEnd_1176220 : Nat := 402644143620995511693779

theorem tailTrace_1176220 : CollatzResearch.WordTrace tailWord_1176220 prefixEnd_1176220 402644143620995511693779 := by
  unfold tailWord_1176220
  simp only [CollatzResearch.WordTrace]
  refine ⟨21450133899381648614023057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28600178532508864818697409 21450133899381648614023057)
  ·
    refine ⟨16087600424536236460517293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21450133899381648614023057 16087600424536236460517293)
    ·
      refine ⟨6032850159201088672693985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16087600424536236460517293 6032850159201088672693985)
      ·
        refine ⟨4524637619400816504520489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6032850159201088672693985 4524637619400816504520489)
        ·
          refine ⟨3393478214550612378390367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4524637619400816504520489 3393478214550612378390367)
          ·
            refine ⟨5090217321825918567585551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3393478214550612378390367 5090217321825918567585551)
            ·
              refine ⟨7635325982738877851378327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5090217321825918567585551 7635325982738877851378327)
              ·
                refine ⟨11452988974108316777067491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7635325982738877851378327 11452988974108316777067491)
                ·
                  refine ⟨17179483461162475165601237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11452988974108316777067491 17179483461162475165601237)
                  ·
                    refine ⟨402644143620995511693779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 17179483461162475165601237 402644143620995511693779)
                    ·
                      rfl

theorem cell22_1176220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 1, 1, 7].length) (baseStart_1176220 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1176220 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1176220 prefixEnd_1176220 := by exact prefixLift 1176220
  have htrace : WordTrace (prefixWord ++ tailWord_1176220) baseStart_1176220 baseEnd_1176220 := by
    simpa [prefixWord, tailWord_1176220, baseEnd_1176220] using wordTrace_append hprefix tailTrace_1176220
  have hstable : (prefixWord ++ tailWord_1176220).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1176220).length < 2 ^ (prefixWord ++ tailWord_1176220).sum := by decide
  have hdescent : baseEnd_1176220 < baseStart_1176220 := by decide
  rcases family_descends (prefixWord ++ tailWord_1176220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1176222 : List Nat := [4, 3, 1, 1, 1, 1, 1, 5, 5]
def baseStart_1176222 : Nat := 118140960795 + 1176222 * 2 ^ 59
def prefixEnd_1176222 : Nat := 4983230072969 + 3 ^ 40 * 1176222 * 2
def baseEnd_1176222 : Nat := 134214942753956057714591

theorem tailTrace_1176222 : CollatzResearch.WordTrace tailWord_1176222 prefixEnd_1176222 134214942753956057714591 := by
  unfold tailWord_1176222
  simp only [CollatzResearch.WordTrace]
  refine ⟨5362542593094506446202365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28600227163170701046412613 5362542593094506446202365)
  ·
    refine ⟨2010953472410439917325887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5362542593094506446202365 2010953472410439917325887)
    ·
      refine ⟨3016430208615659875988831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2010953472410439917325887 3016430208615659875988831)
      ·
        refine ⟨4524645312923489813983247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3016430208615659875988831 4524645312923489813983247)
        ·
          refine ⟨6786967969385234720974871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4524645312923489813983247 6786967969385234720974871)
          ·
            refine ⟨10180451954077852081462307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6786967969385234720974871 10180451954077852081462307)
            ·
              refine ⟨15270677931116778122193461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10180451954077852081462307 15270677931116778122193461)
              ·
                refine ⟨1431626056042197948955637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15270677931116778122193461 1431626056042197948955637)
                ·
                  refine ⟨134214942753956057714591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1431626056042197948955637 134214942753956057714591)
                  ·
                    rfl

theorem cell22_1176222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 5, 5].length) (baseStart_1176222 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1176222 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1176222 prefixEnd_1176222 := by exact prefixLift 1176222
  have htrace : WordTrace (prefixWord ++ tailWord_1176222) baseStart_1176222 baseEnd_1176222 := by
    simpa [prefixWord, tailWord_1176222, baseEnd_1176222] using wordTrace_append hprefix tailTrace_1176222
  have hstable : (prefixWord ++ tailWord_1176222).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1176222).length < 2 ^ (prefixWord ++ tailWord_1176222).sum := by decide
  have hdescent : baseEnd_1176222 < baseStart_1176222 := by decide
  rcases family_descends (prefixWord ++ tailWord_1176222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1176233 : List Nat := [1, 2, 1, 1, 1, 1, 2, 5, 8]
def baseStart_1176233 : Nat := 118140960795 + 1176233 * 2 ^ 59
def prefixEnd_1176233 : Nat := 4983230072969 + 3 ^ 40 * 1176233 * 2
def baseEnd_1176233 : Nat := 134216197928889270372913

theorem tailTrace_1176233 : CollatzResearch.WordTrace tailWord_1176233 prefixEnd_1176233 134216197928889270372913 := by
  unfold tailWord_1176233
  simp only [CollatzResearch.WordTrace]
  refine ⟨42900741947716200448269353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28600494631810800298846235 42900741947716200448269353)
  ·
    refine ⟨32175556460787150336202015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42900741947716200448269353 32175556460787150336202015)
    ·
      refine ⟨48263334691180725504303023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32175556460787150336202015 48263334691180725504303023)
      ·
        refine ⟨72395002036771088256454535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48263334691180725504303023 72395002036771088256454535)
        ·
          refine ⟨108592503055156632384681803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72395002036771088256454535 108592503055156632384681803)
          ·
            refine ⟨162888754582734948577022705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108592503055156632384681803 162888754582734948577022705)
            ·
              refine ⟨122166565937051211432767029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 162888754582734948577022705 122166565937051211432767029)
              ·
                refine ⟨11453115556598551071821909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 122166565937051211432767029 11453115556598551071821909)
                ·
                  refine ⟨134216197928889270372913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 11453115556598551071821909 134216197928889270372913)
                  ·
                    rfl

theorem cell22_1176233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 5, 8].length) (baseStart_1176233 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1176233 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1176233 prefixEnd_1176233 := by exact prefixLift 1176233
  have htrace : WordTrace (prefixWord ++ tailWord_1176233) baseStart_1176233 baseEnd_1176233 := by
    simpa [prefixWord, tailWord_1176233, baseEnd_1176233] using wordTrace_append hprefix tailTrace_1176233
  have hstable : (prefixWord ++ tailWord_1176233).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1176233).length < 2 ^ (prefixWord ++ tailWord_1176233).sum := by decide
  have hdescent : baseEnd_1176233 < baseStart_1176233 := by decide
  rcases family_descends (prefixWord ++ tailWord_1176233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1176252 : List Nat := [2, 2, 2, 3, 1, 1, 3, 3, 1, 4]
def baseStart_1176252 : Nat := 118140960795 + 1176252 * 2 ^ 59
def prefixEnd_1176252 : Nat := 4983230072969 + 3 ^ 40 * 1176252 * 2
def baseEnd_1176252 : Nat := 402655097874958094893681

theorem tailTrace_1176252 : CollatzResearch.WordTrace tailWord_1176252 prefixEnd_1176252 402655097874958094893681 := by
  unfold tailWord_1176252
  simp only [CollatzResearch.WordTrace]
  refine ⟨21450717467323683346605505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28600956623098244462140673 21450717467323683346605505)
  ·
    refine ⟨16088038100492762509954129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21450717467323683346605505 16088038100492762509954129)
    ·
      refine ⟨12066028575369571882465597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16088038100492762509954129 12066028575369571882465597)
      ·
        refine ⟨4524760715763589455924599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12066028575369571882465597 4524760715763589455924599)
        ·
          refine ⟨6787141073645384183886899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4524760715763589455924599 6787141073645384183886899)
          ·
            refine ⟨10180711610468076275830349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6787141073645384183886899 10180711610468076275830349)
            ·
              refine ⟨3817766853925528603436381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10180711610468076275830349 3817766853925528603436381)
              ·
                refine ⟨1431662570222073226288643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3817766853925528603436381 1431662570222073226288643)
                ·
                  refine ⟨2147493855333109839432965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1431662570222073226288643 2147493855333109839432965)
                  ·
                    refine ⟨402655097874958094893681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2147493855333109839432965 402655097874958094893681)
                    ·
                      rfl

theorem cell22_1176252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 3, 3, 1, 4].length) (baseStart_1176252 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1176252 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1176252 prefixEnd_1176252 := by exact prefixLift 1176252
  have htrace : WordTrace (prefixWord ++ tailWord_1176252) baseStart_1176252 baseEnd_1176252 := by
    simpa [prefixWord, tailWord_1176252, baseEnd_1176252] using wordTrace_append hprefix tailTrace_1176252
  have hstable : (prefixWord ++ tailWord_1176252).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1176252).length < 2 ^ (prefixWord ++ tailWord_1176252).sum := by decide
  have hdescent : baseEnd_1176252 < baseStart_1176252 := by decide
  rcases family_descends (prefixWord ++ tailWord_1176252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1176280 : List Nat := [2, 1, 2, 2, 3, 2, 1, 2, 1, 6]
def baseStart_1176280 : Nat := 118140960795 + 1176280 * 2 ^ 59
def prefixEnd_1176280 : Nat := 4983230072969 + 3 ^ 40 * 1176280 * 2
def baseEnd_1176280 : Nat := 402664682847175355193595

theorem tailTrace_1176280 : CollatzResearch.WordTrace tailWord_1176280 prefixEnd_1176280 402664682847175355193595 := by
  unfold tailWord_1176280
  simp only [CollatzResearch.WordTrace]
  refine ⟨21451228089272963737615147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28601637452363951650153529 21451228089272963737615147)
  ·
    refine ⟨32176842133909445606422721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21451228089272963737615147 32176842133909445606422721)
    ·
      refine ⟨24132631600432084204817041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32176842133909445606422721 24132631600432084204817041)
      ·
        refine ⟨18099473700324063153612781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24132631600432084204817041 18099473700324063153612781)
        ·
          refine ⟨6787302637621523682604793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18099473700324063153612781 6787302637621523682604793)
          ·
            refine ⟨5090476978216142761953595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6787302637621523682604793 5090476978216142761953595)
            ·
              refine ⟨7635715467324214142930393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5090476978216142761953595 7635715467324214142930393)
              ·
                refine ⟨5726786600493160607197795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7635715467324214142930393 5726786600493160607197795)
                ·
                  refine ⟨8590179900739740910796693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5726786600493160607197795 8590179900739740910796693)
                  ·
                    refine ⟨402664682847175355193595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8590179900739740910796693 402664682847175355193595)
                    ·
                      rfl

theorem cell22_1176280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 2, 1, 6].length) (baseStart_1176280 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1176280 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1176280 prefixEnd_1176280 := by exact prefixLift 1176280
  have htrace : WordTrace (prefixWord ++ tailWord_1176280) baseStart_1176280 baseEnd_1176280 := by
    simpa [prefixWord, tailWord_1176280, baseEnd_1176280] using wordTrace_append hprefix tailTrace_1176280
  have hstable : (prefixWord ++ tailWord_1176280).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1176280).length < 2 ^ (prefixWord ++ tailWord_1176280).sum := by decide
  have hdescent : baseEnd_1176280 < baseStart_1176280 := by decide
  rcases family_descends (prefixWord ++ tailWord_1176280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1176355 : List Nat := [1, 1, 1, 4, 2, 1, 1, 2, 4, 5]
def baseStart_1176355 : Nat := 118140960795 + 1176355 * 2 ^ 59
def prefixEnd_1176355 : Nat := 4983230072969 + 3 ^ 40 * 1176355 * 2
def baseEnd_1176355 : Nat := 402690356879900159568365

theorem tailTrace_1176355 : CollatzResearch.WordTrace tailWord_1176355 prefixEnd_1176355 402690356879900159568365 := by
  unfold tailWord_1176355
  simp only [CollatzResearch.WordTrace]
  refine ⟨42905191653274215284210519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28603461102182810189473679 42905191653274215284210519)
  ·
    refine ⟨64357787479911322926315779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42905191653274215284210519 64357787479911322926315779)
    ·
      refine ⟨96536681219866984389473669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64357787479911322926315779 96536681219866984389473669)
      ·
        refine ⟨18100627728725059573026313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 96536681219866984389473669 18100627728725059573026313)
        ·
          refine ⟨13575470796543794679769735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18100627728725059573026313 13575470796543794679769735)
          ·
            refine ⟨20363206194815692019654603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13575470796543794679769735 20363206194815692019654603)
            ·
              refine ⟨30544809292223538029481905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20363206194815692019654603 30544809292223538029481905)
              ·
                refine ⟨22908606969167653522111429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30544809292223538029481905 22908606969167653522111429)
                ·
                  refine ⟨4295363806718935035395893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22908606969167653522111429 4295363806718935035395893)
                  ·
                    refine ⟨402690356879900159568365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4295363806718935035395893 402690356879900159568365)
                    ·
                      rfl

theorem cell22_1176355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 2, 4, 5].length) (baseStart_1176355 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1176355 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1176355 prefixEnd_1176355 := by exact prefixLift 1176355
  have htrace : WordTrace (prefixWord ++ tailWord_1176355) baseStart_1176355 baseEnd_1176355 := by
    simpa [prefixWord, tailWord_1176355, baseEnd_1176355] using wordTrace_append hprefix tailTrace_1176355
  have hstable : (prefixWord ++ tailWord_1176355).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1176355).length < 2 ^ (prefixWord ++ tailWord_1176355).sum := by decide
  have hdescent : baseEnd_1176355 < baseStart_1176355 := by decide
  rcases family_descends (prefixWord ++ tailWord_1176355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1176402 : List Nat := [3, 2, 2, 1, 1, 2, 3, 2, 6]
def baseStart_1176402 : Nat := 118140960795 + 1176402 * 2 ^ 59
def prefixEnd_1176402 : Nat := 4983230072969 + 3 ^ 40 * 1176402 * 2
def baseEnd_1176402 : Nat := 134235481980135901214407

theorem tailTrace_1176402 : CollatzResearch.WordTrace tailWord_1176402 prefixEnd_1176402 134235481980135901214407 := by
  unfold tailWord_1176402
  simp only [CollatzResearch.WordTrace]
  refine ⟨10726726471025985577792865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28604603922735961540780973 10726726471025985577792865)
  ·
    refine ⟨8045044853269489183344649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10726726471025985577792865 8045044853269489183344649)
    ·
      refine ⟨6033783639952116887508487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8045044853269489183344649 6033783639952116887508487)
      ·
        refine ⟨9050675459928175331262731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6033783639952116887508487 9050675459928175331262731)
        ·
          refine ⟨13576013189892262996894097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9050675459928175331262731 13576013189892262996894097)
          ·
            refine ⟨10182009892419197247670573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13576013189892262996894097 10182009892419197247670573)
            ·
              refine ⟨3818253709657198967876465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10182009892419197247670573 3818253709657198967876465)
              ·
                refine ⟨2863690282242899225907349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3818253709657198967876465 2863690282242899225907349)
                ·
                  refine ⟨134235481980135901214407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2863690282242899225907349 134235481980135901214407)
                  ·
                    rfl

theorem cell22_1176402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 3, 2, 6].length) (baseStart_1176402 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1176402 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1176402 prefixEnd_1176402 := by exact prefixLift 1176402
  have htrace : WordTrace (prefixWord ++ tailWord_1176402) baseStart_1176402 baseEnd_1176402 := by
    simpa [prefixWord, tailWord_1176402, baseEnd_1176402] using wordTrace_append hprefix tailTrace_1176402
  have hstable : (prefixWord ++ tailWord_1176402).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1176402).length < 2 ^ (prefixWord ++ tailWord_1176402).sum := by decide
  have hdescent : baseEnd_1176402 < baseStart_1176402 := by decide
  rcases family_descends (prefixWord ++ tailWord_1176402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1176419 : List Nat := [1, 1, 1, 5, 3, 1, 1, 5, 4]
def baseStart_1176419 : Nat := 118140960795 + 1176419 * 2 ^ 59
def prefixEnd_1176419 : Nat := 4983230072969 + 3 ^ 40 * 1176419 * 2
def baseEnd_1176419 : Nat := 134237421795941775322723

theorem tailTrace_1176419 : CollatzResearch.WordTrace tailWord_1176419 prefixEnd_1176419 134237421795941775322723 := by
  unfold tailWord_1176419
  simp only [CollatzResearch.WordTrace]
  refine ⟨42907525925042354214540311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28605017283361569476360207 42907525925042354214540311)
  ·
    refine ⟨64361288887563531321810467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42907525925042354214540311 64361288887563531321810467)
    ·
      refine ⟨96541933331345296982715701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64361288887563531321810467 96541933331345296982715701)
      ·
        refine ⟨9050806249813621592129597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 96541933331345296982715701 9050806249813621592129597)
        ·
          refine ⟨3394052343680108097048599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9050806249813621592129597 3394052343680108097048599)
          ·
            refine ⟨5091078515520162145572899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3394052343680108097048599 5091078515520162145572899)
            ·
              refine ⟨7636617773280243218359349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5091078515520162145572899 7636617773280243218359349)
              ·
                refine ⟨715932916245022801721189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7636617773280243218359349 715932916245022801721189)
                ·
                  refine ⟨134237421795941775322723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 715932916245022801721189 134237421795941775322723)
                  ·
                    rfl

theorem cell22_1176419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 5, 4].length) (baseStart_1176419 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1176419 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1176419 prefixEnd_1176419 := by exact prefixLift 1176419
  have htrace : WordTrace (prefixWord ++ tailWord_1176419) baseStart_1176419 baseEnd_1176419 := by
    simpa [prefixWord, tailWord_1176419, baseEnd_1176419] using wordTrace_append hprefix tailTrace_1176419
  have hstable : (prefixWord ++ tailWord_1176419).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1176419).length < 2 ^ (prefixWord ++ tailWord_1176419).sum := by decide
  have hdescent : baseEnd_1176419 < baseStart_1176419 := by decide
  rcases family_descends (prefixWord ++ tailWord_1176419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1176432 : List Nat := [2, 1, 1, 1, 4, 1, 2, 4, 2, 4]
def baseStart_1176432 : Nat := 118140960795 + 1176432 * 2 ^ 59
def prefixEnd_1176432 : Nat := 4983230072969 + 3 ^ 40 * 1176432 * 2
def baseEnd_1176432 : Nat := 402716715553497625393129

theorem tailTrace_1176432 : CollatzResearch.WordTrace tailWord_1176432 prefixEnd_1176432 402716715553497625393129 := by
  unfold tailWord_1176432
  simp only [CollatzResearch.WordTrace]
  refine ⟨21454000036997628717381775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28605333382663504956509033 21454000036997628717381775)
  ·
    refine ⟨32181000055496443076072663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21454000036997628717381775 32181000055496443076072663)
    ·
      refine ⟨48271500083244664614108995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32181000055496443076072663 48271500083244664614108995)
      ·
        refine ⟨72407250124866996921163493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48271500083244664614108995 72407250124866996921163493)
        ·
          refine ⟨13576359398412561922718155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 72407250124866996921163493 13576359398412561922718155)
          ·
            refine ⟨20364539097618842884077233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13576359398412561922718155 20364539097618842884077233)
            ·
              refine ⟨15273404323214132163057925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20364539097618842884077233 15273404323214132163057925)
              ·
                refine ⟨2863763310602649780573361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15273404323214132163057925 2863763310602649780573361)
                ·
                  refine ⟨2147822482951987335430021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2863763310602649780573361 2147822482951987335430021)
                  ·
                    refine ⟨402716715553497625393129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2147822482951987335430021 402716715553497625393129)
                    ·
                      rfl

theorem cell22_1176432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 4, 2, 4].length) (baseStart_1176432 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1176432 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1176432 prefixEnd_1176432 := by exact prefixLift 1176432
  have htrace : WordTrace (prefixWord ++ tailWord_1176432) baseStart_1176432 baseEnd_1176432 := by
    simpa [prefixWord, tailWord_1176432, baseEnd_1176432] using wordTrace_append hprefix tailTrace_1176432
  have hstable : (prefixWord ++ tailWord_1176432).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1176432).length < 2 ^ (prefixWord ++ tailWord_1176432).sum := by decide
  have hdescent : baseEnd_1176432 < baseStart_1176432 := by decide
  rcases family_descends (prefixWord ++ tailWord_1176432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1176451 : List Nat := [1, 1, 1, 3, 4, 1, 5, 1, 2, 3]
def baseStart_1176451 : Nat := 118140960795 + 1176451 * 2 ^ 59
def prefixEnd_1176451 : Nat := 4983230072969 + 3 ^ 40 * 1176451 * 2
def baseEnd_1176451 : Nat := 402723219641787909168071

theorem tailTrace_1176451 : CollatzResearch.WordTrace tailWord_1176451 prefixEnd_1176451 402723219641787909168071 := by
  unfold tailWord_1176451
  simp only [CollatzResearch.WordTrace]
  refine ⟨42908693060926423679705207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28605795373950949119803471 42908693060926423679705207)
  ·
    refine ⟨64363039591389635519557811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42908693060926423679705207 64363039591389635519557811)
    ·
      refine ⟨96544559387084453279336717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64363039591389635519557811 96544559387084453279336717)
      ·
        refine ⟨36204209770156669979751269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 96544559387084453279336717 36204209770156669979751269)
        ·
          refine ⟨6788289331904375621203363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 36204209770156669979751269 6788289331904375621203363)
          ·
            refine ⟨10182433997856563431805045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6788289331904375621203363 10182433997856563431805045)
            ·
              refine ⟨954603187299052821731723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10182433997856563431805045 954603187299052821731723)
              ·
                refine ⟨1431904780948579232597585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 954603187299052821731723 1431904780948579232597585)
                ·
                  refine ⟨1073928585711434424448189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1431904780948579232597585 1073928585711434424448189)
                  ·
                    refine ⟨402723219641787909168071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1073928585711434424448189 402723219641787909168071)
                    ·
                      rfl

theorem cell22_1176451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 5, 1, 2, 3].length) (baseStart_1176451 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1176451 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1176451 prefixEnd_1176451 := by exact prefixLift 1176451
  have htrace : WordTrace (prefixWord ++ tailWord_1176451) baseStart_1176451 baseEnd_1176451 := by
    simpa [prefixWord, tailWord_1176451, baseEnd_1176451] using wordTrace_append hprefix tailTrace_1176451
  have hstable : (prefixWord ++ tailWord_1176451).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1176451).length < 2 ^ (prefixWord ++ tailWord_1176451).sum := by decide
  have hdescent : baseEnd_1176451 < baseStart_1176451 := by decide
  rcases family_descends (prefixWord ++ tailWord_1176451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1176470 : List Nat := [5, 3, 1, 1, 1, 1, 3, 3, 4]
def baseStart_1176470 : Nat := 118140960795 + 1176470 * 2 ^ 59
def prefixEnd_1176470 : Nat := 4983230072969 + 3 ^ 40 * 1176470 * 2
def baseEnd_1176470 : Nat := 134243241243359397647671

theorem tailTrace_1176470 : CollatzResearch.WordTrace tailWord_1176470 prefixEnd_1176470 134243241243359397647671 := by
  unfold tailWord_1176470
  simp only [CollatzResearch.WordTrace]
  refine ⟨2681836627991099370290429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 28606257365238393283097909 2681836627991099370290429)
  ·
    refine ⟨1005688735496662263858911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2681836627991099370290429 1005688735496662263858911)
    ·
      refine ⟨1508533103244993395788367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1005688735496662263858911 1508533103244993395788367)
      ·
        refine ⟨2262799654867490093682551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1508533103244993395788367 2262799654867490093682551)
        ·
          refine ⟨3394199482301235140523827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2262799654867490093682551 3394199482301235140523827)
          ·
            refine ⟨5091299223451852710785741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3394199482301235140523827 5091299223451852710785741)
            ·
              refine ⟨1909237208794444766544653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5091299223451852710785741 1909237208794444766544653)
              ·
                refine ⟨715963953297916787454245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1909237208794444766544653 715963953297916787454245)
                ·
                  refine ⟨134243241243359397647671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 715963953297916787454245 134243241243359397647671)
                  ·
                    rfl

theorem cell22_1176470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 3, 3, 4].length) (baseStart_1176470 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1176470 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1176470 prefixEnd_1176470 := by exact prefixLift 1176470
  have htrace : WordTrace (prefixWord ++ tailWord_1176470) baseStart_1176470 baseEnd_1176470 := by
    simpa [prefixWord, tailWord_1176470, baseEnd_1176470] using wordTrace_append hprefix tailTrace_1176470
  have hstable : (prefixWord ++ tailWord_1176470).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1176470).length < 2 ^ (prefixWord ++ tailWord_1176470).sum := by decide
  have hdescent : baseEnd_1176470 < baseStart_1176470 := by decide
  rcases family_descends (prefixWord ++ tailWord_1176470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1176502 : List Nat := [5, 1, 4, 1, 1, 1, 1, 3, 2, 3]
def baseStart_1176502 : Nat := 118140960795 + 1176502 * 2 ^ 59
def prefixEnd_1176502 : Nat := 4983230072969 + 3 ^ 40 * 1176502 * 2
def baseEnd_1176502 : Nat := 402740677984040776142915

theorem tailTrace_1176502 : CollatzResearch.WordTrace tailWord_1176502 prefixEnd_1176502 402740677984040776142915 := by
  unfold tailWord_1176502
  simp only [CollatzResearch.WordTrace]
  refine ⟨2681909573983853711863235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 28607035455827772926541173 2681909573983853711863235)
  ·
    refine ⟨4022864360975780567794853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2681909573983853711863235 4022864360975780567794853)
    ·
      refine ⟨754287067682958856461535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4022864360975780567794853 754287067682958856461535)
      ·
        refine ⟨1131430601524438284692303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 754287067682958856461535 1131430601524438284692303)
        ·
          refine ⟨1697145902286657427038455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1131430601524438284692303 1697145902286657427038455)
          ·
            refine ⟨2545718853429986140557683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1697145902286657427038455 2545718853429986140557683)
            ·
              refine ⟨3818578280144979210836525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2545718853429986140557683 3818578280144979210836525)
              ·
                refine ⟨1431966855054367204063697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3818578280144979210836525 1431966855054367204063697)
                ·
                  refine ⟨1073975141290775403047773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1431966855054367204063697 1073975141290775403047773)
                  ·
                    refine ⟨402740677984040776142915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1073975141290775403047773 402740677984040776142915)
                    ·
                      rfl

theorem cell22_1176502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 1, 3, 2, 3].length) (baseStart_1176502 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1176502 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1176502 prefixEnd_1176502 := by exact prefixLift 1176502
  have htrace : WordTrace (prefixWord ++ tailWord_1176502) baseStart_1176502 baseEnd_1176502 := by
    simpa [prefixWord, tailWord_1176502, baseEnd_1176502] using wordTrace_append hprefix tailTrace_1176502
  have hstable : (prefixWord ++ tailWord_1176502).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1176502).length < 2 ^ (prefixWord ++ tailWord_1176502).sum := by decide
  have hdescent : baseEnd_1176502 < baseStart_1176502 := by decide
  rcases family_descends (prefixWord ++ tailWord_1176502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1176569 : List Nat := [1, 2, 1, 3, 1, 3, 4, 1, 1, 5]
def baseStart_1176569 : Nat := 118140960795 + 1176569 * 2 ^ 59
def prefixEnd_1176569 : Nat := 4983230072969 + 3 ^ 40 * 1176569 * 2
def baseEnd_1176569 : Nat := 402763613453274934717709

theorem tailTrace_1176569 : CollatzResearch.WordTrace tailWord_1176569 prefixEnd_1176569 402763613453274934717709 := by
  unfold tailWord_1176569
  simp only [CollatzResearch.WordTrace]
  refine ⟨42912996874498929832500761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28608664582999286555000507 42912996874498929832500761)
  ·
    refine ⟨32184747655874197374375571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42912996874498929832500761 32184747655874197374375571)
    ·
      refine ⟨48277121483811296061563357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32184747655874197374375571 48277121483811296061563357)
      ·
        refine ⟨18103920556429236023086259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48277121483811296061563357 18103920556429236023086259)
        ·
          refine ⟨27155880834643854034629389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18103920556429236023086259 27155880834643854034629389)
          ·
            refine ⟨10183455312991445262986021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27155880834643854034629389 10183455312991445262986021)
            ·
              refine ⟨1909397871185895986809879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10183455312991445262986021 1909397871185895986809879)
              ·
                refine ⟨2864096806778843980214819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1909397871185895986809879 2864096806778843980214819)
                ·
                  refine ⟨4296145210168265970322229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2864096806778843980214819 4296145210168265970322229)
                  ·
                    refine ⟨402763613453274934717709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4296145210168265970322229 402763613453274934717709)
                    ·
                      rfl

theorem cell22_1176569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 4, 1, 1, 5].length) (baseStart_1176569 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1176569 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1176569 prefixEnd_1176569 := by exact prefixLift 1176569
  have htrace : WordTrace (prefixWord ++ tailWord_1176569) baseStart_1176569 baseEnd_1176569 := by
    simpa [prefixWord, tailWord_1176569, baseEnd_1176569] using wordTrace_append hprefix tailTrace_1176569
  have hstable : (prefixWord ++ tailWord_1176569).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1176569).length < 2 ^ (prefixWord ++ tailWord_1176569).sum := by decide
  have hdescent : baseEnd_1176569 < baseStart_1176569 := by decide
  rcases family_descends (prefixWord ++ tailWord_1176569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1176584 : List Nat := [2, 1, 3, 2, 1, 4, 1, 1, 1, 6]
def baseStart_1176584 : Nat := 118140960795 + 1176584 * 2 ^ 59
def prefixEnd_1176584 : Nat := 4983230072969 + 3 ^ 40 * 1176584 * 2
def baseEnd_1176584 : Nat := 402768748259819895592663

theorem tailTrace_1176584 : CollatzResearch.WordTrace tailWord_1176584 prefixEnd_1176584 402768748259819895592663 := by
  unfold tailWord_1176584
  simp only [CollatzResearch.WordTrace]
  refine ⟨21456771984722293697148403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28609029312963058262864537 21456771984722293697148403)
  ·
    refine ⟨32185157977083440545722605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21456771984722293697148403 32185157977083440545722605)
    ·
      refine ⟨12069434241406290204645977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32185157977083440545722605 12069434241406290204645977)
      ·
        refine ⟨9052075681054717653484483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12069434241406290204645977 9052075681054717653484483)
        ·
          refine ⟨13578113521582076480226725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9052075681054717653484483 13578113521582076480226725)
          ·
            refine ⟨2545896285296639340042511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13578113521582076480226725 2545896285296639340042511)
            ·
              refine ⟨3818844427944959010063767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2545896285296639340042511 3818844427944959010063767)
              ·
                refine ⟨5728266641917438515095651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3818844427944959010063767 5728266641917438515095651)
                ·
                  refine ⟨8592399962876157772643477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5728266641917438515095651 8592399962876157772643477)
                  ·
                    refine ⟨402768748259819895592663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8592399962876157772643477 402768748259819895592663)
                    ·
                      rfl

theorem cell22_1176584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 1, 1, 1, 6].length) (baseStart_1176584 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1176584 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1176584 prefixEnd_1176584 := by exact prefixLift 1176584
  have htrace : WordTrace (prefixWord ++ tailWord_1176584) baseStart_1176584 baseEnd_1176584 := by
    simpa [prefixWord, tailWord_1176584, baseEnd_1176584] using wordTrace_append hprefix tailTrace_1176584
  have hstable : (prefixWord ++ tailWord_1176584).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1176584).length < 2 ^ (prefixWord ++ tailWord_1176584).sum := by decide
  have hdescent : baseEnd_1176584 < baseStart_1176584 := by decide
  rcases family_descends (prefixWord ++ tailWord_1176584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1176599 : List Nat := [1, 1, 3, 5, 1, 2, 9]
def baseStart_1176599 : Nat := 118140960795 + 1176599 * 2 ^ 59
def prefixEnd_1176599 : Nat := 4983230072969 + 3 ^ 40 * 1176599 * 2
def baseEnd_1176599 : Nat := 14917551224680179869171

theorem tailTrace_1176599 : CollatzResearch.WordTrace tailWord_1176599 prefixEnd_1176599 14917551224680179869171 := by
  unfold tailWord_1176599
  simp only [CollatzResearch.WordTrace]
  refine ⟨42914091064390244956092851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28609394042926829970728567 42914091064390244956092851)
  ·
    refine ⟨64371136596585367434139277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42914091064390244956092851 64371136596585367434139277)
    ·
      refine ⟨24139176223719512787802229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64371136596585367434139277 24139176223719512787802229)
      ·
        refine ⟨2263047770973704323856459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 24139176223719512787802229 2263047770973704323856459)
        ·
          refine ⟨3394571656460556485784689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2263047770973704323856459 3394571656460556485784689)
          ·
            refine ⟨2545928742345417364338517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3394571656460556485784689 2545928742345417364338517)
            ·
              refine ⟨14917551224680179869171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2545928742345417364338517 14917551224680179869171)
              ·
                rfl

theorem cell22_1176599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 9].length) (baseStart_1176599 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1176599 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1176599 prefixEnd_1176599 := by exact prefixLift 1176599
  have htrace : WordTrace (prefixWord ++ tailWord_1176599) baseStart_1176599 baseEnd_1176599 := by
    simpa [prefixWord, tailWord_1176599, baseEnd_1176599] using wordTrace_append hprefix tailTrace_1176599
  have hstable : (prefixWord ++ tailWord_1176599).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1176599).length < 2 ^ (prefixWord ++ tailWord_1176599).sum := by decide
  have hdescent : baseEnd_1176599 < baseStart_1176599 := by decide
  rcases family_descends (prefixWord ++ tailWord_1176599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1176704 : List Nat := [2, 1, 1, 2, 1, 3, 3, 1, 3, 5]
def baseStart_1176704 : Nat := 118140960795 + 1176704 * 2 ^ 59
def prefixEnd_1176704 : Nat := 4983230072969 + 3 ^ 40 * 1176704 * 2
def baseEnd_1176704 : Nat := 402809826712179582592295

theorem tailTrace_1176704 : CollatzResearch.WordTrace tailWord_1176704 prefixEnd_1176704 402809826712179582592295 := by
  unfold tailWord_1176704
  simp only [CollatzResearch.WordTrace]
  refine ⟨21458960364504923944332583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28611947152673231925776777 21458960364504923944332583)
  ·
    refine ⟨32188440546757385916498875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21458960364504923944332583 32188440546757385916498875)
    ·
      refine ⟨48282660820136078874748313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32188440546757385916498875 48282660820136078874748313)
      ·
        refine ⟨36211995615102059156061235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48282660820136078874748313 36211995615102059156061235)
        ·
          refine ⟨54317993422653088734091853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36211995615102059156061235 54317993422653088734091853)
          ·
            refine ⟨20369247533494908275284445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54317993422653088734091853 20369247533494908275284445)
            ·
              refine ⟨7638467825060590603231667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20369247533494908275284445 7638467825060590603231667)
              ·
                refine ⟨11457701737590885904847501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7638467825060590603231667 11457701737590885904847501)
                ·
                  refine ⟨4296638151596582214317813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11457701737590885904847501 4296638151596582214317813)
                  ·
                    refine ⟨402809826712179582592295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4296638151596582214317813 402809826712179582592295)
                    ·
                      rfl

theorem cell22_1176704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 1, 3, 5].length) (baseStart_1176704 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1176704 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1176704 prefixEnd_1176704 := by exact prefixLift 1176704
  have htrace : WordTrace (prefixWord ++ tailWord_1176704) baseStart_1176704 baseEnd_1176704 := by
    simpa [prefixWord, tailWord_1176704, baseEnd_1176704] using wordTrace_append hprefix tailTrace_1176704
  have hstable : (prefixWord ++ tailWord_1176704).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1176704).length < 2 ^ (prefixWord ++ tailWord_1176704).sum := by decide
  have hdescent : baseEnd_1176704 < baseStart_1176704 := by decide
  rcases family_descends (prefixWord ++ tailWord_1176704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1176719 : List Nat := [1, 1, 2, 1, 1, 1, 1, 2, 8, 4]
def baseStart_1176719 : Nat := 118140960795 + 1176719 * 2 ^ 59
def prefixEnd_1176719 : Nat := 4983230072969 + 3 ^ 40 * 1176719 * 2
def baseEnd_1176719 : Nat := 402814961518724543467249

theorem tailTrace_1176719 : CollatzResearch.WordTrace tailWord_1176719 prefixEnd_1176719 402814961518724543467249 := by
  unfold tailWord_1176719
  simp only [CollatzResearch.WordTrace]
  refine ⟨42918467823955505450461211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28612311882637003633640807 42918467823955505450461211)
  ·
    refine ⟨64377701735933258175691817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42918467823955505450461211 64377701735933258175691817)
    ·
      refine ⟨48283276301949943631768863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64377701735933258175691817 48283276301949943631768863)
      ·
        refine ⟨72424914452924915447653295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48283276301949943631768863 72424914452924915447653295)
        ·
          refine ⟨108637371679387373171479943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72424914452924915447653295 108637371679387373171479943)
          ·
            refine ⟨162956057519081059757219915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108637371679387373171479943 162956057519081059757219915)
            ·
              refine ⟨244434086278621589635829873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 162956057519081059757219915 244434086278621589635829873)
              ·
                refine ⟨183325564708966192226872405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 244434086278621589635829873 183325564708966192226872405)
                ·
                  refine ⟨2148346461433197565158661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 183325564708966192226872405 2148346461433197565158661)
                  ·
                    refine ⟨402814961518724543467249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2148346461433197565158661 402814961518724543467249)
                    ·
                      rfl

theorem cell22_1176719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 8, 4].length) (baseStart_1176719 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1176719 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1176719 prefixEnd_1176719 := by exact prefixLift 1176719
  have htrace : WordTrace (prefixWord ++ tailWord_1176719) baseStart_1176719 baseEnd_1176719 := by
    simpa [prefixWord, tailWord_1176719, baseEnd_1176719] using wordTrace_append hprefix tailTrace_1176719
  have hstable : (prefixWord ++ tailWord_1176719).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1176719).length < 2 ^ (prefixWord ++ tailWord_1176719).sum := by decide
  have hdescent : baseEnd_1176719 < baseStart_1176719 := by decide
  rcases family_descends (prefixWord ++ tailWord_1176719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1176723 : List Nat := [1, 1, 1, 2, 1, 2, 8, 2, 4]
def baseStart_1176723 : Nat := 118140960795 + 1176723 * 2 ^ 59
def prefixEnd_1176723 : Nat := 4983230072969 + 3 ^ 40 * 1176723 * 2
def baseEnd_1176723 : Nat := 134272110266823288789079

theorem tailTrace_1176723 : CollatzResearch.WordTrace tailWord_1176723 prefixEnd_1176723 134272110266823288789079 := by
  unfold tailWord_1176723
  simp only [CollatzResearch.WordTrace]
  refine ⟨42918613715941014133606823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28612409143960676089071215 42918613715941014133606823)
  ·
    refine ⟨64377920573911521200410235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42918613715941014133606823 64377920573911521200410235)
    ·
      refine ⟨96566880860867281800615353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64377920573911521200410235 96566880860867281800615353)
      ·
        refine ⟨72425160645650461350461515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96566880860867281800615353 72425160645650461350461515)
        ·
          refine ⟨108637740968475692025692273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72425160645650461350461515 108637740968475692025692273)
          ·
            refine ⟨81478305726356769019269205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 108637740968475692025692273 81478305726356769019269205)
            ·
              refine ⟨954823895230743386944561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 81478305726356769019269205 954823895230743386944561)
              ·
                refine ⟨716117921423057540208421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 954823895230743386944561 716117921423057540208421)
                ·
                  refine ⟨134272110266823288789079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 716117921423057540208421 134272110266823288789079)
                  ·
                    rfl

theorem cell22_1176723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 8, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 8, 2, 4].length) (baseStart_1176723 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1176723 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1176723 prefixEnd_1176723 := by exact prefixLift 1176723
  have htrace : WordTrace (prefixWord ++ tailWord_1176723) baseStart_1176723 baseEnd_1176723 := by
    simpa [prefixWord, tailWord_1176723, baseEnd_1176723] using wordTrace_append hprefix tailTrace_1176723
  have hstable : (prefixWord ++ tailWord_1176723).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1176723).length < 2 ^ (prefixWord ++ tailWord_1176723).sum := by decide
  have hdescent : baseEnd_1176723 < baseStart_1176723 := by decide
  rcases family_descends (prefixWord ++ tailWord_1176723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1176753 : List Nat := [1, 2, 2, 5, 1, 1, 3, 1, 2, 4]
def baseStart_1176753 : Nat := 118140960795 + 1176753 * 2 ^ 59
def prefixEnd_1176753 : Nat := 4983230072969 + 3 ^ 40 * 1176753 * 2
def baseEnd_1176753 : Nat := 402826600413559788117145

theorem tailTrace_1176753 : CollatzResearch.WordTrace tailWord_1176753 prefixEnd_1176753 402826600413559788117145 := by
  unfold tailWord_1176753
  simp only [CollatzResearch.WordTrace]
  refine ⟨42919707905832329257198913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28613138603888219504799275 42919707905832329257198913)
  ·
    refine ⟨32189780929374246942899185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42919707905832329257198913 32189780929374246942899185)
    ·
      refine ⟨24142335697030685207174389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32189780929374246942899185 24142335697030685207174389)
      ·
        refine ⟨2263343971596626738172599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 24142335697030685207174389 2263343971596626738172599)
        ·
          refine ⟨3395015957394940107258899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2263343971596626738172599 3395015957394940107258899)
          ·
            refine ⟨5092523936092410160888349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3395015957394940107258899 5092523936092410160888349)
            ·
              refine ⟨1909696476034653810333131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5092523936092410160888349 1909696476034653810333131)
              ·
                refine ⟨2864544714051980715499697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1909696476034653810333131 2864544714051980715499697)
                ·
                  refine ⟨2148408535538985536624773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2864544714051980715499697 2148408535538985536624773)
                  ·
                    refine ⟨402826600413559788117145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2148408535538985536624773 402826600413559788117145)
                    ·
                      rfl

theorem cell22_1176753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 3, 1, 2, 4].length) (baseStart_1176753 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1176753 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1176753 prefixEnd_1176753 := by exact prefixLift 1176753
  have htrace : WordTrace (prefixWord ++ tailWord_1176753) baseStart_1176753 baseEnd_1176753 := by
    simpa [prefixWord, tailWord_1176753, baseEnd_1176753] using wordTrace_append hprefix tailTrace_1176753
  have hstable : (prefixWord ++ tailWord_1176753).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1176753).length < 2 ^ (prefixWord ++ tailWord_1176753).sum := by decide
  have hdescent : baseEnd_1176753 < baseStart_1176753 := by decide
  rcases family_descends (prefixWord ++ tailWord_1176753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1176772 : List Nat := [2, 3, 3, 1, 3, 2, 1, 2, 2, 3]
def baseStart_1176772 : Nat := 118140960795 + 1176772 * 2 ^ 59
def prefixEnd_1176772 : Nat := 4983230072969 + 3 ^ 40 * 1176772 * 2
def baseEnd_1176772 : Nat := 402833104501850071892087

theorem tailTrace_1176772 : CollatzResearch.WordTrace tailWord_1176772 prefixEnd_1176772 402833104501850071892087 := by
  unfold tailWord_1176772
  simp only [CollatzResearch.WordTrace]
  refine ⟨21460200446381747751070285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28613600595175663668093713 21460200446381747751070285)
  ·
    refine ⟨8047575167393155406651357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21460200446381747751070285 8047575167393155406651357)
    ·
      refine ⟨3017840687772433277494259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8047575167393155406651357 3017840687772433277494259)
      ·
        refine ⟨4526761031658649916241389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3017840687772433277494259 4526761031658649916241389)
        ·
          refine ⟨1697535386871993718590521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4526761031658649916241389 1697535386871993718590521)
          ·
            refine ⟨1273151540153995288942891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1697535386871993718590521 1273151540153995288942891)
            ·
              refine ⟨1909727310230992933414337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1273151540153995288942891 1909727310230992933414337)
              ·
                refine ⟨1432295482673244700060753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1909727310230992933414337 1432295482673244700060753)
                ·
                  refine ⟨1074221612004933525045565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1432295482673244700060753 1074221612004933525045565)
                  ·
                    refine ⟨402833104501850071892087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1074221612004933525045565 402833104501850071892087)
                    ·
                      rfl

theorem cell22_1176772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 2, 1, 2, 2, 3].length) (baseStart_1176772 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1176772 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1176772 prefixEnd_1176772 := by exact prefixLift 1176772
  have htrace : WordTrace (prefixWord ++ tailWord_1176772) baseStart_1176772 baseEnd_1176772 := by
    simpa [prefixWord, tailWord_1176772, baseEnd_1176772] using wordTrace_append hprefix tailTrace_1176772
  have hstable : (prefixWord ++ tailWord_1176772).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1176772).length < 2 ^ (prefixWord ++ tailWord_1176772).sum := by decide
  have hdescent : baseEnd_1176772 < baseStart_1176772 := by decide
  rcases family_descends (prefixWord ++ tailWord_1176772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1176834 : List Nat := [3, 4, 1, 1, 4, 1, 1, 1, 3, 3]
def baseStart_1176834 : Nat := 118140960795 + 1176834 * 2 ^ 59
def prefixEnd_1176834 : Nat := 4983230072969 + 3 ^ 40 * 1176834 * 2
def baseEnd_1176834 : Nat := 402854328368902576841897

theorem tailTrace_1176834 : CollatzResearch.WordTrace tailWord_1176834 prefixEnd_1176834 402854328368902576841897 := by
  unfold tailWord_1176834
  simp only [CollatzResearch.WordTrace]
  refine ⟨10730665554634720022724389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28615108145692586727265037 10730665554634720022724389)
  ·
    refine ⟨2011999791494010004260823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10730665554634720022724389 2011999791494010004260823)
    ·
      refine ⟨3017999687241015006391235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2011999791494010004260823 3017999687241015006391235)
      ·
        refine ⟨4526999530861522509586853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3017999687241015006391235 4526999530861522509586853)
        ·
          refine ⟨848812412036535470547535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4526999530861522509586853 848812412036535470547535)
          ·
            refine ⟨1273218618054803205821303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 848812412036535470547535 1273218618054803205821303)
            ·
              refine ⟨1909827927082204808731955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1273218618054803205821303 1909827927082204808731955)
              ·
                refine ⟨2864741890623307213097933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1909827927082204808731955 2864741890623307213097933)
                ·
                  refine ⟨1074278208983740204911725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2864741890623307213097933 1074278208983740204911725)
                  ·
                    refine ⟨402854328368902576841897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1074278208983740204911725 402854328368902576841897)
                    ·
                      rfl

theorem cell22_1176834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 4, 1, 1, 1, 3, 3].length) (baseStart_1176834 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1176834 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1176834 prefixEnd_1176834 := by exact prefixLift 1176834
  have htrace : WordTrace (prefixWord ++ tailWord_1176834) baseStart_1176834 baseEnd_1176834 := by
    simpa [prefixWord, tailWord_1176834, baseEnd_1176834] using wordTrace_append hprefix tailTrace_1176834
  have hstable : (prefixWord ++ tailWord_1176834).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1176834).length < 2 ^ (prefixWord ++ tailWord_1176834).sum := by decide
  have hdescent : baseEnd_1176834 < baseStart_1176834 := by decide
  rcases family_descends (prefixWord ++ tailWord_1176834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1176890 : List Nat := [3, 1, 1, 1, 4, 1, 4, 2, 2, 3]
def baseStart_1176890 : Nat := 118140960795 + 1176890 * 2 ^ 59
def prefixEnd_1176890 : Nat := 4983230072969 + 3 ^ 40 * 1176890 * 2
def baseEnd_1176890 : Nat := 402873498313337097441725

theorem tailTrace_1176890 : CollatzResearch.WordTrace tailWord_1176890 prefixEnd_1176890 402873498313337097441725 := by
  unfold tailWord_1176890
  simp only [CollatzResearch.WordTrace]
  refine ⟨10731176176584000413734031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28616469804224001103290749 10731176176584000413734031)
  ·
    refine ⟨16096764264876000620601047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10731176176584000413734031 16096764264876000620601047)
    ·
      refine ⟨24145146397314000930901571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16096764264876000620601047 24145146397314000930901571)
      ·
        refine ⟨36217719595971001396352357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24145146397314000930901571 36217719595971001396352357)
        ·
          refine ⟨6790822424244562761816067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 36217719595971001396352357 6790822424244562761816067)
          ·
            refine ⟨10186233636366844142724101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6790822424244562761816067 10186233636366844142724101)
            ·
              refine ⟨1909918806818783276760769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10186233636366844142724101 1909918806818783276760769)
              ·
                refine ⟨1432439105114087457570577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1909918806818783276760769 1432439105114087457570577)
                ·
                  refine ⟨1074329328835565593177933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1432439105114087457570577 1074329328835565593177933)
                  ·
                    refine ⟨402873498313337097441725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1074329328835565593177933 402873498313337097441725)
                    ·
                      rfl

theorem cell22_1176890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 4, 2, 2, 3].length) (baseStart_1176890 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1176890 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1176890 prefixEnd_1176890 := by exact prefixLift 1176890
  have htrace : WordTrace (prefixWord ++ tailWord_1176890) baseStart_1176890 baseEnd_1176890 := by
    simpa [prefixWord, tailWord_1176890, baseEnd_1176890] using wordTrace_append hprefix tailTrace_1176890
  have hstable : (prefixWord ++ tailWord_1176890).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1176890).length < 2 ^ (prefixWord ++ tailWord_1176890).sum := by decide
  have hdescent : baseEnd_1176890 < baseStart_1176890 := by decide
  rcases family_descends (prefixWord ++ tailWord_1176890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1176892 : List Nat := [2, 2, 2, 2, 1, 5, 2, 2, 4]
def baseStart_1176892 : Nat := 118140960795 + 1176892 * 2 ^ 59
def prefixEnd_1176892 : Nat := 4983230072969 + 3 ^ 40 * 1176892 * 2
def baseEnd_1176892 : Nat := 134291394318069919630573

theorem tailTrace_1176892 : CollatzResearch.WordTrace tailWord_1176892 prefixEnd_1176892 134291394318069919630573 := by
  unfold tailWord_1176892
  simp only [CollatzResearch.WordTrace]
  refine ⟨21462388826164377998254465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28616518434885837331005953 21462388826164377998254465)
  ·
    refine ⟨16096791619623283498690849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21462388826164377998254465 16096791619623283498690849)
    ·
      refine ⟨12072593714717462624018137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16096791619623283498690849 12072593714717462624018137)
      ·
        refine ⟨9054445286038096968013603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12072593714717462624018137 9054445286038096968013603)
        ·
          refine ⟨13581667929057145452020405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9054445286038096968013603 13581667929057145452020405)
          ·
            refine ⟨1273281368349107386126913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 13581667929057145452020405 1273281368349107386126913)
            ·
              refine ⟨954961026261830539595185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1273281368349107386126913 954961026261830539595185)
              ·
                refine ⟨716220769696372904696389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 954961026261830539595185 716220769696372904696389)
                ·
                  refine ⟨134291394318069919630573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 716220769696372904696389 134291394318069919630573)
                  ·
                    rfl

theorem cell22_1176892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 5, 2, 2, 4].length) (baseStart_1176892 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1176892 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1176892 prefixEnd_1176892 := by exact prefixLift 1176892
  have htrace : WordTrace (prefixWord ++ tailWord_1176892) baseStart_1176892 baseEnd_1176892 := by
    simpa [prefixWord, tailWord_1176892, baseEnd_1176892] using wordTrace_append hprefix tailTrace_1176892
  have hstable : (prefixWord ++ tailWord_1176892).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1176892).length < 2 ^ (prefixWord ++ tailWord_1176892).sum := by decide
  have hdescent : baseEnd_1176892 < baseStart_1176892 := by decide
  rcases family_descends (prefixWord ++ tailWord_1176892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1176903 : List Nat := [1, 1, 4, 1, 2, 5, 1, 7]
def baseStart_1176903 : Nat := 118140960795 + 1176903 * 2 ^ 59
def prefixEnd_1176903 : Nat := 4983230072969 + 3 ^ 40 * 1176903 * 2
def baseEnd_1176903 : Nat := 44764216497667710762965

theorem tailTrace_1176903 : CollatzResearch.WordTrace tailWord_1176903 prefixEnd_1176903 44764216497667710762965 := by
  unfold tailWord_1176903
  simp only [CollatzResearch.WordTrace]
  refine ⟨42925178855288904875159363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28616785903525936583439575 42925178855288904875159363)
  ·
    refine ⟨64387768282933357312739045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42925178855288904875159363 64387768282933357312739045)
    ·
      refine ⟨12072706553050004496138571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 64387768282933357312739045 12072706553050004496138571)
      ·
        refine ⟨18109059829575006744207857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12072706553050004496138571 18109059829575006744207857)
        ·
          refine ⟨13581794872181255058155893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18109059829575006744207857 13581794872181255058155893)
          ·
            refine ⟨1273293269266992661702115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 13581794872181255058155893 1273293269266992661702115)
            ·
              refine ⟨1909939903900488992553173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1273293269266992661702115 1909939903900488992553173)
              ·
                refine ⟨44764216497667710762965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1909939903900488992553173 44764216497667710762965)
                ·
                  rfl

theorem cell22_1176903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 5, 1, 7].length) (baseStart_1176903 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1176903 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1176903 prefixEnd_1176903 := by exact prefixLift 1176903
  have htrace : WordTrace (prefixWord ++ tailWord_1176903) baseStart_1176903 baseEnd_1176903 := by
    simpa [prefixWord, tailWord_1176903, baseEnd_1176903] using wordTrace_append hprefix tailTrace_1176903
  have hstable : (prefixWord ++ tailWord_1176903).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1176903).length < 2 ^ (prefixWord ++ tailWord_1176903).sum := by decide
  have hdescent : baseEnd_1176903 < baseStart_1176903 := by decide
  rcases family_descends (prefixWord ++ tailWord_1176903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1176963 : List Nat := [1, 1, 1, 3, 5, 1, 2, 1, 2, 5]
def baseStart_1176963 : Nat := 118140960795 + 1176963 * 2 ^ 59
def prefixEnd_1176963 : Nat := 4983230072969 + 3 ^ 40 * 1176963 * 2
def baseEnd_1176963 : Nat := 402898487705189240366501

theorem tailTrace_1176963 : CollatzResearch.WordTrace tailWord_1176963 prefixEnd_1176963 402898487705189240366501 := by
  unfold tailWord_1176963
  simp only [CollatzResearch.WordTrace]
  refine ⟨42927367235071535122343543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28618244823381023414895695 42927367235071535122343543)
  ·
    refine ⟨64391050852607302683515315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42927367235071535122343543 64391050852607302683515315)
    ·
      refine ⟨96586576278910954025272973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64391050852607302683515315 96586576278910954025272973)
      ·
        refine ⟨36219966104591607759477365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 96586576278910954025272973 36219966104591607759477365)
        ·
          refine ⟨3395621822305463227451003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 36219966104591607759477365 3395621822305463227451003)
          ·
            refine ⟨5093432733458194841176505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3395621822305463227451003 5093432733458194841176505)
            ·
              refine ⟨3820074550093646130882379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5093432733458194841176505 3820074550093646130882379)
              ·
                refine ⟨5730111825140469196323569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3820074550093646130882379 5730111825140469196323569)
                ·
                  refine ⟨4297583868855351897242677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5730111825140469196323569 4297583868855351897242677)
                  ·
                    refine ⟨402898487705189240366501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4297583868855351897242677 402898487705189240366501)
                    ·
                      rfl

theorem cell22_1176963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 2, 1, 2, 5].length) (baseStart_1176963 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1176963 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1176963 prefixEnd_1176963 := by exact prefixLift 1176963
  have htrace : WordTrace (prefixWord ++ tailWord_1176963) baseStart_1176963 baseEnd_1176963 := by
    simpa [prefixWord, tailWord_1176963, baseEnd_1176963] using wordTrace_append hprefix tailTrace_1176963
  have hstable : (prefixWord ++ tailWord_1176963).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1176963).length < 2 ^ (prefixWord ++ tailWord_1176963).sum := by decide
  have hdescent : baseEnd_1176963 < baseStart_1176963 := by decide
  rcases family_descends (prefixWord ++ tailWord_1176963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1177038 : List Nat := [4, 1, 1, 1, 2, 1, 4, 8]
def baseStart_1177038 : Nat := 118140960795 + 1177038 * 2 ^ 59
def prefixEnd_1177038 : Nat := 4983230072969 + 3 ^ 40 * 1177038 * 2
def baseEnd_1177038 : Nat := 44769351304212671637919

theorem tailTrace_1177038 : CollatzResearch.WordTrace tailWord_1177038 prefixEnd_1177038 44769351304212671637919 := by
  unfold tailWord_1177038
  simp only [CollatzResearch.WordTrace]
  refine ⟨5366262838724977866415471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28620068473199881954215845 5366262838724977866415471)
  ·
    refine ⟨8049394258087466799623207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5366262838724977866415471 8049394258087466799623207)
    ·
      refine ⟨12074091387131200199434811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8049394258087466799623207 12074091387131200199434811)
      ·
        refine ⟨18111137080696800299152217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12074091387131200199434811 18111137080696800299152217)
        ·
          refine ⟨13583352810522600224364163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18111137080696800299152217 13583352810522600224364163)
          ·
            refine ⟨20375029215783900336546245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13583352810522600224364163 20375029215783900336546245)
            ·
              refine ⟨3820317977959481313102421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20375029215783900336546245 3820317977959481313102421)
              ·
                refine ⟨44769351304212671637919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3820317977959481313102421 44769351304212671637919)
                ·
                  rfl

theorem cell22_1177038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 4, 8].length) (baseStart_1177038 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1177038 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1177038 prefixEnd_1177038 := by exact prefixLift 1177038
  have htrace : WordTrace (prefixWord ++ tailWord_1177038) baseStart_1177038 baseEnd_1177038 := by
    simpa [prefixWord, tailWord_1177038, baseEnd_1177038] using wordTrace_append hprefix tailTrace_1177038
  have hstable : (prefixWord ++ tailWord_1177038).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1177038).length < 2 ^ (prefixWord ++ tailWord_1177038).sum := by decide
  have hdescent : baseEnd_1177038 < baseStart_1177038 := by decide
  rcases family_descends (prefixWord ++ tailWord_1177038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1177134 : List Nat := [4, 1, 3, 1, 2, 2, 3, 1, 5]
def baseStart_1177134 : Nat := 118140960795 + 1177134 * 2 ^ 59
def prefixEnd_1177134 : Nat := 4983230072969 + 3 ^ 40 * 1177134 * 2
def baseEnd_1177134 : Nat := 134319008166600598113659

theorem tailTrace_1177134 : CollatzResearch.WordTrace tailWord_1177134 prefixEnd_1177134 134319008166600598113659 := by
  unfold tailWord_1177134
  simp only [CollatzResearch.WordTrace]
  refine ⟨5366700514681503915852307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28622402744968020884545637 5366700514681503915852307)
  ·
    refine ⟨8050050772022255873778461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5366700514681503915852307 8050050772022255873778461)
    ·
      refine ⟨3018769039508345952666923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8050050772022255873778461 3018769039508345952666923)
      ·
        refine ⟨4528153559262518929000385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3018769039508345952666923 4528153559262518929000385)
        ·
          refine ⟨3396115169446889196750289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4528153559262518929000385 3396115169446889196750289)
          ·
            refine ⟨2547086377085166897562717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3396115169446889196750289 2547086377085166897562717)
            ·
              refine ⟨955157391406937586586019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2547086377085166897562717 955157391406937586586019)
              ·
                refine ⟨1432736087110406379879029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 955157391406937586586019 1432736087110406379879029)
                ·
                  refine ⟨134319008166600598113659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1432736087110406379879029 134319008166600598113659)
                  ·
                    rfl

theorem cell22_1177134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 3, 1, 5].length) (baseStart_1177134 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1177134 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1177134 prefixEnd_1177134 := by exact prefixLift 1177134
  have htrace : WordTrace (prefixWord ++ tailWord_1177134) baseStart_1177134 baseEnd_1177134 := by
    simpa [prefixWord, tailWord_1177134, baseEnd_1177134] using wordTrace_append hprefix tailTrace_1177134
  have hstable : (prefixWord ++ tailWord_1177134).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1177134).length < 2 ^ (prefixWord ++ tailWord_1177134).sum := by decide
  have hdescent : baseEnd_1177134 < baseStart_1177134 := by decide
  rcases family_descends (prefixWord ++ tailWord_1177134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1177145 : List Nat := [1, 2, 1, 5, 1, 2, 2, 2, 6]
def baseStart_1177145 : Nat := 118140960795 + 1177145 * 2 ^ 59
def prefixEnd_1177145 : Nat := 4983230072969 + 3 ^ 40 * 1177145 * 2
def baseEnd_1177145 : Nat := 134320263341533810771981

theorem tailTrace_1177145 : CollatzResearch.WordTrace tailWord_1177145 prefixEnd_1177145 134320263341533810771981 := by
  unfold tailWord_1177145
  simp only [CollatzResearch.WordTrace]
  refine ⟨42934005320412180205468889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28622670213608120136979259 42934005320412180205468889)
  ·
    refine ⟨32200503990309135154101667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42934005320412180205468889 32200503990309135154101667)
    ·
      refine ⟨48300755985463702731152501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32200503990309135154101667 48300755985463702731152501)
      ·
        refine ⟨4528195873637222131045547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 48300755985463702731152501 4528195873637222131045547)
        ·
          refine ⟨6792293810455833196568321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4528195873637222131045547 6792293810455833196568321)
          ·
            refine ⟨5094220357841874897426241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6792293810455833196568321 5094220357841874897426241)
            ·
              refine ⟨3820665268381406173069681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5094220357841874897426241 3820665268381406173069681)
              ·
                refine ⟨2865498951286054629802261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3820665268381406173069681 2865498951286054629802261)
                ·
                  refine ⟨134320263341533810771981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2865498951286054629802261 134320263341533810771981)
                  ·
                    rfl

theorem cell22_1177145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 2, 2, 6].length) (baseStart_1177145 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1177145 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1177145 prefixEnd_1177145 := by exact prefixLift 1177145
  have htrace : WordTrace (prefixWord ++ tailWord_1177145) baseStart_1177145 baseEnd_1177145 := by
    simpa [prefixWord, tailWord_1177145, baseEnd_1177145] using wordTrace_append hprefix tailTrace_1177145
  have hstable : (prefixWord ++ tailWord_1177145).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1177145).length < 2 ^ (prefixWord ++ tailWord_1177145).sum := by decide
  have hdescent : baseEnd_1177145 < baseStart_1177145 := by decide
  rcases family_descends (prefixWord ++ tailWord_1177145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1177175 : List Nat := [1, 1, 3, 2, 2, 3, 1, 1, 4, 4]
def baseStart_1177175 : Nat := 118140960795 + 1177175 * 2 ^ 59
def prefixEnd_1177175 : Nat := 4983230072969 + 3 ^ 40 * 1177175 * 2
def baseEnd_1177175 : Nat := 402971059637691354065851

theorem tailTrace_1177175 : CollatzResearch.WordTrace tailWord_1177175 prefixEnd_1177175 402971059637691354065851 := by
  unfold tailWord_1177175
  simp only [CollatzResearch.WordTrace]
  refine ⟨42935099510303495329060979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28623399673535663552707319 42935099510303495329060979)
  ·
    refine ⟨64402649265455242993591469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42935099510303495329060979 64402649265455242993591469)
    ·
      refine ⟨24150993474545716122596801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64402649265455242993591469 24150993474545716122596801)
      ·
        refine ⟨18113245105909287091947601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24150993474545716122596801 18113245105909287091947601)
        ·
          refine ⟨13584933829431965318960701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18113245105909287091947601 13584933829431965318960701)
          ·
            refine ⟨5094350186036986994610263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13584933829431965318960701 5094350186036986994610263)
            ·
              refine ⟨7641525279055480491915395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5094350186036986994610263 7641525279055480491915395)
              ·
                refine ⟨11462287918583220737873093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7641525279055480491915395 11462287918583220737873093)
                ·
                  refine ⟨2149178984734353888351205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11462287918583220737873093 2149178984734353888351205)
                  ·
                    refine ⟨402971059637691354065851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2149178984734353888351205 402971059637691354065851)
                    ·
                      rfl

theorem cell22_1177175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 1, 4, 4].length) (baseStart_1177175 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1177175 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1177175 prefixEnd_1177175 := by exact prefixLift 1177175
  have htrace : WordTrace (prefixWord ++ tailWord_1177175) baseStart_1177175 baseEnd_1177175 := by
    simpa [prefixWord, tailWord_1177175, baseEnd_1177175] using wordTrace_append hprefix tailTrace_1177175
  have hstable : (prefixWord ++ tailWord_1177175).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1177175).length < 2 ^ (prefixWord ++ tailWord_1177175).sum := by decide
  have hdescent : baseEnd_1177175 < baseStart_1177175 := by decide
  rcases family_descends (prefixWord ++ tailWord_1177175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1177194 : List Nat := [3, 1, 3, 2, 1, 3, 1, 3, 2, 3]
def baseStart_1177194 : Nat := 118140960795 + 1177194 * 2 ^ 59
def prefixEnd_1177194 : Nat := 4983230072969 + 3 ^ 40 * 1177194 * 2
def baseEnd_1177194 : Nat := 402977563725981637840793

theorem tailTrace_1177194 : CollatzResearch.WordTrace tailWord_1177194 prefixEnd_1177194 402977563725981637840793 := by
  unfold tailWord_1177194
  simp only [CollatzResearch.WordTrace]
  refine ⟨10733948124308665393500659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28623861664823107716001757 10733948124308665393500659)
  ·
    refine ⟨16100922186462998090250989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10733948124308665393500659 16100922186462998090250989)
    ·
      refine ⟨6037845819923624283844121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16100922186462998090250989 6037845819923624283844121)
      ·
        refine ⟨4528384364942718212883091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6037845819923624283844121 4528384364942718212883091)
        ·
          refine ⟨6792576547414077319324637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4528384364942718212883091 6792576547414077319324637)
          ·
            refine ⟨2547216205280278994746739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6792576547414077319324637 2547216205280278994746739)
            ·
              refine ⟨3820824307920418492120109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2547216205280278994746739 3820824307920418492120109)
              ·
                refine ⟨1432809115470156934545041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3820824307920418492120109 1432809115470156934545041)
                ·
                  refine ⟨1074606836602617700908781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1432809115470156934545041 1074606836602617700908781)
                  ·
                    refine ⟨402977563725981637840793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1074606836602617700908781 402977563725981637840793)
                    ·
                      rfl

theorem cell22_1177194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 1, 3, 2, 3].length) (baseStart_1177194 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1177194 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1177194 prefixEnd_1177194 := by exact prefixLift 1177194
  have htrace : WordTrace (prefixWord ++ tailWord_1177194) baseStart_1177194 baseEnd_1177194 := by
    simpa [prefixWord, tailWord_1177194, baseEnd_1177194] using wordTrace_append hprefix tailTrace_1177194
  have hstable : (prefixWord ++ tailWord_1177194).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1177194).length < 2 ^ (prefixWord ++ tailWord_1177194).sum := by decide
  have hdescent : baseEnd_1177194 < baseStart_1177194 := by decide
  rcases family_descends (prefixWord ++ tailWord_1177194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1177252 : List Nat := [2, 3, 1, 2, 2, 2, 2, 3, 5]
def baseStart_1177252 : Nat := 118140960795 + 1177252 * 2 ^ 59
def prefixEnd_1177252 : Nat := 4983230072969 + 3 ^ 40 * 1177252 * 2
def baseEnd_1177252 : Nat := 134332472770429606630205

theorem tailTrace_1177252 : CollatzResearch.WordTrace tailWord_1177252 prefixEnd_1177252 134332472770429606630205 := by
  unfold tailWord_1177252
  simp only [CollatzResearch.WordTrace]
  refine ⟨21468953965512268739807005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28625271954016358319742673 21468953965512268739807005)
  ·
    refine ⟨8050857737067100777427627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21468953965512268739807005 8050857737067100777427627)
    ·
      refine ⟨12076286605600651166141441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8050857737067100777427627 12076286605600651166141441)
      ·
        refine ⟨9057214954200488374606081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12076286605600651166141441 9057214954200488374606081)
        ·
          refine ⟨6792911215650366280954561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9057214954200488374606081 6792911215650366280954561)
          ·
            refine ⟨5094683411737774710715921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6792911215650366280954561 5094683411737774710715921)
            ·
              refine ⟨3821012558803331033036941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5094683411737774710715921 3821012558803331033036941)
              ·
                refine ⟨1432879709551249137388853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3821012558803331033036941 1432879709551249137388853)
                ·
                  refine ⟨134332472770429606630205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1432879709551249137388853 134332472770429606630205)
                  ·
                    rfl

theorem cell22_1177252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 2, 3, 5].length) (baseStart_1177252 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1177252 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1177252 prefixEnd_1177252 := by exact prefixLift 1177252
  have htrace : WordTrace (prefixWord ++ tailWord_1177252) baseStart_1177252 baseEnd_1177252 := by
    simpa [prefixWord, tailWord_1177252, baseEnd_1177252] using wordTrace_append hprefix tailTrace_1177252
  have hstable : (prefixWord ++ tailWord_1177252).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1177252).length < 2 ^ (prefixWord ++ tailWord_1177252).sum := by decide
  have hdescent : baseEnd_1177252 < baseStart_1177252 := by decide
  rcases family_descends (prefixWord ++ tailWord_1177252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1177280 : List Nat := [2, 1, 1, 2, 4, 1, 1, 2, 8]
def baseStart_1177280 : Nat := 118140960795 + 1177280 * 2 ^ 59
def prefixEnd_1177280 : Nat := 4983230072969 + 3 ^ 40 * 1177280 * 2
def baseEnd_1177280 : Nat := 134335667761168693396843

theorem tailTrace_1177280 : CollatzResearch.WordTrace tailWord_1177280 prefixEnd_1177280 134335667761168693396843 := by
  unfold tailWord_1177280
  simp only [CollatzResearch.WordTrace]
  refine ⟨21469464587461549130816647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28625952783282065507755529 21469464587461549130816647)
  ·
    refine ⟨32204196881192323696224971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21469464587461549130816647 32204196881192323696224971)
    ·
      refine ⟨48306295321788485544337457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32204196881192323696224971 48306295321788485544337457)
      ·
        refine ⟨36229721491341364158253093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48306295321788485544337457 36229721491341364158253093)
        ·
          refine ⟨6793072779626505779672455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 36229721491341364158253093 6793072779626505779672455)
          ·
            refine ⟨10189609169439758669508683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6793072779626505779672455 10189609169439758669508683)
            ·
              refine ⟨15284413754159638004263025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10189609169439758669508683 15284413754159638004263025)
              ·
                refine ⟨11463310315619728503197269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15284413754159638004263025 11463310315619728503197269)
                ·
                  refine ⟨134335667761168693396843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 11463310315619728503197269 134335667761168693396843)
                  ·
                    rfl

theorem cell22_1177280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 8].length) (baseStart_1177280 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1177280 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1177280 prefixEnd_1177280 := by exact prefixLift 1177280
  have htrace : WordTrace (prefixWord ++ tailWord_1177280) baseStart_1177280 baseEnd_1177280 := by
    simpa [prefixWord, tailWord_1177280, baseEnd_1177280] using wordTrace_append hprefix tailTrace_1177280
  have hstable : (prefixWord ++ tailWord_1177280).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1177280).length < 2 ^ (prefixWord ++ tailWord_1177280).sum := by decide
  have hdescent : baseEnd_1177280 < baseStart_1177280 := by decide
  rcases family_descends (prefixWord ++ tailWord_1177280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1177286 : List Nat := [6, 1, 2, 1, 1, 2, 1, 1, 7]
def baseStart_1177286 : Nat := 118140960795 + 1177286 * 2 ^ 59
def prefixEnd_1177286 : Nat := 4983230072969 + 3 ^ 40 * 1177286 * 2
def baseEnd_1177286 : Nat := 134336352402041354846837

theorem tailTrace_1177286 : CollatzResearch.WordTrace tailWord_1177286 prefixEnd_1177286 134336352402041354846837 := by
  unfold tailWord_1177286
  simp only [CollatzResearch.WordTrace]
  refine ⟨1341848375403167540198491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 28626098675267574190901141 1341848375403167540198491)
  ·
    refine ⟨2012772563104751310297737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1341848375403167540198491 2012772563104751310297737)
    ·
      refine ⟨1509579422328563482723303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2012772563104751310297737 1509579422328563482723303)
      ·
        refine ⟨2264369133492845224084955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1509579422328563482723303 2264369133492845224084955)
        ·
          refine ⟨3396553700239267836127433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2264369133492845224084955 3396553700239267836127433)
          ·
            refine ⟨2547415275179450877095575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3396553700239267836127433 2547415275179450877095575)
            ·
              refine ⟨3821122912769176315643363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2547415275179450877095575 3821122912769176315643363)
              ·
                refine ⟨5731684369153764473465045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3821122912769176315643363 5731684369153764473465045)
                ·
                  refine ⟨134336352402041354846837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5731684369153764473465045 134336352402041354846837)
                  ·
                    rfl

theorem cell22_1177286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 1, 1, 7].length) (baseStart_1177286 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1177286 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1177286 prefixEnd_1177286 := by exact prefixLift 1177286
  have htrace : WordTrace (prefixWord ++ tailWord_1177286) baseStart_1177286 baseEnd_1177286 := by
    simpa [prefixWord, tailWord_1177286, baseEnd_1177286] using wordTrace_append hprefix tailTrace_1177286
  have hstable : (prefixWord ++ tailWord_1177286).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1177286).length < 2 ^ (prefixWord ++ tailWord_1177286).sum := by decide
  have hdescent : baseEnd_1177286 < baseStart_1177286 := by decide
  rcases family_descends (prefixWord ++ tailWord_1177286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1177295 : List Nat := [1, 1, 2, 1, 1, 3, 1, 4, 3, 5]
def baseStart_1177295 : Nat := 118140960795 + 1177295 * 2 ^ 59
def prefixEnd_1177295 : Nat := 4983230072969 + 3 ^ 40 * 1177295 * 2
def baseEnd_1177295 : Nat := 403012138090051041065483

theorem tailTrace_1177295 : CollatzResearch.WordTrace tailWord_1177295 prefixEnd_1177295 403012138090051041065483 := by
  unfold tailWord_1177295
  simp only [CollatzResearch.WordTrace]
  refine ⟨42939476269868755823429339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28626317513245837215619559 42939476269868755823429339)
  ·
    refine ⟨64409214404803133735144009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42939476269868755823429339 64409214404803133735144009)
    ·
      refine ⟨48306910803602350301358007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64409214404803133735144009 48306910803602350301358007)
      ·
        refine ⟨72460366205403525452037011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48306910803602350301358007 72460366205403525452037011)
        ·
          refine ⟨108690549308105288178055517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72460366205403525452037011 108690549308105288178055517)
          ·
            refine ⟨40758955990539483066770819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 108690549308105288178055517 40758955990539483066770819)
            ·
              refine ⟨61138433985809224600156229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40758955990539483066770819 61138433985809224600156229)
              ·
                refine ⟨11463456372339229612529293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 61138433985809224600156229 11463456372339229612529293)
                ·
                  refine ⟨4298796139627211104698485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11463456372339229612529293 4298796139627211104698485)
                  ·
                    refine ⟨403012138090051041065483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4298796139627211104698485 403012138090051041065483)
                    ·
                      rfl

theorem cell22_1177295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 4, 3, 5].length) (baseStart_1177295 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1177295 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1177295 prefixEnd_1177295 := by exact prefixLift 1177295
  have htrace : WordTrace (prefixWord ++ tailWord_1177295) baseStart_1177295 baseEnd_1177295 := by
    simpa [prefixWord, tailWord_1177295, baseEnd_1177295] using wordTrace_append hprefix tailTrace_1177295
  have hstable : (prefixWord ++ tailWord_1177295).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1177295).length < 2 ^ (prefixWord ++ tailWord_1177295).sum := by decide
  have hdescent : baseEnd_1177295 < baseStart_1177295 := by decide
  rcases family_descends (prefixWord ++ tailWord_1177295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1177297 : List Nat := [1, 2, 2, 1, 2, 5, 2, 1, 6]
def baseStart_1177297 : Nat := 118140960795 + 1177297 * 2 ^ 59
def prefixEnd_1177297 : Nat := 4983230072969 + 3 ^ 40 * 1177297 * 2
def baseEnd_1177297 : Nat := 134337607576974567505159

theorem tailTrace_1177297 : CollatzResearch.WordTrace tailWord_1177297 prefixEnd_1177297 134337607576974567505159 := by
  unfold tailWord_1177297
  simp only [CollatzResearch.WordTrace]
  refine ⟨42939549215861510165002145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28626366143907673443334763 42939549215861510165002145)
  ·
    refine ⟨32204661911896132623751609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42939549215861510165002145 32204661911896132623751609)
    ·
      refine ⟨24153496433922099467813707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32204661911896132623751609 24153496433922099467813707)
      ·
        refine ⟨36230244650883149201720561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24153496433922099467813707 36230244650883149201720561)
        ·
          refine ⟨27172683488162361901290421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36230244650883149201720561 27172683488162361901290421)
          ·
            refine ⟨2547439077015221428245977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 27172683488162361901290421 2547439077015221428245977)
            ·
              refine ⟨1910579307761416071184483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2547439077015221428245977 1910579307761416071184483)
              ·
                refine ⟨2865868961642124106776725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1910579307761416071184483 2865868961642124106776725)
                ·
                  refine ⟨134337607576974567505159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2865868961642124106776725 134337607576974567505159)
                  ·
                    rfl

theorem cell22_1177297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 2, 1, 6].length) (baseStart_1177297 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1177297 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1177297 prefixEnd_1177297 := by exact prefixLift 1177297
  have htrace : WordTrace (prefixWord ++ tailWord_1177297) baseStart_1177297 baseEnd_1177297 := by
    simpa [prefixWord, tailWord_1177297, baseEnd_1177297] using wordTrace_append hprefix tailTrace_1177297
  have hstable : (prefixWord ++ tailWord_1177297).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1177297).length < 2 ^ (prefixWord ++ tailWord_1177297).sum := by decide
  have hdescent : baseEnd_1177297 < baseStart_1177297 := by decide
  rcases family_descends (prefixWord ++ tailWord_1177297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1177312 : List Nat := [2, 1, 1, 3, 1, 2, 5, 1, 1, 5]
def baseStart_1177312 : Nat := 118140960795 + 1177312 * 2 ^ 59
def prefixEnd_1177312 : Nat := 4983230072969 + 3 ^ 40 * 1177312 * 2
def baseEnd_1177312 : Nat := 403017957537468663390431

theorem tailTrace_1177312 : CollatzResearch.WordTrace tailWord_1177312 prefixEnd_1177312 403017957537468663390431 := by
  unfold tailWord_1177312
  simp only [CollatzResearch.WordTrace]
  refine ⟨21470048155403583863399095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28626730873871445151198793 21470048155403583863399095)
  ·
    refine ⟨32205072233105375795098643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21470048155403583863399095 32205072233105375795098643)
    ·
      refine ⟨48307608349658063692647965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32205072233105375795098643 48307608349658063692647965)
      ·
        refine ⟨18115353131121773884742987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48307608349658063692647965 18115353131121773884742987)
        ·
          refine ⟨27173029696682660827114481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18115353131121773884742987 27173029696682660827114481)
          ·
            refine ⟨20379772272511995620335861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27173029696682660827114481 20379772272511995620335861)
            ·
              refine ⟨1910603650547999589406487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 20379772272511995620335861 1910603650547999589406487)
              ·
                refine ⟨2865905475821999384109731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1910603650547999589406487 2865905475821999384109731)
                ·
                  refine ⟨4298858213732999076164597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2865905475821999384109731 4298858213732999076164597)
                  ·
                    refine ⟨403017957537468663390431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4298858213732999076164597 403017957537468663390431)
                    ·
                      rfl

theorem cell22_1177312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 5, 1, 1, 5].length) (baseStart_1177312 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1177312 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1177312 prefixEnd_1177312 := by exact prefixLift 1177312
  have htrace : WordTrace (prefixWord ++ tailWord_1177312) baseStart_1177312 baseEnd_1177312 := by
    simpa [prefixWord, tailWord_1177312, baseEnd_1177312] using wordTrace_append hprefix tailTrace_1177312
  have hstable : (prefixWord ++ tailWord_1177312).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1177312).length < 2 ^ (prefixWord ++ tailWord_1177312).sum := by decide
  have hdescent : baseEnd_1177312 < baseStart_1177312 := by decide
  rcases family_descends (prefixWord ++ tailWord_1177312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1177327 : List Nat := [1, 1, 2, 1, 5, 1, 2, 3, 2, 4]
def baseStart_1177327 : Nat := 118140960795 + 1177327 * 2 ^ 59
def prefixEnd_1177327 : Nat := 4983230072969 + 3 ^ 40 * 1177327 * 2
def baseEnd_1177327 : Nat := 403023092344013624265385

theorem tailTrace_1177327 : CollatzResearch.WordTrace tailWord_1177327 prefixEnd_1177327 403023092344013624265385 := by
  unfold tailWord_1177327
  simp only [CollatzResearch.WordTrace]
  refine ⟨42940643405752825288594235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28627095603835216859062823 42940643405752825288594235)
  ·
    refine ⟨64410965108629237932891353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42940643405752825288594235 64410965108629237932891353)
    ·
      refine ⟨48308223831471928449668515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64410965108629237932891353 48308223831471928449668515)
      ·
        refine ⟨72462335747207892674502773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48308223831471928449668515 72462335747207892674502773)
        ·
          refine ⟨6793343976300739938234635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 72462335747207892674502773 6793343976300739938234635)
          ·
            refine ⟨10190015964451109907351953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6793343976300739938234635 10190015964451109907351953)
            ·
              refine ⟨7642511973338332430513965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10190015964451109907351953 7642511973338332430513965)
              ·
                refine ⟨2865941990001874661442737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7642511973338332430513965 2865941990001874661442737)
                ·
                  refine ⟨2149456492501405996082053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2865941990001874661442737 2149456492501405996082053)
                  ·
                    refine ⟨403023092344013624265385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2149456492501405996082053 403023092344013624265385)
                    ·
                      rfl

theorem cell22_1177327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 3, 2, 4].length) (baseStart_1177327 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1177327 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1177327 prefixEnd_1177327 := by exact prefixLift 1177327
  have htrace : WordTrace (prefixWord ++ tailWord_1177327) baseStart_1177327 baseEnd_1177327 := by
    simpa [prefixWord, tailWord_1177327, baseEnd_1177327] using wordTrace_append hprefix tailTrace_1177327
  have hstable : (prefixWord ++ tailWord_1177327).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1177327).length < 2 ^ (prefixWord ++ tailWord_1177327).sum := by decide
  have hdescent : baseEnd_1177327 < baseStart_1177327 := by decide
  rcases family_descends (prefixWord ++ tailWord_1177327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1177346 : List Nat := [3, 4, 1, 1, 1, 1, 2, 4, 2, 3]
def baseStart_1177346 : Nat := 118140960795 + 1177346 * 2 ^ 59
def prefixEnd_1177346 : Nat := 4983230072969 + 3 ^ 40 * 1177346 * 2
def baseEnd_1177346 : Nat := 403029596432303908040327

theorem tailTrace_1177346 : CollatzResearch.WordTrace tailWord_1177346 prefixEnd_1177346 403029596432303908040327 := by
  unfold tailWord_1177346
  simp only [CollatzResearch.WordTrace]
  refine ⟨10735334098170997883383973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28627557595122661022357261 10735334098170997883383973)
  ·
    refine ⟨2012875143407062103134495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10735334098170997883383973 2012875143407062103134495)
    ·
      refine ⟨3019312715110593154701743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2012875143407062103134495 3019312715110593154701743)
      ·
        refine ⟨4528969072665889732052615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3019312715110593154701743 4528969072665889732052615)
        ·
          refine ⟨6793453608998834598078923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4528969072665889732052615 6793453608998834598078923)
          ·
            refine ⟨10190180413498251897118385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6793453608998834598078923 10190180413498251897118385)
            ·
              refine ⟨7642635310123688922838789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10190180413498251897118385 7642635310123688922838789)
              ·
                refine ⟨1432994120648191673032273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7642635310123688922838789 1432994120648191673032273)
                ·
                  refine ⟨1074745590486143754774205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1432994120648191673032273 1074745590486143754774205)
                  ·
                    refine ⟨403029596432303908040327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1074745590486143754774205 403029596432303908040327)
                    ·
                      rfl

theorem cell22_1177346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 4, 2, 3].length) (baseStart_1177346 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1177346 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1177346 prefixEnd_1177346 := by exact prefixLift 1177346
  have htrace : WordTrace (prefixWord ++ tailWord_1177346) baseStart_1177346 baseEnd_1177346 := by
    simpa [prefixWord, tailWord_1177346, baseEnd_1177346] using wordTrace_append hprefix tailTrace_1177346
  have hstable : (prefixWord ++ tailWord_1177346).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1177346).length < 2 ^ (prefixWord ++ tailWord_1177346).sum := by decide
  have hdescent : baseEnd_1177346 < baseStart_1177346 := by decide
  rcases family_descends (prefixWord ++ tailWord_1177346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1177417 : List Nat := [1, 2, 1, 1, 2, 4, 1, 1, 5, 4]
def baseStart_1177417 : Nat := 118140960795 + 1177417 * 2 ^ 59
def prefixEnd_1177417 : Nat := 4983230072969 + 3 ^ 40 * 1177417 * 2
def baseEnd_1177417 : Nat := 403053901183283389515109

theorem tailTrace_1177417 : CollatzResearch.WordTrace tailWord_1177417 prefixEnd_1177417 403053901183283389515109 := by
  unfold tailWord_1177417
  simp only [CollatzResearch.WordTrace]
  refine ⟨42943925975426770659370505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28629283983617847106247003 42943925975426770659370505)
  ·
    refine ⟨32207944481570077994527879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42943925975426770659370505 32207944481570077994527879)
    ·
      refine ⟨48311916722355116991791819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32207944481570077994527879 48311916722355116991791819)
      ·
        refine ⟨72467875083532675487687729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48311916722355116991791819 72467875083532675487687729)
        ·
          refine ⟨54350906312649506615765797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72467875083532675487687729 54350906312649506615765797)
          ·
            refine ⟨10190794933621782490456087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 54350906312649506615765797 10190794933621782490456087)
            ·
              refine ⟨15286192400432673735684131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10190794933621782490456087 15286192400432673735684131)
              ·
                refine ⟨22929288600649010603526197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15286192400432673735684131 22929288600649010603526197)
                ·
                  refine ⟨2149620806310844744080581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 22929288600649010603526197 2149620806310844744080581)
                  ·
                    refine ⟨403053901183283389515109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2149620806310844744080581 403053901183283389515109)
                    ·
                      rfl

theorem cell22_1177417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 1, 5, 4].length) (baseStart_1177417 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1177417 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1177417 prefixEnd_1177417 := by exact prefixLift 1177417
  have htrace : WordTrace (prefixWord ++ tailWord_1177417) baseStart_1177417 baseEnd_1177417 := by
    simpa [prefixWord, tailWord_1177417, baseEnd_1177417] using wordTrace_append hprefix tailTrace_1177417
  have hstable : (prefixWord ++ tailWord_1177417).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1177417).length < 2 ^ (prefixWord ++ tailWord_1177417).sum := by decide
  have hdescent : baseEnd_1177417 < baseStart_1177417 := by decide
  rcases family_descends (prefixWord ++ tailWord_1177417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1177421 : List Nat := [1, 6, 1, 2, 1, 1, 2, 3, 5]
def baseStart_1177421 : Nat := 118140960795 + 1177421 * 2 ^ 59
def prefixEnd_1177421 : Nat := 4983230072969 + 3 ^ 40 * 1177421 * 2
def baseEnd_1177421 : Nat := 134351756821676237471699

theorem tailTrace_1177421 : CollatzResearch.WordTrace tailWord_1177421 prefixEnd_1177421 134351756821676237471699 := by
  unfold tailWord_1177421
  simp only [CollatzResearch.WordTrace]
  refine ⟨42944071867412279342516117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28629381244941519561677411 42944071867412279342516117)
  ·
    refine ⟨2013003368784950594180443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 42944071867412279342516117 2013003368784950594180443)
    ·
      refine ⟨3019505053177425891270665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2013003368784950594180443 3019505053177425891270665)
      ·
        refine ⟨2264628789883069418452999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3019505053177425891270665 2264628789883069418452999)
        ·
          refine ⟨3396943184824604127679499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2264628789883069418452999 3396943184824604127679499)
          ·
            refine ⟨5095414777236906191519249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3396943184824604127679499 5095414777236906191519249)
            ·
              refine ⟨3821561082927679643639437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5095414777236906191519249 3821561082927679643639437)
              ·
                refine ⟨1433085406097879866364789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3821561082927679643639437 1433085406097879866364789)
                ·
                  refine ⟨134351756821676237471699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1433085406097879866364789 134351756821676237471699)
                  ·
                    rfl

theorem cell22_1177421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 2, 3, 5].length) (baseStart_1177421 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1177421 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1177421 prefixEnd_1177421 := by exact prefixLift 1177421
  have htrace : WordTrace (prefixWord ++ tailWord_1177421) baseStart_1177421 baseEnd_1177421 := by
    simpa [prefixWord, tailWord_1177421, baseEnd_1177421] using wordTrace_append hprefix tailTrace_1177421
  have hstable : (prefixWord ++ tailWord_1177421).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1177421).length < 2 ^ (prefixWord ++ tailWord_1177421).sum := by decide
  have hdescent : baseEnd_1177421 < baseStart_1177421 := by decide
  rcases family_descends (prefixWord ++ tailWord_1177421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1177434 : List Nat := [3, 1, 1, 2, 1, 3, 2, 4, 1, 4]
def baseStart_1177434 : Nat := 118140960795 + 1177434 * 2 ^ 59
def prefixEnd_1177434 : Nat := 4983230072969 + 3 ^ 40 * 1177434 * 2
def baseEnd_1177434 : Nat := 403059720630701011840057

theorem tailTrace_1177434 : CollatzResearch.WordTrace tailWord_1177434 prefixEnd_1177434 403059720630701011840057 := by
  unfold tailWord_1177434
  simp only [CollatzResearch.WordTrace]
  refine ⟨10736136504091295640684839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28629697344243455041826237 10736136504091295640684839)
  ·
    refine ⟨16104204756136943461027259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10736136504091295640684839 16104204756136943461027259)
    ·
      refine ⟨24156307134205415191540889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16104204756136943461027259 24156307134205415191540889)
      ·
        refine ⟨18117230350654061393655667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24156307134205415191540889 18117230350654061393655667)
        ·
          refine ⟨27175845525981092090483501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18117230350654061393655667 27175845525981092090483501)
          ·
            refine ⟨10190942072242909533931313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27175845525981092090483501 10190942072242909533931313)
            ·
              refine ⟨7643206554182182150448485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10190942072242909533931313 7643206554182182150448485)
              ·
                refine ⟨1433101228909159153209091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7643206554182182150448485 1433101228909159153209091)
                ·
                  refine ⟨2149651843363738729813637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1433101228909159153209091 2149651843363738729813637)
                  ·
                    refine ⟨403059720630701011840057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2149651843363738729813637 403059720630701011840057)
                    ·
                      rfl

theorem cell22_1177434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 4, 1, 4].length) (baseStart_1177434 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1177434 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1177434 prefixEnd_1177434 := by exact prefixLift 1177434
  have htrace : WordTrace (prefixWord ++ tailWord_1177434) baseStart_1177434 baseEnd_1177434 := by
    simpa [prefixWord, tailWord_1177434, baseEnd_1177434] using wordTrace_append hprefix tailTrace_1177434
  have hstable : (prefixWord ++ tailWord_1177434).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1177434).length < 2 ^ (prefixWord ++ tailWord_1177434).sum := by decide
  have hdescent : baseEnd_1177434 < baseStart_1177434 := by decide
  rcases family_descends (prefixWord ++ tailWord_1177434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1177477 : List Nat := [1, 3, 1, 1, 3, 2, 2, 9]
def baseStart_1177477 : Nat := 118140960795 + 1177477 * 2 ^ 59
def prefixEnd_1177477 : Nat := 4983230072969 + 3 ^ 40 * 1177477 * 2
def baseEnd_1177477 : Nat := 44786048934384803668325

theorem tailTrace_1177477 : CollatzResearch.WordTrace tailWord_1177477 prefixEnd_1177477 44786048934384803668325 := by
  unfold tailWord_1177477
  simp only [CollatzResearch.WordTrace]
  refine ⟨42946114355209400906554685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28630742903472933937703123 42946114355209400906554685)
  ·
    refine ⟨16104792883203525339958007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42946114355209400906554685 16104792883203525339958007)
    ·
      refine ⟨24157189324805288009937011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16104792883203525339958007 24157189324805288009937011)
      ·
        refine ⟨36235783987207932014905517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24157189324805288009937011 36235783987207932014905517)
        ·
          refine ⟨13588418995202974505589569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36235783987207932014905517 13588418995202974505589569)
          ·
            refine ⟨10191314246402230879192177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13588418995202974505589569 10191314246402230879192177)
            ·
              refine ⟨7643485684801673159394133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10191314246402230879192177 7643485684801673159394133)
              ·
                refine ⟨44786048934384803668325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 7643485684801673159394133 44786048934384803668325)
                ·
                  rfl

theorem cell22_1177477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 9].length) (baseStart_1177477 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1177477 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1177477 prefixEnd_1177477 := by exact prefixLift 1177477
  have htrace : WordTrace (prefixWord ++ tailWord_1177477) baseStart_1177477 baseEnd_1177477 := by
    simpa [prefixWord, tailWord_1177477, baseEnd_1177477] using wordTrace_append hprefix tailTrace_1177477
  have hstable : (prefixWord ++ tailWord_1177477).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1177477).length < 2 ^ (prefixWord ++ tailWord_1177477).sum := by decide
  have hdescent : baseEnd_1177477 < baseStart_1177477 := by decide
  rcases family_descends (prefixWord ++ tailWord_1177477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1177507 : List Nat := [1, 1, 1, 4, 1, 2, 1, 2, 1, 8]
def baseStart_1177507 : Nat := 118140960795 + 1177507 * 2 ^ 59
def prefixEnd_1177507 : Nat := 4983230072969 + 3 ^ 40 * 1177507 * 2
def baseEnd_1177507 : Nat := 403084710022553154764833

theorem tailTrace_1177507 : CollatzResearch.WordTrace tailWord_1177507 prefixEnd_1177507 403084710022553154764833 := by
  unfold tailWord_1177507
  simp only [CollatzResearch.WordTrace]
  refine ⟨42947208545100716030146775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28631472363400477353431183 42947208545100716030146775)
  ·
    refine ⟨64420812817651074045220163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42947208545100716030146775 64420812817651074045220163)
    ·
      refine ⟨96631219226476611067830245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64420812817651074045220163 96631219226476611067830245)
      ·
        refine ⟨18118353604964364575218171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 96631219226476611067830245 18118353604964364575218171)
        ·
          refine ⟨27177530407446546862827257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18118353604964364575218171 27177530407446546862827257)
          ·
            refine ⟨20383147805584910147120443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27177530407446546862827257 20383147805584910147120443)
            ·
              refine ⟨30574721708377365220680665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20383147805584910147120443 30574721708377365220680665)
              ·
                refine ⟨22931041281283023915510499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30574721708377365220680665 22931041281283023915510499)
                ·
                  refine ⟨34396561921924535873265749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22931041281283023915510499 34396561921924535873265749)
                  ·
                    refine ⟨403084710022553154764833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 34396561921924535873265749 403084710022553154764833)
                    ·
                      rfl

theorem cell22_1177507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 2, 1, 8].length) (baseStart_1177507 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1177507 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1177507 prefixEnd_1177507 := by exact prefixLift 1177507
  have htrace : WordTrace (prefixWord ++ tailWord_1177507) baseStart_1177507 baseEnd_1177507 := by
    simpa [prefixWord, tailWord_1177507, baseEnd_1177507] using wordTrace_append hprefix tailTrace_1177507
  have hstable : (prefixWord ++ tailWord_1177507).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1177507).length < 2 ^ (prefixWord ++ tailWord_1177507).sum := by decide
  have hdescent : baseEnd_1177507 < baseStart_1177507 := by decide
  rcases family_descends (prefixWord ++ tailWord_1177507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1177509 : List Nat := [1, 3, 1, 2, 1, 1, 1, 4, 5, 3]
def baseStart_1177509 : Nat := 118140960795 + 1177509 * 2 ^ 59
def prefixEnd_1177509 : Nat := 4983230072969 + 3 ^ 40 * 1177509 * 2
def baseEnd_1177509 : Nat := 403085394663425816214827

theorem tailTrace_1177509 : CollatzResearch.WordTrace tailWord_1177509 prefixEnd_1177509 403085394663425816214827 := by
  unfold tailWord_1177509
  simp only [CollatzResearch.WordTrace]
  refine ⟨42947281491093470371719581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28631520994062313581146387 42947281491093470371719581)
  ·
    refine ⟨16105230559160051389394843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42947281491093470371719581 16105230559160051389394843)
    ·
      refine ⟨24157845838740077084092265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16105230559160051389394843 24157845838740077084092265)
      ·
        refine ⟨18118384379055057813069199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24157845838740077084092265 18118384379055057813069199)
        ·
          refine ⟨27177576568582586719603799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18118384379055057813069199 27177576568582586719603799)
          ·
            refine ⟨40766364852873880079405699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27177576568582586719603799 40766364852873880079405699)
            ·
              refine ⟨61149547279310820119108549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40766364852873880079405699 61149547279310820119108549)
              ·
                refine ⟨11465540114870778772332853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 61149547279310820119108549 11465540114870778772332853)
                ·
                  refine ⟨1074894385769135509906205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 11465540114870778772332853 1074894385769135509906205)
                  ·
                    refine ⟨403085394663425816214827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1074894385769135509906205 403085394663425816214827)
                    ·
                      rfl

theorem cell22_1177509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 4, 5, 3].length) (baseStart_1177509 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1177509 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1177509 prefixEnd_1177509 := by exact prefixLift 1177509
  have htrace : WordTrace (prefixWord ++ tailWord_1177509) baseStart_1177509 baseEnd_1177509 := by
    simpa [prefixWord, tailWord_1177509, baseEnd_1177509] using wordTrace_append hprefix tailTrace_1177509
  have hstable : (prefixWord ++ tailWord_1177509).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1177509).length < 2 ^ (prefixWord ++ tailWord_1177509).sum := by decide
  have hdescent : baseEnd_1177509 < baseStart_1177509 := by decide
  rcases family_descends (prefixWord ++ tailWord_1177509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1177532 : List Nat := [2, 2, 2, 5, 1, 2, 2, 1, 2, 3]
def baseStart_1177532 : Nat := 118140960795 + 1177532 * 2 ^ 59
def prefixEnd_1177532 : Nat := 4983230072969 + 3 ^ 40 * 1177532 * 2
def baseEnd_1177532 : Nat := 403093268033461422889757

theorem tailTrace_1177532 : CollatzResearch.WordTrace tailWord_1177532 prefixEnd_1177532 403093268033461422889757 := by
  unfold tailWord_1177532
  simp only [CollatzResearch.WordTrace]
  refine ⟨21474060185005072649903425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28632080246673430199871233 21474060185005072649903425)
  ·
    refine ⟨16105545138753804487427569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21474060185005072649903425 16105545138753804487427569)
    ·
      refine ⟨12079158854065353365570677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16105545138753804487427569 12079158854065353365570677)
      ·
        refine ⟨1132421142568626878022251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 12079158854065353365570677 1132421142568626878022251)
        ·
          refine ⟨1698631713852940317033377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1132421142568626878022251 1698631713852940317033377)
          ·
            refine ⟨1273973785389705237775033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1698631713852940317033377 1273973785389705237775033)
            ·
              refine ⟨955480339042278928331275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1273973785389705237775033 955480339042278928331275)
              ·
                refine ⟨1433220508563418392496913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 955480339042278928331275 1433220508563418392496913)
                ·
                  refine ⟨1074915381422563794372685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1433220508563418392496913 1074915381422563794372685)
                  ·
                    refine ⟨403093268033461422889757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1074915381422563794372685 403093268033461422889757)
                    ·
                      rfl

theorem cell22_1177532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 2, 2, 1, 2, 3].length) (baseStart_1177532 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1177532 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1177532 prefixEnd_1177532 := by exact prefixLift 1177532
  have htrace : WordTrace (prefixWord ++ tailWord_1177532) baseStart_1177532 baseEnd_1177532 := by
    simpa [prefixWord, tailWord_1177532, baseEnd_1177532] using wordTrace_append hprefix tailTrace_1177532
  have hstable : (prefixWord ++ tailWord_1177532).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1177532).length < 2 ^ (prefixWord ++ tailWord_1177532).sum := by decide
  have hdescent : baseEnd_1177532 < baseStart_1177532 := by decide
  rcases family_descends (prefixWord ++ tailWord_1177532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1177633 : List Nat := [1, 2, 3, 2, 4, 1, 1, 1, 4, 3]
def baseStart_1177633 : Nat := 118140960795 + 1177633 * 2 ^ 59
def prefixEnd_1177633 : Nat := 4983230072969 + 3 ^ 40 * 1177633 * 2
def baseEnd_1177633 : Nat := 403127842397530826114447

theorem tailTrace_1177633 : CollatzResearch.WordTrace tailWord_1177633 prefixEnd_1177633 403127842397530826114447 := by
  unfold tailWord_1177633
  simp only [CollatzResearch.WordTrace]
  refine ⟨42951804142644239549233553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28634536095096159699489035 42951804142644239549233553)
  ·
    refine ⟨32213853106983179661925165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42951804142644239549233553 32213853106983179661925165)
    ·
      refine ⟨12080194915118692373221937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32213853106983179661925165 12080194915118692373221937)
      ·
        refine ⟨9060146186339019279916453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12080194915118692373221937 9060146186339019279916453)
        ·
          refine ⟨1698777409938566114984335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9060146186339019279916453 1698777409938566114984335)
          ·
            refine ⟨2548166114907849172476503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1698777409938566114984335 2548166114907849172476503)
            ·
              refine ⟨3822249172361773758714755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2548166114907849172476503 3822249172361773758714755)
              ·
                refine ⟨5733373758542660638072133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3822249172361773758714755 5733373758542660638072133)
                ·
                  refine ⟨1075007579726748869638525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5733373758542660638072133 1075007579726748869638525)
                  ·
                    refine ⟨403127842397530826114447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1075007579726748869638525 403127842397530826114447)
                    ·
                      rfl

theorem cell22_1177633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 1, 1, 4, 3].length) (baseStart_1177633 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1177633 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1177633 prefixEnd_1177633 := by exact prefixLift 1177633
  have htrace : WordTrace (prefixWord ++ tailWord_1177633) baseStart_1177633 baseEnd_1177633 := by
    simpa [prefixWord, tailWord_1177633, baseEnd_1177633] using wordTrace_append hprefix tailTrace_1177633
  have hstable : (prefixWord ++ tailWord_1177633).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1177633).length < 2 ^ (prefixWord ++ tailWord_1177633).sum := by decide
  have hdescent : baseEnd_1177633 < baseStart_1177633 := by decide
  rcases family_descends (prefixWord ++ tailWord_1177633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1177650 : List Nat := [3, 2, 1, 1, 2, 4, 3, 1, 2, 3]
def baseStart_1177650 : Nat := 118140960795 + 1177650 * 2 ^ 59
def prefixEnd_1177650 : Nat := 4983230072969 + 3 ^ 40 * 1177650 * 2
def baseEnd_1177650 : Nat := 403133661844948448439395

theorem tailTrace_1177650 : CollatzResearch.WordTrace tailWord_1177650 prefixEnd_1177650 403133661844948448439395 := by
  unfold tailWord_1177650
  simp only [CollatzResearch.WordTrace]
  refine ⟨10738106045895662863150601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28634949455721767635068269 10738106045895662863150601)
  ·
    refine ⟨8053579534421747147362951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10738106045895662863150601 8053579534421747147362951)
    ·
      refine ⟨12080369301632620721044427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8053579534421747147362951 12080369301632620721044427)
      ·
        refine ⟨18120553952448931081566641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12080369301632620721044427 18120553952448931081566641)
        ·
          refine ⟨13590415464336698311174981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18120553952448931081566641 13590415464336698311174981)
          ·
            refine ⟨2548202899563130933345309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13590415464336698311174981 2548202899563130933345309)
            ·
              refine ⟨955576087336174100004491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2548202899563130933345309 955576087336174100004491)
              ·
                refine ⟨1433364131004261150006737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 955576087336174100004491 1433364131004261150006737)
                ·
                  refine ⟨1075023098253195862505053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1433364131004261150006737 1075023098253195862505053)
                  ·
                    refine ⟨403133661844948448439395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1075023098253195862505053 403133661844948448439395)
                    ·
                      rfl

theorem cell22_1177650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 3, 1, 2, 3].length) (baseStart_1177650 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1177650 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1177650 prefixEnd_1177650 := by exact prefixLift 1177650
  have htrace : WordTrace (prefixWord ++ tailWord_1177650) baseStart_1177650 baseEnd_1177650 := by
    simpa [prefixWord, tailWord_1177650, baseEnd_1177650] using wordTrace_append hprefix tailTrace_1177650
  have hstable : (prefixWord ++ tailWord_1177650).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1177650).length < 2 ^ (prefixWord ++ tailWord_1177650).sum := by decide
  have hdescent : baseEnd_1177650 < baseStart_1177650 := by decide
  rcases family_descends (prefixWord ++ tailWord_1177650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1177708 : List Nat := [2, 2, 1, 1, 3, 3, 4, 1, 5]
def baseStart_1177708 : Nat := 118140960795 + 1177708 * 2 ^ 59
def prefixEnd_1177708 : Nat := 4983230072969 + 3 ^ 40 * 1177708 * 2
def baseEnd_1177708 : Nat := 134384505476751876829739

theorem tailTrace_1177708 : CollatzResearch.WordTrace tailWord_1177708 prefixEnd_1177708 134384505476751876829739 := by
  unfold tailWord_1177708
  simp only [CollatzResearch.WordTrace]
  refine ⟨21477269808686263679106889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28636359744915018238809185 21477269808686263679106889)
  ·
    refine ⟨16107952356514697759330167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21477269808686263679106889 16107952356514697759330167)
    ·
      refine ⟨24161928534772046638995251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16107952356514697759330167 24161928534772046638995251)
      ·
        refine ⟨36242892802158069958492877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24161928534772046638995251 36242892802158069958492877)
        ·
          refine ⟨13591084800809276234434829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36242892802158069958492877 13591084800809276234434829)
          ·
            refine ⟨5096656800303478587913061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13591084800809276234434829 5096656800303478587913061)
            ·
              refine ⟨955623150056902235233699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5096656800303478587913061 955623150056902235233699)
              ·
                refine ⟨1433434725085353352850549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 955623150056902235233699 1433434725085353352850549)
                ·
                  refine ⟨134384505476751876829739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1433434725085353352850549 134384505476751876829739)
                  ·
                    rfl

theorem cell22_1177708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 5].length) (baseStart_1177708 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1177708 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1177708 prefixEnd_1177708 := by exact prefixLift 1177708
  have htrace : WordTrace (prefixWord ++ tailWord_1177708) baseStart_1177708 baseEnd_1177708 := by
    simpa [prefixWord, tailWord_1177708, baseEnd_1177708] using wordTrace_append hprefix tailTrace_1177708
  have hstable : (prefixWord ++ tailWord_1177708).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1177708).length < 2 ^ (prefixWord ++ tailWord_1177708).sum := by decide
  have hdescent : baseEnd_1177708 < baseStart_1177708 := by decide
  rcases family_descends (prefixWord ++ tailWord_1177708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1177770 : List Nat := [3, 1, 5, 1, 2, 1, 1, 2, 6]
def baseStart_1177770 : Nat := 118140960795 + 1177770 * 2 ^ 59
def prefixEnd_1177770 : Nat := 4983230072969 + 3 ^ 40 * 1177770 * 2
def baseEnd_1177770 : Nat := 134391580099102711813009

theorem tailTrace_1177770 : CollatzResearch.WordTrace tailWord_1177770 prefixEnd_1177770 134391580099102711813009 := by
  unfold tailWord_1177770
  simp only [CollatzResearch.WordTrace]
  refine ⟨10739200235786977986742691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28637867295431941297980509 10739200235786977986742691)
  ·
    refine ⟨16108800353680466980114037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10739200235786977986742691 16108800353680466980114037)
    ·
      refine ⟨1510200033157543779385691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 16108800353680466980114037 1510200033157543779385691)
      ·
        refine ⟨2265300049736315669078537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1510200033157543779385691 2265300049736315669078537)
        ·
          refine ⟨1698975037302236751808903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2265300049736315669078537 1698975037302236751808903)
          ·
            refine ⟨2548462555953355127713355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1698975037302236751808903 2548462555953355127713355)
            ·
              refine ⟨3822693833930032691570033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2548462555953355127713355 3822693833930032691570033)
              ·
                refine ⟨2867020375447524518677525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3822693833930032691570033 2867020375447524518677525)
                ·
                  refine ⟨134391580099102711813009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2867020375447524518677525 134391580099102711813009)
                  ·
                    rfl

theorem cell22_1177770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 1, 2, 6].length) (baseStart_1177770 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1177770 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1177770 prefixEnd_1177770 := by exact prefixLift 1177770
  have htrace : WordTrace (prefixWord ++ tailWord_1177770) baseStart_1177770 baseEnd_1177770 := by
    simpa [prefixWord, tailWord_1177770, baseEnd_1177770] using wordTrace_append hprefix tailTrace_1177770
  have hstable : (prefixWord ++ tailWord_1177770).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1177770).length < 2 ^ (prefixWord ++ tailWord_1177770).sum := by decide
  have hdescent : baseEnd_1177770 < baseStart_1177770 := by decide
  rcases family_descends (prefixWord ++ tailWord_1177770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1177783 : List Nat := [1, 1, 3, 1, 4, 2, 3, 1, 2, 4]
def baseStart_1177783 : Nat := 118140960795 + 1177783 * 2 ^ 59
def prefixEnd_1177783 : Nat := 4983230072969 + 3 ^ 40 * 1177783 * 2
def baseEnd_1177783 : Nat := 403179190462980434863987

theorem tailTrace_1177783 : CollatzResearch.WordTrace tailWord_1177783 prefixEnd_1177783 403179190462980434863987 := by
  unfold tailWord_1177783
  simp only [CollatzResearch.WordTrace]
  refine ⟨42957275092100815167194003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28638183394733876778129335 42957275092100815167194003)
  ·
    refine ⟨64435912638151222750791005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42957275092100815167194003 64435912638151222750791005)
    ·
      refine ⟨24163467239306708531546627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64435912638151222750791005 24163467239306708531546627)
      ·
        refine ⟨36245200858960062797319941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24163467239306708531546627 36245200858960062797319941)
        ·
          refine ⟨6795975161055011774497489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 36245200858960062797319941 6795975161055011774497489)
          ·
            refine ⟨5096981370791258830873117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6795975161055011774497489 5096981370791258830873117)
            ·
              refine ⟨1911368014046722061577419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5096981370791258830873117 1911368014046722061577419)
              ·
                refine ⟨2867052021070083092366129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1911368014046722061577419 2867052021070083092366129)
                ·
                  refine ⟨2150289015802562319274597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2867052021070083092366129 2150289015802562319274597)
                  ·
                    refine ⟨403179190462980434863987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2150289015802562319274597 403179190462980434863987)
                    ·
                      rfl

theorem cell22_1177783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 3, 1, 2, 4].length) (baseStart_1177783 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1177783 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1177783 prefixEnd_1177783 := by exact prefixLift 1177783
  have htrace : WordTrace (prefixWord ++ tailWord_1177783) baseStart_1177783 baseEnd_1177783 := by
    simpa [prefixWord, tailWord_1177783, baseEnd_1177783] using wordTrace_append hprefix tailTrace_1177783
  have hstable : (prefixWord ++ tailWord_1177783).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1177783).length < 2 ^ (prefixWord ++ tailWord_1177783).sum := by decide
  have hdescent : baseEnd_1177783 < baseStart_1177783 := by decide
  rcases family_descends (prefixWord ++ tailWord_1177783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1177841 : List Nat := [1, 2, 2, 2, 2, 1, 2, 2, 1, 7]
def baseStart_1177841 : Nat := 118140960795 + 1177841 * 2 ^ 59
def prefixEnd_1177841 : Nat := 4983230072969 + 3 ^ 40 * 1177841 * 2
def baseEnd_1177841 : Nat := 403199045048287616913809

theorem tailTrace_1177841 : CollatzResearch.WordTrace tailWord_1177841 prefixEnd_1177841 403199045048287616913809 := by
  unfold tailWord_1177841
  simp only [CollatzResearch.WordTrace]
  refine ⟨42959390525890691072805377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28639593683927127381870251 42959390525890691072805377)
  ·
    refine ⟨32219542894418018304604033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42959390525890691072805377 32219542894418018304604033)
    ·
      refine ⟨24164657170813513728453025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32219542894418018304604033 24164657170813513728453025)
      ·
        refine ⟨18123492878110135296339769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24164657170813513728453025 18123492878110135296339769)
        ·
          refine ⟨13592619658582601472254827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18123492878110135296339769 13592619658582601472254827)
          ·
            refine ⟨20388929487873902208382241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13592619658582601472254827 20388929487873902208382241)
            ·
              refine ⟨15291697115905426656286681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20388929487873902208382241 15291697115905426656286681)
              ·
                refine ⟨11468772836929069992215011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15291697115905426656286681 11468772836929069992215011)
                ·
                  refine ⟨17203159255393604988322517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11468772836929069992215011 17203159255393604988322517)
                  ·
                    refine ⟨403199045048287616913809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 17203159255393604988322517 403199045048287616913809)
                    ·
                      rfl

theorem cell22_1177841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 2, 1, 7].length) (baseStart_1177841 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1177841 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1177841 prefixEnd_1177841 := by exact prefixLift 1177841
  have htrace : WordTrace (prefixWord ++ tailWord_1177841) baseStart_1177841 baseEnd_1177841 := by
    simpa [prefixWord, tailWord_1177841, baseEnd_1177841] using wordTrace_append hprefix tailTrace_1177841
  have hstable : (prefixWord ++ tailWord_1177841).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1177841).length < 2 ^ (prefixWord ++ tailWord_1177841).sum := by decide
  have hdescent : baseEnd_1177841 < baseStart_1177841 := by decide
  rcases family_descends (prefixWord ++ tailWord_1177841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1177864 : List Nat := [2, 1, 3, 2, 3, 2, 3, 2, 1, 3]
def baseStart_1177864 : Nat := 118140960795 + 1177864 * 2 ^ 59
def prefixEnd_1177864 : Nat := 4983230072969 + 3 ^ 40 * 1177864 * 2
def baseEnd_1177864 : Nat := 403206918418323223588739

theorem tailTrace_1177864 : CollatzResearch.WordTrace tailWord_1177864 prefixEnd_1177864 403206918418323223588739 := by
  unfold tailWord_1177864
  simp only [CollatzResearch.WordTrace]
  refine ⟨21480114702403683000446323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28640152936538244000595097 21480114702403683000446323)
  ·
    refine ⟨32220172053605524500669485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21480114702403683000446323 32220172053605524500669485)
    ·
      refine ⟨12082564520102071687751057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32220172053605524500669485 12082564520102071687751057)
      ·
        refine ⟨9061923390076553765813293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12082564520102071687751057 9061923390076553765813293)
        ·
          refine ⟨3398221271278707662179985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9061923390076553765813293 3398221271278707662179985)
          ·
            refine ⟨2548665953459030746634989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3398221271278707662179985 2548665953459030746634989)
            ·
              refine ⟨955749732547136529988121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2548665953459030746634989 955749732547136529988121)
              ·
                refine ⟨716812299410352397491091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 955749732547136529988121 716812299410352397491091)
                ·
                  refine ⟨1075218449115528596236637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 716812299410352397491091 1075218449115528596236637)
                  ·
                    refine ⟨403206918418323223588739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1075218449115528596236637 403206918418323223588739)
                    ·
                      rfl

theorem cell22_1177864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 3, 2, 1, 3].length) (baseStart_1177864 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1177864 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1177864 prefixEnd_1177864 := by exact prefixLift 1177864
  have htrace : WordTrace (prefixWord ++ tailWord_1177864) baseStart_1177864 baseEnd_1177864 := by
    simpa [prefixWord, tailWord_1177864, baseEnd_1177864] using wordTrace_append hprefix tailTrace_1177864
  have hstable : (prefixWord ++ tailWord_1177864).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1177864).length < 2 ^ (prefixWord ++ tailWord_1177864).sum := by decide
  have hdescent : baseEnd_1177864 < baseStart_1177864 := by decide
  rcases family_descends (prefixWord ++ tailWord_1177864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1177890 : List Nat := [3, 3, 1, 1, 3, 2, 1, 1, 3, 4]
def baseStart_1177890 : Nat := 118140960795 + 1177890 * 2 ^ 59
def prefixEnd_1177890 : Nat := 4983230072969 + 3 ^ 40 * 1177890 * 2
def baseEnd_1177890 : Nat := 403215818749667822438659

theorem tailTrace_1177890 : CollatzResearch.WordTrace tailWord_1177890 prefixEnd_1177890 403215818749667822438659 := by
  unfold tailWord_1177890
  simp only [CollatzResearch.WordTrace]
  refine ⟨10740294425678293110334781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28640785135142114960892749 10740294425678293110334781)
  ·
    refine ⟨4027610409629359916375543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10740294425678293110334781 4027610409629359916375543)
    ·
      refine ⟨6041415614444039874563315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4027610409629359916375543 6041415614444039874563315)
      ·
        refine ⟨9062123421666059811844973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6041415614444039874563315 9062123421666059811844973)
        ·
          refine ⟨3398296283124772429441865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9062123421666059811844973 3398296283124772429441865)
          ·
            refine ⟨2548722212343579322081399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3398296283124772429441865 2548722212343579322081399)
            ·
              refine ⟨3823083318515368983122099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2548722212343579322081399 3823083318515368983122099)
              ·
                refine ⟨5734624977773053474683149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3823083318515368983122099 5734624977773053474683149)
                ·
                  refine ⟨2150484366664895053006181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5734624977773053474683149 2150484366664895053006181)
                  ·
                    refine ⟨403215818749667822438659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2150484366664895053006181 403215818749667822438659)
                    ·
                      rfl

theorem cell22_1177890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 1, 1, 3, 4].length) (baseStart_1177890 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1177890 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1177890 prefixEnd_1177890 := by exact prefixLift 1177890
  have htrace : WordTrace (prefixWord ++ tailWord_1177890) baseStart_1177890 baseEnd_1177890 := by
    simpa [prefixWord, tailWord_1177890, baseEnd_1177890] using wordTrace_append hprefix tailTrace_1177890
  have hstable : (prefixWord ++ tailWord_1177890).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1177890).length < 2 ^ (prefixWord ++ tailWord_1177890).sum := by decide
  have hdescent : baseEnd_1177890 < baseStart_1177890 := by decide
  rcases family_descends (prefixWord ++ tailWord_1177890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1177903 : List Nat := [1, 1, 2, 1, 2, 1, 4, 1, 6, 3]
def baseStart_1177903 : Nat := 118140960795 + 1177903 * 2 ^ 59
def prefixEnd_1177903 : Nat := 4983230072969 + 3 ^ 40 * 1177903 * 2
def baseEnd_1177903 : Nat := 403220268915340121863619

theorem tailTrace_1177903 : CollatzResearch.WordTrace tailWord_1177903 prefixEnd_1177903 403220268915340121863619 := by
  unfold tailWord_1177903
  simp only [CollatzResearch.WordTrace]
  refine ⟨42961651851666075661562363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28641101234444050441041575 42961651851666075661562363)
  ·
    refine ⟨64442477777499113492343545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42961651851666075661562363 64442477777499113492343545)
    ·
      refine ⟨48331858333124335119257659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64442477777499113492343545 48331858333124335119257659)
      ·
        refine ⟨72497787499686502678886489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48331858333124335119257659 72497787499686502678886489)
        ·
          refine ⟨54373340624764877009164867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72497787499686502678886489 54373340624764877009164867)
          ·
            refine ⟨81560010937147315513747301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54373340624764877009164867 81560010937147315513747301)
            ·
              refine ⟨15292502050715121658827619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 81560010937147315513747301 15292502050715121658827619)
              ·
                refine ⟨22938753076072682488241429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15292502050715121658827619 22938753076072682488241429)
                ·
                  refine ⟨1075254050440906991636317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 22938753076072682488241429 1075254050440906991636317)
                  ·
                    refine ⟨403220268915340121863619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1075254050440906991636317 403220268915340121863619)
                    ·
                      rfl

theorem cell22_1177903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 1, 6, 3].length) (baseStart_1177903 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1177903 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1177903 prefixEnd_1177903 := by exact prefixLift 1177903
  have htrace : WordTrace (prefixWord ++ tailWord_1177903) baseStart_1177903 baseEnd_1177903 := by
    simpa [prefixWord, tailWord_1177903, baseEnd_1177903] using wordTrace_append hprefix tailTrace_1177903
  have hstable : (prefixWord ++ tailWord_1177903).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1177903).length < 2 ^ (prefixWord ++ tailWord_1177903).sum := by decide
  have hdescent : baseEnd_1177903 < baseStart_1177903 := by decide
  rcases family_descends (prefixWord ++ tailWord_1177903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1177952 : List Nat := [2, 1, 1, 3, 5, 2, 1, 1, 2, 4]
def baseStart_1177952 : Nat := 118140960795 + 1177952 * 2 ^ 59
def prefixEnd_1177952 : Nat := 4983230072969 + 3 ^ 40 * 1177952 * 2
def baseEnd_1177952 : Nat := 403237042616720327388469

theorem tailTrace_1177952 : CollatzResearch.WordTrace tailWord_1177952 prefixEnd_1177952 403237042616720327388469 := by
  unfold tailWord_1177952
  simp only [CollatzResearch.WordTrace]
  refine ⟨21481719514244278515048055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28642292685659038020064073 21481719514244278515048055)
  ·
    refine ⟨32222579271366417772572083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21481719514244278515048055 32222579271366417772572083)
    ·
      refine ⟨48333868907049626658858125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32222579271366417772572083 48333868907049626658858125)
      ·
        refine ⟨18125200840143609997071797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48333868907049626658858125 18125200840143609997071797)
        ·
          refine ⟨1699237578763463437225481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 18125200840143609997071797 1699237578763463437225481)
          ·
            refine ⟨1274428184072597577919111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1699237578763463437225481 1274428184072597577919111)
            ·
              refine ⟨1911642276108896366878667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1274428184072597577919111 1911642276108896366878667)
              ·
                refine ⟨2867463414163344550318001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1911642276108896366878667 2867463414163344550318001)
                ·
                  refine ⟨2150597560622508412738501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2867463414163344550318001 2150597560622508412738501)
                  ·
                    refine ⟨403237042616720327388469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2150597560622508412738501 403237042616720327388469)
                    ·
                      rfl

theorem cell22_1177952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 2, 1, 1, 2, 4].length) (baseStart_1177952 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1177952 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1177952 prefixEnd_1177952 := by exact prefixLift 1177952
  have htrace : WordTrace (prefixWord ++ tailWord_1177952) baseStart_1177952 baseEnd_1177952 := by
    simpa [prefixWord, tailWord_1177952, baseEnd_1177952] using wordTrace_append hprefix tailTrace_1177952
  have hstable : (prefixWord ++ tailWord_1177952).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1177952).length < 2 ^ (prefixWord ++ tailWord_1177952).sum := by decide
  have hdescent : baseEnd_1177952 < baseStart_1177952 := by decide
  rcases family_descends (prefixWord ++ tailWord_1177952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1177965 : List Nat := [1, 5, 1, 1, 1, 2, 1, 2, 5, 3]
def baseStart_1177965 : Nat := 118140960795 + 1177965 * 2 ^ 59
def prefixEnd_1177965 : Nat := 4983230072969 + 3 ^ 40 * 1177965 * 2
def baseEnd_1177965 : Nat := 403241492782392626813429

theorem tailTrace_1177965 : CollatzResearch.WordTrace tailWord_1177965 prefixEnd_1177965 403241492782392626813429 := by
  unfold tailWord_1177965
  simp only [CollatzResearch.WordTrace]
  refine ⟨42963913177441460250319349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28642608784960973500212899 42963913177441460250319349)
  ·
    refine ⟨4027866860385136898467439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 42963913177441460250319349 4027866860385136898467439)
    ·
      refine ⟨6041800290577705347701159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4027866860385136898467439 6041800290577705347701159)
      ·
        refine ⟨9062700435866558021551739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6041800290577705347701159 9062700435866558021551739)
        ·
          refine ⟨13594050653799837032327609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9062700435866558021551739 13594050653799837032327609)
          ·
            refine ⟨10195537990349877774245707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13594050653799837032327609 10195537990349877774245707)
            ·
              refine ⟨15293306985524816661368561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10195537990349877774245707 15293306985524816661368561)
              ·
                refine ⟨11469980239143612496026421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15293306985524816661368561 11469980239143612496026421)
                ·
                  refine ⟨1075310647419713671502477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 11469980239143612496026421 1075310647419713671502477)
                  ·
                    refine ⟨403241492782392626813429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1075310647419713671502477 403241492782392626813429)
                    ·
                      rfl

theorem cell22_1177965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 2, 5, 3].length) (baseStart_1177965 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1177965 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1177965 prefixEnd_1177965 := by exact prefixLift 1177965
  have htrace : WordTrace (prefixWord ++ tailWord_1177965) baseStart_1177965 baseEnd_1177965 := by
    simpa [prefixWord, tailWord_1177965, baseEnd_1177965] using wordTrace_append hprefix tailTrace_1177965
  have hstable : (prefixWord ++ tailWord_1177965).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1177965).length < 2 ^ (prefixWord ++ tailWord_1177965).sum := by decide
  have hdescent : baseEnd_1177965 < baseStart_1177965 := by decide
  rcases family_descends (prefixWord ++ tailWord_1177965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1178085 : List Nat := [1, 3, 1, 5, 2, 10]
def baseStart_1178085 : Nat := 118140960795 + 1178085 * 2 ^ 59
def prefixEnd_1178085 : Nat := 4983230072969 + 3 ^ 40 * 1178085 * 2
def baseEnd_1178085 : Nat := 4978797175737682886581

theorem tailTrace_1178085 : CollatzResearch.WordTrace tailWord_1178085 prefixEnd_1178085 4978797175737682886581 := by
  unfold tailWord_1178085
  simp only [CollatzResearch.WordTrace]
  refine ⟨42968289937006720744687709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28645526624671147163125139 42968289937006720744687709)
  ·
    refine ⟨16113108726377520279257891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42968289937006720744687709 16113108726377520279257891)
    ·
      refine ⟨24169663089566280418886837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16113108726377520279257891 24169663089566280418886837)
      ·
        refine ⟨2265905914646838789270641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 24169663089566280418886837 2265905914646838789270641)
        ·
          refine ⟨1699429435985129091952981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2265905914646838789270641 1699429435985129091952981)
          ·
            refine ⟨4978797175737682886581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 1699429435985129091952981 4978797175737682886581)
            ·
              rfl

theorem cell22_1178085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 10].length) (baseStart_1178085 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1178085 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1178085 prefixEnd_1178085 := by exact prefixLift 1178085
  have htrace : WordTrace (prefixWord ++ tailWord_1178085) baseStart_1178085 baseEnd_1178085 := by
    simpa [prefixWord, tailWord_1178085, baseEnd_1178085] using wordTrace_append hprefix tailTrace_1178085
  have hstable : (prefixWord ++ tailWord_1178085).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1178085).length < 2 ^ (prefixWord ++ tailWord_1178085).sum := by decide
  have hdescent : baseEnd_1178085 < baseStart_1178085 := by decide
  rcases family_descends (prefixWord ++ tailWord_1178085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1178145 : List Nat := [1, 2, 3, 2, 2, 1, 1, 1, 4, 5]
def baseStart_1178145 : Nat := 118140960795 + 1178145 * 2 ^ 59
def prefixEnd_1178145 : Nat := 4983230072969 + 3 ^ 40 * 1178145 * 2
def baseEnd_1178145 : Nat := 403303110460932157312877

theorem tailTrace_1178145 : CollatzResearch.WordTrace tailWord_1178145 prefixEnd_1178145 403303110460932157312877 := by
  unfold tailWord_1178145
  simp only [CollatzResearch.WordTrace]
  refine ⟨42970478316789350991871889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28646985544526233994581259 42970478316789350991871889)
  ·
    refine ⟨32227858737592013243903917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42970478316789350991871889 32227858737592013243903917)
    ·
      refine ⟨12085447026597004966463969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32227858737592013243903917 12085447026597004966463969)
      ·
        refine ⟨9064085269947753724847977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12085447026597004966463969 9064085269947753724847977)
        ·
          refine ⟨6798063952460815293635983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9064085269947753724847977 6798063952460815293635983)
          ·
            refine ⟨10197095928691222940453975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6798063952460815293635983 10197095928691222940453975)
            ·
              refine ⟨15295643893036834410680963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10197095928691222940453975 15295643893036834410680963)
              ·
                refine ⟨22943465839555251616021445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15295643893036834410680963 22943465839555251616021445)
                ·
                  refine ⟨4301899844916609678004021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22943465839555251616021445 4301899844916609678004021)
                  ·
                    refine ⟨403303110460932157312877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4301899844916609678004021 403303110460932157312877)
                    ·
                      rfl

theorem cell22_1178145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 1, 4, 5].length) (baseStart_1178145 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1178145 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1178145 prefixEnd_1178145 := by exact prefixLift 1178145
  have htrace : WordTrace (prefixWord ++ tailWord_1178145) baseStart_1178145 baseEnd_1178145 := by
    simpa [prefixWord, tailWord_1178145, baseEnd_1178145] using wordTrace_append hprefix tailTrace_1178145
  have hstable : (prefixWord ++ tailWord_1178145).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1178145).length < 2 ^ (prefixWord ++ tailWord_1178145).sum := by decide
  have hdescent : baseEnd_1178145 < baseStart_1178145 := by decide
  rcases family_descends (prefixWord ++ tailWord_1178145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1178147 : List Nat := [1, 1, 1, 4, 4, 1, 3, 2, 5]
def baseStart_1178147 : Nat := 118140960795 + 1178147 * 2 ^ 59
def prefixEnd_1178147 : Nat := 4983230072969 + 3 ^ 40 * 1178147 * 2
def baseEnd_1178147 : Nat := 134434598367268272920957

theorem tailTrace_1178147 : CollatzResearch.WordTrace tailWord_1178147 prefixEnd_1178147 134434598367268272920957 := by
  unfold tailWord_1178147
  simp only [CollatzResearch.WordTrace]
  refine ⟨42970551262782105333444695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28647034175188070222296463 42970551262782105333444695)
  ·
    refine ⟨64455826894173158000167043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42970551262782105333444695 64455826894173158000167043)
    ·
      refine ⟨96683740341259737000250565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64455826894173158000167043 96683740341259737000250565)
      ·
        refine ⟨18128201313986200687546981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 96683740341259737000250565 18128201313986200687546981)
        ·
          refine ⟨3399037746372412628915059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18128201313986200687546981 3399037746372412628915059)
          ·
            refine ⟨5098556619558618943372589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3399037746372412628915059 5098556619558618943372589)
            ·
              refine ⟨1911958732334482103764721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5098556619558618943372589 1911958732334482103764721)
              ·
                refine ⟨1433969049250861577823541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1911958732334482103764721 1433969049250861577823541)
                ·
                  refine ⟨134434598367268272920957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1433969049250861577823541 134434598367268272920957)
                  ·
                    rfl

theorem cell22_1178147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 3, 2, 5].length) (baseStart_1178147 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1178147 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1178147 prefixEnd_1178147 := by exact prefixLift 1178147
  have htrace : WordTrace (prefixWord ++ tailWord_1178147) baseStart_1178147 baseEnd_1178147 := by
    simpa [prefixWord, tailWord_1178147, baseEnd_1178147] using wordTrace_append hprefix tailTrace_1178147
  have hstable : (prefixWord ++ tailWord_1178147).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1178147).length < 2 ^ (prefixWord ++ tailWord_1178147).sum := by decide
  have hdescent : baseEnd_1178147 < baseStart_1178147 := by decide
  rcases family_descends (prefixWord ++ tailWord_1178147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1178160 : List Nat := [2, 1, 1, 1, 2, 3, 2, 1, 5, 4]
def baseStart_1178160 : Nat := 118140960795 + 1178160 * 2 ^ 59
def prefixEnd_1178160 : Nat := 4983230072969 + 3 ^ 40 * 1178160 * 2
def baseEnd_1178160 : Nat := 403308245267477118187831

theorem tailTrace_1178160 : CollatzResearch.WordTrace tailWord_1178160 prefixEnd_1178160 403308245267477118187831 := by
  unfold tailWord_1178160
  simp only [CollatzResearch.WordTrace]
  refine ⟨21485512705867504276833967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28647350274490005702445289 21485512705867504276833967)
  ·
    refine ⟨32228269058801256415250951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21485512705867504276833967 32228269058801256415250951)
    ·
      refine ⟨48342403588201884622876427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32228269058801256415250951 48342403588201884622876427)
      ·
        refine ⟨72513605382302826934314641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48342403588201884622876427 72513605382302826934314641)
        ·
          refine ⟨54385204036727120200735981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72513605382302826934314641 54385204036727120200735981)
          ·
            refine ⟨20394451513772670075275993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54385204036727120200735981 20394451513772670075275993)
            ·
              refine ⟨15295838635329502556456995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20394451513772670075275993 15295838635329502556456995)
              ·
                refine ⟨22943757952994253834685493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15295838635329502556456995 22943757952994253834685493)
                ·
                  refine ⟨2150977308093211297001765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 22943757952994253834685493 2150977308093211297001765)
                  ·
                    refine ⟨403308245267477118187831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2150977308093211297001765 403308245267477118187831)
                    ·
                      rfl

theorem cell22_1178160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 1, 5, 4].length) (baseStart_1178160 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1178160 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1178160 prefixEnd_1178160 := by exact prefixLift 1178160
  have htrace : WordTrace (prefixWord ++ tailWord_1178160) baseStart_1178160 baseEnd_1178160 := by
    simpa [prefixWord, tailWord_1178160, baseEnd_1178160] using wordTrace_append hprefix tailTrace_1178160
  have hstable : (prefixWord ++ tailWord_1178160).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1178160).length < 2 ^ (prefixWord ++ tailWord_1178160).sum := by decide
  have hdescent : baseEnd_1178160 < baseStart_1178160 := by decide
  rcases family_descends (prefixWord ++ tailWord_1178160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1178175 : List Nat := [1, 1, 2, 2, 3, 2, 1, 4, 6]
def baseStart_1178175 : Nat := 118140960795 + 1178175 * 2 ^ 59
def prefixEnd_1178175 : Nat := 4983230072969 + 3 ^ 40 * 1178175 * 2
def baseEnd_1178175 : Nat := 134437793358007359687595

theorem tailTrace_1178175 : CollatzResearch.WordTrace tailWord_1178175 prefixEnd_1178175 134437793358007359687595 := by
  unfold tailWord_1178175
  simp only [CollatzResearch.WordTrace]
  refine ⟨42971572506680666115463979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28647715004453777410309319 42971572506680666115463979)
  ·
    refine ⟨64457358760020999173195969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42971572506680666115463979 64457358760020999173195969)
    ·
      refine ⟨48343019070015749379896977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64457358760020999173195969 48343019070015749379896977)
      ·
        refine ⟨36257264302511812034922733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48343019070015749379896977 36257264302511812034922733)
        ·
          refine ⟨13596474113441929513096025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36257264302511812034922733 13596474113441929513096025)
          ·
            refine ⟨10197355585081447134822019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13596474113441929513096025 10197355585081447134822019)
            ·
              refine ⟨15296033377622170702233029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10197355585081447134822019 15296033377622170702233029)
              ·
                refine ⟨2868006258304157006668693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15296033377622170702233029 2868006258304157006668693)
                ·
                  refine ⟨134437793358007359687595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2868006258304157006668693 134437793358007359687595)
                  ·
                    rfl

theorem cell22_1178175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 4, 6].length) (baseStart_1178175 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1178175 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1178175 prefixEnd_1178175 := by exact prefixLift 1178175
  have htrace : WordTrace (prefixWord ++ tailWord_1178175) baseStart_1178175 baseEnd_1178175 := by
    simpa [prefixWord, tailWord_1178175, baseEnd_1178175] using wordTrace_append hprefix tailTrace_1178175
  have hstable : (prefixWord ++ tailWord_1178175).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1178175).length < 2 ^ (prefixWord ++ tailWord_1178175).sum := by decide
  have hdescent : baseEnd_1178175 < baseStart_1178175 := by decide
  rcases family_descends (prefixWord ++ tailWord_1178175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1178192 : List Nat := [2, 1, 1, 1, 1, 3, 2, 7, 4]
def baseStart_1178192 : Nat := 118140960795 + 1178192 * 2 ^ 59
def prefixEnd_1178192 : Nat := 4983230072969 + 3 ^ 40 * 1178192 * 2
def baseEnd_1178192 : Nat := 134439733173813233795911

theorem tailTrace_1178192 : CollatzResearch.WordTrace tailWord_1178192 prefixEnd_1178192 134439733173813233795911 := by
  unfold tailWord_1178192
  simp only [CollatzResearch.WordTrace]
  refine ⟨21486096273809539009416415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28648128365079385345888553 21486096273809539009416415)
  ·
    refine ⟨32229144410714308514124623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21486096273809539009416415 32229144410714308514124623)
    ·
      refine ⟨48343716616071462771186935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32229144410714308514124623 48343716616071462771186935)
      ·
        refine ⟨72515574924107194156780403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48343716616071462771186935 72515574924107194156780403)
        ·
          refine ⟨108773362386160791235170605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72515574924107194156780403 108773362386160791235170605)
          ·
            refine ⟨40790010894810296713188977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 108773362386160791235170605 40790010894810296713188977)
            ·
              refine ⟨30592508171107722534891733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40790010894810296713188977 30592508171107722534891733)
              ·
                refine ⟨717011910260337246911525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 30592508171107722534891733 717011910260337246911525)
                ·
                  refine ⟨134439733173813233795911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 717011910260337246911525 134439733173813233795911)
                  ·
                    rfl

theorem cell22_1178192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 7, 4].length) (baseStart_1178192 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1178192 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1178192 prefixEnd_1178192 := by exact prefixLift 1178192
  have htrace : WordTrace (prefixWord ++ tailWord_1178192) baseStart_1178192 baseEnd_1178192 := by
    simpa [prefixWord, tailWord_1178192, baseEnd_1178192] using wordTrace_append hprefix tailTrace_1178192
  have hstable : (prefixWord ++ tailWord_1178192).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1178192).length < 2 ^ (prefixWord ++ tailWord_1178192).sum := by decide
  have hdescent : baseEnd_1178192 < baseStart_1178192 := by decide
  rcases family_descends (prefixWord ++ tailWord_1178192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1178220 : List Nat := [2, 2, 1, 1, 3, 1, 3, 9]
def baseStart_1178220 : Nat := 118140960795 + 1178220 * 2 ^ 59
def prefixEnd_1178220 : Nat := 4983230072969 + 3 ^ 40 * 1178220 * 2
def baseEnd_1178220 : Nat := 44814309388184106854183

theorem tailTrace_1178220 : CollatzResearch.WordTrace tailWord_1178220 prefixEnd_1178220 44814309388184106854183 := by
  unfold tailWord_1178220
  simp only [CollatzResearch.WordTrace]
  refine ⟨21486606895758819400426057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28648809194345092533901409 21486606895758819400426057)
  ·
    refine ⟨16114955171819114550319543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21486606895758819400426057 16114955171819114550319543)
    ·
      refine ⟨24172432757728671825479315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16114955171819114550319543 24172432757728671825479315)
      ·
        refine ⟨36258649136593007738218973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24172432757728671825479315 36258649136593007738218973)
        ·
          refine ⟨13596993426222377901832115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36258649136593007738218973 13596993426222377901832115)
          ·
            refine ⟨20395490139333566852748173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13596993426222377901832115 20395490139333566852748173)
            ·
              refine ⟨7648308802250087569780565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20395490139333566852748173 7648308802250087569780565)
              ·
                refine ⟨44814309388184106854183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 7648308802250087569780565 44814309388184106854183)
                ·
                  rfl

theorem cell22_1178220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 9].length) (baseStart_1178220 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1178220 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1178220 prefixEnd_1178220 := by exact prefixLift 1178220
  have htrace : WordTrace (prefixWord ++ tailWord_1178220) baseStart_1178220 baseEnd_1178220 := by
    simpa [prefixWord, tailWord_1178220, baseEnd_1178220] using wordTrace_append hprefix tailTrace_1178220
  have hstable : (prefixWord ++ tailWord_1178220).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1178220).length < 2 ^ (prefixWord ++ tailWord_1178220).sum := by decide
  have hdescent : baseEnd_1178220 < baseStart_1178220 := by decide
  rcases family_descends (prefixWord ++ tailWord_1178220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1178252 : List Nat := [2, 2, 1, 2, 1, 1, 2, 1, 7, 3]
def baseStart_1178252 : Nat := 118140960795 + 1178252 * 2 ^ 59
def prefixEnd_1178252 : Nat := 4983230072969 + 3 ^ 40 * 1178252 * 2
def baseEnd_1178252 : Nat := 403339738747619544887549

theorem tailTrace_1178252 : CollatzResearch.WordTrace tailWord_1178252 prefixEnd_1178252 403339738747619544887549 := by
  unfold tailWord_1178252
  simp only [CollatzResearch.WordTrace]
  refine ⟨21487190463700854133008505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28649587284934472177344673 21487190463700854133008505)
  ·
    refine ⟨16115392847775640599756379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21487190463700854133008505 16115392847775640599756379)
    ·
      refine ⟨24173089271663460899634569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16115392847775640599756379 24173089271663460899634569)
      ·
        refine ⟨18129816953747595674725927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24173089271663460899634569 18129816953747595674725927)
        ·
          refine ⟨27194725430621393512088891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18129816953747595674725927 27194725430621393512088891)
          ·
            refine ⟨40792088145932090268133337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27194725430621393512088891 40792088145932090268133337)
            ·
              refine ⟨30594066109449067701100003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40792088145932090268133337 30594066109449067701100003)
              ·
                refine ⟨45891099164173601551650005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30594066109449067701100003 45891099164173601551650005)
                ·
                  refine ⟨1075572636660318786366797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 45891099164173601551650005 1075572636660318786366797)
                  ·
                    refine ⟨403339738747619544887549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1075572636660318786366797 403339738747619544887549)
                    ·
                      rfl

theorem cell22_1178252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 7, 3].length) (baseStart_1178252 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1178252 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1178252 prefixEnd_1178252 := by exact prefixLift 1178252
  have htrace : WordTrace (prefixWord ++ tailWord_1178252) baseStart_1178252 baseEnd_1178252 := by
    simpa [prefixWord, tailWord_1178252, baseEnd_1178252] using wordTrace_append hprefix tailTrace_1178252
  have hstable : (prefixWord ++ tailWord_1178252).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1178252).length < 2 ^ (prefixWord ++ tailWord_1178252).sum := by decide
  have hdescent : baseEnd_1178252 < baseStart_1178252 := by decide
  rcases family_descends (prefixWord ++ tailWord_1178252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1178286 : List Nat := [4, 1, 4, 1, 1, 1, 1, 1, 5, 3]
def baseStart_1178286 : Nat := 118140960795 + 1178286 * 2 ^ 59
def prefixEnd_1178286 : Nat := 4983230072969 + 3 ^ 40 * 1178286 * 2
def baseEnd_1178286 : Nat := 403351377642454789537445

theorem tailTrace_1178286 : CollatzResearch.WordTrace tailWord_1178286 prefixEnd_1178286 403351377642454789537445 := by
  unfold tailWord_1178286
  simp only [CollatzResearch.WordTrace]
  refine ⟨5371952626159816509094339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28650414006185688048503141 5371952626159816509094339)
  ·
    refine ⟨8057928939239724763641509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5371952626159816509094339 8057928939239724763641509)
    ·
      refine ⟨1510861676107448393182783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8057928939239724763641509 1510861676107448393182783)
      ·
        refine ⟨2266292514161172589774175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1510861676107448393182783 2266292514161172589774175)
        ·
          refine ⟨3399438771241758884661263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2266292514161172589774175 3399438771241758884661263)
          ·
            refine ⟨5099158156862638326991895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3399438771241758884661263 5099158156862638326991895)
            ·
              refine ⟨7648737235293957490487843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5099158156862638326991895 7648737235293957490487843)
              ·
                refine ⟨11473105852940936235731765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7648737235293957490487843 11473105852940936235731765)
                ·
                  refine ⟨1075603673713212772099853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 11473105852940936235731765 1075603673713212772099853)
                  ·
                    refine ⟨403351377642454789537445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1075603673713212772099853 403351377642454789537445)
                    ·
                      rfl

theorem cell22_1178286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 1, 5, 3].length) (baseStart_1178286 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1178286 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1178286 prefixEnd_1178286 := by exact prefixLift 1178286
  have htrace : WordTrace (prefixWord ++ tailWord_1178286) baseStart_1178286 baseEnd_1178286 := by
    simpa [prefixWord, tailWord_1178286, baseEnd_1178286] using wordTrace_append hprefix tailTrace_1178286
  have hstable : (prefixWord ++ tailWord_1178286).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1178286).length < 2 ^ (prefixWord ++ tailWord_1178286).sum := by decide
  have hdescent : baseEnd_1178286 < baseStart_1178286 := by decide
  rcases family_descends (prefixWord ++ tailWord_1178286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1178316 : List Nat := [2, 2, 1, 5, 1, 3, 1, 2, 5]
def baseStart_1178316 : Nat := 118140960795 + 1178316 * 2 ^ 59
def prefixEnd_1178316 : Nat := 4983230072969 + 3 ^ 40 * 1178316 * 2
def baseEnd_1178316 : Nat := 134453882418514903762451

theorem tailTrace_1178316 : CollatzResearch.WordTrace tailWord_1178316 prefixEnd_1178316 134453882418514903762451 := by
  unfold tailWord_1178316
  simp only [CollatzResearch.WordTrace]
  refine ⟨21488357599584923598173401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28651143466113231464231201 21488357599584923598173401)
  ·
    refine ⟨16116268199688692698630051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21488357599584923598173401 16116268199688692698630051)
    ·
      refine ⟨24174402299533039047945077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16116268199688692698630051 24174402299533039047945077)
      ·
        refine ⟨2266350215581222410744851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 24174402299533039047945077 2266350215581222410744851)
        ·
          refine ⟨3399525323371833616117277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2266350215581222410744851 3399525323371833616117277)
          ·
            refine ⟨1274821996264437606043979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3399525323371833616117277 1274821996264437606043979)
            ·
              refine ⟨1912232994396656409065969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1274821996264437606043979 1912232994396656409065969)
              ·
                refine ⟨1434174745797492306799477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1912232994396656409065969 1434174745797492306799477)
                ·
                  refine ⟨134453882418514903762451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1434174745797492306799477 134453882418514903762451)
                  ·
                    rfl

theorem cell22_1178316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 3, 1, 2, 5].length) (baseStart_1178316 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1178316 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1178316 prefixEnd_1178316 := by exact prefixLift 1178316
  have htrace : WordTrace (prefixWord ++ tailWord_1178316) baseStart_1178316 baseEnd_1178316 := by
    simpa [prefixWord, tailWord_1178316, baseEnd_1178316] using wordTrace_append hprefix tailTrace_1178316
  have hstable : (prefixWord ++ tailWord_1178316).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1178316).length < 2 ^ (prefixWord ++ tailWord_1178316).sum := by decide
  have hdescent : baseEnd_1178316 < baseStart_1178316 := by decide
  rcases family_descends (prefixWord ++ tailWord_1178316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1178327 : List Nat := [1, 1, 3, 2, 1, 4, 1, 3, 6]
def baseStart_1178327 : Nat := 118140960795 + 1178327 * 2 ^ 59
def prefixEnd_1178327 : Nat := 4983230072969 + 3 ^ 40 * 1178327 * 2
def baseEnd_1178327 : Nat := 134455137593448116420773

theorem tailTrace_1178327 : CollatzResearch.WordTrace tailWord_1178327 prefixEnd_1178327 134455137593448116420773 := by
  unfold tailWord_1178327
  simp only [CollatzResearch.WordTrace]
  refine ⟨42977116402129996074997235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28651410934753330716664823 42977116402129996074997235)
  ·
    refine ⟨64465674603194994112495853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42977116402129996074997235 64465674603194994112495853)
    ·
      refine ⟨24174627976198122792185945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64465674603194994112495853 24174627976198122792185945)
      ·
        refine ⟨18130970982148592094139459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24174627976198122792185945 18130970982148592094139459)
        ·
          refine ⟨27196456473222888141209189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18130970982148592094139459 27196456473222888141209189)
          ·
            refine ⟨5099335588729291526476723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27196456473222888141209189 5099335588729291526476723)
            ·
              refine ⟨7649003383093937289715085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5099335588729291526476723 7649003383093937289715085)
              ·
                refine ⟨2868376268660226483643157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7649003383093937289715085 2868376268660226483643157)
                ·
                  refine ⟨134455137593448116420773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2868376268660226483643157 134455137593448116420773)
                  ·
                    rfl

theorem cell22_1178327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 3, 6].length) (baseStart_1178327 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1178327 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1178327 prefixEnd_1178327 := by exact prefixLift 1178327
  have htrace : WordTrace (prefixWord ++ tailWord_1178327) baseStart_1178327 baseEnd_1178327 := by
    simpa [prefixWord, tailWord_1178327, baseEnd_1178327] using wordTrace_append hprefix tailTrace_1178327
  have hstable : (prefixWord ++ tailWord_1178327).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1178327).length < 2 ^ (prefixWord ++ tailWord_1178327).sum := by decide
  have hdescent : baseEnd_1178327 < baseStart_1178327 := by decide
  rcases family_descends (prefixWord ++ tailWord_1178327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1178432 : List Nat := [2, 1, 1, 2, 2, 1, 1, 2, 3, 7]
def baseStart_1178432 : Nat := 118140960795 + 1178432 * 2 ^ 59
def prefixEnd_1178432 : Nat := 4983230072969 + 3 ^ 40 * 1178432 * 2
def baseEnd_1178432 : Nat := 403401356426159075386997

theorem tailTrace_1178432 : CollatzResearch.WordTrace tailWord_1178432 prefixEnd_1178432 403401356426159075386997 := by
  unfold tailWord_1178432
  simp only [CollatzResearch.WordTrace]
  refine ⟨21490473033374799503784775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28653964044499732671713033 21490473033374799503784775)
  ·
    refine ⟨32235709550062199255677163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21490473033374799503784775 32235709550062199255677163)
    ·
      refine ⟨48353564325093298883515745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32235709550062199255677163 48353564325093298883515745)
      ·
        refine ⟨36265173243819974162636809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48353564325093298883515745 36265173243819974162636809)
        ·
          refine ⟨27198879932864980621977607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36265173243819974162636809 27198879932864980621977607)
          ·
            refine ⟨40798319899297470932966411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27198879932864980621977607 40798319899297470932966411)
            ·
              refine ⟨61197479848946206399449617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40798319899297470932966411 61197479848946206399449617)
              ·
                refine ⟨45898109886709654799587213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 61197479848946206399449617 45898109886709654799587213)
                ·
                  refine ⟨17211791207516120549845205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 45898109886709654799587213 17211791207516120549845205)
                  ·
                    refine ⟨403401356426159075386997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 17211791207516120549845205 403401356426159075386997)
                    ·
                      rfl

theorem cell22_1178432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 2, 3, 7].length) (baseStart_1178432 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1178432 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1178432 prefixEnd_1178432 := by exact prefixLift 1178432
  have htrace : WordTrace (prefixWord ++ tailWord_1178432) baseStart_1178432 baseEnd_1178432 := by
    simpa [prefixWord, tailWord_1178432, baseEnd_1178432] using wordTrace_append hprefix tailTrace_1178432
  have hstable : (prefixWord ++ tailWord_1178432).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1178432).length < 2 ^ (prefixWord ++ tailWord_1178432).sum := by decide
  have hdescent : baseEnd_1178432 < baseStart_1178432 := by decide
  rcases family_descends (prefixWord ++ tailWord_1178432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1178464 : List Nat := [2, 1, 1, 3, 3, 1, 1, 3, 3, 4]
def baseStart_1178464 : Nat := 118140960795 + 1178464 * 2 ^ 59
def prefixEnd_1178464 : Nat := 4983230072969 + 3 ^ 40 * 1178464 * 2
def baseEnd_1178464 : Nat := 403412310680121658586899

theorem tailTrace_1178464 : CollatzResearch.WordTrace tailWord_1178464 prefixEnd_1178464 403412310680121658586899 := by
  unfold tailWord_1178464
  simp only [CollatzResearch.WordTrace]
  refine ⟨21491056601316834236367223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28654742135089112315156297 21491056601316834236367223)
  ·
    refine ⟨32236584901975251354550835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21491056601316834236367223 32236584901975251354550835)
    ·
      refine ⟨48354877352962877031826253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32236584901975251354550835 48354877352962877031826253)
      ·
        refine ⟨18133079007361078886934845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48354877352962877031826253 18133079007361078886934845)
        ·
          refine ⟨6799904627760404582600567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18133079007361078886934845 6799904627760404582600567)
          ·
            refine ⟨10199856941640606873900851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6799904627760404582600567 10199856941640606873900851)
            ·
              refine ⟨15299785412460910310851277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10199856941640606873900851 15299785412460910310851277)
              ·
                refine ⟨5737419529672841366569229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15299785412460910310851277 5737419529672841366569229)
                ·
                  refine ⟨2151532323627315512463461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5737419529672841366569229 2151532323627315512463461)
                  ·
                    refine ⟨403412310680121658586899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2151532323627315512463461 403412310680121658586899)
                    ·
                      rfl

theorem cell22_1178464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 3, 3, 4].length) (baseStart_1178464 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1178464 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1178464 prefixEnd_1178464 := by exact prefixLift 1178464
  have htrace : WordTrace (prefixWord ++ tailWord_1178464) baseStart_1178464 baseEnd_1178464 := by
    simpa [prefixWord, tailWord_1178464, baseEnd_1178464] using wordTrace_append hprefix tailTrace_1178464
  have hstable : (prefixWord ++ tailWord_1178464).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1178464).length < 2 ^ (prefixWord ++ tailWord_1178464).sum := by decide
  have hdescent : baseEnd_1178464 < baseStart_1178464 := by decide
  rcases family_descends (prefixWord ++ tailWord_1178464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1178481 : List Nat := [1, 2, 2, 2, 1, 5, 1, 3, 1, 4]
def baseStart_1178481 : Nat := 118140960795 + 1178481 * 2 ^ 59
def prefixEnd_1178481 : Nat := 4983230072969 + 3 ^ 40 * 1178481 * 2
def baseEnd_1178481 : Nat := 403418130127539280911847

theorem tailTrace_1178481 : CollatzResearch.WordTrace tailWord_1178481 prefixEnd_1178481 403418130127539280911847 := by
  unfold tailWord_1178481
  simp only [CollatzResearch.WordTrace]
  refine ⟨42982733243572080376103297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28655155495714720250735531 42982733243572080376103297)
  ·
    refine ⟨32237049932679060282077473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42982733243572080376103297 32237049932679060282077473)
    ·
      refine ⟨24177787449509295211558105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32237049932679060282077473 24177787449509295211558105)
      ·
        refine ⟨18133340587131971408668579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24177787449509295211558105 18133340587131971408668579)
        ·
          refine ⟨27200010880697957113002869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18133340587131971408668579 27200010880697957113002869)
          ·
            refine ⟨2550001020065433479344019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 27200010880697957113002869 2550001020065433479344019)
            ·
              refine ⟨3825001530098150219016029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2550001020065433479344019 3825001530098150219016029)
              ·
                refine ⟨1434375573786806332131011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3825001530098150219016029 1434375573786806332131011)
                ·
                  refine ⟨2151563360680209498196517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1434375573786806332131011 2151563360680209498196517)
                  ·
                    refine ⟨403418130127539280911847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2151563360680209498196517 403418130127539280911847)
                    ·
                      rfl

theorem cell22_1178481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 1, 3, 1, 4].length) (baseStart_1178481 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1178481 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1178481 prefixEnd_1178481 := by exact prefixLift 1178481
  have htrace : WordTrace (prefixWord ++ tailWord_1178481) baseStart_1178481 baseEnd_1178481 := by
    simpa [prefixWord, tailWord_1178481, baseEnd_1178481] using wordTrace_append hprefix tailTrace_1178481
  have hstable : (prefixWord ++ tailWord_1178481).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1178481).length < 2 ^ (prefixWord ++ tailWord_1178481).sum := by decide
  have hdescent : baseEnd_1178481 < baseStart_1178481 := by decide
  rcases family_descends (prefixWord ++ tailWord_1178481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1178530 : List Nat := [3, 3, 1, 2, 2, 3, 1, 3, 4]
def baseStart_1178530 : Nat := 118140960795 + 1178530 * 2 ^ 59
def prefixEnd_1178530 : Nat := 4983230072969 + 3 ^ 40 * 1178530 * 2
def baseEnd_1178530 : Nat := 134478301276306495478899

theorem tailTrace_1178530 : CollatzResearch.WordTrace tailWord_1178530 prefixEnd_1178530 134478301276306495478899 := by
  unfold tailWord_1178530
  simp only [CollatzResearch.WordTrace]
  refine ⟨10746130105098640436159261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28656346946929707829758029 10746130105098640436159261)
  ·
    refine ⟨4029798789411990163559723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10746130105098640436159261 4029798789411990163559723)
    ·
      refine ⟨6044698184117985245339585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4029798789411990163559723 6044698184117985245339585)
      ·
        refine ⟨4533523638088488934004689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6044698184117985245339585 4533523638088488934004689)
        ·
          refine ⟨3400142728566366700503517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4533523638088488934004689 3400142728566366700503517)
          ·
            refine ⟨1275053523212387512688819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3400142728566366700503517 1275053523212387512688819)
            ·
              refine ⟨1912580284818581269033229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1275053523212387512688819 1912580284818581269033229)
              ·
                refine ⟨717217606806967975887461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1912580284818581269033229 717217606806967975887461)
                ·
                  refine ⟨134478301276306495478899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 717217606806967975887461 134478301276306495478899)
                  ·
                    rfl

theorem cell22_1178530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 3, 1, 3, 4].length) (baseStart_1178530 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1178530 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1178530 prefixEnd_1178530 := by exact prefixLift 1178530
  have htrace : WordTrace (prefixWord ++ tailWord_1178530) baseStart_1178530 baseEnd_1178530 := by
    simpa [prefixWord, tailWord_1178530, baseEnd_1178530] using wordTrace_append hprefix tailTrace_1178530
  have hstable : (prefixWord ++ tailWord_1178530).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1178530).length < 2 ^ (prefixWord ++ tailWord_1178530).sum := by decide
  have hdescent : baseEnd_1178530 < baseStart_1178530 := by decide
  rcases family_descends (prefixWord ++ tailWord_1178530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1178554 : List Nat := [3, 1, 1, 1, 2, 1, 4, 1, 2, 6]
def baseStart_1178554 : Nat := 118140960795 + 1178554 * 2 ^ 59
def prefixEnd_1178554 : Nat := 4983230072969 + 3 ^ 40 * 1178554 * 2
def baseEnd_1178554 : Nat := 403443119519391423836623

theorem tailTrace_1178554 : CollatzResearch.WordTrace tailWord_1178554 prefixEnd_1178554 403443119519391423836623 := by
  unfold tailWord_1178554
  simp only [CollatzResearch.WordTrace]
  refine ⟨10746348943076903460877679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28656930514871742562340477 10746348943076903460877679)
  ·
    refine ⟨16119523414615355191316519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10746348943076903460877679 16119523414615355191316519)
    ·
      refine ⟨24179285121923032786974779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16119523414615355191316519 24179285121923032786974779)
      ·
        refine ⟨36268927682884549180462169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24179285121923032786974779 36268927682884549180462169)
        ·
          refine ⟨27201695762163411885346627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36268927682884549180462169 27201695762163411885346627)
          ·
            refine ⟨40802543643245117828019941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27201695762163411885346627 40802543643245117828019941)
            ·
              refine ⟨7650476933108459592753739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40802543643245117828019941 7650476933108459592753739)
              ·
                refine ⟨11475715399662689389130609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7650476933108459592753739 11475715399662689389130609)
                ·
                  refine ⟨8606786549747017041847957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11475715399662689389130609 8606786549747017041847957)
                  ·
                    refine ⟨403443119519391423836623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8606786549747017041847957 403443119519391423836623)
                    ·
                      rfl

theorem cell22_1178554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 1, 2, 6].length) (baseStart_1178554 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1178554 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1178554 prefixEnd_1178554 := by exact prefixLift 1178554
  have htrace : WordTrace (prefixWord ++ tailWord_1178554) baseStart_1178554 baseEnd_1178554 := by
    simpa [prefixWord, tailWord_1178554, baseEnd_1178554] using wordTrace_append hprefix tailTrace_1178554
  have hstable : (prefixWord ++ tailWord_1178554).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1178554).length < 2 ^ (prefixWord ++ tailWord_1178554).sum := by decide
  have hdescent : baseEnd_1178554 < baseStart_1178554 := by decide
  rcases family_descends (prefixWord ++ tailWord_1178554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1178566 : List Nat := [6, 1, 3, 1, 1, 2, 1, 2, 1, 4]
def baseStart_1178566 : Nat := 118140960795 + 1178566 * 2 ^ 59
def prefixEnd_1178566 : Nat := 4983230072969 + 3 ^ 40 * 1178566 * 2
def baseEnd_1178566 : Nat := 403447227364627392536587

theorem tailTrace_1178566 : CollatzResearch.WordTrace tailWord_1178566 prefixEnd_1178566 403447227364627392536587 := by
  unfold tailWord_1178566
  simp only [CollatzResearch.WordTrace]
  refine ⟨1343307295258254371654611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 28657222298842759928631701 1343307295258254371654611)
  ·
    refine ⟨2014960942887381557481917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1343307295258254371654611 2014960942887381557481917)
    ·
      refine ⟨755610353582768084055719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2014960942887381557481917 755610353582768084055719)
      ·
        refine ⟨1133415530374152126083579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 755610353582768084055719 1133415530374152126083579)
        ·
          refine ⟨1700123295561228189125369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1133415530374152126083579 1700123295561228189125369)
          ·
            refine ⟨1275092471670921141844027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1700123295561228189125369 1275092471670921141844027)
            ·
              refine ⟨1912638707506381712766041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1275092471670921141844027 1912638707506381712766041)
              ·
                refine ⟨1434479030629786284574531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1912638707506381712766041 1434479030629786284574531)
                ·
                  refine ⟨2151718545944679426861797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1434479030629786284574531 2151718545944679426861797)
                  ·
                    refine ⟨403447227364627392536587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2151718545944679426861797 403447227364627392536587)
                    ·
                      rfl

theorem cell22_1178566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 2, 1, 2, 1, 4].length) (baseStart_1178566 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1178566 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1178566 prefixEnd_1178566 := by exact prefixLift 1178566
  have htrace : WordTrace (prefixWord ++ tailWord_1178566) baseStart_1178566 baseEnd_1178566 := by
    simpa [prefixWord, tailWord_1178566, baseEnd_1178566] using wordTrace_append hprefix tailTrace_1178566
  have hstable : (prefixWord ++ tailWord_1178566).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1178566).length < 2 ^ (prefixWord ++ tailWord_1178566).sum := by decide
  have hdescent : baseEnd_1178566 < baseStart_1178566 := by decide
  rcases family_descends (prefixWord ++ tailWord_1178566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1178607 : List Nat := [1, 1, 2, 1, 4, 5, 2, 2, 1, 3]
def baseStart_1178607 : Nat := 118140960795 + 1178607 * 2 ^ 59
def prefixEnd_1178607 : Nat := 4983230072969 + 3 ^ 40 * 1178607 * 2
def baseEnd_1178607 : Nat := 403461262502516952261461

theorem tailTrace_1178607 : CollatzResearch.WordTrace tailWord_1178607 prefixEnd_1178607 403461262502516952261461 := by
  unfold tailWord_1178607
  simp only [CollatzResearch.WordTrace]
  refine ⟨42987328841115603895190075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28658219227410402596793383 42987328841115603895190075)
  ·
    refine ⟨64480993261673405842785113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42987328841115603895190075 64480993261673405842785113)
    ·
      refine ⟨48360744946255054382088835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64480993261673405842785113 48360744946255054382088835)
      ·
        refine ⟨72541117419382581573133253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48360744946255054382088835 72541117419382581573133253)
        ·
          refine ⟨13601459516134234044962485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 72541117419382581573133253 13601459516134234044962485)
          ·
            refine ⟨1275136829637584441715233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 13601459516134234044962485 1275136829637584441715233)
            ·
              refine ⟨956352622228188331286425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1275136829637584441715233 956352622228188331286425)
              ·
                refine ⟨717264466671141248464819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 956352622228188331286425 717264466671141248464819)
                ·
                  refine ⟨1075896700006711872697229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 717264466671141248464819 1075896700006711872697229)
                  ·
                    refine ⟨403461262502516952261461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1075896700006711872697229 403461262502516952261461)
                    ·
                      rfl

theorem cell22_1178607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 5, 2, 2, 1, 3].length) (baseStart_1178607 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1178607 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1178607 prefixEnd_1178607 := by exact prefixLift 1178607
  have htrace : WordTrace (prefixWord ++ tailWord_1178607) baseStart_1178607 baseEnd_1178607 := by
    simpa [prefixWord, tailWord_1178607, baseEnd_1178607] using wordTrace_append hprefix tailTrace_1178607
  have hstable : (prefixWord ++ tailWord_1178607).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1178607).length < 2 ^ (prefixWord ++ tailWord_1178607).sum := by decide
  have hdescent : baseEnd_1178607 < baseStart_1178607 := by decide
  rcases family_descends (prefixWord ++ tailWord_1178607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1178631 : List Nat := [1, 1, 4, 3, 1, 1, 3, 2, 6]
def baseStart_1178631 : Nat := 118140960795 + 1178631 * 2 ^ 59
def prefixEnd_1178631 : Nat := 4983230072969 + 3 ^ 40 * 1178631 * 2
def baseEnd_1178631 : Nat := 134489826064329629887129

theorem tailTrace_1178631 : CollatzResearch.WordTrace tailWord_1178631 prefixEnd_1178631 134489826064329629887129 := by
  unfold tailWord_1178631
  simp only [CollatzResearch.WordTrace]
  refine ⟨42988204193028655994063747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28658802795352437329375831 42988204193028655994063747)
  ·
    refine ⟨64482306289542983991095621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42988204193028655994063747 64482306289542983991095621)
    ·
      refine ⟨12090432429289309498330429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 64482306289542983991095621 12090432429289309498330429)
      ·
        refine ⟨4533912160983491061873911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12090432429289309498330429 4533912160983491061873911)
        ·
          refine ⟨6800868241475236592810867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4533912160983491061873911 6800868241475236592810867)
          ·
            refine ⟨10201302362212854889216301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6800868241475236592810867 10201302362212854889216301)
            ·
              refine ⟨3825488385829820583456113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10201302362212854889216301 3825488385829820583456113)
              ·
                refine ⟨2869116289372365437592085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3825488385829820583456113 2869116289372365437592085)
                ·
                  refine ⟨134489826064329629887129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2869116289372365437592085 134489826064329629887129)
                  ·
                    rfl

theorem cell22_1178631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 3, 2, 6].length) (baseStart_1178631 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1178631 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1178631 prefixEnd_1178631 := by exact prefixLift 1178631
  have htrace : WordTrace (prefixWord ++ tailWord_1178631) baseStart_1178631 baseEnd_1178631 := by
    simpa [prefixWord, tailWord_1178631, baseEnd_1178631] using wordTrace_append hprefix tailTrace_1178631
  have hstable : (prefixWord ++ tailWord_1178631).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1178631).length < 2 ^ (prefixWord ++ tailWord_1178631).sum := by decide
  have hdescent : baseEnd_1178631 < baseStart_1178631 := by decide
  rcases family_descends (prefixWord ++ tailWord_1178631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1178648 : List Nat := [2, 1, 2, 3, 2, 2, 1, 5, 4]
def baseStart_1178648 : Nat := 118140960795 + 1178648 * 2 ^ 59
def prefixEnd_1178648 : Nat := 4983230072969 + 3 ^ 40 * 1178648 * 2
def baseEnd_1178648 : Nat := 134491765880135503995445

theorem tailTrace_1178648 : CollatzResearch.WordTrace tailWord_1178648 prefixEnd_1178648 134491765880135503995445 := by
  unfold tailWord_1178648
  simp only [CollatzResearch.WordTrace]
  refine ⟨21494412116983533948716299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28659216155978045264955065 21494412116983533948716299)
  ·
    refine ⟨32241618175475300923074449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21494412116983533948716299 32241618175475300923074449)
    ·
      refine ⟨24181213631606475692305837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32241618175475300923074449 24181213631606475692305837)
      ·
        refine ⟨9067955111852428384614689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24181213631606475692305837 9067955111852428384614689)
        ·
          refine ⟨6800966333889321288461017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9067955111852428384614689 6800966333889321288461017)
          ·
            refine ⟨5100724750416990966345763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6800966333889321288461017 5100724750416990966345763)
            ·
              refine ⟨7651087125625486449518645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5100724750416990966345763 7651087125625486449518645)
              ·
                refine ⟨717289418027389354642373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7651087125625486449518645 717289418027389354642373)
                ·
                  refine ⟨134491765880135503995445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 717289418027389354642373 134491765880135503995445)
                  ·
                    rfl

theorem cell22_1178648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 5, 4].length) (baseStart_1178648 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1178648 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1178648 prefixEnd_1178648 := by exact prefixLift 1178648
  have htrace : WordTrace (prefixWord ++ tailWord_1178648) baseStart_1178648 baseEnd_1178648 := by
    simpa [prefixWord, tailWord_1178648, baseEnd_1178648] using wordTrace_append hprefix tailTrace_1178648
  have hstable : (prefixWord ++ tailWord_1178648).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1178648).length < 2 ^ (prefixWord ++ tailWord_1178648).sum := by decide
  have hdescent : baseEnd_1178648 < baseStart_1178648 := by decide
  rcases family_descends (prefixWord ++ tailWord_1178648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1178661 : List Nat := [1, 3, 1, 2, 2, 2, 2, 1, 4, 4]
def baseStart_1178661 : Nat := 118140960795 + 1178661 * 2 ^ 59
def prefixEnd_1178661 : Nat := 4983230072969 + 3 ^ 40 * 1178661 * 2
def baseEnd_1178661 : Nat := 403479747806078811411295

theorem tailTrace_1178661 : CollatzResearch.WordTrace tailWord_1178661 prefixEnd_1178661 403479747806078811411295 := by
  unfold tailWord_1178661
  simp only [CollatzResearch.WordTrace]
  refine ⟨42989298382919971117655837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28659532255279980745103891 42989298382919971117655837)
  ·
    refine ⟨16120986893594989169120939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42989298382919971117655837 16120986893594989169120939)
    ·
      refine ⟨24181480340392483753681409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16120986893594989169120939 24181480340392483753681409)
      ·
        refine ⟨18136110255294362815261057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24181480340392483753681409 18136110255294362815261057)
        ·
          refine ⟨13602082691470772111445793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18136110255294362815261057 13602082691470772111445793)
          ·
            refine ⟨10201562018603079083584345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13602082691470772111445793 10201562018603079083584345)
            ·
              refine ⟨7651171513952309312688259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10201562018603079083584345 7651171513952309312688259)
              ·
                refine ⟨11476757270928463969032389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7651171513952309312688259 11476757270928463969032389)
                ·
                  refine ⟨2151891988299086994193573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11476757270928463969032389 2151891988299086994193573)
                  ·
                    refine ⟨403479747806078811411295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2151891988299086994193573 403479747806078811411295)
                    ·
                      rfl

theorem cell22_1178661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 1, 4, 4].length) (baseStart_1178661 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1178661 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1178661 prefixEnd_1178661 := by exact prefixLift 1178661
  have htrace : WordTrace (prefixWord ++ tailWord_1178661) baseStart_1178661 baseEnd_1178661 := by
    simpa [prefixWord, tailWord_1178661, baseEnd_1178661] using wordTrace_append hprefix tailTrace_1178661
  have hstable : (prefixWord ++ tailWord_1178661).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1178661).length < 2 ^ (prefixWord ++ tailWord_1178661).sum := by decide
  have hdescent : baseEnd_1178661 < baseStart_1178661 := by decide
  rcases family_descends (prefixWord ++ tailWord_1178661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1178678 : List Nat := [5, 1, 2, 1, 1, 2, 1, 2, 1, 6]
def baseStart_1178678 : Nat := 118140960795 + 1178678 * 2 ^ 59
def prefixEnd_1178678 : Nat := 4983230072969 + 3 ^ 40 * 1178678 * 2
def baseEnd_1178678 : Nat := 403485567253496433736243

theorem tailTrace_1178678 : CollatzResearch.WordTrace tailWord_1178678 prefixEnd_1178678 403485567253496433736243 := by
  unfold tailWord_1178678
  simp only [CollatzResearch.WordTrace]
  refine ⟨2686869901491148938814043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 28659945615905588680683125 2686869901491148938814043)
  ·
    refine ⟨4030304852236723408221065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2686869901491148938814043 4030304852236723408221065)
    ·
      refine ⟨3022728639177542556165799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4030304852236723408221065 3022728639177542556165799)
      ·
        refine ⟨4534092958766313834248699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3022728639177542556165799 4534092958766313834248699)
        ·
          refine ⟨6801139438149470751373049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4534092958766313834248699 6801139438149470751373049)
          ·
            refine ⟨5100854578612103063529787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6801139438149470751373049 5100854578612103063529787)
            ·
              refine ⟨7651281867918154595294681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5100854578612103063529787 7651281867918154595294681)
              ·
                refine ⟨5738461400938615946471011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7651281867918154595294681 5738461400938615946471011)
                ·
                  refine ⟨8607692101407923919706517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5738461400938615946471011 8607692101407923919706517)
                  ·
                    refine ⟨403485567253496433736243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8607692101407923919706517 403485567253496433736243)
                    ·
                      rfl

theorem cell22_1178678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 2, 1, 6].length) (baseStart_1178678 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1178678 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1178678 prefixEnd_1178678 := by exact prefixLift 1178678
  have htrace : WordTrace (prefixWord ++ tailWord_1178678) baseStart_1178678 baseEnd_1178678 := by
    simpa [prefixWord, tailWord_1178678, baseEnd_1178678] using wordTrace_append hprefix tailTrace_1178678
  have hstable : (prefixWord ++ tailWord_1178678).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1178678).length < 2 ^ (prefixWord ++ tailWord_1178678).sum := by decide
  have hdescent : baseEnd_1178678 < baseStart_1178678 := by decide
  rcases family_descends (prefixWord ++ tailWord_1178678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1178708 : List Nat := [2, 4, 1, 1, 1, 1, 2, 2, 5, 3]
def baseStart_1178708 : Nat := 118140960795 + 1178708 * 2 ^ 59
def prefixEnd_1178708 : Nat := 4983230072969 + 3 ^ 40 * 1178708 * 2
def baseEnd_1178708 : Nat := 403495836866586355486151

theorem tailTrace_1178708 : CollatzResearch.WordTrace tailWord_1178708 prefixEnd_1178708 403495836866586355486151 := by
  unfold tailWord_1178708
  simp only [CollatzResearch.WordTrace]
  refine ⟨21495506306874849072308389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28660675075833132096411185 21495506306874849072308389)
  ·
    refine ⟨4030407432539034201057823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21495506306874849072308389 4030407432539034201057823)
    ·
      refine ⟨6045611148808551301586735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4030407432539034201057823 6045611148808551301586735)
      ·
        refine ⟨9068416723212826952380103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6045611148808551301586735 9068416723212826952380103)
        ·
          refine ⟨13602625084819240428570155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9068416723212826952380103 13602625084819240428570155)
          ·
            refine ⟨20403937627228860642855233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13602625084819240428570155 20403937627228860642855233)
            ·
              refine ⟨15302953220421645482141425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20403937627228860642855233 15302953220421645482141425)
              ·
                refine ⟨11477214915316234111606069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15302953220421645482141425 11477214915316234111606069)
                ·
                  refine ⟨1075988898310896947963069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 11477214915316234111606069 1075988898310896947963069)
                  ·
                    refine ⟨403495836866586355486151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1075988898310896947963069 403495836866586355486151)
                    ·
                      rfl

theorem cell22_1178708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 2, 5, 3].length) (baseStart_1178708 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1178708 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1178708 prefixEnd_1178708 := by exact prefixLift 1178708
  have htrace : WordTrace (prefixWord ++ tailWord_1178708) baseStart_1178708 baseEnd_1178708 := by
    simpa [prefixWord, tailWord_1178708, baseEnd_1178708] using wordTrace_append hprefix tailTrace_1178708
  have hstable : (prefixWord ++ tailWord_1178708).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1178708).length < 2 ^ (prefixWord ++ tailWord_1178708).sum := by decide
  have hdescent : baseEnd_1178708 < baseStart_1178708 := by decide
  rcases family_descends (prefixWord ++ tailWord_1178708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1178721 : List Nat := [1, 2, 3, 1, 1, 2, 4, 1, 7]
def baseStart_1178721 : Nat := 118140960795 + 1178721 * 2 ^ 59
def prefixEnd_1178721 : Nat := 4983230072969 + 3 ^ 40 * 1178721 * 2
def baseEnd_1178721 : Nat := 134500095677419551637037

theorem tailTrace_1178721 : CollatzResearch.WordTrace tailWord_1178721 prefixEnd_1178721 134500095677419551637037 := by
  unfold tailWord_1178721
  simp only [CollatzResearch.WordTrace]
  refine ⟨42991486762702601364840017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28660991175135067576560011 42991486762702601364840017)
  ·
    refine ⟨32243615072026951023630013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42991486762702601364840017 32243615072026951023630013)
    ·
      refine ⟨12091355652010106633861255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32243615072026951023630013 12091355652010106633861255)
      ·
        refine ⟨18137033478015159950791883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12091355652010106633861255 18137033478015159950791883)
        ·
          refine ⟨27205550217022739926187825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18137033478015159950791883 27205550217022739926187825)
          ·
            refine ⟨20404162662767054944640869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27205550217022739926187825 20404162662767054944640869)
            ·
              refine ⟨3825780499268822802120163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20404162662767054944640869 3825780499268822802120163)
              ·
                refine ⟨5738670748903234203180245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3825780499268822802120163 5738670748903234203180245)
                ·
                  refine ⟨134500095677419551637037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5738670748903234203180245 134500095677419551637037)
                  ·
                    rfl

theorem cell22_1178721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 4, 1, 7].length) (baseStart_1178721 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1178721 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1178721 prefixEnd_1178721 := by exact prefixLift 1178721
  have htrace : WordTrace (prefixWord ++ tailWord_1178721) baseStart_1178721 baseEnd_1178721 := by
    simpa [prefixWord, tailWord_1178721, baseEnd_1178721] using wordTrace_append hprefix tailTrace_1178721
  have hstable : (prefixWord ++ tailWord_1178721).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1178721).length < 2 ^ (prefixWord ++ tailWord_1178721).sum := by decide
  have hdescent : baseEnd_1178721 < baseStart_1178721 := by decide
  rcases family_descends (prefixWord ++ tailWord_1178721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1178736 : List Nat := [2, 1, 1, 1, 5, 1, 2, 1, 1, 7]
def baseStart_1178736 : Nat := 118140960795 + 1178736 * 2 ^ 59
def prefixEnd_1178736 : Nat := 4983230072969 + 3 ^ 40 * 1178736 * 2
def baseEnd_1178736 : Nat := 403505421838803615786065

theorem tailTrace_1178736 : CollatzResearch.WordTrace tailWord_1178736 prefixEnd_1178736 403505421838803615786065 := by
  unfold tailWord_1178736
  simp only [CollatzResearch.WordTrace]
  refine ⟨21496016928824129463318031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28661355905098839284424041 21496016928824129463318031)
  ·
    refine ⟨32244025393236194194977047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21496016928824129463318031 32244025393236194194977047)
    ·
      refine ⟨48366038089854291292465571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32244025393236194194977047 48366038089854291292465571)
      ·
        refine ⟨72549057134781436938698357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48366038089854291292465571 72549057134781436938698357)
        ·
          refine ⟨6801474106385759713002971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 72549057134781436938698357 6801474106385759713002971)
          ·
            refine ⟨10202211159578639569504457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6801474106385759713002971 10202211159578639569504457)
            ·
              refine ⟨7651658369683979677128343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10202211159578639569504457 7651658369683979677128343)
              ·
                refine ⟨11477487554525969515692515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7651658369683979677128343 11477487554525969515692515)
                ·
                  refine ⟨17216231331788954273538773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11477487554525969515692515 17216231331788954273538773)
                  ·
                    refine ⟨403505421838803615786065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 17216231331788954273538773 403505421838803615786065)
                    ·
                      rfl

theorem cell22_1178736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 1, 1, 7].length) (baseStart_1178736 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1178736 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1178736 prefixEnd_1178736 := by exact prefixLift 1178736
  have htrace : WordTrace (prefixWord ++ tailWord_1178736) baseStart_1178736 baseEnd_1178736 := by
    simpa [prefixWord, tailWord_1178736, baseEnd_1178736] using wordTrace_append hprefix tailTrace_1178736
  have hstable : (prefixWord ++ tailWord_1178736).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1178736).length < 2 ^ (prefixWord ++ tailWord_1178736).sum := by decide
  have hdescent : baseEnd_1178736 < baseStart_1178736 := by decide
  rcases family_descends (prefixWord ++ tailWord_1178736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1178738 : List Nat := [3, 2, 1, 2, 2, 1, 3, 3, 5]
def baseStart_1178738 : Nat := 118140960795 + 1178738 * 2 ^ 59
def prefixEnd_1178738 : Nat := 4983230072969 + 3 ^ 40 * 1178738 * 2
def baseEnd_1178738 : Nat := 134502035493225425745353

theorem tailTrace_1178738 : CollatzResearch.WordTrace tailWord_1178738 prefixEnd_1178738 134502035493225425745353 := by
  unfold tailWord_1178738
  simp only [CollatzResearch.WordTrace]
  refine ⟨10748026700910253317052217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28661404535760675512139245 10748026700910253317052217)
  ·
    refine ⟨8061020025682689987789163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10748026700910253317052217 8061020025682689987789163)
    ·
      refine ⟨12091530038524034981683745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8061020025682689987789163 12091530038524034981683745)
      ·
        refine ⟨9068647528893026236262809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12091530038524034981683745 9068647528893026236262809)
        ·
          refine ⟨6801485646669769677197107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9068647528893026236262809 6801485646669769677197107)
          ·
            refine ⟨10202228470004654515795661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6801485646669769677197107 10202228470004654515795661)
            ·
              refine ⟨3825835676251745443423373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10202228470004654515795661 3825835676251745443423373)
              ·
                refine ⟨1434688378594404541283765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3825835676251745443423373 1434688378594404541283765)
                ·
                  refine ⟨134502035493225425745353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1434688378594404541283765 134502035493225425745353)
                  ·
                    rfl

theorem cell22_1178738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 3, 3, 5].length) (baseStart_1178738 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1178738 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1178738 prefixEnd_1178738 := by exact prefixLift 1178738
  have htrace : WordTrace (prefixWord ++ tailWord_1178738) baseStart_1178738 baseEnd_1178738 := by
    simpa [prefixWord, tailWord_1178738, baseEnd_1178738] using wordTrace_append hprefix tailTrace_1178738
  have hstable : (prefixWord ++ tailWord_1178738).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1178738).length < 2 ^ (prefixWord ++ tailWord_1178738).sum := by decide
  have hdescent : baseEnd_1178738 < baseStart_1178738 := by decide
  rcases family_descends (prefixWord ++ tailWord_1178738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1178817 : List Nat := [1, 2, 6, 1, 1, 1, 1, 5, 4]
def baseStart_1178817 : Nat := 118140960795 + 1178817 * 2 ^ 59
def prefixEnd_1178817 : Nat := 4983230072969 + 3 ^ 40 * 1178817 * 2
def baseEnd_1178817 : Nat := 134511049931382134836939

theorem tailTrace_1178817 : CollatzResearch.WordTrace tailWord_1178817 prefixEnd_1178817 134511049931382134836939 := by
  unfold tailWord_1178817
  simp only [CollatzResearch.WordTrace]
  refine ⟨42994988170354809760334705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28663325446903206506889803 42994988170354809760334705)
  ·
    refine ⟨32246241127766107320251029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42994988170354809760334705 32246241127766107320251029)
    ·
      refine ⟨1511542552864036280636767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 32246241127766107320251029 1511542552864036280636767)
      ·
        refine ⟨2267313829296054420955151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1511542552864036280636767 2267313829296054420955151)
        ·
          refine ⟨3400970743944081631432727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2267313829296054420955151 3400970743944081631432727)
          ·
            refine ⟨5101456115916122447149091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3400970743944081631432727 5101456115916122447149091)
            ·
              refine ⟨7652184173874183670723637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5101456115916122447149091 7652184173874183670723637)
              ·
                refine ⟨717392266300704719130341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7652184173874183670723637 717392266300704719130341)
                ·
                  refine ⟨134511049931382134836939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 717392266300704719130341 134511049931382134836939)
                  ·
                    rfl

theorem cell22_1178817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 5, 4].length) (baseStart_1178817 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1178817 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1178817 prefixEnd_1178817 := by exact prefixLift 1178817
  have htrace : WordTrace (prefixWord ++ tailWord_1178817) baseStart_1178817 baseEnd_1178817 := by
    simpa [prefixWord, tailWord_1178817, baseEnd_1178817] using wordTrace_append hprefix tailTrace_1178817
  have hstable : (prefixWord ++ tailWord_1178817).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1178817).length < 2 ^ (prefixWord ++ tailWord_1178817).sum := by decide
  have hdescent : baseEnd_1178817 < baseStart_1178817 := by decide
  rcases family_descends (prefixWord ++ tailWord_1178817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1178860 : List Nat := [2, 2, 1, 1, 2, 4, 2, 2, 3, 3]
def baseStart_1178860 : Nat := 118140960795 + 1178860 * 2 ^ 59
def prefixEnd_1178860 : Nat := 4983230072969 + 3 ^ 40 * 1178860 * 2
def baseEnd_1178860 : Nat := 403547869572908625685685

theorem tailTrace_1178860 : CollatzResearch.WordTrace tailWord_1178860 prefixEnd_1178860 403547869572908625685685 := by
  unfold tailWord_1178860
  simp only [CollatzResearch.WordTrace]
  refine ⟨21498278254599514052075017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28664371006132685402766689 21498278254599514052075017)
  ·
    refine ⟨16123708690949635539056263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21498278254599514052075017 16123708690949635539056263)
    ·
      refine ⟨24185563036424453308584395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16123708690949635539056263 24185563036424453308584395)
      ·
        refine ⟨36278344554636679962876593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24185563036424453308584395 36278344554636679962876593)
        ·
          refine ⟨27208758415977509972157445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36278344554636679962876593 27208758415977509972157445)
          ·
            refine ⟨5101642202995783119779521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27208758415977509972157445 5101642202995783119779521)
            ·
              refine ⟨3826231652246837339834641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5101642202995783119779521 3826231652246837339834641)
              ·
                refine ⟨2869673739185128004875981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3826231652246837339834641 2869673739185128004875981)
                ·
                  refine ⟨1076127652194423001828493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2869673739185128004875981 1076127652194423001828493)
                  ·
                    refine ⟨403547869572908625685685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1076127652194423001828493 403547869572908625685685)
                    ·
                      rfl

theorem cell22_1178860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 3, 3].length) (baseStart_1178860 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1178860 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1178860 prefixEnd_1178860 := by exact prefixLift 1178860
  have htrace : WordTrace (prefixWord ++ tailWord_1178860) baseStart_1178860 baseEnd_1178860 := by
    simpa [prefixWord, tailWord_1178860, baseEnd_1178860] using wordTrace_append hprefix tailTrace_1178860
  have hstable : (prefixWord ++ tailWord_1178860).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1178860).length < 2 ^ (prefixWord ++ tailWord_1178860).sum := by decide
  have hdescent : baseEnd_1178860 < baseStart_1178860 := by decide
  rcases family_descends (prefixWord ++ tailWord_1178860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1178868 : List Nat := [2, 6, 1, 2, 1, 2, 1, 3, 4]
def baseStart_1178868 : Nat := 118140960795 + 1178868 * 2 ^ 59
def prefixEnd_1178868 : Nat := 4983230072969 + 3 ^ 40 * 1178868 * 2
def baseEnd_1178868 : Nat := 134516869378799757161887

theorem tailTrace_1178868 : CollatzResearch.WordTrace tailWord_1178868 prefixEnd_1178868 134516869378799757161887 := by
  unfold tailWord_1178868
  simp only [CollatzResearch.WordTrace]
  refine ⟨21498424146585022735220629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28664565528780030313627505 21498424146585022735220629)
  ·
    refine ⟨1007738631871172940713467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 21498424146585022735220629 1007738631871172940713467)
    ·
      refine ⟨1511607947806759411070201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1007738631871172940713467 1511607947806759411070201)
      ·
        refine ⟨1133705960855069558302651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1511607947806759411070201 1133705960855069558302651)
        ·
          refine ⟨1700558941282604337453977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1133705960855069558302651 1700558941282604337453977)
          ·
            refine ⟨1275419205961953253090483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1700558941282604337453977 1275419205961953253090483)
            ·
              refine ⟨1913128808942929879635725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1275419205961953253090483 1913128808942929879635725)
              ·
                refine ⟨717423303353598704863397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1913128808942929879635725 717423303353598704863397)
                ·
                  refine ⟨134516869378799757161887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 717423303353598704863397 134516869378799757161887)
                  ·
                    rfl

theorem cell22_1178868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 2, 1, 3, 4].length) (baseStart_1178868 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1178868 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1178868 prefixEnd_1178868 := by exact prefixLift 1178868
  have htrace : WordTrace (prefixWord ++ tailWord_1178868) baseStart_1178868 baseEnd_1178868 := by
    simpa [prefixWord, tailWord_1178868, baseEnd_1178868] using wordTrace_append hprefix tailTrace_1178868
  have hstable : (prefixWord ++ tailWord_1178868).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1178868).length < 2 ^ (prefixWord ++ tailWord_1178868).sum := by decide
  have hdescent : baseEnd_1178868 < baseStart_1178868 := by decide
  rcases family_descends (prefixWord ++ tailWord_1178868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1178967 : List Nat := [1, 1, 3, 2, 3, 2, 2, 3, 2, 3]
def baseStart_1178967 : Nat := 118140960795 + 1178967 * 2 ^ 59
def prefixEnd_1178967 : Nat := 4983230072969 + 3 ^ 40 * 1178967 * 2
def baseEnd_1178967 : Nat := 403584497859596013260357

theorem tailTrace_1178967 : CollatzResearch.WordTrace tailWord_1178967 prefixEnd_1178967 403584497859596013260357 := by
  unfold tailWord_1178967
  simp only [CollatzResearch.WordTrace]
  refine ⟨43000459119811385378295155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28666972746540923585530103 43000459119811385378295155)
  ·
    refine ⟨64500688679717078067442733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43000459119811385378295155 64500688679717078067442733)
    ·
      refine ⟨24187758254893904275291025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64500688679717078067442733 24187758254893904275291025)
      ·
        refine ⟨18140818691170428206468269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24187758254893904275291025 18140818691170428206468269)
        ·
          refine ⟨6802807009188910577425601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18140818691170428206468269 6802807009188910577425601)
          ·
            refine ⟨5102105256891682933069201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6802807009188910577425601 5102105256891682933069201)
            ·
              refine ⟨3826578942668762199801901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5102105256891682933069201 3826578942668762199801901)
              ·
                refine ⟨1434967103500785824925713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3826578942668762199801901 1434967103500785824925713)
                ·
                  refine ⟨1076225327625589368694285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1434967103500785824925713 1076225327625589368694285)
                  ·
                    refine ⟨403584497859596013260357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1076225327625589368694285 403584497859596013260357)
                    ·
                      rfl

theorem cell22_1178967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 2, 3, 2, 3].length) (baseStart_1178967 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1178967 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1178967 prefixEnd_1178967 := by exact prefixLift 1178967
  have htrace : WordTrace (prefixWord ++ tailWord_1178967) baseStart_1178967 baseEnd_1178967 := by
    simpa [prefixWord, tailWord_1178967, baseEnd_1178967] using wordTrace_append hprefix tailTrace_1178967
  have hstable : (prefixWord ++ tailWord_1178967).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1178967).length < 2 ^ (prefixWord ++ tailWord_1178967).sum := by decide
  have hdescent : baseEnd_1178967 < baseStart_1178967 := by decide
  rcases family_descends (prefixWord ++ tailWord_1178967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1179012 : List Nat := [2, 3, 2, 1, 1, 3, 1, 3, 3, 3]
def baseStart_1179012 : Nat := 118140960795 + 1179012 * 2 ^ 59
def prefixEnd_1179012 : Nat := 4983230072969 + 3 ^ 40 * 1179012 * 2
def baseEnd_1179012 : Nat := 403599902279230895885219

theorem tailTrace_1179012 : CollatzResearch.WordTrace tailWord_1179012 prefixEnd_1179012 403599902279230895885219 := by
  unfold tailWord_1179012
  simp only [CollatzResearch.WordTrace]
  refine ⟨21501050202324179031841645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28668066936432238709122193 21501050202324179031841645)
  ·
    refine ⟨8062893825871567136940617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21501050202324179031841645 8062893825871567136940617)
    ·
      refine ⟨6047170369403675352705463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8062893825871567136940617 6047170369403675352705463)
      ·
        refine ⟨9070755554105513029058195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6047170369403675352705463 9070755554105513029058195)
        ·
          refine ⟨13606133331158269543587293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9070755554105513029058195 13606133331158269543587293)
          ·
            refine ⟨5102299999184351078845235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13606133331158269543587293 5102299999184351078845235)
            ·
              refine ⟨7653449998776526618267853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5102299999184351078845235 7653449998776526618267853)
              ·
                refine ⟨2870043749541197481850445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7653449998776526618267853 2870043749541197481850445)
                ·
                  refine ⟨1076266406077949055693917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2870043749541197481850445 1076266406077949055693917)
                  ·
                    refine ⟨403599902279230895885219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1076266406077949055693917 403599902279230895885219)
                    ·
                      rfl

theorem cell22_1179012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 3, 3, 3].length) (baseStart_1179012 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1179012 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1179012 prefixEnd_1179012 := by exact prefixLift 1179012
  have htrace : WordTrace (prefixWord ++ tailWord_1179012) baseStart_1179012 baseEnd_1179012 := by
    simpa [prefixWord, tailWord_1179012, baseEnd_1179012] using wordTrace_append hprefix tailTrace_1179012
  have hstable : (prefixWord ++ tailWord_1179012).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1179012).length < 2 ^ (prefixWord ++ tailWord_1179012).sum := by decide
  have hdescent : baseEnd_1179012 < baseStart_1179012 := by decide
  rcases family_descends (prefixWord ++ tailWord_1179012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1179076 : List Nat := [2, 3, 3, 2, 1, 3, 2, 1, 5]
def baseStart_1179076 : Nat := 118140960795 + 1179076 * 2 ^ 59
def prefixEnd_1179076 : Nat := 4983230072969 + 3 ^ 40 * 1179076 * 2
def baseEnd_1179076 : Nat := 134540603595718687428341

theorem tailTrace_1179076 : CollatzResearch.WordTrace tailWord_1179076 prefixEnd_1179076 134540603595718687428341 := by
  unfold tailWord_1179076
  simp only [CollatzResearch.WordTrace]
  refine ⟨21502217338208248497006541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28669623117610997996008721 21502217338208248497006541)
  ·
    refine ⟨8063331501828093186377453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21502217338208248497006541 8063331501828093186377453)
    ·
      refine ⟨3023749313185534944891545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8063331501828093186377453 3023749313185534944891545)
      ·
        refine ⟨2267811984889151208668659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3023749313185534944891545 2267811984889151208668659)
        ·
          refine ⟨3401717977333726813002989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2267811984889151208668659 3401717977333726813002989)
          ·
            refine ⟨1275644241500147554876121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3401717977333726813002989 1275644241500147554876121)
            ·
              refine ⟨956733181125110666157091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1275644241500147554876121 956733181125110666157091)
              ·
                refine ⟨1435099771687665999235637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 956733181125110666157091 1435099771687665999235637)
                ·
                  refine ⟨134540603595718687428341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1435099771687665999235637 134540603595718687428341)
                  ·
                    rfl

theorem cell22_1179076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 3, 2, 1, 5].length) (baseStart_1179076 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1179076 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1179076 prefixEnd_1179076 := by exact prefixLift 1179076
  have htrace : WordTrace (prefixWord ++ tailWord_1179076) baseStart_1179076 baseEnd_1179076 := by
    simpa [prefixWord, tailWord_1179076, baseEnd_1179076] using wordTrace_append hprefix tailTrace_1179076
  have hstable : (prefixWord ++ tailWord_1179076).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1179076).length < 2 ^ (prefixWord ++ tailWord_1179076).sum := by decide
  have hdescent : baseEnd_1179076 < baseStart_1179076 := by decide
  rcases family_descends (prefixWord ++ tailWord_1179076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1179121 : List Nat := [1, 2, 2, 2, 3, 4, 2, 2, 4]
def baseStart_1179121 : Nat := 118140960795 + 1179121 * 2 ^ 59
def prefixEnd_1179121 : Nat := 4983230072969 + 3 ^ 40 * 1179121 * 2
def baseEnd_1179121 : Nat := 134545738402263648303295

theorem tailTrace_1179121 : CollatzResearch.WordTrace tailWord_1179121 prefixEnd_1179121 134545738402263648303295 := by
  unfold tailWord_1179121
  simp only [CollatzResearch.WordTrace]
  refine ⟨43006075961253469679401217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28670717307502313119600811 43006075961253469679401217)
  ·
    refine ⟨32254556970940102259550913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43006075961253469679401217 32254556970940102259550913)
    ·
      refine ⟨24190917728205076694663185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32254556970940102259550913 24190917728205076694663185)
      ·
        refine ⟨18143188296153807520997389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24190917728205076694663185 18143188296153807520997389)
        ·
          refine ⟨6803695611057677820374021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18143188296153807520997389 6803695611057677820374021)
          ·
            refine ⟨1275692927073314591320129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6803695611057677820374021 1275692927073314591320129)
            ·
              refine ⟨956769695304985943490097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1275692927073314591320129 956769695304985943490097)
              ·
                refine ⟨717577271478739457617573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 956769695304985943490097 717577271478739457617573)
                ·
                  refine ⟨134545738402263648303295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 717577271478739457617573 134545738402263648303295)
                  ·
                    rfl

theorem cell22_1179121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 4, 2, 2, 4].length) (baseStart_1179121 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1179121 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1179121 prefixEnd_1179121 := by exact prefixLift 1179121
  have htrace : WordTrace (prefixWord ++ tailWord_1179121) baseStart_1179121 baseEnd_1179121 := by
    simpa [prefixWord, tailWord_1179121, baseEnd_1179121] using wordTrace_append hprefix tailTrace_1179121
  have hstable : (prefixWord ++ tailWord_1179121).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1179121).length < 2 ^ (prefixWord ++ tailWord_1179121).sum := by decide
  have hdescent : baseEnd_1179121 < baseStart_1179121 := by decide
  rcases family_descends (prefixWord ++ tailWord_1179121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1179145 : List Nat := [1, 2, 1, 1, 3, 1, 3, 2, 2, 6]
def baseStart_1179145 : Nat := 118140960795 + 1179145 * 2 ^ 59
def prefixEnd_1179145 : Nat := 4983230072969 + 3 ^ 40 * 1179145 * 2
def baseEnd_1179145 : Nat := 403645430897262882309811

theorem tailTrace_1179145 : CollatzResearch.WordTrace tailWord_1179145 prefixEnd_1179145 403645430897262882309811 := by
  unfold tailWord_1179145
  simp only [CollatzResearch.WordTrace]
  refine ⟨43006951313166521778274889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28671300875444347852183259 43006951313166521778274889)
  ·
    refine ⟨32255213484874891333706167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43006951313166521778274889 32255213484874891333706167)
    ·
      refine ⟨48382820227312337000559251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32255213484874891333706167 48382820227312337000559251)
      ·
        refine ⟨72574230340968505500838877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48382820227312337000559251 72574230340968505500838877)
        ·
          refine ⟨27215336377863189562814579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 72574230340968505500838877 27215336377863189562814579)
          ·
            refine ⟨40823004566794784344221869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27215336377863189562814579 40823004566794784344221869)
            ·
              refine ⟨15308626712548044129083201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40823004566794784344221869 15308626712548044129083201)
              ·
                refine ⟨11481470034411033096812401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15308626712548044129083201 11481470034411033096812401)
                ·
                  refine ⟨8611102525808274822609301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11481470034411033096812401 8611102525808274822609301)
                  ·
                    refine ⟨403645430897262882309811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8611102525808274822609301 403645430897262882309811)
                    ·
                      rfl

theorem cell22_1179145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 2, 2, 6].length) (baseStart_1179145 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1179145 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1179145 prefixEnd_1179145 := by exact prefixLift 1179145
  have htrace : WordTrace (prefixWord ++ tailWord_1179145) baseStart_1179145 baseEnd_1179145 := by
    simpa [prefixWord, tailWord_1179145, baseEnd_1179145] using wordTrace_append hprefix tailTrace_1179145
  have hstable : (prefixWord ++ tailWord_1179145).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1179145).length < 2 ^ (prefixWord ++ tailWord_1179145).sum := by decide
  have hdescent : baseEnd_1179145 < baseStart_1179145 := by decide
  rcases family_descends (prefixWord ++ tailWord_1179145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1179192 : List Nat := [2, 1, 2, 1, 4, 2, 2, 1, 2, 5]
def baseStart_1179192 : Nat := 118140960795 + 1179192 * 2 ^ 59
def prefixEnd_1179192 : Nat := 4983230072969 + 3 ^ 40 * 1179192 * 2
def baseEnd_1179192 : Nat := 403661519957770426384667

theorem tailTrace_1179192 : CollatzResearch.WordTrace tailWord_1179192 prefixEnd_1179192 403661519957770426384667 := by
  unfold tailWord_1179192
  simp only [CollatzResearch.WordTrace]
  refine ⟨21504332771998124402617915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28672443695997499203490553 21504332771998124402617915)
  ·
    refine ⟨32256499157997186603926873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21504332771998124402617915 32256499157997186603926873)
    ·
      refine ⟨24192374368497889952945155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32256499157997186603926873 24192374368497889952945155)
      ·
        refine ⟨36288561552746834929417733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24192374368497889952945155 36288561552746834929417733)
        ·
          refine ⟨6804105291140031549265825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 36288561552746834929417733 6804105291140031549265825)
          ·
            refine ⟨5103078968355023661949369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6804105291140031549265825 5103078968355023661949369)
            ·
              refine ⟨3827309226266267746462027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5103078968355023661949369 3827309226266267746462027)
              ·
                refine ⟨5740963839399401619693041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3827309226266267746462027 5740963839399401619693041)
                ·
                  refine ⟨4305722879549551214769781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5740963839399401619693041 4305722879549551214769781)
                  ·
                    refine ⟨403661519957770426384667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4305722879549551214769781 403661519957770426384667)
                    ·
                      rfl

theorem cell22_1179192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 1, 2, 5].length) (baseStart_1179192 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1179192 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1179192 prefixEnd_1179192 := by exact prefixLift 1179192
  have htrace : WordTrace (prefixWord ++ tailWord_1179192) baseStart_1179192 baseEnd_1179192 := by
    simpa [prefixWord, tailWord_1179192, baseEnd_1179192] using wordTrace_append hprefix tailTrace_1179192
  have hstable : (prefixWord ++ tailWord_1179192).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1179192).length < 2 ^ (prefixWord ++ tailWord_1179192).sum := by decide
  have hdescent : baseEnd_1179192 < baseStart_1179192 := by decide
  rcases family_descends (prefixWord ++ tailWord_1179192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1179194 : List Nat := [3, 1, 1, 1, 3, 2, 5, 1, 5]
def baseStart_1179194 : Nat := 118140960795 + 1179194 * 2 ^ 59
def prefixEnd_1179194 : Nat := 4983230072969 + 3 ^ 40 * 1179194 * 2
def baseEnd_1179194 : Nat := 134554068199547695944887

theorem tailTrace_1179194 : CollatzResearch.WordTrace tailWord_1179194 prefixEnd_1179194 134554068199547695944887 := by
  unfold tailWord_1179194
  simp only [CollatzResearch.WordTrace]
  refine ⟨10752184622497250786702159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28672492326659335431205757 10752184622497250786702159)
  ·
    refine ⟨16128276933745876180053239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10752184622497250786702159 16128276933745876180053239)
    ·
      refine ⟨24192415400618814270079859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16128276933745876180053239 24192415400618814270079859)
      ·
        refine ⟨36288623100928221405119789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24192415400618814270079859 36288623100928221405119789)
        ·
          refine ⟨13608233662848083026919921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36288623100928221405119789 13608233662848083026919921)
          ·
            refine ⟨10206175247136062270189941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13608233662848083026919921 10206175247136062270189941)
            ·
              refine ⟨956828929419005837830307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10206175247136062270189941 956828929419005837830307)
              ·
                refine ⟨1435243394128508756745461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 956828929419005837830307 1435243394128508756745461)
                ·
                  refine ⟨134554068199547695944887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1435243394128508756745461 134554068199547695944887)
                  ·
                    rfl

theorem cell22_1179194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 5, 1, 5].length) (baseStart_1179194 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1179194 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1179194 prefixEnd_1179194 := by exact prefixLift 1179194
  have htrace : WordTrace (prefixWord ++ tailWord_1179194) baseStart_1179194 baseEnd_1179194 := by
    simpa [prefixWord, tailWord_1179194, baseEnd_1179194] using wordTrace_append hprefix tailTrace_1179194
  have hstable : (prefixWord ++ tailWord_1179194).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1179194).length < 2 ^ (prefixWord ++ tailWord_1179194).sum := by decide
  have hdescent : baseEnd_1179194 < baseStart_1179194 := by decide
  rcases family_descends (prefixWord ++ tailWord_1179194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1179239 : List Nat := [1, 1, 5, 1, 1, 1, 2, 6, 4]
def baseStart_1179239 : Nat := 118140960795 + 1179239 * 2 ^ 59
def prefixEnd_1179239 : Nat := 4983230072969 + 3 ^ 40 * 1179239 * 2
def baseEnd_1179239 : Nat := 134559203006092656819841

theorem tailTrace_1179239 : CollatzResearch.WordTrace tailWord_1179239 prefixEnd_1179239 134559203006092656819841 := by
  unfold tailWord_1179239
  simp only [CollatzResearch.WordTrace]
  refine ⟨43010379774825975832196771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28673586516550650554797847 43010379774825975832196771)
  ·
    refine ⟨64515569662238963748295157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43010379774825975832196771 64515569662238963748295157)
    ·
      refine ⟨6048334655834902851402671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 64515569662238963748295157 6048334655834902851402671)
      ·
        refine ⟨9072501983752354277104007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6048334655834902851402671 9072501983752354277104007)
        ·
          refine ⟨13608752975628531415656011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9072501983752354277104007 13608752975628531415656011)
          ·
            refine ⟨20413129463442797123484017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13608752975628531415656011 20413129463442797123484017)
            ·
              refine ⟨15309847097582097842613013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20413129463442797123484017 15309847097582097842613013)
              ·
                refine ⟨717649082699160836372485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 15309847097582097842613013 717649082699160836372485)
                ·
                  refine ⟨134559203006092656819841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 717649082699160836372485 134559203006092656819841)
                  ·
                    rfl

theorem cell22_1179239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 6, 4].length) (baseStart_1179239 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1179239 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1179239 prefixEnd_1179239 := by exact prefixLift 1179239
  have htrace : WordTrace (prefixWord ++ tailWord_1179239) baseStart_1179239 baseEnd_1179239 := by
    simpa [prefixWord, tailWord_1179239, baseEnd_1179239] using wordTrace_append hprefix tailTrace_1179239
  have hstable : (prefixWord ++ tailWord_1179239).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1179239).length < 2 ^ (prefixWord ++ tailWord_1179239).sum := by decide
  have hdescent : baseEnd_1179239 < baseStart_1179239 := by decide
  rcases family_descends (prefixWord ++ tailWord_1179239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1179269 : List Nat := [1, 3, 1, 1, 4, 1, 4, 1, 2, 4]
def baseStart_1179269 : Nat := 118140960795 + 1179269 * 2 ^ 59
def prefixEnd_1179269 : Nat := 4983230072969 + 3 ^ 40 * 1179269 * 2
def baseEnd_1179269 : Nat := 403687878631367892209431

theorem tailTrace_1179269 : CollatzResearch.WordTrace tailWord_1179269 prefixEnd_1179269 403687878631367892209431 := by
  unfold tailWord_1179269
  simp only [CollatzResearch.WordTrace]
  refine ⟨43011473964717290955788861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28674315976478193970525907 43011473964717290955788861)
  ·
    refine ⟨16129302736768984108420823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43011473964717290955788861 16129302736768984108420823)
    ·
      refine ⟨24193954105153476162631235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16129302736768984108420823 24193954105153476162631235)
      ·
        refine ⟨36290931157730214243946853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24193954105153476162631235 36290931157730214243946853)
        ·
          refine ⟨6804549592074415170740035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 36290931157730214243946853 6804549592074415170740035)
          ·
            refine ⟨10206824388111622756110053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6804549592074415170740035 10206824388111622756110053)
            ·
              refine ⟨1913779572770929266770635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10206824388111622756110053 1913779572770929266770635)
              ·
                refine ⟨2870669359156393900155953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1913779572770929266770635 2870669359156393900155953)
                ·
                  refine ⟨2153002019367295425116965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2870669359156393900155953 2153002019367295425116965)
                  ·
                    refine ⟨403687878631367892209431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2153002019367295425116965 403687878631367892209431)
                    ·
                      rfl

theorem cell22_1179269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 4, 1, 2, 4].length) (baseStart_1179269 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1179269 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1179269 prefixEnd_1179269 := by exact prefixLift 1179269
  have htrace : WordTrace (prefixWord ++ tailWord_1179269) baseStart_1179269 baseEnd_1179269 := by
    simpa [prefixWord, tailWord_1179269, baseEnd_1179269] using wordTrace_append hprefix tailTrace_1179269
  have hstable : (prefixWord ++ tailWord_1179269).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1179269).length < 2 ^ (prefixWord ++ tailWord_1179269).sum := by decide
  have hdescent : baseEnd_1179269 < baseStart_1179269 := by decide
  rcases family_descends (prefixWord ++ tailWord_1179269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1179284 : List Nat := [2, 4, 2, 2, 2, 10]
def baseStart_1179284 : Nat := 118140960795 + 1179284 * 2 ^ 59
def prefixEnd_1179284 : Nat := 4983230072969 + 3 ^ 40 * 1179284 * 2
def baseEnd_1179284 : Nat := 4983864363431022877585

theorem tailTrace_1179284 : CollatzResearch.WordTrace tailWord_1179284 prefixEnd_1179284 4983864363431022877585 := by
  unfold tailWord_1179284
  simp only [CollatzResearch.WordTrace]
  refine ⟨21506010529831474258792453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28674680706441965678389937 21506010529831474258792453)
  ·
    refine ⟨4032376974343401423523585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21506010529831474258792453 4032376974343401423523585)
    ·
      refine ⟨3024282730757551067642689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4032376974343401423523585 3024282730757551067642689)
      ·
        refine ⟨2268212048068163300732017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3024282730757551067642689 2268212048068163300732017)
        ·
          refine ⟨1701159036051122475549013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2268212048068163300732017 1701159036051122475549013)
          ·
            refine ⟨4983864363431022877585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 1701159036051122475549013 4983864363431022877585)
            ·
              rfl

theorem cell22_1179284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 10].length) (baseStart_1179284 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1179284 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1179284 prefixEnd_1179284 := by exact prefixLift 1179284
  have htrace : WordTrace (prefixWord ++ tailWord_1179284) baseStart_1179284 baseEnd_1179284 := by
    simpa [prefixWord, tailWord_1179284, baseEnd_1179284] using wordTrace_append hprefix tailTrace_1179284
  have hstable : (prefixWord ++ tailWord_1179284).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1179284).length < 2 ^ (prefixWord ++ tailWord_1179284).sum := by decide
  have hdescent : baseEnd_1179284 < baseStart_1179284 := by decide
  rcases family_descends (prefixWord ++ tailWord_1179284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1179299 : List Nat := [1, 1, 1, 4, 1, 1, 4, 3, 3, 3]
def baseStart_1179299 : Nat := 118140960795 + 1179299 * 2 ^ 59
def prefixEnd_1179299 : Nat := 4983230072969 + 3 ^ 40 * 1179299 * 2
def baseEnd_1179299 : Nat := 403698148244457813959339

theorem tailTrace_1179299 : CollatzResearch.WordTrace tailWord_1179299 prefixEnd_1179299 403698148244457813959339 := by
  unfold tailWord_1179299
  simp only [CollatzResearch.WordTrace]
  refine ⟨43012568154608606079380951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28675045436405737386253967 43012568154608606079380951)
  ·
    refine ⟨64518852231912909119071427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43012568154608606079380951 64518852231912909119071427)
    ·
      refine ⟨96778278347869363678607141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64518852231912909119071427 96778278347869363678607141)
      ·
        refine ⟨18145927190225505689738839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 96778278347869363678607141 18145927190225505689738839)
        ·
          refine ⟨27218890785338258534608259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18145927190225505689738839 27218890785338258534608259)
          ·
            refine ⟨40828336178007387801912389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27218890785338258534608259 40828336178007387801912389)
            ·
              refine ⟨7655313033376385212858573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40828336178007387801912389 7655313033376385212858573)
              ·
                refine ⟨2870742387516144454821965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7655313033376385212858573 2870742387516144454821965)
                ·
                  refine ⟨1076528395318554170558237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2870742387516144454821965 1076528395318554170558237)
                  ·
                    refine ⟨403698148244457813959339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1076528395318554170558237 403698148244457813959339)
                    ·
                      rfl

theorem cell22_1179299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 3, 3, 3].length) (baseStart_1179299 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1179299 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1179299 prefixEnd_1179299 := by exact prefixLift 1179299
  have htrace : WordTrace (prefixWord ++ tailWord_1179299) baseStart_1179299 baseEnd_1179299 := by
    simpa [prefixWord, tailWord_1179299, baseEnd_1179299] using wordTrace_append hprefix tailTrace_1179299
  have hstable : (prefixWord ++ tailWord_1179299).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1179299).length < 2 ^ (prefixWord ++ tailWord_1179299).sum := by decide
  have hdescent : baseEnd_1179299 < baseStart_1179299 := by decide
  rcases family_descends (prefixWord ++ tailWord_1179299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1179318 : List Nat := [5, 1, 3, 1, 1, 2, 3, 6]
def baseStart_1179318 : Nat := 118140960795 + 1179318 * 2 ^ 59
def prefixEnd_1179318 : Nat := 4983230072969 + 3 ^ 40 * 1179318 * 2
def baseEnd_1179318 : Nat := 44856072481416455303809

theorem tailTrace_1179318 : CollatzResearch.WordTrace tailWord_1179318 prefixEnd_1179318 44856072481416455303809 := by
  unfold tailWord_1179318
  simp only [CollatzResearch.WordTrace]
  refine ⟨2688328821346235770270163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 28675507427693181549548405 2688328821346235770270163)
  ·
    refine ⟨4032493232019353655405245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2688328821346235770270163 4032493232019353655405245)
    ·
      refine ⟨1512184962007257620776967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4032493232019353655405245 1512184962007257620776967)
      ·
        refine ⟨2268277443010886431165451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1512184962007257620776967 2268277443010886431165451)
        ·
          refine ⟨3402416164516329646748177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2268277443010886431165451 3402416164516329646748177)
          ·
            refine ⟨2551812123387247235061133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3402416164516329646748177 2551812123387247235061133)
            ·
              refine ⟨956929546270217713147925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2551812123387247235061133 956929546270217713147925)
              ·
                refine ⟨44856072481416455303809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 956929546270217713147925 44856072481416455303809)
                ·
                  rfl

theorem cell22_1179318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 3, 6].length) (baseStart_1179318 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1179318 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1179318 prefixEnd_1179318 := by exact prefixLift 1179318
  have htrace : WordTrace (prefixWord ++ tailWord_1179318) baseStart_1179318 baseEnd_1179318 := by
    simpa [prefixWord, tailWord_1179318, baseEnd_1179318] using wordTrace_append hprefix tailTrace_1179318
  have hstable : (prefixWord ++ tailWord_1179318).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1179318).length < 2 ^ (prefixWord ++ tailWord_1179318).sum := by decide
  have hdescent : baseEnd_1179318 < baseStart_1179318 := by decide
  rcases family_descends (prefixWord ++ tailWord_1179318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1179327 : List Nat := [1, 1, 2, 2, 2, 3, 1, 2, 1, 7]
def baseStart_1179327 : Nat := 118140960795 + 1179327 * 2 ^ 59
def prefixEnd_1179327 : Nat := 4983230072969 + 3 ^ 40 * 1179327 * 2
def baseEnd_1179327 : Nat := 403707733216675074259253

theorem tailTrace_1179327 : CollatzResearch.WordTrace tailWord_1179327 prefixEnd_1179327 403707733216675074259253 := by
  unfold tailWord_1179327
  simp only [CollatzResearch.WordTrace]
  refine ⟨43013589398507166861400235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28675726265671444574266823 43013589398507166861400235)
  ·
    refine ⟨64520384097760750292100353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43013589398507166861400235 64520384097760750292100353)
    ·
      refine ⟨48390288073320562719075265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64520384097760750292100353 48390288073320562719075265)
      ·
        refine ⟨36292716054990422039306449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48390288073320562719075265 36292716054990422039306449)
        ·
          refine ⟨27219537041242816529479837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36292716054990422039306449 27219537041242816529479837)
          ·
            refine ⟨10207326390466056198554939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27219537041242816529479837 10207326390466056198554939)
            ·
              refine ⟨15310989585699084297832409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10207326390466056198554939 15310989585699084297832409)
              ·
                refine ⟨11483242189274313223374307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15310989585699084297832409 11483242189274313223374307)
                ·
                  refine ⟨17224863283911469835061461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11483242189274313223374307 17224863283911469835061461)
                  ·
                    refine ⟨403707733216675074259253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 17224863283911469835061461 403707733216675074259253)
                    ·
                      rfl

theorem cell22_1179327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 2, 1, 7].length) (baseStart_1179327 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1179327 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1179327 prefixEnd_1179327 := by exact prefixLift 1179327
  have htrace : WordTrace (prefixWord ++ tailWord_1179327) baseStart_1179327 baseEnd_1179327 := by
    simpa [prefixWord, tailWord_1179327, baseEnd_1179327] using wordTrace_append hprefix tailTrace_1179327
  have hstable : (prefixWord ++ tailWord_1179327).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1179327).length < 2 ^ (prefixWord ++ tailWord_1179327).sum := by decide
  have hdescent : baseEnd_1179327 < baseStart_1179327 := by decide
  rcases family_descends (prefixWord ++ tailWord_1179327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1179346 : List Nat := [3, 2, 2, 2, 2, 1, 3, 2, 5]
def baseStart_1179346 : Nat := 118140960795 + 1179346 * 2 ^ 59
def prefixEnd_1179346 : Nat := 4983230072969 + 3 ^ 40 * 1179346 * 2
def baseEnd_1179346 : Nat := 134571412434988452678065

theorem tailTrace_1179346 : CollatzResearch.WordTrace tailWord_1179346 prefixEnd_1179346 134571412434988452678065 := by
  unfold tailWord_1179346
  simp only [CollatzResearch.WordTrace]
  refine ⟨10753570596359583276585473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28676188256958888737561261 10753570596359583276585473)
  ·
    refine ⟨8065177947269687457439105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10753570596359583276585473 8065177947269687457439105)
    ·
      refine ⟨6048883460452265593079329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8065177947269687457439105 6048883460452265593079329)
      ·
        refine ⟨4536662595339199194809497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6048883460452265593079329 4536662595339199194809497)
        ·
          refine ⟨3402496946504399396107123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4536662595339199194809497 3402496946504399396107123)
          ·
            refine ⟨5103745419756599094160685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3402496946504399396107123 5103745419756599094160685)
            ·
              refine ⟨1913904532408724660310257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5103745419756599094160685 1913904532408724660310257)
              ·
                refine ⟨1435428399306543495232693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1913904532408724660310257 1435428399306543495232693)
                ·
                  refine ⟨134571412434988452678065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1435428399306543495232693 134571412434988452678065)
                  ·
                    rfl

theorem cell22_1179346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 3, 2, 5].length) (baseStart_1179346 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1179346 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1179346 prefixEnd_1179346 := by exact prefixLift 1179346
  have htrace : WordTrace (prefixWord ++ tailWord_1179346) baseStart_1179346 baseEnd_1179346 := by
    simpa [prefixWord, tailWord_1179346, baseEnd_1179346] using wordTrace_append hprefix tailTrace_1179346
  have hstable : (prefixWord ++ tailWord_1179346).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1179346).length < 2 ^ (prefixWord ++ tailWord_1179346).sum := by decide
  have hdescent : baseEnd_1179346 < baseStart_1179346 := by decide
  rcases family_descends (prefixWord ++ tailWord_1179346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1179363 : List Nat := [1, 1, 1, 7, 2, 1, 3, 1, 5]
def baseStart_1179363 : Nat := 118140960795 + 1179363 * 2 ^ 59
def prefixEnd_1179363 : Nat := 4983230072969 + 3 ^ 40 * 1179363 * 2
def baseEnd_1179363 : Nat := 134573352250794326786381

theorem tailTrace_1179363 : CollatzResearch.WordTrace tailWord_1179363 prefixEnd_1179363 134573352250794326786381 := by
  unfold tailWord_1179363
  simp only [CollatzResearch.WordTrace]
  refine ⟨43014902426376745009710743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28676601617584496673140495 43014902426376745009710743)
  ·
    refine ⟨64522353639565117514566115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43014902426376745009710743 64522353639565117514566115)
    ·
      refine ⟨96783530459347676271849173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64522353639565117514566115 96783530459347676271849173)
      ·
        refine ⟨2268363995140961162621465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 96783530459347676271849173 2268363995140961162621465)
        ·
          refine ⟨1701272996355720871966099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2268363995140961162621465 1701272996355720871966099)
          ·
            refine ⟨2551909494533581307949149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1701272996355720871966099 2551909494533581307949149)
            ·
              refine ⟨956966060450092990480931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2551909494533581307949149 956966060450092990480931)
              ·
                refine ⟨1435449090675139485721397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 956966060450092990480931 1435449090675139485721397)
                ·
                  refine ⟨134573352250794326786381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1435449090675139485721397 134573352250794326786381)
                  ·
                    rfl

theorem cell22_1179363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 3, 1, 5].length) (baseStart_1179363 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1179363 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1179363 prefixEnd_1179363 := by exact prefixLift 1179363
  have htrace : WordTrace (prefixWord ++ tailWord_1179363) baseStart_1179363 baseEnd_1179363 := by
    simpa [prefixWord, tailWord_1179363, baseEnd_1179363] using wordTrace_append hprefix tailTrace_1179363
  have hstable : (prefixWord ++ tailWord_1179363).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1179363).length < 2 ^ (prefixWord ++ tailWord_1179363).sum := by decide
  have hdescent : baseEnd_1179363 < baseStart_1179363 := by decide
  rcases family_descends (prefixWord ++ tailWord_1179363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1179374 : List Nat := [4, 1, 2, 1, 1, 2, 1, 4, 6]
def baseStart_1179374 : Nat := 118140960795 + 1179374 * 2 ^ 59
def prefixEnd_1179374 : Nat := 4983230072969 + 3 ^ 40 * 1179374 * 2
def baseEnd_1179374 : Nat := 134574607425727539444703

theorem tailTrace_1179374 : CollatzResearch.WordTrace tailWord_1179374 prefixEnd_1179374 134574607425727539444703 := by
  unfold tailWord_1179374
  simp only [CollatzResearch.WordTrace]
  refine ⟨5376912953667111736045147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28676869086224595925574117 5376912953667111736045147)
  ·
    refine ⟨8065369430500667604067721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5376912953667111736045147 8065369430500667604067721)
    ·
      refine ⟨6049027072875500703050791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8065369430500667604067721 6049027072875500703050791)
      ·
        refine ⟨9073540609313251054576187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6049027072875500703050791 9073540609313251054576187)
        ·
          refine ⟨13610310913969876581864281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9073540609313251054576187 13610310913969876581864281)
          ·
            refine ⟨10207733185477407436398211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13610310913969876581864281 10207733185477407436398211)
            ·
              refine ⟨15311599778216111154597317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10207733185477407436398211 15311599778216111154597317)
              ·
                refine ⟨2870924958415520841486997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15311599778216111154597317 2870924958415520841486997)
                ·
                  refine ⟨134574607425727539444703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2870924958415520841486997 134574607425727539444703)
                  ·
                    rfl

theorem cell22_1179374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 4, 6].length) (baseStart_1179374 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1179374 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1179374 prefixEnd_1179374 := by exact prefixLift 1179374
  have htrace : WordTrace (prefixWord ++ tailWord_1179374) baseStart_1179374 baseEnd_1179374 := by
    simpa [prefixWord, tailWord_1179374, baseEnd_1179374] using wordTrace_append hprefix tailTrace_1179374
  have hstable : (prefixWord ++ tailWord_1179374).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1179374).length < 2 ^ (prefixWord ++ tailWord_1179374).sum := by decide
  have hdescent : baseEnd_1179374 < baseStart_1179374 := by decide
  rcases family_descends (prefixWord ++ tailWord_1179374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1179391 : List Nat := [1, 1, 2, 2, 1, 3, 5, 3, 4]
def baseStart_1179391 : Nat := 118140960795 + 1179391 * 2 ^ 59
def prefixEnd_1179391 : Nat := 4983230072969 + 3 ^ 40 * 1179391 * 2
def baseEnd_1179391 : Nat := 134576547241533413553019

theorem tailTrace_1179391 : CollatzResearch.WordTrace tailWord_1179391 prefixEnd_1179391 134576547241533413553019 := by
  unfold tailWord_1179391
  simp only [CollatzResearch.WordTrace]
  refine ⟨43015923670275305791730027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28677282446850203861153351 43015923670275305791730027)
  ·
    refine ⟨64523885505412958687595041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43015923670275305791730027 64523885505412958687595041)
    ·
      refine ⟨48392914129059719015696281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64523885505412958687595041 48392914129059719015696281)
      ·
        refine ⟨36294685596794789261772211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48392914129059719015696281 36294685596794789261772211)
        ·
          refine ⟨54442028395192183892658317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36294685596794789261772211 54442028395192183892658317)
          ·
            refine ⟨20415760648197068959746869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54442028395192183892658317 20415760648197068959746869)
            ·
              refine ⟨1913977560768475214976269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 20415760648197068959746869 1913977560768475214976269)
              ·
                refine ⟨717741585288178205616101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1913977560768475214976269 717741585288178205616101)
                ·
                  refine ⟨134576547241533413553019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 717741585288178205616101 134576547241533413553019)
                  ·
                    rfl

theorem cell22_1179391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 5, 3, 4].length) (baseStart_1179391 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1179391 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1179391 prefixEnd_1179391 := by exact prefixLift 1179391
  have htrace : WordTrace (prefixWord ++ tailWord_1179391) baseStart_1179391 baseEnd_1179391 := by
    simpa [prefixWord, tailWord_1179391, baseEnd_1179391] using wordTrace_append hprefix tailTrace_1179391
  have hstable : (prefixWord ++ tailWord_1179391).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1179391).length < 2 ^ (prefixWord ++ tailWord_1179391).sum := by decide
  have hdescent : baseEnd_1179391 < baseStart_1179391 := by decide
  rcases family_descends (prefixWord ++ tailWord_1179391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1179404 : List Nat := [2, 2, 1, 2, 2, 1, 3, 1, 4, 4]
def baseStart_1179404 : Nat := 118140960795 + 1179404 * 2 ^ 59
def prefixEnd_1179404 : Nat := 4983230072969 + 3 ^ 40 * 1179404 * 2
def baseEnd_1179404 : Nat := 403734091890272540084017

theorem tailTrace_1179404 : CollatzResearch.WordTrace tailWord_1179404 prefixEnd_1179404 403734091890272540084017 := by
  unfold tailWord_1179404
  simp only [CollatzResearch.WordTrace]
  refine ⟨21508198909614104505976633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28677598546152139341302177 21508198909614104505976633)
  ·
    refine ⟨16131149182210578379482475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21508198909614104505976633 16131149182210578379482475)
    ·
      refine ⟨24196723773315867569223713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16131149182210578379482475 24196723773315867569223713)
      ·
        refine ⟨18147542829986900676917785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24196723773315867569223713 18147542829986900676917785)
        ·
          refine ⟨13610657122490175507688339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18147542829986900676917785 13610657122490175507688339)
          ·
            refine ⟨20415985683735263261532509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13610657122490175507688339 20415985683735263261532509)
            ·
              refine ⟨7655994631400723723074691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20415985683735263261532509 7655994631400723723074691)
              ·
                refine ⟨11483991947101085584612037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7655994631400723723074691 11483991947101085584612037)
                ·
                  refine ⟨2153248490081453547114757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11483991947101085584612037 2153248490081453547114757)
                  ·
                    refine ⟨403734091890272540084017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2153248490081453547114757 403734091890272540084017)
                    ·
                      rfl

theorem cell22_1179404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 1, 4, 4].length) (baseStart_1179404 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1179404 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1179404 prefixEnd_1179404 := by exact prefixLift 1179404
  have htrace : WordTrace (prefixWord ++ tailWord_1179404) baseStart_1179404 baseEnd_1179404 := by
    simpa [prefixWord, tailWord_1179404, baseEnd_1179404] using wordTrace_append hprefix tailTrace_1179404
  have hstable : (prefixWord ++ tailWord_1179404).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1179404).length < 2 ^ (prefixWord ++ tailWord_1179404).sum := by decide
  have hdescent : baseEnd_1179404 < baseStart_1179404 := by decide
  rcases family_descends (prefixWord ++ tailWord_1179404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1179406 : List Nat := [4, 1, 1, 2, 1, 1, 4, 1, 4, 3]
def baseStart_1179406 : Nat := 118140960795 + 1179406 * 2 ^ 59
def prefixEnd_1179406 : Nat := 4983230072969 + 3 ^ 40 * 1179406 * 2
def baseEnd_1179406 : Nat := 403734776531145201534011

theorem tailTrace_1179406 : CollatzResearch.WordTrace tailWord_1179406 prefixEnd_1179406 403734776531145201534011 := by
  unfold tailWord_1179406
  simp only [CollatzResearch.WordTrace]
  refine ⟨5377058845652620419190759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28677647176813975569017381 5377058845652620419190759)
  ·
    refine ⟨8065588268478930628786139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5377058845652620419190759 8065588268478930628786139)
    ·
      refine ⟨12098382402718395943179209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8065588268478930628786139 12098382402718395943179209)
      ·
        refine ⟨9073786802038796957384407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12098382402718395943179209 9073786802038796957384407)
        ·
          refine ⟨13610680203058195436076611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9073786802038796957384407 13610680203058195436076611)
          ·
            refine ⟨20416020304587293154114917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13610680203058195436076611 20416020304587293154114917)
            ·
              refine ⟨3828003807110117466396547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20416020304587293154114917 3828003807110117466396547)
              ·
                refine ⟨5742005710665176199594821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3828003807110117466396547 5742005710665176199594821)
                ·
                  refine ⟨1076626070749720537424029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5742005710665176199594821 1076626070749720537424029)
                  ·
                    refine ⟨403734776531145201534011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1076626070749720537424029 403734776531145201534011)
                    ·
                      rfl

theorem cell22_1179406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 4, 1, 4, 3].length) (baseStart_1179406 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1179406 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1179406 prefixEnd_1179406 := by exact prefixLift 1179406
  have htrace : WordTrace (prefixWord ++ tailWord_1179406) baseStart_1179406 baseEnd_1179406 := by
    simpa [prefixWord, tailWord_1179406, baseEnd_1179406] using wordTrace_append hprefix tailTrace_1179406
  have hstable : (prefixWord ++ tailWord_1179406).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1179406).length < 2 ^ (prefixWord ++ tailWord_1179406).sum := by decide
  have hdescent : baseEnd_1179406 < baseStart_1179406 := by decide
  rcases family_descends (prefixWord ++ tailWord_1179406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1179502 : List Nat := [4, 1, 2, 3, 1, 2, 2, 3, 1, 3]
def baseStart_1179502 : Nat := 118140960795 + 1179502 * 2 ^ 59
def prefixEnd_1179502 : Nat := 4983230072969 + 3 ^ 40 * 1179502 * 2
def baseEnd_1179502 : Nat := 403767639293032951133717

theorem tailTrace_1179502 : CollatzResearch.WordTrace tailWord_1179502 prefixEnd_1179502 403767639293032951133717 := by
  unfold tailWord_1179502
  simp only [CollatzResearch.WordTrace]
  refine ⟨5377496521609146468627595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28679981448582114499347173 5377496521609146468627595)
  ·
    refine ⟨8066244782413719702941393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5377496521609146468627595 8066244782413719702941393)
    ·
      refine ⟨6049683586810289777206045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8066244782413719702941393 6049683586810289777206045)
      ·
        refine ⟨2268631345053858666452267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6049683586810289777206045 2268631345053858666452267)
        ·
          refine ⟨3402947017580787999678401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2268631345053858666452267 3402947017580787999678401)
          ·
            refine ⟨2552210263185590999758801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3402947017580787999678401 2552210263185590999758801)
            ·
              refine ⟨1914157697389193249819101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2552210263185590999758801 1914157697389193249819101)
              ·
                refine ⟨717809136520947468682163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1914157697389193249819101 717809136520947468682163)
                ·
                  refine ⟨1076713704781421203023245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 717809136520947468682163 1076713704781421203023245)
                  ·
                    refine ⟨403767639293032951133717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1076713704781421203023245 403767639293032951133717)
                    ·
                      rfl

theorem cell22_1179502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 2, 3, 1, 3].length) (baseStart_1179502 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1179502 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1179502 prefixEnd_1179502 := by exact prefixLift 1179502
  have htrace : WordTrace (prefixWord ++ tailWord_1179502) baseStart_1179502 baseEnd_1179502 := by
    simpa [prefixWord, tailWord_1179502, baseEnd_1179502] using wordTrace_append hprefix tailTrace_1179502
  have hstable : (prefixWord ++ tailWord_1179502).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1179502).length < 2 ^ (prefixWord ++ tailWord_1179502).sum := by decide
  have hdescent : baseEnd_1179502 < baseStart_1179502 := by decide
  rcases family_descends (prefixWord ++ tailWord_1179502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1179556 : List Nat := [2, 3, 1, 2, 1, 3, 2, 1, 1, 6]
def baseStart_1179556 : Nat := 118140960795 + 1179556 * 2 ^ 59
def prefixEnd_1179556 : Nat := 4983230072969 + 3 ^ 40 * 1179556 * 2
def baseEnd_1179556 : Nat := 403786124596594810283551

theorem tailTrace_1179556 : CollatzResearch.WordTrace tailWord_1179556 prefixEnd_1179556 403786124596594810283551 := by
  unfold tailWord_1179556
  simp only [CollatzResearch.WordTrace]
  refine ⟨21510970857338769485743261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28681294476451692647657681 21510970857338769485743261)
  ·
    refine ⟨8066614071502038557153723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21510970857338769485743261 8066614071502038557153723)
    ·
      refine ⟨12099921107253057835730585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8066614071502038557153723 12099921107253057835730585)
      ·
        refine ⟨9074940830439793376797939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12099921107253057835730585 9074940830439793376797939)
        ·
          refine ⟨13612411245659690065196909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9074940830439793376797939 13612411245659690065196909)
          ·
            refine ⟨5104654217122383774448841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13612411245659690065196909 5104654217122383774448841)
            ·
              refine ⟨3828490662841787830836631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5104654217122383774448841 3828490662841787830836631)
              ·
                refine ⟨5742735994262681746254947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3828490662841787830836631 5742735994262681746254947)
                ·
                  refine ⟨8614103991394022619382421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5742735994262681746254947 8614103991394022619382421)
                  ·
                    refine ⟨403786124596594810283551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8614103991394022619382421 403786124596594810283551)
                    ·
                      rfl

theorem cell22_1179556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 2, 1, 1, 6].length) (baseStart_1179556 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1179556 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1179556 prefixEnd_1179556 := by exact prefixLift 1179556
  have htrace : WordTrace (prefixWord ++ tailWord_1179556) baseStart_1179556 baseEnd_1179556 := by
    simpa [prefixWord, tailWord_1179556, baseEnd_1179556] using wordTrace_append hprefix tailTrace_1179556
  have hstable : (prefixWord ++ tailWord_1179556).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1179556).length < 2 ^ (prefixWord ++ tailWord_1179556).sum := by decide
  have hdescent : baseEnd_1179556 < baseStart_1179556 := by decide
  rcases family_descends (prefixWord ++ tailWord_1179556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1179573 : List Nat := [1, 3, 3, 2, 1, 3, 1, 2, 2, 4]
def baseStart_1179573 : Nat := 118140960795 + 1179573 * 2 ^ 59
def prefixEnd_1179573 : Nat := 4983230072969 + 3 ^ 40 * 1179573 * 2
def baseEnd_1179573 : Nat := 403791944044012432608499

theorem tailTrace_1179573 : CollatzResearch.WordTrace tailWord_1179573 prefixEnd_1179573 403791944044012432608499 := by
  unfold tailWord_1179573
  simp only [CollatzResearch.WordTrace]
  refine ⟨43022561755615950874855373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28681707837077300583236915 43022561755615950874855373)
  ·
    refine ⟨16133460658355981578070765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43022561755615950874855373 16133460658355981578070765)
    ·
      refine ⟨6050047746883493091776537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16133460658355981578070765 6050047746883493091776537)
      ·
        refine ⟨4537535810162619818832403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6050047746883493091776537 4537535810162619818832403)
        ·
          refine ⟨6806303715243929728248605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4537535810162619818832403 6806303715243929728248605)
          ·
            refine ⟨2552363893216473648093227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6806303715243929728248605 2552363893216473648093227)
            ·
              refine ⟨3828545839824710472139841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2552363893216473648093227 3828545839824710472139841)
              ·
                refine ⟨2871409379868532854104881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3828545839824710472139841 2871409379868532854104881)
                ·
                  refine ⟨2153557034901399640578661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2871409379868532854104881 2153557034901399640578661)
                  ·
                    refine ⟨403791944044012432608499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2153557034901399640578661 403791944044012432608499)
                    ·
                      rfl

theorem cell22_1179573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 1, 2, 2, 4].length) (baseStart_1179573 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1179573 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1179573 prefixEnd_1179573 := by exact prefixLift 1179573
  have htrace : WordTrace (prefixWord ++ tailWord_1179573) baseStart_1179573 baseEnd_1179573 := by
    simpa [prefixWord, tailWord_1179573, baseEnd_1179573] using wordTrace_append hprefix tailTrace_1179573
  have hstable : (prefixWord ++ tailWord_1179573).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1179573).length < 2 ^ (prefixWord ++ tailWord_1179573).sum := by decide
  have hdescent : baseEnd_1179573 < baseStart_1179573 := by decide
  rcases family_descends (prefixWord ++ tailWord_1179573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1179592 : List Nat := [2, 1, 3, 1, 4, 3, 2, 1, 2, 3]
def baseStart_1179592 : Nat := 118140960795 + 1179592 * 2 ^ 59
def prefixEnd_1179592 : Nat := 4983230072969 + 3 ^ 40 * 1179592 * 2
def baseEnd_1179592 : Nat := 403798448132302716383441

theorem tailTrace_1179592 : CollatzResearch.WordTrace tailWord_1179592 prefixEnd_1179592 403798448132302716383441 := by
  unfold tailWord_1179592
  simp only [CollatzResearch.WordTrace]
  refine ⟨21511627371273558559898515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28682169828364744746531353 21511627371273558559898515)
  ·
    refine ⟨32267441056910337839847773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21511627371273558559898515 32267441056910337839847773)
    ·
      refine ⟨12100290396341376689942915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32267441056910337839847773 12100290396341376689942915)
      ·
        refine ⟨18150435594512065034914373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12100290396341376689942915 18150435594512065034914373)
        ·
          refine ⟨3403206673971012194046445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18150435594512065034914373 3403206673971012194046445)
          ·
            refine ⟨1276202502739129572767417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3403206673971012194046445 1276202502739129572767417)
            ·
              refine ⟨957151877054347179575563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1276202502739129572767417 957151877054347179575563)
              ·
                refine ⟨1435727815581520769363345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 957151877054347179575563 1435727815581520769363345)
                ·
                  refine ⟨1076795861686140577022509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1435727815581520769363345 1076795861686140577022509)
                  ·
                    refine ⟨403798448132302716383441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1076795861686140577022509 403798448132302716383441)
                    ·
                      rfl

theorem cell22_1179592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 3, 2, 1, 2, 3].length) (baseStart_1179592 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1179592 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1179592 prefixEnd_1179592 := by exact prefixLift 1179592
  have htrace : WordTrace (prefixWord ++ tailWord_1179592) baseStart_1179592 baseEnd_1179592 := by
    simpa [prefixWord, tailWord_1179592, baseEnd_1179592] using wordTrace_append hprefix tailTrace_1179592
  have hstable : (prefixWord ++ tailWord_1179592).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1179592).length < 2 ^ (prefixWord ++ tailWord_1179592).sum := by decide
  have hdescent : baseEnd_1179592 < baseStart_1179592 := by decide
  rcases family_descends (prefixWord ++ tailWord_1179592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1179620 : List Nat := [2, 3, 1, 1, 1, 1, 4, 5, 1, 3]
def baseStart_1179620 : Nat := 118140960795 + 1179620 * 2 ^ 59
def prefixEnd_1179620 : Nat := 4983230072969 + 3 ^ 40 * 1179620 * 2
def baseEnd_1179620 : Nat := 403808033104519976683355

theorem tailTrace_1179620 : CollatzResearch.WordTrace tailWord_1179620 prefixEnd_1179620 403808033104519976683355 := by
  unfold tailWord_1179620
  simp only [CollatzResearch.WordTrace]
  refine ⟨21512137993222838950908157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28682850657630451934544209 21512137993222838950908157)
  ·
    refine ⟨8067051747458564606590559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21512137993222838950908157 8067051747458564606590559)
    ·
      refine ⟨12100577621187846909885839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8067051747458564606590559 12100577621187846909885839)
      ·
        refine ⟨18150866431781770364828759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12100577621187846909885839 18150866431781770364828759)
        ·
          refine ⟨27226299647672655547243139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18150866431781770364828759 27226299647672655547243139)
          ·
            refine ⟨40839449471508983320864709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27226299647672655547243139 40839449471508983320864709)
            ·
              refine ⟨7657396775907934372662133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40839449471508983320864709 7657396775907934372662133)
              ·
                refine ⟨717880947741368847437075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7657396775907934372662133 717880947741368847437075)
                ·
                  refine ⟨1076821421612053271155613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 717880947741368847437075 1076821421612053271155613)
                  ·
                    refine ⟨403808033104519976683355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1076821421612053271155613 403808033104519976683355)
                    ·
                      rfl

theorem cell22_1179620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 5, 1, 3].length) (baseStart_1179620 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1179620 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1179620 prefixEnd_1179620 := by exact prefixLift 1179620
  have htrace : WordTrace (prefixWord ++ tailWord_1179620) baseStart_1179620 baseEnd_1179620 := by
    simpa [prefixWord, tailWord_1179620, baseEnd_1179620] using wordTrace_append hprefix tailTrace_1179620
  have hstable : (prefixWord ++ tailWord_1179620).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1179620).length < 2 ^ (prefixWord ++ tailWord_1179620).sum := by decide
  have hdescent : baseEnd_1179620 < baseStart_1179620 := by decide
  rcases family_descends (prefixWord ++ tailWord_1179620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
