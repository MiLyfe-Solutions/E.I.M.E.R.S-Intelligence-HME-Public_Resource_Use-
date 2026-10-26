import V185TrunkScan23Chunk0186

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_1106674 : List Nat := [3, 2, 1, 3, 1, 2, 3, 1, 1, 3, 3]
def baseStart_1106674 : Nat := 118140960795 + 1106674 * 2 ^ 59
def prefixEnd_1106674 : Nat := 4983230072969 + 3 ^ 40 * 1106674 * 2
def baseEnd_1106674 : Nat := 568255689833908366585505

theorem tailTrace_1106674 : CollatzResearch.WordTrace tailWord_1106674 prefixEnd_1106674 568255689833908366585505 := by
  unfold tailWord_1106674
  simp only [CollatzResearch.WordTrace]
  refine ⟨10090929198179144429215769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26909144528477718477908717 10090929198179144429215769)
  ·
    refine ⟨7568196898634358321911827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10090929198179144429215769 7568196898634358321911827)
    ·
      refine ⟨11352295347951537482867741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7568196898634358321911827 11352295347951537482867741)
      ·
        refine ⟨4257110755481826556075403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11352295347951537482867741 4257110755481826556075403)
        ·
          refine ⟨6385666133222739834113105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4257110755481826556075403 6385666133222739834113105)
          ·
            refine ⟨4789249599917054875584829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6385666133222739834113105 4789249599917054875584829)
            ·
              refine ⟨1795968599968895578344311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4789249599917054875584829 1795968599968895578344311)
              ·
                refine ⟨2693952899953343367516467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1795968599968895578344311 2693952899953343367516467)
                ·
                  refine ⟨4040929349930015051274701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2693952899953343367516467 4040929349930015051274701)
                  ·
                    refine ⟨1515348506223755644228013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4040929349930015051274701 1515348506223755644228013)
                    ·
                      refine ⟨568255689833908366585505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1515348506223755644228013 568255689833908366585505)
                      ·
                        rfl

theorem cell23_1106674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 3, 1, 1, 3, 3].length) (baseStart_1106674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1106674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1106674 prefixEnd_1106674 := by exact prefixLift 1106674
  have htrace : WordTrace (prefixWord ++ tailWord_1106674) baseStart_1106674 baseEnd_1106674 := by
    simpa [prefixWord, tailWord_1106674, baseEnd_1106674] using wordTrace_append hprefix tailTrace_1106674
  have hstable : (prefixWord ++ tailWord_1106674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1106674).length < 2 ^ (prefixWord ++ tailWord_1106674).sum := by decide
  have hdescent : baseEnd_1106674 < baseStart_1106674 := by decide
  rcases family_descends (prefixWord ++ tailWord_1106674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1106734 : List Nat := [4, 1, 3, 2, 1, 1, 1, 2, 2, 1, 5]
def baseStart_1106734 : Nat := 118140960795 + 1106734 * 2 ^ 59
def prefixEnd_1106734 : Nat := 4983230072969 + 3 ^ 40 * 1106734 * 2
def baseEnd_1106734 : Nat := 568286498673178131835229

theorem tailTrace_1106734 : CollatzResearch.WordTrace tailWord_1106734 prefixEnd_1106734 568286498673178131835229 := by
  unfold tailWord_1106734
  simp only [CollatzResearch.WordTrace]
  refine ⟨5045738146562400995505907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26910603448332805309364837 5045738146562400995505907)
  ·
    refine ⟨7568607219843601493258861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5045738146562400995505907 7568607219843601493258861)
    ·
      refine ⟨2838227707441350559972073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7568607219843601493258861 2838227707441350559972073)
      ·
        refine ⟨2128670780581012919979055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2838227707441350559972073 2128670780581012919979055)
        ·
          refine ⟨3193006170871519379968583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2128670780581012919979055 3193006170871519379968583)
          ·
            refine ⟨4789509256307279069952875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3193006170871519379968583 4789509256307279069952875)
            ·
              refine ⟨7184263884460918604929313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4789509256307279069952875 7184263884460918604929313)
              ·
                refine ⟨5388197913345688953696985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7184263884460918604929313 5388197913345688953696985)
                ·
                  refine ⟨4041148435009266715272739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5388197913345688953696985 4041148435009266715272739)
                  ·
                    refine ⟨6061722652513900072909109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4041148435009266715272739 6061722652513900072909109)
                    ·
                      refine ⟨568286498673178131835229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6061722652513900072909109 568286498673178131835229)
                      ·
                        rfl

theorem cell23_1106734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 2, 2, 1, 5].length) (baseStart_1106734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1106734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1106734 prefixEnd_1106734 := by exact prefixLift 1106734
  have htrace : WordTrace (prefixWord ++ tailWord_1106734) baseStart_1106734 baseEnd_1106734 := by
    simpa [prefixWord, tailWord_1106734, baseEnd_1106734] using wordTrace_append hprefix tailTrace_1106734
  have hstable : (prefixWord ++ tailWord_1106734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1106734).length < 2 ^ (prefixWord ++ tailWord_1106734).sum := by decide
  have hdescent : baseEnd_1106734 < baseStart_1106734 := by decide
  rcases family_descends (prefixWord ++ tailWord_1106734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1106777 : List Nat := [1, 2, 1, 2, 2, 4, 2, 1, 1, 2, 5]
def baseStart_1106777 : Nat := 118140960795 + 1106777 * 2 ^ 59
def prefixEnd_1106777 : Nat := 4983230072969 + 3 ^ 40 * 1106777 * 2
def baseEnd_1106777 : Nat := 568308578341321463597531

theorem tailTrace_1106777 : CollatzResearch.WordTrace tailWord_1106777 prefixEnd_1106777 568308578341321463597531 := by
  unfold tailWord_1106777
  simp only [CollatzResearch.WordTrace]
  refine ⟨40367473511343426307862585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26911649007562284205241723 40367473511343426307862585)
  ·
    refine ⟨30275605133507569730896939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40367473511343426307862585 30275605133507569730896939)
    ·
      refine ⟨45413407700261354596345409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30275605133507569730896939 45413407700261354596345409)
      ·
        refine ⟨34060055775196015947259057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45413407700261354596345409 34060055775196015947259057)
        ·
          refine ⟨25545041831397011960444293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34060055775196015947259057 25545041831397011960444293)
          ·
            refine ⟨4789695343386939742583305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25545041831397011960444293 4789695343386939742583305)
            ·
              refine ⟨3592271507540204806937479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4789695343386939742583305 3592271507540204806937479)
              ·
                refine ⟨5388407261310307210406219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3592271507540204806937479 5388407261310307210406219)
                ·
                  refine ⟨8082610891965460815609329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5388407261310307210406219 8082610891965460815609329)
                  ·
                    refine ⟨6061958168974095611706997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8082610891965460815609329 6061958168974095611706997)
                    ·
                      refine ⟨568308578341321463597531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6061958168974095611706997 568308578341321463597531)
                      ·
                        rfl

theorem cell23_1106777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 2, 1, 1, 2, 5].length) (baseStart_1106777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1106777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1106777 prefixEnd_1106777 := by exact prefixLift 1106777
  have htrace : WordTrace (prefixWord ++ tailWord_1106777) baseStart_1106777 baseEnd_1106777 := by
    simpa [prefixWord, tailWord_1106777, baseEnd_1106777] using wordTrace_append hprefix tailTrace_1106777
  have hstable : (prefixWord ++ tailWord_1106777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1106777).length < 2 ^ (prefixWord ++ tailWord_1106777).sum := by decide
  have hdescent : baseEnd_1106777 < baseStart_1106777 := by decide
  rcases family_descends (prefixWord ++ tailWord_1106777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1106838 : List Nat := [5, 3, 1, 1, 1, 1, 1, 2, 1, 3, 4]
def baseStart_1106838 : Nat := 118140960795 + 1106838 * 2 ^ 59
def prefixEnd_1106838 : Nat := 4983230072969 + 3 ^ 40 * 1106838 * 2
def baseEnd_1106838 : Nat := 568339900661245724934751

theorem tailTrace_1106838 : CollatzResearch.WordTrace tailWord_1106838 prefixEnd_1106838 568339900661245724934751 := by
  unfold tailWord_1106838
  simp only [CollatzResearch.WordTrace]
  refine ⟨2523106147757652107864573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 26913132242748289150555445 2523106147757652107864573)
  ·
    refine ⟨946164805409119540449215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2523106147757652107864573 946164805409119540449215)
    ·
      refine ⟨1419247208113679310673823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 946164805409119540449215 1419247208113679310673823)
      ·
        refine ⟨2128870812170518966010735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1419247208113679310673823 2128870812170518966010735)
        ·
          refine ⟨3193306218255778449016103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2128870812170518966010735 3193306218255778449016103)
          ·
            refine ⟨4789959327383667673524155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3193306218255778449016103 4789959327383667673524155)
            ·
              refine ⟨7184938991075501510286233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4789959327383667673524155 7184938991075501510286233)
              ·
                refine ⟨5388704243306626132714675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7184938991075501510286233 5388704243306626132714675)
                ·
                  refine ⟨8083056364959939199072013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5388704243306626132714675 8083056364959939199072013)
                  ·
                    refine ⟨3031146136859977199652005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8083056364959939199072013 3031146136859977199652005)
                    ·
                      refine ⟨568339900661245724934751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3031146136859977199652005 568339900661245724934751)
                      ·
                        rfl

theorem cell23_1106838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 2, 1, 3, 4].length) (baseStart_1106838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1106838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1106838 prefixEnd_1106838 := by exact prefixLift 1106838
  have htrace : WordTrace (prefixWord ++ tailWord_1106838) baseStart_1106838 baseEnd_1106838 := by
    simpa [prefixWord, tailWord_1106838, baseEnd_1106838] using wordTrace_append hprefix tailTrace_1106838
  have hstable : (prefixWord ++ tailWord_1106838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1106838).length < 2 ^ (prefixWord ++ tailWord_1106838).sum := by decide
  have hdescent : baseEnd_1106838 < baseStart_1106838 := by decide
  rcases family_descends (prefixWord ++ tailWord_1106838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1106865 : List Nat := [1, 2, 2, 4, 3, 2, 1, 3, 1, 4]
def baseStart_1106865 : Nat := 118140960795 + 1106865 * 2 ^ 59
def prefixEnd_1106865 : Nat := 4983230072969 + 3 ^ 40 * 1106865 * 2
def baseEnd_1106865 : Nat := 189451254879639039765709

theorem tailTrace_1106865 : CollatzResearch.WordTrace tailWord_1106865 prefixEnd_1106865 189451254879639039765709 := by
  unfold tailWord_1106865
  simp only [CollatzResearch.WordTrace]
  refine ⟨40370683135024617337066049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26913788756683078224710699 40370683135024617337066049)
  ·
    refine ⟨30278012351268463002799537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40370683135024617337066049 30278012351268463002799537)
    ·
      refine ⟨22708509263451347252099653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30278012351268463002799537 22708509263451347252099653)
      ·
        refine ⟨4257845486897127609768685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22708509263451347252099653 4257845486897127609768685)
        ·
          refine ⟨1596692057586422853663257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4257845486897127609768685 1596692057586422853663257)
          ·
            refine ⟨1197519043189817140247443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1596692057586422853663257 1197519043189817140247443)
            ·
              refine ⟨1796278564784725710371165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1197519043189817140247443 1796278564784725710371165)
              ·
                refine ⟨673604461794272141389187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1796278564784725710371165 673604461794272141389187)
                ·
                  refine ⟨1010406692691408212083781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 673604461794272141389187 1010406692691408212083781)
                  ·
                    refine ⟨189451254879639039765709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1010406692691408212083781 189451254879639039765709)
                    ·
                      rfl

theorem cell23_1106865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 2, 1, 3, 1, 4].length) (baseStart_1106865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1106865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1106865 prefixEnd_1106865 := by exact prefixLift 1106865
  have htrace : WordTrace (prefixWord ++ tailWord_1106865) baseStart_1106865 baseEnd_1106865 := by
    simpa [prefixWord, tailWord_1106865, baseEnd_1106865] using wordTrace_append hprefix tailTrace_1106865
  have hstable : (prefixWord ++ tailWord_1106865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1106865).length < 2 ^ (prefixWord ++ tailWord_1106865).sum := by decide
  have hdescent : baseEnd_1106865 < baseStart_1106865 := by decide
  rcases family_descends (prefixWord ++ tailWord_1106865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1106874 : List Nat := [3, 1, 1, 1, 2, 1, 3, 5, 1, 5]
def baseStart_1106874 : Nat := 118140960795 + 1106874 * 2 ^ 59
def prefixEnd_1106874 : Nat := 4983230072969 + 3 ^ 40 * 1106874 * 2
def baseEnd_1106874 : Nat := 189452795321602528028195

theorem tailTrace_1106874 : CollatzResearch.WordTrace tailWord_1106874 prefixEnd_1106874 189452795321602528028195 := by
  unfold tailWord_1106874
  simp only [CollatzResearch.WordTrace]
  refine ⟨10092752847998002968535919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26914007594661341249429117 10092752847998002968535919)
  ·
    refine ⟨15139129271997004452803879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10092752847998002968535919 15139129271997004452803879)
    ·
      refine ⟨22708693907995506679205819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15139129271997004452803879 22708693907995506679205819)
      ·
        refine ⟨34063040861993260018808729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22708693907995506679205819 34063040861993260018808729)
        ·
          refine ⟨25547280646494945014106547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34063040861993260018808729 25547280646494945014106547)
          ·
            refine ⟨38320920969742417521159821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25547280646494945014106547 38320920969742417521159821)
            ·
              refine ⟨14370345363653406570434933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38320920969742417521159821 14370345363653406570434933)
              ·
                refine ⟨1347219877842506865978275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14370345363653406570434933 1347219877842506865978275)
                ·
                  refine ⟨2020829816763760298967413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1347219877842506865978275 2020829816763760298967413)
                  ·
                    refine ⟨189452795321602528028195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2020829816763760298967413 189452795321602528028195)
                    ·
                      rfl

theorem cell23_1106874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 5, 1, 5].length) (baseStart_1106874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1106874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1106874 prefixEnd_1106874 := by exact prefixLift 1106874
  have htrace : WordTrace (prefixWord ++ tailWord_1106874) baseStart_1106874 baseEnd_1106874 := by
    simpa [prefixWord, tailWord_1106874, baseEnd_1106874] using wordTrace_append hprefix tailTrace_1106874
  have hstable : (prefixWord ++ tailWord_1106874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1106874).length < 2 ^ (prefixWord ++ tailWord_1106874).sum := by decide
  have hdescent : baseEnd_1106874 < baseStart_1106874 := by decide
  rcases family_descends (prefixWord ++ tailWord_1106874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1106911 : List Nat := [1, 1, 2, 3, 5, 1, 1, 1, 3, 1, 4]
def baseStart_1106911 : Nat := 118140960795 + 1106911 * 2 ^ 59
def prefixEnd_1106911 : Nat := 4983230072969 + 3 ^ 40 * 1106911 * 2
def baseEnd_1106911 : Nat := 568377384749023939321915

theorem tailTrace_1106911 : CollatzResearch.WordTrace tailWord_1106911 prefixEnd_1106911 568377384749023939321915 := by
  unfold tailWord_1106911
  simp only [CollatzResearch.WordTrace]
  refine ⟨40372360892857967193240587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26914907261905311462160391 40372360892857967193240587)
  ·
    refine ⟨60558541339286950789860881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40372360892857967193240587 60558541339286950789860881)
    ·
      refine ⟨45418906004465213092395661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60558541339286950789860881 45418906004465213092395661)
      ·
        refine ⟨17032089751674454909648373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45418906004465213092395661 17032089751674454909648373)
        ·
          refine ⟨1596758414219480147779535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 17032089751674454909648373 1596758414219480147779535)
          ·
            refine ⟨2395137621329220221669303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1596758414219480147779535 2395137621329220221669303)
            ·
              refine ⟨3592706431993830332503955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2395137621329220221669303 3592706431993830332503955)
              ·
                refine ⟨5389059647990745498755933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3592706431993830332503955 5389059647990745498755933)
                ·
                  refine ⟨2020897367996529562033475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5389059647990745498755933 2020897367996529562033475)
                  ·
                    refine ⟨3031346051994794343050213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2020897367996529562033475 3031346051994794343050213)
                    ·
                      refine ⟨568377384749023939321915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3031346051994794343050213 568377384749023939321915)
                      ·
                        rfl

theorem cell23_1106911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 1, 1, 3, 1, 4].length) (baseStart_1106911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1106911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1106911 prefixEnd_1106911 := by exact prefixLift 1106911
  have htrace : WordTrace (prefixWord ++ tailWord_1106911) baseStart_1106911 baseEnd_1106911 := by
    simpa [prefixWord, tailWord_1106911, baseEnd_1106911] using wordTrace_append hprefix tailTrace_1106911
  have hstable : (prefixWord ++ tailWord_1106911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1106911).length < 2 ^ (prefixWord ++ tailWord_1106911).sum := by decide
  have hdescent : baseEnd_1106911 < baseStart_1106911 := by decide
  rcases family_descends (prefixWord ++ tailWord_1106911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1106934 : List Nat := [5, 1, 1, 1, 3, 12]
def baseStart_1106934 : Nat := 118140960795 + 1106934 * 2 ^ 59
def prefixEnd_1106934 : Nat := 4983230072969 + 3 ^ 40 * 1106934 * 2
def baseEnd_1106934 : Nat := 2339050184378919133063

theorem tailTrace_1106934 : CollatzResearch.WordTrace tailWord_1106934 prefixEnd_1106934 2339050184378919133063 := by
  unfold tailWord_1106934
  simp only [CollatzResearch.WordTrace]
  refine ⟨2523324985735915132582991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 26915466514516428080885237 2523324985735915132582991)
  ·
    refine ⟨3784987478603872698874487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2523324985735915132582991 3784987478603872698874487)
    ·
      refine ⟨5677481217905809048311731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3784987478603872698874487 5677481217905809048311731)
      ·
        refine ⟨8516221826858713572467597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5677481217905809048311731 8516221826858713572467597)
        ·
          refine ⟨3193583185072017589675349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8516221826858713572467597 3193583185072017589675349)
          ·
            refine ⟨2339050184378919133063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 3193583185072017589675349 2339050184378919133063)
            ·
              rfl

theorem cell23_1106934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 12].length) (baseStart_1106934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1106934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1106934 prefixEnd_1106934 := by exact prefixLift 1106934
  have htrace : WordTrace (prefixWord ++ tailWord_1106934) baseStart_1106934 baseEnd_1106934 := by
    simpa [prefixWord, tailWord_1106934, baseEnd_1106934] using wordTrace_append hprefix tailTrace_1106934
  have hstable : (prefixWord ++ tailWord_1106934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1106934).length < 2 ^ (prefixWord ++ tailWord_1106934).sum := by decide
  have hdescent : baseEnd_1106934 < baseStart_1106934 := by decide
  rcases family_descends (prefixWord ++ tailWord_1106934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1106988 : List Nat := [2, 2, 1, 1, 1, 2, 5, 3, 1, 3, 2]
def baseStart_1106988 : Nat := 118140960795 + 1106988 * 2 ^ 59
def prefixEnd_1106988 : Nat := 4983230072969 + 3 ^ 40 * 1106988 * 2
def baseEnd_1106988 : Nat := 568416922759420138059061

theorem tailTrace_1106988 : CollatzResearch.WordTrace tailWord_1106988 prefixEnd_1106988 568416922759420138059061 := by
  unfold tailWord_1106988
  simp only [CollatzResearch.WordTrace]
  refine ⟨20187584656789504671896809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26916779542386006229195745 20187584656789504671896809)
  ·
    refine ⟨15140688492592128503922607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20187584656789504671896809 15140688492592128503922607)
    ·
      refine ⟨22711032738888192755883911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15140688492592128503922607 22711032738888192755883911)
      ·
        refine ⟨34066549108332289133825867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22711032738888192755883911 34066549108332289133825867)
        ·
          refine ⟨51099823662498433700738801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34066549108332289133825867 51099823662498433700738801)
          ·
            refine ⟨38324867746873825275554101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51099823662498433700738801 38324867746873825275554101)
            ·
              refine ⟨3592956351269421119583197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 38324867746873825275554101 3592956351269421119583197)
              ·
                refine ⟨1347358631726032919843699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3592956351269421119583197 1347358631726032919843699)
                ·
                  refine ⟨2021037947589049379765549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1347358631726032919843699 2021037947589049379765549)
                  ·
                    refine ⟨757889230345893517412081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2021037947589049379765549 757889230345893517412081)
                    ·
                      refine ⟨568416922759420138059061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 757889230345893517412081 568416922759420138059061)
                      ·
                        rfl

theorem cell23_1106988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 3, 2].length) (baseStart_1106988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1106988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1106988 prefixEnd_1106988 := by exact prefixLift 1106988
  have htrace : WordTrace (prefixWord ++ tailWord_1106988) baseStart_1106988 baseEnd_1106988 := by
    simpa [prefixWord, tailWord_1106988, baseEnd_1106988] using wordTrace_append hprefix tailTrace_1106988
  have hstable : (prefixWord ++ tailWord_1106988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1106988).length < 2 ^ (prefixWord ++ tailWord_1106988).sum := by decide
  have hdescent : baseEnd_1106988 < baseStart_1106988 := by decide
  rcases family_descends (prefixWord ++ tailWord_1106988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1106994 : List Nat := [3, 2, 1, 1, 2, 2, 1, 1, 4, 6]
def baseStart_1106994 : Nat := 118140960795 + 1106994 * 2 ^ 59
def prefixEnd_1106994 : Nat := 4983230072969 + 3 ^ 40 * 1106994 * 2
def baseEnd_1106994 : Nat := 189473334547782371528011

theorem tailTrace_1106994 : CollatzResearch.WordTrace tailWord_1106994 prefixEnd_1106994 189473334547782371528011 := by
  unfold tailWord_1106994
  simp only [CollatzResearch.WordTrace]
  refine ⟨10093847037889318092128009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26916925434371514912341357 10093847037889318092128009)
  ·
    refine ⟨7570385278416988569096007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10093847037889318092128009 7570385278416988569096007)
    ·
      refine ⟨11355577917625482853644011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7570385278416988569096007 11355577917625482853644011)
      ·
        refine ⟨17033366876438224280466017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11355577917625482853644011 17033366876438224280466017)
        ·
          refine ⟨12775025157328668210349513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17033366876438224280466017 12775025157328668210349513)
          ·
            refine ⟨9581268867996501157762135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12775025157328668210349513 9581268867996501157762135)
            ·
              refine ⟨14371903301994751736643203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9581268867996501157762135 14371903301994751736643203)
              ·
                refine ⟨21557854952992127604964805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14371903301994751736643203 21557854952992127604964805)
                ·
                  refine ⟨4042097803686023925930901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21557854952992127604964805 4042097803686023925930901)
                  ·
                    refine ⟨189473334547782371528011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4042097803686023925930901 189473334547782371528011)
                    ·
                      rfl

theorem cell23_1106994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 1, 4, 6].length) (baseStart_1106994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1106994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1106994 prefixEnd_1106994 := by exact prefixLift 1106994
  have htrace : WordTrace (prefixWord ++ tailWord_1106994) baseStart_1106994 baseEnd_1106994 := by
    simpa [prefixWord, tailWord_1106994, baseEnd_1106994] using wordTrace_append hprefix tailTrace_1106994
  have hstable : (prefixWord ++ tailWord_1106994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1106994).length < 2 ^ (prefixWord ++ tailWord_1106994).sum := by decide
  have hdescent : baseEnd_1106994 < baseStart_1106994 := by decide
  rcases family_descends (prefixWord ++ tailWord_1106994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1107018 : List Nat := [3, 1, 2, 1, 1, 2, 5, 1, 1, 4, 2]
def baseStart_1107018 : Nat := 118140960795 + 1107018 * 2 ^ 59
def prefixEnd_1107018 : Nat := 4983230072969 + 3 ^ 40 * 1107018 * 2
def baseEnd_1107018 : Nat := 568432327179055020683923

theorem tailTrace_1107018 : CollatzResearch.WordTrace tailWord_1107018 prefixEnd_1107018 568432327179055020683923 := by
  unfold tailWord_1107018
  simp only [CollatzResearch.WordTrace]
  refine ⟨10094065875867581116846427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26917509002313549644923805 10094065875867581116846427)
  ·
    refine ⟨15141098813801371675269641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10094065875867581116846427 15141098813801371675269641)
    ·
      refine ⟨11355824110351028756452231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15141098813801371675269641 11355824110351028756452231)
      ·
        refine ⟨17033736165526543134678347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11355824110351028756452231 17033736165526543134678347)
        ·
          refine ⟨25550604248289814702017521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17033736165526543134678347 25550604248289814702017521)
          ·
            refine ⟨19162953186217361026513141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25550604248289814702017521 19162953186217361026513141)
            ·
              refine ⟨1796526861207877596235607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 19162953186217361026513141 1796526861207877596235607)
              ·
                refine ⟨2694790291811816394353411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1796526861207877596235607 2694790291811816394353411)
                ·
                  refine ⟨4042185437717724591530117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2694790291811816394353411 4042185437717724591530117)
                  ·
                    refine ⟨757909769572073360911897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4042185437717724591530117 757909769572073360911897)
                    ·
                      refine ⟨568432327179055020683923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 757909769572073360911897 568432327179055020683923)
                      ·
                        rfl

theorem cell23_1107018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 5, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 5, 1, 1, 4, 2].length) (baseStart_1107018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1107018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1107018 prefixEnd_1107018 := by exact prefixLift 1107018
  have htrace : WordTrace (prefixWord ++ tailWord_1107018) baseStart_1107018 baseEnd_1107018 := by
    simpa [prefixWord, tailWord_1107018, baseEnd_1107018] using wordTrace_append hprefix tailTrace_1107018
  have hstable : (prefixWord ++ tailWord_1107018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1107018).length < 2 ^ (prefixWord ++ tailWord_1107018).sum := by decide
  have hdescent : baseEnd_1107018 < baseStart_1107018 := by decide
  rcases family_descends (prefixWord ++ tailWord_1107018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1107064 : List Nat := [2, 1, 2, 1, 1, 1, 5, 1, 1, 1, 7]
def baseStart_1107064 : Nat := 118140960795 + 1107064 * 2 ^ 59
def prefixEnd_1107064 : Nat := 4983230072969 + 3 ^ 40 * 1107064 * 2
def baseEnd_1107064 : Nat := 568455947289161840708711

theorem tailTrace_1107064 : CollatzResearch.WordTrace tailWord_1107064 prefixEnd_1107064 568455947289161840708711 := by
  unfold tailWord_1107064
  simp only [CollatzResearch.WordTrace]
  refine ⟨20188970630651837161780123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26918627507535782882373497 20188970630651837161780123)
  ·
    refine ⟨30283455945977755742670185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20188970630651837161780123 30283455945977755742670185)
    ·
      refine ⟨22712591959483316807002639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30283455945977755742670185 22712591959483316807002639)
      ·
        refine ⟨34068887939224975210503959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22712591959483316807002639 34068887939224975210503959)
        ·
          refine ⟨51103331908837462815755939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34068887939224975210503959 51103331908837462815755939)
          ·
            refine ⟨76654997863256194223633909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51103331908837462815755939 76654997863256194223633909)
            ·
              refine ⟨7186406049680268208465679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 76654997863256194223633909 7186406049680268208465679)
              ·
                refine ⟨10779609074520402312698519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7186406049680268208465679 10779609074520402312698519)
                ·
                  refine ⟨16169413611780603469047779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10779609074520402312698519 16169413611780603469047779)
                  ·
                    refine ⟨24254120417670905203571669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16169413611780603469047779 24254120417670905203571669)
                    ·
                      refine ⟨568455947289161840708711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 24254120417670905203571669 568455947289161840708711)
                      ·
                        rfl

theorem cell23_1107064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 1, 1, 1, 7].length) (baseStart_1107064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1107064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1107064 prefixEnd_1107064 := by exact prefixLift 1107064
  have htrace : WordTrace (prefixWord ++ tailWord_1107064) baseStart_1107064 baseEnd_1107064 := by
    simpa [prefixWord, tailWord_1107064, baseEnd_1107064] using wordTrace_append hprefix tailTrace_1107064
  have hstable : (prefixWord ++ tailWord_1107064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1107064).length < 2 ^ (prefixWord ++ tailWord_1107064).sum := by decide
  have hdescent : baseEnd_1107064 < baseStart_1107064 := by decide
  rcases family_descends (prefixWord ++ tailWord_1107064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1107084 : List Nat := [2, 2, 1, 2, 1, 1, 1, 3, 2, 8]
def baseStart_1107084 : Nat := 118140960795 + 1107084 * 2 ^ 59
def prefixEnd_1107084 : Nat := 4983230072969 + 3 ^ 40 * 1107084 * 2
def baseEnd_1107084 : Nat := 189488738967417254152873

theorem tailTrace_1107084 : CollatzResearch.WordTrace tailWord_1107084 prefixEnd_1107084 189488738967417254152873 := by
  unfold tailWord_1107084
  simp only [CollatzResearch.WordTrace]
  refine ⟨20189335360615608869644153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26919113814154145159525537 20189335360615608869644153)
  ·
    refine ⟨15142001520461706652233115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20189335360615608869644153 15142001520461706652233115)
    ·
      refine ⟨22713002280692559978349673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15142001520461706652233115 22713002280692559978349673)
      ·
        refine ⟨17034751710519419983762255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22713002280692559978349673 17034751710519419983762255)
        ·
          refine ⟨25552127565779129975643383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17034751710519419983762255 25552127565779129975643383)
          ·
            refine ⟨38328191348668694963465075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25552127565779129975643383 38328191348668694963465075)
            ·
              refine ⟨57492287023003042445197613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38328191348668694963465075 57492287023003042445197613)
              ·
                refine ⟨21559607633626140916949105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 57492287023003042445197613 21559607633626140916949105)
                ·
                  refine ⟨16169705725219605687711829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21559607633626140916949105 16169705725219605687711829)
                  ·
                    refine ⟨189488738967417254152873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 16169705725219605687711829 189488738967417254152873)
                    ·
                      rfl

theorem cell23_1107084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 2, 8].length) (baseStart_1107084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1107084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1107084 prefixEnd_1107084 := by exact prefixLift 1107084
  have htrace : WordTrace (prefixWord ++ tailWord_1107084) baseStart_1107084 baseEnd_1107084 := by
    simpa [prefixWord, tailWord_1107084, baseEnd_1107084] using wordTrace_append hprefix tailTrace_1107084
  have hstable : (prefixWord ++ tailWord_1107084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1107084).length < 2 ^ (prefixWord ++ tailWord_1107084).sum := by decide
  have hdescent : baseEnd_1107084 < baseStart_1107084 := by decide
  rcases family_descends (prefixWord ++ tailWord_1107084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1107091 : List Nat := [1, 1, 1, 2, 1, 2, 5, 3, 2, 1, 4]
def baseStart_1107091 : Nat := 118140960795 + 1107091 * 2 ^ 59
def prefixEnd_1107091 : Nat := 4983230072969 + 3 ^ 40 * 1107091 * 2
def baseEnd_1107091 : Nat := 568469811266833235071087

theorem tailTrace_1107091 : CollatzResearch.WordTrace tailWord_1107091 prefixEnd_1107091 568469811266833235071087 := by
  unfold tailWord_1107091
  simp only [CollatzResearch.WordTrace]
  refine ⟨40378926032205857934793127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26919284021470571956528751 40378926032205857934793127)
  ·
    refine ⟨60568389048308786902189691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40378926032205857934793127 60568389048308786902189691)
    ·
      refine ⟨90852583572463180353284537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60568389048308786902189691 90852583572463180353284537)
      ·
        refine ⟨68139437679347385264963403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90852583572463180353284537 68139437679347385264963403)
        ·
          refine ⟨102209156519021077897445105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68139437679347385264963403 102209156519021077897445105)
          ·
            refine ⟨76656867389265808423083829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 102209156519021077897445105 76656867389265808423083829)
            ·
              refine ⟨7186581317743669539664109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 76656867389265808423083829 7186581317743669539664109)
              ·
                refine ⟨2694967994153876077374041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7186581317743669539664109 2694967994153876077374041)
                ·
                  refine ⟨2021225995615407058030531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2694967994153876077374041 2021225995615407058030531)
                  ·
                    refine ⟨3031838993423110587045797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2021225995615407058030531 3031838993423110587045797)
                    ·
                      refine ⟨568469811266833235071087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3031838993423110587045797 568469811266833235071087)
                      ·
                        rfl

theorem cell23_1107091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 3, 2, 1, 4].length) (baseStart_1107091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1107091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1107091 prefixEnd_1107091 := by exact prefixLift 1107091
  have htrace : WordTrace (prefixWord ++ tailWord_1107091) baseStart_1107091 baseEnd_1107091 := by
    simpa [prefixWord, tailWord_1107091, baseEnd_1107091] using wordTrace_append hprefix tailTrace_1107091
  have hstable : (prefixWord ++ tailWord_1107091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1107091).length < 2 ^ (prefixWord ++ tailWord_1107091).sum := by decide
  have hdescent : baseEnd_1107091 < baseStart_1107091 := by decide
  rcases family_descends (prefixWord ++ tailWord_1107091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1107108 : List Nat := [2, 3, 1, 2, 3, 1, 2, 2, 2, 1, 4]
def baseStart_1107108 : Nat := 118140960795 + 1107108 * 2 ^ 59
def prefixEnd_1107108 : Nat := 4983230072969 + 3 ^ 40 * 1107108 * 2
def baseEnd_1107108 : Nat := 568478540437959668558509

theorem tailTrace_1107108 : CollatzResearch.WordTrace tailWord_1107108 prefixEnd_1107108 568478540437959668558509 := by
  unfold tailWord_1107108
  simp only [CollatzResearch.WordTrace]
  refine ⟨20189773036572134919080989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26919697382096179892107985 20189773036572134919080989)
  ·
    refine ⟨7571164888714550594655371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20189773036572134919080989 7571164888714550594655371)
    ·
      refine ⟨11356747333071825891983057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7571164888714550594655371 11356747333071825891983057)
      ·
        refine ⟨8517560499803869418987293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11356747333071825891983057 8517560499803869418987293)
        ·
          refine ⟨3194085187426451032120235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8517560499803869418987293 3194085187426451032120235)
          ·
            refine ⟨4791127781139676548180353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3194085187426451032120235 4791127781139676548180353)
            ·
              refine ⟨3593345835854757411135265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4791127781139676548180353 3593345835854757411135265)
              ·
                refine ⟨2695009376891068058351449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3593345835854757411135265 2695009376891068058351449)
                ·
                  refine ⟨2021257032668301043763587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2695009376891068058351449 2021257032668301043763587)
                  ·
                    refine ⟨3031885549002451565645381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2021257032668301043763587 3031885549002451565645381)
                    ·
                      refine ⟨568478540437959668558509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3031885549002451565645381 568478540437959668558509)
                      ·
                        rfl

theorem cell23_1107108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 2, 2, 2, 1, 4].length) (baseStart_1107108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1107108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1107108 prefixEnd_1107108 := by exact prefixLift 1107108
  have htrace : WordTrace (prefixWord ++ tailWord_1107108) baseStart_1107108 baseEnd_1107108 := by
    simpa [prefixWord, tailWord_1107108, baseEnd_1107108] using wordTrace_append hprefix tailTrace_1107108
  have hstable : (prefixWord ++ tailWord_1107108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1107108).length < 2 ^ (prefixWord ++ tailWord_1107108).sum := by decide
  have hdescent : baseEnd_1107108 < baseStart_1107108 := by decide
  rcases family_descends (prefixWord ++ tailWord_1107108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1107242 : List Nat := [3, 1, 4, 2, 1, 2, 1, 3, 2, 4]
def baseStart_1107242 : Nat := 118140960795 + 1107242 * 2 ^ 59
def prefixEnd_1107242 : Nat := 4983230072969 + 3 ^ 40 * 1107242 * 2
def baseEnd_1107242 : Nat := 189515782281887381427631

theorem tailTrace_1107242 : CollatzResearch.WordTrace tailWord_1107242 prefixEnd_1107242 189515782281887381427631 := by
  unfold tailWord_1107242
  simp only [CollatzResearch.WordTrace]
  refine ⟨10096108363664702680884995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26922955636439207149026653 10096108363664702680884995)
  ·
    refine ⟨15144162545497054021327493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10096108363664702680884995 15144162545497054021327493)
    ·
      refine ⟨2839530477280697628998905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15144162545497054021327493 2839530477280697628998905)
      ·
        refine ⟨2129647857960523221749179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2839530477280697628998905 2129647857960523221749179)
        ·
          refine ⟨3194471786940784832623769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2129647857960523221749179 3194471786940784832623769)
          ·
            refine ⟨2395853840205588624467827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3194471786940784832623769 2395853840205588624467827)
            ·
              refine ⟨3593780760308382936701741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2395853840205588624467827 3593780760308382936701741)
              ·
                refine ⟨1347667785115643601263153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3593780760308382936701741 1347667785115643601263153)
                ·
                  refine ⟨1010750838836732700947365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1347667785115643601263153 1010750838836732700947365)
                  ·
                    refine ⟨189515782281887381427631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1010750838836732700947365 189515782281887381427631)
                    ·
                      rfl

theorem cell23_1107242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 1, 3, 2, 4].length) (baseStart_1107242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1107242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1107242 prefixEnd_1107242 := by exact prefixLift 1107242
  have htrace : WordTrace (prefixWord ++ tailWord_1107242) baseStart_1107242 baseEnd_1107242 := by
    simpa [prefixWord, tailWord_1107242, baseEnd_1107242] using wordTrace_append hprefix tailTrace_1107242
  have hstable : (prefixWord ++ tailWord_1107242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1107242).length < 2 ^ (prefixWord ++ tailWord_1107242).sum := by decide
  have hdescent : baseEnd_1107242 < baseStart_1107242 := by decide
  rcases family_descends (prefixWord ++ tailWord_1107242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1107245 : List Nat := [1, 5, 3, 1, 1, 1, 2, 1, 1, 1, 6]
def baseStart_1107245 : Nat := 118140960795 + 1107245 * 2 ^ 59
def prefixEnd_1107245 : Nat := 4983230072969 + 3 ^ 40 * 1107245 * 2
def baseEnd_1107245 : Nat := 568548887287625632545379

theorem tailTrace_1107245 : CollatzResearch.WordTrace tailWord_1107245 prefixEnd_1107245 568548887287625632545379 := by
  unfold tailWord_1107245
  simp only [CollatzResearch.WordTrace]
  refine ⟨40384542873647942235899189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26923028582431961490599459 40384542873647942235899189)
  ·
    refine ⟨3786050894404494584615549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 40384542873647942235899189 3786050894404494584615549)
    ·
      refine ⟨1419769085401685469230831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3786050894404494584615549 1419769085401685469230831)
      ·
        refine ⟨2129653628102528203846247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1419769085401685469230831 2129653628102528203846247)
        ·
          refine ⟨3194480442153792305769371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2129653628102528203846247 3194480442153792305769371)
          ·
            refine ⟨4791720663230688458654057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3194480442153792305769371 4791720663230688458654057)
            ·
              refine ⟨3593790497423016343990543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4791720663230688458654057 3593790497423016343990543)
              ·
                refine ⟨5390685746134524515985815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3593790497423016343990543 5390685746134524515985815)
                ·
                  refine ⟨8086028619201786773978723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5390685746134524515985815 8086028619201786773978723)
                  ·
                    refine ⟨12129042928802680160968085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8086028619201786773978723 12129042928802680160968085)
                    ·
                      refine ⟨568548887287625632545379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 12129042928802680160968085 568548887287625632545379)
                      ·
                        rfl

theorem cell23_1107245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 2, 1, 1, 1, 6].length) (baseStart_1107245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1107245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1107245 prefixEnd_1107245 := by exact prefixLift 1107245
  have htrace : WordTrace (prefixWord ++ tailWord_1107245) baseStart_1107245 baseEnd_1107245 := by
    simpa [prefixWord, tailWord_1107245, baseEnd_1107245] using wordTrace_append hprefix tailTrace_1107245
  have hstable : (prefixWord ++ tailWord_1107245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1107245).length < 2 ^ (prefixWord ++ tailWord_1107245).sum := by decide
  have hdescent : baseEnd_1107245 < baseStart_1107245 := by decide
  rcases family_descends (prefixWord ++ tailWord_1107245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1107248 : List Nat := [2, 1, 1, 1, 2, 2, 4, 3, 1, 3, 3]
def baseStart_1107248 : Nat := 118140960795 + 1107248 * 2 ^ 59
def prefixEnd_1107248 : Nat := 4983230072969 + 3 ^ 40 * 1107248 * 2
def baseEnd_1107248 : Nat := 568550427729589120807865

theorem tailTrace_1107248 : CollatzResearch.WordTrace tailWord_1107248 prefixEnd_1107248 568550427729589120807865 := by
  unfold tailWord_1107248
  simp only [CollatzResearch.WordTrace]
  refine ⟨20192326146318536874129199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26923101528424715832172265 20192326146318536874129199)
  ·
    refine ⟨30288489219477805311193799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20192326146318536874129199 30288489219477805311193799)
    ·
      refine ⟨45432733829216707966790699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30288489219477805311193799 45432733829216707966790699)
      ·
        refine ⟨68149100743825061950186049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45432733829216707966790699 68149100743825061950186049)
        ·
          refine ⟨51111825557868796462639537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68149100743825061950186049 51111825557868796462639537)
          ·
            refine ⟨38333869168401597346979653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51111825557868796462639537 38333869168401597346979653)
            ·
              refine ⟨7187600469075299502558685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38333869168401597346979653 7187600469075299502558685)
              ·
                refine ⟨2695350175903237313459507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7187600469075299502558685 2695350175903237313459507)
                ·
                  refine ⟨4043025263854855970189261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2695350175903237313459507 4043025263854855970189261)
                  ·
                    refine ⟨1516134473945570988820973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4043025263854855970189261 1516134473945570988820973)
                    ·
                      refine ⟨568550427729589120807865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1516134473945570988820973 568550427729589120807865)
                      ·
                        rfl

theorem cell23_1107248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 3, 1, 3, 3].length) (baseStart_1107248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1107248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1107248 prefixEnd_1107248 := by exact prefixLift 1107248
  have htrace : WordTrace (prefixWord ++ tailWord_1107248) baseStart_1107248 baseEnd_1107248 := by
    simpa [prefixWord, tailWord_1107248, baseEnd_1107248] using wordTrace_append hprefix tailTrace_1107248
  have hstable : (prefixWord ++ tailWord_1107248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1107248).length < 2 ^ (prefixWord ++ tailWord_1107248).sum := by decide
  have hdescent : baseEnd_1107248 < baseStart_1107248 := by decide
  rcases family_descends (prefixWord ++ tailWord_1107248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1107265 : List Nat := [1, 2, 5, 2, 1, 1, 1, 1, 3, 3, 3]
def baseStart_1107265 : Nat := 118140960795 + 1107265 * 2 ^ 59
def prefixEnd_1107265 : Nat := 4983230072969 + 3 ^ 40 * 1107265 * 2
def baseEnd_1107265 : Nat := 568559156900715554295287

theorem tailTrace_1107265 : CollatzResearch.WordTrace tailWord_1107265 prefixEnd_1107265 568559156900715554295287 := by
  unfold tailWord_1107265
  simp only [CollatzResearch.WordTrace]
  refine ⟨40385272333575485651627249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26923514889050323767751499 40385272333575485651627249)
  ·
    refine ⟨30288954250181614238720437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40385272333575485651627249 30288954250181614238720437)
    ·
      refine ⟨2839589460954526334880041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 30288954250181614238720437 2839589460954526334880041)
      ·
        refine ⟨2129692095715894751160031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2839589460954526334880041 2129692095715894751160031)
        ·
          refine ⟨3194538143573842126740047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2129692095715894751160031 3194538143573842126740047)
          ·
            refine ⟨4791807215360763190110071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3194538143573842126740047 4791807215360763190110071)
            ·
              refine ⟨7187710823041144785165107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4791807215360763190110071 7187710823041144785165107)
              ·
                refine ⟨10781566234561717177747661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7187710823041144785165107 10781566234561717177747661)
                ·
                  refine ⟨4043087337960643941655373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10781566234561717177747661 4043087337960643941655373)
                  ·
                    refine ⟨1516157751735241478120765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4043087337960643941655373 1516157751735241478120765)
                    ·
                      refine ⟨568559156900715554295287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1516157751735241478120765 568559156900715554295287)
                      ·
                        rfl

theorem cell23_1107265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 1, 3, 3, 3].length) (baseStart_1107265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1107265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1107265 prefixEnd_1107265 := by exact prefixLift 1107265
  have htrace : WordTrace (prefixWord ++ tailWord_1107265) baseStart_1107265 baseEnd_1107265 := by
    simpa [prefixWord, tailWord_1107265, baseEnd_1107265] using wordTrace_append hprefix tailTrace_1107265
  have hstable : (prefixWord ++ tailWord_1107265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1107265).length < 2 ^ (prefixWord ++ tailWord_1107265).sum := by decide
  have hdescent : baseEnd_1107265 < baseStart_1107265 := by decide
  rcases family_descends (prefixWord ++ tailWord_1107265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1107356 : List Nat := [2, 2, 3, 4, 1, 2, 1, 1, 1, 4, 2]
def baseStart_1107356 : Nat := 118140960795 + 1107356 * 2 ^ 59
def prefixEnd_1107356 : Nat := 4983230072969 + 3 ^ 40 * 1107356 * 2
def baseEnd_1107356 : Nat := 568605883640274698257369

theorem tailTrace_1107356 : CollatzResearch.WordTrace tailWord_1107356 prefixEnd_1107356 568605883640274698257369 := by
  unfold tailWord_1107356
  simp only [CollatzResearch.WordTrace]
  refine ⟨20194295688122904096594961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26925727584163872128793281 20194295688122904096594961)
  ·
    refine ⟨15145721766092178072446221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20194295688122904096594961 15145721766092178072446221)
    ·
      refine ⟨5679645662284566777167333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15145721766092178072446221 5679645662284566777167333)
      ·
        refine ⟨1064933561678356270718875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5679645662284566777167333 1064933561678356270718875)
        ·
          refine ⟨1597400342517534406078313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1064933561678356270718875 1597400342517534406078313)
          ·
            refine ⟨1198050256888150804558735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1597400342517534406078313 1198050256888150804558735)
            ·
              refine ⟨1797075385332226206838103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1198050256888150804558735 1797075385332226206838103)
              ·
                refine ⟨2695613077998339310257155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1797075385332226206838103 2695613077998339310257155)
                ·
                  refine ⟨4043419616997508965385733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2695613077998339310257155 4043419616997508965385733)
                  ·
                    refine ⟨758141178187032931009825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4043419616997508965385733 758141178187032931009825)
                    ·
                      refine ⟨568605883640274698257369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 758141178187032931009825 568605883640274698257369)
                      ·
                        rfl

theorem cell23_1107356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 2, 1, 1, 1, 4, 2].length) (baseStart_1107356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1107356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1107356 prefixEnd_1107356 := by exact prefixLift 1107356
  have htrace : WordTrace (prefixWord ++ tailWord_1107356) baseStart_1107356 baseEnd_1107356 := by
    simpa [prefixWord, tailWord_1107356, baseEnd_1107356] using wordTrace_append hprefix tailTrace_1107356
  have hstable : (prefixWord ++ tailWord_1107356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1107356).length < 2 ^ (prefixWord ++ tailWord_1107356).sum := by decide
  have hdescent : baseEnd_1107356 < baseStart_1107356 := by decide
  rcases family_descends (prefixWord ++ tailWord_1107356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1107395 : List Nat := [1, 1, 1, 3, 1, 1, 4, 1, 4, 4, 2]
def baseStart_1107395 : Nat := 118140960795 + 1107395 * 2 ^ 59
def prefixEnd_1107395 : Nat := 4983230072969 + 3 ^ 40 * 1107395 * 2
def baseEnd_1107395 : Nat := 568625909385800045669689

theorem tailTrace_1107395 : CollatzResearch.WordTrace tailWord_1107395 prefixEnd_1107395 568625909385800045669689 := by
  unfold tailWord_1107395
  simp only [CollatzResearch.WordTrace]
  refine ⟨40390013823104517853859639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26926675882069678569239759 40390013823104517853859639)
  ·
    refine ⟨60585020734656776780789459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40390013823104517853859639 60585020734656776780789459)
    ·
      refine ⟨90877531101985165171184189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60585020734656776780789459 90877531101985165171184189)
      ·
        refine ⟨34079074163244436939194071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 90877531101985165171184189 34079074163244436939194071)
        ·
          refine ⟨51118611244866655408791107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34079074163244436939194071 51118611244866655408791107)
          ·
            refine ⟨76677916867299983113186661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51118611244866655408791107 76677916867299983113186661)
            ·
              refine ⟨14377109412618746833722499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 76677916867299983113186661 14377109412618746833722499)
              ·
                refine ⟨21565664118928120250583749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14377109412618746833722499 21565664118928120250583749)
                ·
                  refine ⟨4043562022299022546984453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21565664118928120250583749 4043562022299022546984453)
                  ·
                    refine ⟨758167879181066727559585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4043562022299022546984453 758167879181066727559585)
                    ·
                      refine ⟨568625909385800045669689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 758167879181066727559585 568625909385800045669689)
                      ·
                        rfl

theorem cell23_1107395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 1, 4, 4, 2].length) (baseStart_1107395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1107395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1107395 prefixEnd_1107395 := by exact prefixLift 1107395
  have htrace : WordTrace (prefixWord ++ tailWord_1107395) baseStart_1107395 baseEnd_1107395 := by
    simpa [prefixWord, tailWord_1107395, baseEnd_1107395] using wordTrace_append hprefix tailTrace_1107395
  have hstable : (prefixWord ++ tailWord_1107395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1107395).length < 2 ^ (prefixWord ++ tailWord_1107395).sum := by decide
  have hdescent : baseEnd_1107395 < baseStart_1107395 := by decide
  rcases family_descends (prefixWord ++ tailWord_1107395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1107432 : List Nat := [2, 1, 4, 1, 1, 2, 4, 1, 2, 2, 3]
def baseStart_1107432 : Nat := 118140960795 + 1107432 * 2 ^ 59
def prefixEnd_1107432 : Nat := 4983230072969 + 3 ^ 40 * 1107432 * 2
def baseEnd_1107432 : Nat := 568644908170016400907019

theorem tailTrace_1107432 : CollatzResearch.WordTrace tailWord_1107432 prefixEnd_1107432 568644908170016400907019 := by
  unfold tailWord_1107432
  simp only [CollatzResearch.WordTrace]
  refine ⟨20195681661985236586478275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26927575549313648781971033 20195681661985236586478275)
  ·
    refine ⟨30293522492977854879717413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20195681661985236586478275 30293522492977854879717413)
    ·
      refine ⟨5680035467433347789947015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30293522492977854879717413 5680035467433347789947015)
      ·
        refine ⟨8520053201150021684920523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5680035467433347789947015 8520053201150021684920523)
        ·
          refine ⟨12780079801725032527380785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8520053201150021684920523 12780079801725032527380785)
          ·
            refine ⟨9585059851293774395535589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12780079801725032527380785 9585059851293774395535589)
            ·
              refine ⟨1797198722117582699162923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9585059851293774395535589 1797198722117582699162923)
              ·
                refine ⟨2695798083176374048744385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1797198722117582699162923 2695798083176374048744385)
                ·
                  refine ⟨2021848562382280536558289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2695798083176374048744385 2021848562382280536558289)
                  ·
                    refine ⟨1516386421786710402418717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2021848562382280536558289 1516386421786710402418717)
                    ·
                      refine ⟨568644908170016400907019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1516386421786710402418717 568644908170016400907019)
                      ·
                        rfl

theorem cell23_1107432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 4, 1, 2, 2, 3].length) (baseStart_1107432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1107432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1107432 prefixEnd_1107432 := by exact prefixLift 1107432
  have htrace : WordTrace (prefixWord ++ tailWord_1107432) baseStart_1107432 baseEnd_1107432 := by
    simpa [prefixWord, tailWord_1107432, baseEnd_1107432] using wordTrace_append hprefix tailTrace_1107432
  have hstable : (prefixWord ++ tailWord_1107432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1107432).length < 2 ^ (prefixWord ++ tailWord_1107432).sum := by decide
  have hdescent : baseEnd_1107432 < baseStart_1107432 := by decide
  rcases family_descends (prefixWord ++ tailWord_1107432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1107489 : List Nat := [1, 2, 3, 2, 2, 2, 3, 1, 2, 3, 2]
def baseStart_1107489 : Nat := 118140960795 + 1107489 * 2 ^ 59
def prefixEnd_1107489 : Nat := 4983230072969 + 3 ^ 40 * 1107489 * 2
def baseEnd_1107489 : Nat := 568674176567322677894257

theorem tailTrace_1107489 : CollatzResearch.WordTrace tailWord_1107489 prefixEnd_1107489 568674176567322677894257 := by
  unfold tailWord_1107489
  simp only [CollatzResearch.WordTrace]
  refine ⟨40393442284763971907781521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26928961523175981271854347 40393442284763971907781521)
  ·
    refine ⟨30295081713572978930836141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40393442284763971907781521 30295081713572978930836141)
    ·
      refine ⟨11360655642589867099063553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30295081713572978930836141 11360655642589867099063553)
      ·
        refine ⟨8520491731942400324297665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11360655642589867099063553 8520491731942400324297665)
        ·
          refine ⟨6390368798956800243223249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8520491731942400324297665 6390368798956800243223249)
          ·
            refine ⟨4792776599217600182417437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6390368798956800243223249 4792776599217600182417437)
            ·
              refine ⟨1797291224706600068406539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4792776599217600182417437 1797291224706600068406539)
              ·
                refine ⟨2695936837059900102609809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1797291224706600068406539 2695936837059900102609809)
                ·
                  refine ⟨2021952627794925076957357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2695936837059900102609809 2021952627794925076957357)
                  ·
                    refine ⟨758232235423096903859009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2021952627794925076957357 758232235423096903859009)
                    ·
                      refine ⟨568674176567322677894257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 758232235423096903859009 568674176567322677894257)
                      ·
                        rfl

theorem cell23_1107489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 3, 1, 2, 3, 2].length) (baseStart_1107489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1107489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1107489 prefixEnd_1107489 := by exact prefixLift 1107489
  have htrace : WordTrace (prefixWord ++ tailWord_1107489) baseStart_1107489 baseEnd_1107489 := by
    simpa [prefixWord, tailWord_1107489, baseEnd_1107489] using wordTrace_append hprefix tailTrace_1107489
  have hstable : (prefixWord ++ tailWord_1107489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1107489).length < 2 ^ (prefixWord ++ tailWord_1107489).sum := by decide
  have hdescent : baseEnd_1107489 < baseStart_1107489 := by decide
  rcases family_descends (prefixWord ++ tailWord_1107489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1107505 : List Nat := [1, 2, 2, 3, 1, 1, 1, 5, 1, 1, 5]
def baseStart_1107505 : Nat := 118140960795 + 1107505 * 2 ^ 59
def prefixEnd_1107505 : Nat := 4983230072969 + 3 ^ 40 * 1107505 * 2
def baseEnd_1107505 : Nat := 568682392257794615294183

theorem tailTrace_1107505 : CollatzResearch.WordTrace tailWord_1107505 prefixEnd_1107505 568682392257794615294183 := by
  unfold tailWord_1107505
  simp only [CollatzResearch.WordTrace]
  refine ⟨40394025852706006640363969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26929350568470671093575979 40394025852706006640363969)
  ·
    refine ⟨30295519389529504980272977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40394025852706006640363969 30295519389529504980272977)
    ·
      refine ⟨22721639542147128735204733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30295519389529504980272977 22721639542147128735204733)
      ·
        refine ⟨8520614828305173275701775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22721639542147128735204733 8520614828305173275701775)
        ·
          refine ⟨12780922242457759913552663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8520614828305173275701775 12780922242457759913552663)
          ·
            refine ⟨19171383363686639870328995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12780922242457759913552663 19171383363686639870328995)
            ·
              refine ⟨28757075045529959805493493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19171383363686639870328995 28757075045529959805493493)
              ·
                refine ⟨2695975785518433731765015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 28757075045529959805493493 2695975785518433731765015)
                ·
                  refine ⟨4043963678277650597647523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2695975785518433731765015 4043963678277650597647523)
                  ·
                    refine ⟨6065945517416475896471285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4043963678277650597647523 6065945517416475896471285)
                    ·
                      refine ⟨568682392257794615294183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6065945517416475896471285 568682392257794615294183)
                      ·
                        rfl

theorem cell23_1107505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 5, 1, 1, 5].length) (baseStart_1107505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1107505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1107505 prefixEnd_1107505 := by exact prefixLift 1107505
  have htrace : WordTrace (prefixWord ++ tailWord_1107505) baseStart_1107505 baseEnd_1107505 := by
    simpa [prefixWord, tailWord_1107505, baseEnd_1107505] using wordTrace_append hprefix tailTrace_1107505
  have hstable : (prefixWord ++ tailWord_1107505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1107505).length < 2 ^ (prefixWord ++ tailWord_1107505).sum := by decide
  have hdescent : baseEnd_1107505 < baseStart_1107505 := by decide
  rcases family_descends (prefixWord ++ tailWord_1107505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1107512 : List Nat := [2, 1, 2, 1, 4, 3, 1, 1, 4, 4]
def baseStart_1107512 : Nat := 118140960795 + 1107512 * 2 ^ 59
def prefixEnd_1107512 : Nat := 4983230072969 + 3 ^ 40 * 1107512 * 2
def baseEnd_1107512 : Nat := 189561995540792029302217

theorem tailTrace_1107512 : CollatzResearch.WordTrace tailWord_1107512 prefixEnd_1107512 189561995540792029302217 := by
  unfold tailWord_1107512
  simp only [CollatzResearch.WordTrace]
  refine ⟨20197140581840323417934395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26929520775787097890579193 20197140581840323417934395)
  ·
    refine ⟨30295710872760485126901593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20197140581840323417934395 30295710872760485126901593)
    ·
      refine ⟨22721783154570363845176195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30295710872760485126901593 22721783154570363845176195)
      ·
        refine ⟨34082674731855545767764293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22721783154570363845176195 34082674731855545767764293)
        ·
          refine ⟨6390501512222914831455805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34082674731855545767764293 6390501512222914831455805)
          ·
            refine ⟨2396438067083593061795927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6390501512222914831455805 2396438067083593061795927)
            ·
              refine ⟨3594657100625389592693891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2396438067083593061795927 3594657100625389592693891)
              ·
                refine ⟨5391985650938084389040837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3594657100625389592693891 5391985650938084389040837)
                ·
                  refine ⟨1010997309550890822945157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5391985650938084389040837 1010997309550890822945157)
                  ·
                    refine ⟨189561995540792029302217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1010997309550890822945157 189561995540792029302217)
                    ·
                      rfl

theorem cell23_1107512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 1, 1, 4, 4].length) (baseStart_1107512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1107512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1107512 prefixEnd_1107512 := by exact prefixLift 1107512
  have htrace : WordTrace (prefixWord ++ tailWord_1107512) baseStart_1107512 baseEnd_1107512 := by
    simpa [prefixWord, tailWord_1107512, baseEnd_1107512] using wordTrace_append hprefix tailTrace_1107512
  have hstable : (prefixWord ++ tailWord_1107512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1107512).length < 2 ^ (prefixWord ++ tailWord_1107512).sum := by decide
  have hdescent : baseEnd_1107512 < baseStart_1107512 := by decide
  rcases family_descends (prefixWord ++ tailWord_1107512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1107519 : List Nat := [1, 1, 2, 2, 3, 3, 1, 3, 3, 2, 2]
def baseStart_1107519 : Nat := 118140960795 + 1107519 * 2 ^ 59
def prefixEnd_1107519 : Nat := 4983230072969 + 3 ^ 40 * 1107519 * 2
def baseEnd_1107519 : Nat := 568689580986957560519119

theorem tailTrace_1107519 : CollatzResearch.WordTrace tailWord_1107519 prefixEnd_1107519 568689580986957560519119 := by
  unfold tailWord_1107519
  simp only [CollatzResearch.WordTrace]
  refine ⟨40394536474655287031373611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26929690983103524687582407 40394536474655287031373611)
  ·
    refine ⟨60591804711982930547060417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40394536474655287031373611 60591804711982930547060417)
    ·
      refine ⟨45443853533987197910295313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60591804711982930547060417 45443853533987197910295313)
      ·
        refine ⟨34082890150490398432721485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45443853533987197910295313 34082890150490398432721485)
        ·
          refine ⟨12781083806433899412270557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34082890150490398432721485 12781083806433899412270557)
          ·
            refine ⟨4792906427412712279601459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12781083806433899412270557 4792906427412712279601459)
            ·
              refine ⟨7189359641119068419402189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4792906427412712279601459 7189359641119068419402189)
              ·
                refine ⟨2696009865419650657275821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7189359641119068419402189 2696009865419650657275821)
                ·
                  refine ⟨1011003699532368996478433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2696009865419650657275821 1011003699532368996478433)
                  ·
                    refine ⟨758252774649276747358825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1011003699532368996478433 758252774649276747358825)
                    ·
                      refine ⟨568689580986957560519119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 758252774649276747358825 568689580986957560519119)
                      ·
                        rfl

theorem cell23_1107519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 3, 3, 2, 2].length) (baseStart_1107519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1107519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1107519 prefixEnd_1107519 := by exact prefixLift 1107519
  have htrace : WordTrace (prefixWord ++ tailWord_1107519) baseStart_1107519 baseEnd_1107519 := by
    simpa [prefixWord, tailWord_1107519, baseEnd_1107519] using wordTrace_append hprefix tailTrace_1107519
  have hstable : (prefixWord ++ tailWord_1107519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1107519).length < 2 ^ (prefixWord ++ tailWord_1107519).sum := by decide
  have hdescent : baseEnd_1107519 < baseStart_1107519 := by decide
  rcases family_descends (prefixWord ++ tailWord_1107519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1107532 : List Nat := [2, 2, 1, 3, 1, 3, 3, 1, 1, 2, 4]
def baseStart_1107532 : Nat := 118140960795 + 1107532 * 2 ^ 59
def prefixEnd_1107532 : Nat := 4983230072969 + 3 ^ 40 * 1107532 * 2
def baseEnd_1107532 : Nat := 568696256235466009656559

theorem tailTrace_1107532 : CollatzResearch.WordTrace tailWord_1107532 prefixEnd_1107532 568696256235466009656559 := by
  unfold tailWord_1107532
  simp only [CollatzResearch.WordTrace]
  refine ⟨20197505311804095125798425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26930007082405460167731233 20197505311804095125798425)
  ·
    refine ⟨15148128983853071344348819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20197505311804095125798425 15148128983853071344348819)
    ·
      refine ⟨22722193475779607016523229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15148128983853071344348819 22722193475779607016523229)
      ·
        refine ⟨8520822553417352631196211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22722193475779607016523229 8520822553417352631196211)
        ·
          refine ⟨12781233830126028946794317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8520822553417352631196211 12781233830126028946794317)
          ·
            refine ⟨4792962686297260855047869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12781233830126028946794317 4792962686297260855047869)
            ·
              refine ⟨1797361007361472820642951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4792962686297260855047869 1797361007361472820642951)
              ·
                refine ⟨2696041511042209230964427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1797361007361472820642951 2696041511042209230964427)
                ·
                  refine ⟨4044062266563313846446641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2696041511042209230964427 4044062266563313846446641)
                  ·
                    refine ⟨3033046699922485384834981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4044062266563313846446641 3033046699922485384834981)
                    ·
                      refine ⟨568696256235466009656559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3033046699922485384834981 568696256235466009656559)
                      ·
                        rfl

theorem cell23_1107532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 3, 1, 1, 2, 4].length) (baseStart_1107532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1107532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1107532 prefixEnd_1107532 := by exact prefixLift 1107532
  have htrace : WordTrace (prefixWord ++ tailWord_1107532) baseStart_1107532 baseEnd_1107532 := by
    simpa [prefixWord, tailWord_1107532, baseEnd_1107532] using wordTrace_append hprefix tailTrace_1107532
  have hstable : (prefixWord ++ tailWord_1107532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1107532).length < 2 ^ (prefixWord ++ tailWord_1107532).sum := by decide
  have hdescent : baseEnd_1107532 < baseStart_1107532 := by decide
  rcases family_descends (prefixWord ++ tailWord_1107532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1107570 : List Nat := [3, 2, 1, 2, 3, 2, 3, 2, 1, 2, 2]
def baseStart_1107570 : Nat := 118140960795 + 1107570 * 2 ^ 59
def prefixEnd_1107570 : Nat := 4983230072969 + 3 ^ 40 * 1107570 * 2
def baseEnd_1107570 : Nat := 568715768500336860981385

theorem tailTrace_1107570 : CollatzResearch.WordTrace tailWord_1107570 prefixEnd_1107570 568715768500336860981385 := by
  unfold tailWord_1107570
  simp only [CollatzResearch.WordTrace]
  refine ⟨10099099149367630685370041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26930931064980348494320109 10099099149367630685370041)
  ·
    refine ⟨7574324362025723014027531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10099099149367630685370041 7574324362025723014027531)
    ·
      refine ⟨11361486543038584521041297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7574324362025723014027531 11361486543038584521041297)
      ·
        refine ⟨8521114907278938390780973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11361486543038584521041297 8521114907278938390780973)
        ·
          refine ⟨3195418090229601896542865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8521114907278938390780973 3195418090229601896542865)
          ·
            refine ⟨2396563567672201422407149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3195418090229601896542865 2396563567672201422407149)
            ·
              refine ⟨898711337877075533402681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2396563567672201422407149 898711337877075533402681)
              ·
                refine ⟨674033503407806650052011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 898711337877075533402681 674033503407806650052011)
                ·
                  refine ⟨1011050255111709975078017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 674033503407806650052011 1011050255111709975078017)
                  ·
                    refine ⟨758287691333782481308513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1011050255111709975078017 758287691333782481308513)
                    ·
                      refine ⟨568715768500336860981385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 758287691333782481308513 568715768500336860981385)
                      ·
                        rfl

theorem cell23_1107570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 3, 2, 1, 2, 2].length) (baseStart_1107570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1107570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1107570 prefixEnd_1107570 := by exact prefixLift 1107570
  have htrace : WordTrace (prefixWord ++ tailWord_1107570) baseStart_1107570 baseEnd_1107570 := by
    simpa [prefixWord, tailWord_1107570, baseEnd_1107570] using wordTrace_append hprefix tailTrace_1107570
  have hstable : (prefixWord ++ tailWord_1107570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1107570).length < 2 ^ (prefixWord ++ tailWord_1107570).sum := by decide
  have hdescent : baseEnd_1107570 < baseStart_1107570 := by decide
  rcases family_descends (prefixWord ++ tailWord_1107570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1107575 : List Nat := [1, 1, 3, 1, 1, 3, 1, 3, 2, 3, 4]
def baseStart_1107575 : Nat := 118140960795 + 1107575 * 2 ^ 59
def prefixEnd_1107575 : Nat := 4983230072969 + 3 ^ 40 * 1107575 * 2
def baseEnd_1107575 : Nat := 568718335903609341418861

theorem tailTrace_1107575 : CollatzResearch.WordTrace tailWord_1107575 prefixEnd_1107575 568718335903609341418861 := by
  unfold tailWord_1107575
  simp only [CollatzResearch.WordTrace]
  refine ⟨40396578962452408595412179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26931052641634939063608119 40396578962452408595412179)
  ·
    refine ⟨60594868443678612893118269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40396578962452408595412179 60594868443678612893118269)
    ·
      refine ⟨22723075666379479834919351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60594868443678612893118269 22723075666379479834919351)
      ·
        refine ⟨34084613499569219752379027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22723075666379479834919351 34084613499569219752379027)
        ·
          refine ⟨51126920249353829628568541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34084613499569219752379027 51126920249353829628568541)
          ·
            refine ⟨19172595093507686110713203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51126920249353829628568541 19172595093507686110713203)
            ·
              refine ⟨28758892640261529166069805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19172595093507686110713203 28758892640261529166069805)
              ·
                refine ⟨10784584740098073437276177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28758892640261529166069805 10784584740098073437276177)
                ·
                  refine ⟨8088438555073555077957133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10784584740098073437276177 8088438555073555077957133)
                  ·
                    refine ⟨3033164458152583154233925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8088438555073555077957133 3033164458152583154233925)
                    ·
                      refine ⟨568718335903609341418861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3033164458152583154233925 568718335903609341418861)
                      ·
                        rfl

theorem cell23_1107575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 3, 2, 3, 4].length) (baseStart_1107575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1107575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1107575 prefixEnd_1107575 := by exact prefixLift 1107575
  have htrace : WordTrace (prefixWord ++ tailWord_1107575) baseStart_1107575 baseEnd_1107575 := by
    simpa [prefixWord, tailWord_1107575, baseEnd_1107575] using wordTrace_append hprefix tailTrace_1107575
  have hstable : (prefixWord ++ tailWord_1107575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1107575).length < 2 ^ (prefixWord ++ tailWord_1107575).sum := by decide
  have hdescent : baseEnd_1107575 < baseStart_1107575 := by decide
  rcases family_descends (prefixWord ++ tailWord_1107575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1107595 : List Nat := [1, 1, 1, 1, 4, 1, 3, 1, 4, 1, 5]
def baseStart_1107595 : Nat := 118140960795 + 1107595 * 2 ^ 59
def prefixEnd_1107595 : Nat := 4983230072969 + 3 ^ 40 * 1107595 * 2
def baseEnd_1107595 : Nat := 568728605516699263168769

theorem tailTrace_1107595 : CollatzResearch.WordTrace tailWord_1107595 prefixEnd_1107595 568728605516699263168769 := by
  unfold tailWord_1107595
  simp only [CollatzResearch.WordTrace]
  refine ⟨40397308422379952011140239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26931538948253301340760159 40397308422379952011140239)
  ·
    refine ⟨60595962633569928016710359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40397308422379952011140239 60595962633569928016710359)
    ·
      refine ⟨90893943950354892025065539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60595962633569928016710359 90893943950354892025065539)
      ·
        refine ⟨136340915925532338037598309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90893943950354892025065539 136340915925532338037598309)
        ·
          refine ⟨25563921736037313382049683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 136340915925532338037598309 25563921736037313382049683)
          ·
            refine ⟨38345882604055970073074525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25563921736037313382049683 38345882604055970073074525)
            ·
              refine ⟨14379705976520988777402947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38345882604055970073074525 14379705976520988777402947)
              ·
                refine ⟨21569558964781483166104421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14379705976520988777402947 21569558964781483166104421)
                ·
                  refine ⟨4044292305896528093644579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21569558964781483166104421 4044292305896528093644579)
                  ·
                    refine ⟨6066438458844792140466869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4044292305896528093644579 6066438458844792140466869)
                    ·
                      refine ⟨568728605516699263168769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6066438458844792140466869 568728605516699263168769)
                      ·
                        rfl

theorem cell23_1107595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 1, 4, 1, 5].length) (baseStart_1107595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1107595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1107595 prefixEnd_1107595 := by exact prefixLift 1107595
  have htrace : WordTrace (prefixWord ++ tailWord_1107595) baseStart_1107595 baseEnd_1107595 := by
    simpa [prefixWord, tailWord_1107595, baseEnd_1107595] using wordTrace_append hprefix tailTrace_1107595
  have hstable : (prefixWord ++ tailWord_1107595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1107595).length < 2 ^ (prefixWord ++ tailWord_1107595).sum := by decide
  have hdescent : baseEnd_1107595 < baseStart_1107595 := by decide
  rcases family_descends (prefixWord ++ tailWord_1107595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1107609 : List Nat := [1, 2, 1, 2, 1, 2, 2, 4, 4, 2, 2]
def baseStart_1107609 : Nat := 118140960795 + 1107609 * 2 ^ 59
def prefixEnd_1107609 : Nat := 4983230072969 + 3 ^ 40 * 1107609 * 2
def baseEnd_1107609 : Nat := 568735794245862208393705

theorem tailTrace_1107609 : CollatzResearch.WordTrace tailWord_1107609 prefixEnd_1107609 568735794245862208393705 := by
  unfold tailWord_1107609
  simp only [CollatzResearch.WordTrace]
  refine ⟨40397819044329232402149881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26931879362886154934766587 40397819044329232402149881)
  ·
    refine ⟨30298364283246924301612411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40397819044329232402149881 30298364283246924301612411)
    ·
      refine ⟨45447546424870386452418617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30298364283246924301612411 45447546424870386452418617)
      ·
        refine ⟨34085659818652789839313963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45447546424870386452418617 34085659818652789839313963)
        ·
          refine ⟨51128489727979184758970945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34085659818652789839313963 51128489727979184758970945)
          ·
            refine ⟨38346367295984388569228209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51128489727979184758970945 38346367295984388569228209)
            ·
              refine ⟨28759775471988291426921157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38346367295984388569228209 28759775471988291426921157)
              ·
                refine ⟨5392457900997804642547717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28759775471988291426921157 5392457900997804642547717)
                ·
                  refine ⟨1011085856437088370477697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5392457900997804642547717 1011085856437088370477697)
                  ·
                    refine ⟨758314392327816277858273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1011085856437088370477697 758314392327816277858273)
                    ·
                      refine ⟨568735794245862208393705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 758314392327816277858273 568735794245862208393705)
                      ·
                        rfl

theorem cell23_1107609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 4, 4, 2, 2].length) (baseStart_1107609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1107609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1107609 prefixEnd_1107609 := by exact prefixLift 1107609
  have htrace : WordTrace (prefixWord ++ tailWord_1107609) baseStart_1107609 baseEnd_1107609 := by
    simpa [prefixWord, tailWord_1107609, baseEnd_1107609] using wordTrace_append hprefix tailTrace_1107609
  have hstable : (prefixWord ++ tailWord_1107609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1107609).length < 2 ^ (prefixWord ++ tailWord_1107609).sum := by decide
  have hdescent : baseEnd_1107609 < baseStart_1107609 := by decide
  rcases family_descends (prefixWord ++ tailWord_1107609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1107642 : List Nat := [3, 1, 1, 1, 2, 4, 1, 1, 1, 5, 3]
def baseStart_1107642 : Nat := 118140960795 + 1107642 * 2 ^ 59
def prefixEnd_1107642 : Nat := 4983230072969 + 3 ^ 40 * 1107642 * 2
def baseEnd_1107642 : Nat := 568752739107460579281053

theorem tailTrace_1107642 : CollatzResearch.WordTrace tailWord_1107642 prefixEnd_1107642 568752739107460579281053 := by
  unfold tailWord_1107642
  simp only [CollatzResearch.WordTrace]
  refine ⟨10099755663302419759525295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26932681768806452692067453 10099755663302419759525295)
  ·
    refine ⟨15149633494953629639287943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10099755663302419759525295 15149633494953629639287943)
    ·
      refine ⟨22724450242430444458931915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15149633494953629639287943 22724450242430444458931915)
      ·
        refine ⟨34086675363645666688397873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22724450242430444458931915 34086675363645666688397873)
        ·
          refine ⟨25565006522734250016298405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34086675363645666688397873 25565006522734250016298405)
          ·
            refine ⟨4793438723012671878055951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25565006522734250016298405 4793438723012671878055951)
            ·
              refine ⟨7190158084519007817083927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4793438723012671878055951 7190158084519007817083927)
              ·
                refine ⟨10785237126778511725625891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7190158084519007817083927 10785237126778511725625891)
                ·
                  refine ⟨16177855690167767588438837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10785237126778511725625891 16177855690167767588438837)
                  ·
                    refine ⟨1516673970953228211416141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 16177855690167767588438837 1516673970953228211416141)
                    ·
                      refine ⟨568752739107460579281053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1516673970953228211416141 568752739107460579281053)
                      ·
                        rfl

theorem cell23_1107642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 1, 1, 5, 3].length) (baseStart_1107642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1107642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1107642 prefixEnd_1107642 := by exact prefixLift 1107642
  have htrace : WordTrace (prefixWord ++ tailWord_1107642) baseStart_1107642 baseEnd_1107642 := by
    simpa [prefixWord, tailWord_1107642, baseEnd_1107642] using wordTrace_append hprefix tailTrace_1107642
  have hstable : (prefixWord ++ tailWord_1107642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1107642).length < 2 ^ (prefixWord ++ tailWord_1107642).sum := by decide
  have hdescent : baseEnd_1107642 < baseStart_1107642 := by decide
  rcases family_descends (prefixWord ++ tailWord_1107642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1107662 : List Nat := [4, 1, 1, 1, 3, 1, 3, 1, 1, 7]
def baseStart_1107662 : Nat := 118140960795 + 1107662 * 2 ^ 59
def prefixEnd_1107662 : Nat := 4983230072969 + 3 ^ 40 * 1107662 * 2
def baseEnd_1107662 : Nat := 189587669573516833676987

theorem tailTrace_1107662 : CollatzResearch.WordTrace tailWord_1107662 prefixEnd_1107662 189587669573516833676987 := by
  unfold tailWord_1107662
  simp only [CollatzResearch.WordTrace]
  refine ⟨5049969014142152806728655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26933168075424814969219493 5049969014142152806728655)
  ·
    refine ⟨7574953521213229210092983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5049969014142152806728655 7574953521213229210092983)
    ·
      refine ⟨11362430281819843815139475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7574953521213229210092983 11362430281819843815139475)
      ·
        refine ⟨17043645422729765722709213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11362430281819843815139475 17043645422729765722709213)
        ·
          refine ⟨6391367033523662146015955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17043645422729765722709213 6391367033523662146015955)
          ·
            refine ⟨9587050550285493219023933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6391367033523662146015955 9587050550285493219023933)
            ·
              refine ⟨3595143956357059957133975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9587050550285493219023933 3595143956357059957133975)
              ·
                refine ⟨5392715934535589935700963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3595143956357059957133975 5392715934535589935700963)
                ·
                  refine ⟨8089073901803384903551445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5392715934535589935700963 8089073901803384903551445)
                  ·
                    refine ⟨189587669573516833676987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 8089073901803384903551445 189587669573516833676987)
                    ·
                      rfl

theorem cell23_1107662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 3, 1, 1, 7].length) (baseStart_1107662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1107662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1107662 prefixEnd_1107662 := by exact prefixLift 1107662
  have htrace : WordTrace (prefixWord ++ tailWord_1107662) baseStart_1107662 baseEnd_1107662 := by
    simpa [prefixWord, tailWord_1107662, baseEnd_1107662] using wordTrace_append hprefix tailTrace_1107662
  have hstable : (prefixWord ++ tailWord_1107662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1107662).length < 2 ^ (prefixWord ++ tailWord_1107662).sum := by decide
  have hdescent : baseEnd_1107662 < baseStart_1107662 := by decide
  rcases family_descends (prefixWord ++ tailWord_1107662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1107666 : List Nat := [3, 2, 2, 2, 2, 2, 2, 3, 5]
def baseStart_1107666 : Nat := 118140960795 + 1107666 * 2 ^ 59
def prefixEnd_1107666 : Nat := 4983230072969 + 3 ^ 40 * 1107666 * 2
def baseEnd_1107666 : Nat := 63196118071463165042327

theorem tailTrace_1107666 : CollatzResearch.WordTrace tailWord_1107666 prefixEnd_1107666 63196118071463165042327 := by
  unfold tailWord_1107666
  simp only [CollatzResearch.WordTrace]
  refine ⟨10099974501280682784243713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26933265336748487424649901 10099974501280682784243713)
  ·
    refine ⟨7574980875960512088182785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10099974501280682784243713 7574980875960512088182785)
    ·
      refine ⟨5681235656970384066137089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7574980875960512088182785 5681235656970384066137089)
      ·
        refine ⟨4260926742727788049602817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5681235656970384066137089 4260926742727788049602817)
        ·
          refine ⟨3195695057045841037202113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4260926742727788049602817 3195695057045841037202113)
          ·
            refine ⟨2396771292784380777901585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3195695057045841037202113 2396771292784380777901585)
            ·
              refine ⟨1797578469588285583426189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2396771292784380777901585 1797578469588285583426189)
              ·
                refine ⟨674091926095607093784821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1797578469588285583426189 674091926095607093784821)
                ·
                  refine ⟨63196118071463165042327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 674091926095607093784821 63196118071463165042327)
                  ·
                    rfl

theorem cell23_1107666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 2, 3, 5].length) (baseStart_1107666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1107666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1107666 prefixEnd_1107666 := by exact prefixLift 1107666
  have htrace : WordTrace (prefixWord ++ tailWord_1107666) baseStart_1107666 baseEnd_1107666 := by
    simpa [prefixWord, tailWord_1107666, baseEnd_1107666] using wordTrace_append hprefix tailTrace_1107666
  have hstable : (prefixWord ++ tailWord_1107666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1107666).length < 2 ^ (prefixWord ++ tailWord_1107666).sum := by decide
  have hdescent : baseEnd_1107666 < baseStart_1107666 := by decide
  rcases family_descends (prefixWord ++ tailWord_1107666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1107677 : List Nat := [1, 4, 3, 3, 1, 2, 1, 2, 2, 2, 2]
def baseStart_1107677 : Nat := 118140960795 + 1107677 * 2 ^ 59
def prefixEnd_1107677 : Nat := 4983230072969 + 3 ^ 40 * 1107677 * 2
def baseEnd_1107677 : Nat := 568770710930367942343393

theorem tailTrace_1107677 : CollatzResearch.WordTrace tailWord_1107677 prefixEnd_1107677 568770710930367942343393 := by
  unfold tailWord_1107677
  simp only [CollatzResearch.WordTrace]
  refine ⟨40400299208082880015625285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26933532805388586677083523 40400299208082880015625285)
  ·
    refine ⟨7575056101515540002929741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 40400299208082880015625285 7575056101515540002929741)
    ·
      refine ⟨2840646038068327501098653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7575056101515540002929741 2840646038068327501098653)
      ·
        refine ⟨1065242264275622812911995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2840646038068327501098653 1065242264275622812911995)
        ·
          refine ⟨1597863396413434219367993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1065242264275622812911995 1597863396413434219367993)
          ·
            refine ⟨1198397547310075664525995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1597863396413434219367993 1198397547310075664525995)
            ·
              refine ⟨1797596320965113496788993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1198397547310075664525995 1797596320965113496788993)
              ·
                refine ⟨1348197240723835122591745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1797596320965113496788993 1348197240723835122591745)
                ·
                  refine ⟨1011147930542876341943809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1348197240723835122591745 1011147930542876341943809)
                  ·
                    refine ⟨758360947907157256457857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1011147930542876341943809 758360947907157256457857)
                    ·
                      refine ⟨568770710930367942343393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 758360947907157256457857 568770710930367942343393)
                      ·
                        rfl

theorem cell23_1107677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 2, 1, 2, 2, 2, 2].length) (baseStart_1107677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1107677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1107677 prefixEnd_1107677 := by exact prefixLift 1107677
  have htrace : WordTrace (prefixWord ++ tailWord_1107677) baseStart_1107677 baseEnd_1107677 := by
    simpa [prefixWord, tailWord_1107677, baseEnd_1107677] using wordTrace_append hprefix tailTrace_1107677
  have hstable : (prefixWord ++ tailWord_1107677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1107677).length < 2 ^ (prefixWord ++ tailWord_1107677).sum := by decide
  have hdescent : baseEnd_1107677 < baseStart_1107677 := by decide
  rcases family_descends (prefixWord ++ tailWord_1107677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1107699 : List Nat := [1, 1, 1, 2, 2, 3, 4, 1, 2, 4, 2]
def baseStart_1107699 : Nat := 118140960795 + 1107699 * 2 ^ 59
def prefixEnd_1107699 : Nat := 4983230072969 + 3 ^ 40 * 1107699 * 2
def baseEnd_1107699 : Nat := 568782007504766856268291

theorem tailTrace_1107699 : CollatzResearch.WordTrace tailWord_1107699 prefixEnd_1107699 568782007504766856268291 := by
  unfold tailWord_1107699
  simp only [CollatzResearch.WordTrace]
  refine ⟨40401101614003177772926151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26934067742668785181950767 40401101614003177772926151)
  ·
    refine ⟨60601652421004766659389227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40401101614003177772926151 60601652421004766659389227)
    ·
      refine ⟨90902478631507149989083841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60601652421004766659389227 90902478631507149989083841)
      ·
        refine ⟨68176858973630362491812881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90902478631507149989083841 68176858973630362491812881)
        ·
          refine ⟨51132644230222771868859661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68176858973630362491812881 51132644230222771868859661)
          ·
            refine ⟨19174741586333539450822373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51132644230222771868859661 19174741586333539450822373)
            ·
              refine ⟨3595264047437538647029195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19174741586333539450822373 3595264047437538647029195)
              ·
                refine ⟨5392896071156307970543793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3595264047437538647029195 5392896071156307970543793)
                ·
                  refine ⟨4044672053367230977907845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5392896071156307970543793 4044672053367230977907845)
                  ·
                    refine ⟨758376010006355808357721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4044672053367230977907845 758376010006355808357721)
                    ·
                      refine ⟨568782007504766856268291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 758376010006355808357721 568782007504766856268291)
                      ·
                        rfl

theorem cell23_1107699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 4, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 4, 1, 2, 4, 2].length) (baseStart_1107699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1107699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1107699 prefixEnd_1107699 := by exact prefixLift 1107699
  have htrace : WordTrace (prefixWord ++ tailWord_1107699) baseStart_1107699 baseEnd_1107699 := by
    simpa [prefixWord, tailWord_1107699, baseEnd_1107699] using wordTrace_append hprefix tailTrace_1107699
  have hstable : (prefixWord ++ tailWord_1107699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1107699).length < 2 ^ (prefixWord ++ tailWord_1107699).sum := by decide
  have hdescent : baseEnd_1107699 < baseStart_1107699 := by decide
  rcases family_descends (prefixWord ++ tailWord_1107699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1107722 : List Nat := [3, 1, 2, 2, 1, 3, 1, 2, 8]
def baseStart_1107722 : Nat := 118140960795 + 1107722 * 2 ^ 59
def prefixEnd_1107722 : Nat := 4983230072969 + 3 ^ 40 * 1107722 * 2
def baseEnd_1107722 : Nat := 63199313062202251808965

theorem tailTrace_1107722 : CollatzResearch.WordTrace tailWord_1107722 prefixEnd_1107722 63199313062202251808965 := by
  unfold tailWord_1107722
  simp only [CollatzResearch.WordTrace]
  refine ⟨10100485123229963175253355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26934626995279901800675613 10100485123229963175253355)
  ·
    refine ⟨15150727684844944762880033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10100485123229963175253355 15150727684844944762880033)
    ·
      refine ⟨11363045763633708572160025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15150727684844944762880033 11363045763633708572160025)
      ·
        refine ⟨8522284322725281429120019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11363045763633708572160025 8522284322725281429120019)
        ·
          refine ⟨12783426484087922143680029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8522284322725281429120019 12783426484087922143680029)
          ·
            refine ⟨4793784931532970803880011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12783426484087922143680029 4793784931532970803880011)
            ·
              refine ⟨7190677397299456205820017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4793784931532970803880011 7190677397299456205820017)
              ·
                refine ⟨5393008047974592154365013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7190677397299456205820017 5393008047974592154365013)
                ·
                  refine ⟨63199313062202251808965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 5393008047974592154365013 63199313062202251808965)
                  ·
                    rfl

theorem cell23_1107722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 2, 8].length) (baseStart_1107722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1107722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1107722 prefixEnd_1107722 := by exact prefixLift 1107722
  have htrace : WordTrace (prefixWord ++ tailWord_1107722) baseStart_1107722 baseEnd_1107722 := by
    simpa [prefixWord, tailWord_1107722, baseEnd_1107722] using wordTrace_append hprefix tailTrace_1107722
  have hstable : (prefixWord ++ tailWord_1107722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1107722).length < 2 ^ (prefixWord ++ tailWord_1107722).sum := by decide
  have hdescent : baseEnd_1107722 < baseStart_1107722 := by decide
  rcases family_descends (prefixWord ++ tailWord_1107722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1107743 : List Nat := [1, 1, 2, 4, 2, 1, 5, 2, 1, 4]
def baseStart_1107743 : Nat := 118140960795 + 1107743 * 2 ^ 59
def prefixEnd_1107743 : Nat := 4983230072969 + 3 ^ 40 * 1107743 * 2
def baseEnd_1107743 : Nat := 189601533551188228039363

theorem tailTrace_1107743 : CollatzResearch.WordTrace tailWord_1107743 prefixEnd_1107743 189601533551188228039363 := by
  unfold tailWord_1107743
  simp only [CollatzResearch.WordTrace]
  refine ⟨40402706425843773287527883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26935137617229182191685255 40402706425843773287527883)
  ·
    refine ⟨60604059638765659931291825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40402706425843773287527883 60604059638765659931291825)
    ·
      refine ⟨45453044729074244948468869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60604059638765659931291825 45453044729074244948468869)
      ·
        refine ⟨8522445886701420927837913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 45453044729074244948468869 8522445886701420927837913)
        ·
          refine ⟨6391834415026065695878435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8522445886701420927837913 6391834415026065695878435)
          ·
            refine ⟨9587751622539098543817653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6391834415026065695878435 9587751622539098543817653)
            ·
              refine ⟨898851714613040488482905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9587751622539098543817653 898851714613040488482905)
              ·
                refine ⟨674138785959780366362179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 898851714613040488482905 674138785959780366362179)
                ·
                  refine ⟨1011208178939670549543269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 674138785959780366362179 1011208178939670549543269)
                  ·
                    refine ⟨189601533551188228039363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1011208178939670549543269 189601533551188228039363)
                    ·
                      rfl

theorem cell23_1107743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 5, 2, 1, 4].length) (baseStart_1107743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1107743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1107743 prefixEnd_1107743 := by exact prefixLift 1107743
  have htrace : WordTrace (prefixWord ++ tailWord_1107743) baseStart_1107743 baseEnd_1107743 := by
    simpa [prefixWord, tailWord_1107743, baseEnd_1107743] using wordTrace_append hprefix tailTrace_1107743
  have hstable : (prefixWord ++ tailWord_1107743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1107743).length < 2 ^ (prefixWord ++ tailWord_1107743).sum := by decide
  have hdescent : baseEnd_1107743 < baseStart_1107743 := by decide
  rcases family_descends (prefixWord ++ tailWord_1107743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1107756 : List Nat := [2, 2, 1, 1, 1, 7, 2, 1, 6]
def baseStart_1107756 : Nat := 118140960795 + 1107756 * 2 ^ 59
def prefixEnd_1107756 : Nat := 4983230072969 + 3 ^ 40 * 1107756 * 2
def baseEnd_1107756 : Nat := 63201252878008125917281

theorem tailTrace_1107756 : CollatzResearch.WordTrace tailWord_1107756 prefixEnd_1107756 63201252878008125917281 := by
  unfold tailWord_1107756
  simp only [CollatzResearch.WordTrace]
  refine ⟨20201590287398338253875561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26935453716531117671834081 20201590287398338253875561)
  ·
    refine ⟨15151192715548753690406671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20201590287398338253875561 15151192715548753690406671)
    ·
      refine ⟨22726789073323130535610007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15151192715548753690406671 22726789073323130535610007)
      ·
        refine ⟨34090183609984695803415011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22726789073323130535610007 34090183609984695803415011)
        ·
          refine ⟨51135275414977043705122517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34090183609984695803415011 51135275414977043705122517)
          ·
            refine ⟨1198483017538524461838809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 51135275414977043705122517 1198483017538524461838809)
            ·
              refine ⟨898862263153893346379107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1198483017538524461838809 898862263153893346379107)
              ·
                refine ⟨1348293394730840019568661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 898862263153893346379107 1348293394730840019568661)
                ·
                  refine ⟨63201252878008125917281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1348293394730840019568661 63201252878008125917281)
                  ·
                    rfl

theorem cell23_1107756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 6].length) (baseStart_1107756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1107756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1107756 prefixEnd_1107756 := by exact prefixLift 1107756
  have htrace : WordTrace (prefixWord ++ tailWord_1107756) baseStart_1107756 baseEnd_1107756 := by
    simpa [prefixWord, tailWord_1107756, baseEnd_1107756] using wordTrace_append hprefix tailTrace_1107756
  have hstable : (prefixWord ++ tailWord_1107756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1107756).length < 2 ^ (prefixWord ++ tailWord_1107756).sum := by decide
  have hdescent : baseEnd_1107756 < baseStart_1107756 := by decide
  rcases family_descends (prefixWord ++ tailWord_1107756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1107786 : List Nat := [3, 1, 2, 1, 1, 1, 7, 1, 1, 5]
def baseStart_1107786 : Nat := 118140960795 + 1107786 * 2 ^ 59
def prefixEnd_1107786 : Nat := 4983230072969 + 3 ^ 40 * 1107786 * 2
def baseEnd_1107786 : Nat := 189608893440569338626797

theorem tailTrace_1107786 : CollatzResearch.WordTrace tailWord_1107786 prefixEnd_1107786 189608893440569338626797 := by
  unfold tailWord_1107786
  simp only [CollatzResearch.WordTrace]
  refine ⟨10101068691171997907835803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26936183176458661087562141 10101068691171997907835803)
  ·
    refine ⟨15151603036757996861753705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10101068691171997907835803 15151603036757996861753705)
    ·
      refine ⟨11363702277568497646315279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15151603036757996861753705 11363702277568497646315279)
      ·
        refine ⟨17045553416352746469472919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11363702277568497646315279 17045553416352746469472919)
        ·
          refine ⟨25568330124529119704209379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17045553416352746469472919 25568330124529119704209379)
          ·
            refine ⟨38352495186793679556314069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25568330124529119704209379 38352495186793679556314069)
            ·
              refine ⟨898886605940476864601111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 38352495186793679556314069 898886605940476864601111)
              ·
                refine ⟨1348329908910715296901667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 898886605940476864601111 1348329908910715296901667)
                ·
                  refine ⟨2022494863366072945352501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1348329908910715296901667 2022494863366072945352501)
                  ·
                    refine ⟨189608893440569338626797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2022494863366072945352501 189608893440569338626797)
                    ·
                      rfl

theorem cell23_1107786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 7, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 7, 1, 1, 5].length) (baseStart_1107786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1107786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1107786 prefixEnd_1107786 := by exact prefixLift 1107786
  have htrace : WordTrace (prefixWord ++ tailWord_1107786) baseStart_1107786 baseEnd_1107786 := by
    simpa [prefixWord, tailWord_1107786, baseEnd_1107786] using wordTrace_append hprefix tailTrace_1107786
  have hstable : (prefixWord ++ tailWord_1107786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1107786).length < 2 ^ (prefixWord ++ tailWord_1107786).sum := by decide
  have hdescent : baseEnd_1107786 < baseStart_1107786 := by decide
  rcases family_descends (prefixWord ++ tailWord_1107786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1107809 : List Nat := [1, 2, 3, 1, 1, 1, 3, 1, 5, 2, 3]
def baseStart_1107809 : Nat := 118140960795 + 1107809 * 2 ^ 59
def prefixEnd_1107809 : Nat := 4983230072969 + 3 ^ 40 * 1107809 * 2
def baseEnd_1107809 : Nat := 568838490376761425892785

theorem tailTrace_1107809 : CollatzResearch.WordTrace tailWord_1107809 prefixEnd_1107809 568838490376761425892785 := by
  unfold tailWord_1107809
  simp only [CollatzResearch.WordTrace]
  refine ⟨40405113643604666559430481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26936742429069777706286987 40405113643604666559430481)
  ·
    refine ⟨30303835232703499919572861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40405113643604666559430481 30303835232703499919572861)
    ·
      refine ⟨11363938212263812469839823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30303835232703499919572861 11363938212263812469839823)
      ·
        refine ⟨17045907318395718704759735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11363938212263812469839823 17045907318395718704759735)
        ·
          refine ⟨25568860977593578057139603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17045907318395718704759735 25568860977593578057139603)
          ·
            refine ⟨38353291466390367085709405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25568860977593578057139603 38353291466390367085709405)
            ·
              refine ⟨14382484299896387657141027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38353291466390367085709405 14382484299896387657141027)
              ·
                refine ⟨21573726449844581485711541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14382484299896387657141027 21573726449844581485711541)
                ·
                  refine ⟨2022536854672929514285457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 21573726449844581485711541 2022536854672929514285457)
                  ·
                    refine ⟨1516902641004697135714093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2022536854672929514285457 1516902641004697135714093)
                    ·
                      refine ⟨568838490376761425892785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1516902641004697135714093 568838490376761425892785)
                      ·
                        rfl

theorem cell23_1107809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 1, 5, 2, 3].length) (baseStart_1107809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1107809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1107809 prefixEnd_1107809 := by exact prefixLift 1107809
  have htrace : WordTrace (prefixWord ++ tailWord_1107809) baseStart_1107809 baseEnd_1107809 := by
    simpa [prefixWord, tailWord_1107809, baseEnd_1107809] using wordTrace_append hprefix tailTrace_1107809
  have hstable : (prefixWord ++ tailWord_1107809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1107809).length < 2 ^ (prefixWord ++ tailWord_1107809).sum := by decide
  have hdescent : baseEnd_1107809 < baseStart_1107809 := by decide
  rcases family_descends (prefixWord ++ tailWord_1107809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1107816 : List Nat := [2, 1, 4, 2, 1, 1, 1, 5, 2, 4]
def baseStart_1107816 : Nat := 118140960795 + 1107816 * 2 ^ 59
def prefixEnd_1107816 : Nat := 4983230072969 + 3 ^ 40 * 1107816 * 2
def baseEnd_1107816 : Nat := 189614028247114299501751

theorem tailTrace_1107816 : CollatzResearch.WordTrace tailWord_1107816 prefixEnd_1107816 189614028247114299501751 := by
  unfold tailWord_1107816
  simp only [CollatzResearch.WordTrace]
  refine ⟨20202684477289653377467651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26936912636386204503290201 20202684477289653377467651)
  ·
    refine ⟨30304026715934480066201477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20202684477289653377467651 30304026715934480066201477)
    ·
      refine ⟨5682005009237715012412777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30304026715934480066201477 5682005009237715012412777)
      ·
        refine ⟨4261503756928286259309583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5682005009237715012412777 4261503756928286259309583)
        ·
          refine ⟨6392255635392429388964375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4261503756928286259309583 6392255635392429388964375)
          ·
            refine ⟨9588383453088644083446563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6392255635392429388964375 9588383453088644083446563)
            ·
              refine ⟨14382575179632966125169845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9588383453088644083446563 14382575179632966125169845)
              ·
                refine ⟨1348366423090590574234673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14382575179632966125169845 1348366423090590574234673)
                ·
                  refine ⟨1011274817317942930676005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1348366423090590574234673 1011274817317942930676005)
                  ·
                    refine ⟨189614028247114299501751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1011274817317942930676005 189614028247114299501751)
                    ·
                      rfl

theorem cell23_1107816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 5, 2, 4].length) (baseStart_1107816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1107816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1107816 prefixEnd_1107816 := by exact prefixLift 1107816
  have htrace : WordTrace (prefixWord ++ tailWord_1107816) baseStart_1107816 baseEnd_1107816 := by
    simpa [prefixWord, tailWord_1107816, baseEnd_1107816] using wordTrace_append hprefix tailTrace_1107816
  have hstable : (prefixWord ++ tailWord_1107816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1107816).length < 2 ^ (prefixWord ++ tailWord_1107816).sum := by decide
  have hdescent : baseEnd_1107816 < baseStart_1107816 := by decide
  rcases family_descends (prefixWord ++ tailWord_1107816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1107826 : List Nat := [3, 2, 1, 2, 1, 1, 1, 6, 1, 2, 3]
def baseStart_1107826 : Nat := 118140960795 + 1107826 * 2 ^ 59
def prefixEnd_1107826 : Nat := 4983230072969 + 3 ^ 40 * 1107826 * 2
def baseEnd_1107826 : Nat := 568847219547887859380207

theorem tailTrace_1107826 : CollatzResearch.WordTrace tailWord_1107826 prefixEnd_1107826 568847219547887859380207 := by
  unfold tailWord_1107826
  simp only [CollatzResearch.WordTrace]
  refine ⟨10101433421135769615699833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26937155789695385641866221 10101433421135769615699833)
  ·
    refine ⟨7576075065851827211774875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10101433421135769615699833 7576075065851827211774875)
    ·
      refine ⟨11364112598777740817662313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7576075065851827211774875 11364112598777740817662313)
      ·
        refine ⟨8523084449083305613246735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11364112598777740817662313 8523084449083305613246735)
        ·
          refine ⟨12784626673624958419870103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8523084449083305613246735 12784626673624958419870103)
          ·
            refine ⟨19176940010437437629805155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12784626673624958419870103 19176940010437437629805155)
            ·
              refine ⟨28765410015656156444707733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19176940010437437629805155 28765410015656156444707733)
              ·
                refine ⟨1348378594483882333345675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 28765410015656156444707733 1348378594483882333345675)
                ·
                  refine ⟨2022567891725823500018513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1348378594483882333345675 2022567891725823500018513)
                  ·
                    refine ⟨1516925918794367625013885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2022567891725823500018513 1516925918794367625013885)
                    ·
                      refine ⟨568847219547887859380207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1516925918794367625013885 568847219547887859380207)
                      ·
                        rfl

theorem cell23_1107826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 6, 1, 2, 3].length) (baseStart_1107826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1107826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1107826 prefixEnd_1107826 := by exact prefixLift 1107826
  have htrace : WordTrace (prefixWord ++ tailWord_1107826) baseStart_1107826 baseEnd_1107826 := by
    simpa [prefixWord, tailWord_1107826, baseEnd_1107826] using wordTrace_append hprefix tailTrace_1107826
  have hstable : (prefixWord ++ tailWord_1107826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1107826).length < 2 ^ (prefixWord ++ tailWord_1107826).sum := by decide
  have hdescent : baseEnd_1107826 < baseStart_1107826 := by decide
  rcases family_descends (prefixWord ++ tailWord_1107826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1107832 : List Nat := [2, 1, 2, 1, 1, 1, 1, 2, 4, 2, 6]
def baseStart_1107832 : Nat := 118140960795 + 1107832 * 2 ^ 59
def prefixEnd_1107832 : Nat := 4983230072969 + 3 ^ 40 * 1107832 * 2
def baseEnd_1107832 : Nat := 568850300431814835905179

theorem tailTrace_1107832 : CollatzResearch.WordTrace tailWord_1107832 prefixEnd_1107832 568850300431814835905179 := by
  unfold tailWord_1107832
  simp only [CollatzResearch.WordTrace]
  refine ⟨20202976261260670743758875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26937301681680894325011833 20202976261260670743758875)
  ·
    refine ⟨30304464391891006115638313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20202976261260670743758875 30304464391891006115638313)
    ·
      refine ⟨22728348293918254586728735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30304464391891006115638313 22728348293918254586728735)
      ·
        refine ⟨34092522440877381880093103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22728348293918254586728735 34092522440877381880093103)
        ·
          refine ⟨51138783661316072820139655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34092522440877381880093103 51138783661316072820139655)
          ·
            refine ⟨76708175491974109230209483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51138783661316072820139655 76708175491974109230209483)
            ·
              refine ⟨115062263237961163845314225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76708175491974109230209483 115062263237961163845314225)
              ·
                refine ⟨86296697428470872883985669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 115062263237961163845314225 86296697428470872883985669)
                ·
                  refine ⟨16180630767838288665747313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 86296697428470872883985669 16180630767838288665747313)
                  ·
                    refine ⟨12135473075878716499310485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16180630767838288665747313 12135473075878716499310485)
                    ·
                      refine ⟨568850300431814835905179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 12135473075878716499310485 568850300431814835905179)
                      ·
                        rfl

theorem cell23_1107832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 4, 2, 6].length) (baseStart_1107832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1107832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1107832 prefixEnd_1107832 := by exact prefixLift 1107832
  have htrace : WordTrace (prefixWord ++ tailWord_1107832) baseStart_1107832 baseEnd_1107832 := by
    simpa [prefixWord, tailWord_1107832, baseEnd_1107832] using wordTrace_append hprefix tailTrace_1107832
  have hstable : (prefixWord ++ tailWord_1107832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1107832).length < 2 ^ (prefixWord ++ tailWord_1107832).sum := by decide
  have hdescent : baseEnd_1107832 < baseStart_1107832 := by decide
  rcases family_descends (prefixWord ++ tailWord_1107832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1107840 : List Nat := [2, 1, 1, 2, 1, 2, 6, 3, 1, 2, 2]
def baseStart_1107840 : Nat := 118140960795 + 1107840 * 2 ^ 59
def prefixEnd_1107840 : Nat := 4983230072969 + 3 ^ 40 * 1107840 * 2
def baseEnd_1107840 : Nat := 568854408277050804605143

theorem tailTrace_1107840 : CollatzResearch.WordTrace tailWord_1107840 prefixEnd_1107840 568854408277050804605143 := by
  unfold tailWord_1107840
  simp only [CollatzResearch.WordTrace]
  refine ⟨20203122153246179426904487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26937496204328239235872649 20203122153246179426904487)
  ·
    refine ⟨30304683229869269140356731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20203122153246179426904487 30304683229869269140356731)
    ·
      refine ⟨45457024844803903710535097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30304683229869269140356731 45457024844803903710535097)
      ·
        refine ⟨34092768633602927782901323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45457024844803903710535097 34092768633602927782901323)
        ·
          refine ⟨51139152950404391674351985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34092768633602927782901323 51139152950404391674351985)
          ·
            refine ⟨38354364712803293755763989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51139152950404391674351985 38354364712803293755763989)
            ·
              refine ⟨1797860845912654394801437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 38354364712803293755763989 1797860845912654394801437)
              ·
                refine ⟨674197817217245398050539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1797860845912654394801437 674197817217245398050539)
                ·
                  refine ⟨1011296725825868097075809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 674197817217245398050539 1011296725825868097075809)
                  ·
                    refine ⟨758472544369401072806857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1011296725825868097075809 758472544369401072806857)
                    ·
                      refine ⟨568854408277050804605143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 758472544369401072806857 568854408277050804605143)
                      ·
                        rfl

theorem cell23_1107840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 6, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 6, 3, 1, 2, 2].length) (baseStart_1107840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1107840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1107840 prefixEnd_1107840 := by exact prefixLift 1107840
  have htrace : WordTrace (prefixWord ++ tailWord_1107840) baseStart_1107840 baseEnd_1107840 := by
    simpa [prefixWord, tailWord_1107840, baseEnd_1107840] using wordTrace_append hprefix tailTrace_1107840
  have hstable : (prefixWord ++ tailWord_1107840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1107840).length < 2 ^ (prefixWord ++ tailWord_1107840).sum := by decide
  have hdescent : baseEnd_1107840 < baseStart_1107840 := by decide
  rcases family_descends (prefixWord ++ tailWord_1107840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1107843 : List Nat := [1, 1, 1, 3, 4, 2, 4, 1, 1, 2, 3]
def baseStart_1107843 : Nat := 118140960795 + 1107843 * 2 ^ 59
def prefixEnd_1107843 : Nat := 4983230072969 + 3 ^ 40 * 1107843 * 2
def baseEnd_1107843 : Nat := 568855948719014292867629

theorem tailTrace_1107843 : CollatzResearch.WordTrace tailWord_1107843 prefixEnd_1107843 568855948719014292867629 := by
  unfold tailWord_1107843
  simp only [CollatzResearch.WordTrace]
  refine ⟨40406353725481490366168183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26937569150320993577445455 40406353725481490366168183)
  ·
    refine ⟨60609530588222235549252275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40406353725481490366168183 60609530588222235549252275)
    ·
      refine ⟨90914295882333353323878413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60609530588222235549252275 90914295882333353323878413)
      ·
        refine ⟨34092860955875007496454405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 90914295882333353323878413 34092860955875007496454405)
        ·
          refine ⟨6392411429226563905585201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34092860955875007496454405 6392411429226563905585201)
          ·
            refine ⟨4794308571919922929188901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6392411429226563905585201 4794308571919922929188901)
            ·
              refine ⟨898932857234985549222919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4794308571919922929188901 898932857234985549222919)
              ·
                refine ⟨1348399285852478323834379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 898932857234985549222919 1348399285852478323834379)
                ·
                  refine ⟨2022598928778717485751569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1348399285852478323834379 2022598928778717485751569)
                  ·
                    refine ⟨1516949196584038114313677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2022598928778717485751569 1516949196584038114313677)
                    ·
                      refine ⟨568855948719014292867629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1516949196584038114313677 568855948719014292867629)
                      ·
                        rfl

theorem cell23_1107843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 4, 1, 1, 2, 3].length) (baseStart_1107843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1107843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1107843 prefixEnd_1107843 := by exact prefixLift 1107843
  have htrace : WordTrace (prefixWord ++ tailWord_1107843) baseStart_1107843 baseEnd_1107843 := by
    simpa [prefixWord, tailWord_1107843, baseEnd_1107843] using wordTrace_append hprefix tailTrace_1107843
  have hstable : (prefixWord ++ tailWord_1107843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1107843).length < 2 ^ (prefixWord ++ tailWord_1107843).sum := by decide
  have hdescent : baseEnd_1107843 < baseStart_1107843 := by decide
  rcases family_descends (prefixWord ++ tailWord_1107843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1107850 : List Nat := [3, 1, 2, 4, 2, 2, 1, 2, 2, 4]
def baseStart_1107850 : Nat := 118140960795 + 1107850 * 2 ^ 59
def prefixEnd_1107850 : Nat := 4983230072969 + 3 ^ 40 * 1107850 * 2
def baseEnd_1107850 : Nat := 189619847694531921826699

theorem tailTrace_1107850 : CollatzResearch.WordTrace tailWord_1107850 prefixEnd_1107850 189619847694531921826699 := by
  unfold tailWord_1107850
  simp only [CollatzResearch.WordTrace]
  refine ⟨10101652259114032640418251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26937739357637420374448669 10101652259114032640418251)
  ·
    refine ⟨15152478388671048960627377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10101652259114032640418251 15152478388671048960627377)
    ·
      refine ⟨11364358791503286720470533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15152478388671048960627377 11364358791503286720470533)
      ·
        refine ⟨2130817273406866260088225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11364358791503286720470533 2130817273406866260088225)
        ·
          refine ⟨1598112955055149695066169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2130817273406866260088225 1598112955055149695066169)
          ·
            refine ⟨1198584716291362271299627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1598112955055149695066169 1198584716291362271299627)
            ·
              refine ⟨1797877074437043406949441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1198584716291362271299627 1797877074437043406949441)
              ·
                refine ⟨1348407805827782555212081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1797877074437043406949441 1348407805827782555212081)
                ·
                  refine ⟨1011305854370836916409061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1348407805827782555212081 1011305854370836916409061)
                  ·
                    refine ⟨189619847694531921826699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1011305854370836916409061 189619847694531921826699)
                    ·
                      rfl

theorem cell23_1107850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 2, 1, 2, 2, 4].length) (baseStart_1107850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1107850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1107850 prefixEnd_1107850 := by exact prefixLift 1107850
  have htrace : WordTrace (prefixWord ++ tailWord_1107850) baseStart_1107850 baseEnd_1107850 := by
    simpa [prefixWord, tailWord_1107850, baseEnd_1107850] using wordTrace_append hprefix tailTrace_1107850
  have hstable : (prefixWord ++ tailWord_1107850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1107850).length < 2 ^ (prefixWord ++ tailWord_1107850).sum := by decide
  have hdescent : baseEnd_1107850 < baseStart_1107850 := by decide
  rcases family_descends (prefixWord ++ tailWord_1107850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1107880 : List Nat := [2, 1, 6, 2, 1, 2, 2, 7]
def baseStart_1107880 : Nat := 118140960795 + 1107880 * 2 ^ 59
def prefixEnd_1107880 : Nat := 4983230072969 + 3 ^ 40 * 1107880 * 2
def baseEnd_1107880 : Nat := 21069442500119653633517

theorem tailTrace_1107880 : CollatzResearch.WordTrace tailWord_1107880 prefixEnd_1107880 21069442500119653633517 := by
  unfold tailWord_1107880
  simp only [CollatzResearch.WordTrace]
  refine ⟨20203851613173722842632547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26938468817564963790176729 20203851613173722842632547)
  ·
    refine ⟨30305777419760584263948821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20203851613173722842632547 30305777419760584263948821)
    ·
      refine ⟨1420583316551277387372601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 30305777419760584263948821 1420583316551277387372601)
      ·
        refine ⟨1065437487413458040529451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1420583316551277387372601 1065437487413458040529451)
        ·
          refine ⟨1598156231120187060794177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1065437487413458040529451 1598156231120187060794177)
          ·
            refine ⟨1198617173340140295595633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1598156231120187060794177 1198617173340140295595633)
            ·
              refine ⟨898962880005105221696725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1198617173340140295595633 898962880005105221696725)
              ·
                refine ⟨21069442500119653633517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 898962880005105221696725 21069442500119653633517)
                ·
                  rfl

theorem cell23_1107880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 2, 2, 7].length) (baseStart_1107880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1107880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1107880 prefixEnd_1107880 := by exact prefixLift 1107880
  have htrace : WordTrace (prefixWord ++ tailWord_1107880) baseStart_1107880 baseEnd_1107880 := by
    simpa [prefixWord, tailWord_1107880, baseEnd_1107880] using wordTrace_append hprefix tailTrace_1107880
  have hstable : (prefixWord ++ tailWord_1107880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1107880).length < 2 ^ (prefixWord ++ tailWord_1107880).sum := by decide
  have hdescent : baseEnd_1107880 < baseStart_1107880 := by decide
  rcases family_descends (prefixWord ++ tailWord_1107880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1107896 : List Nat := [2, 1, 2, 1, 2, 3, 2, 1, 3, 4, 2]
def baseStart_1107896 : Nat := 118140960795 + 1107896 * 2 ^ 59
def prefixEnd_1107896 : Nat := 4983230072969 + 3 ^ 40 * 1107896 * 2
def baseEnd_1107896 : Nat := 568883163193702585504885

theorem tailTrace_1107896 : CollatzResearch.WordTrace tailWord_1107896 prefixEnd_1107896 568883163193702585504885 := by
  unfold tailWord_1107896
  simp only [CollatzResearch.WordTrace]
  refine ⟨20204143397144740208923771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26938857862859653611898361 20204143397144740208923771)
  ·
    refine ⟨30306215095717110313385657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20204143397144740208923771 30306215095717110313385657)
    ·
      refine ⟨22729661321787832735039243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30306215095717110313385657 22729661321787832735039243)
      ·
        refine ⟨34094491982681749102558865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22729661321787832735039243 34094491982681749102558865)
        ·
          refine ⟨25570868987011311826919149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34094491982681749102558865 25570868987011311826919149)
          ·
            refine ⟨9589075870129241935094681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25570868987011311826919149 9589075870129241935094681)
            ·
              refine ⟨7191806902596931451321011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9589075870129241935094681 7191806902596931451321011)
              ·
                refine ⟨10787710353895397176981517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7191806902596931451321011 10787710353895397176981517)
                ·
                  refine ⟨4045391382710773941368069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10787710353895397176981517 4045391382710773941368069)
                  ·
                    refine ⟨758510884258270114006513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4045391382710773941368069 758510884258270114006513)
                    ·
                      refine ⟨568883163193702585504885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 758510884258270114006513 568883163193702585504885)
                      ·
                        rfl

theorem cell23_1107896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 1, 3, 4, 2].length) (baseStart_1107896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1107896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1107896 prefixEnd_1107896 := by exact prefixLift 1107896
  have htrace : WordTrace (prefixWord ++ tailWord_1107896) baseStart_1107896 baseEnd_1107896 := by
    simpa [prefixWord, tailWord_1107896, baseEnd_1107896] using wordTrace_append hprefix tailTrace_1107896
  have hstable : (prefixWord ++ tailWord_1107896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1107896).length < 2 ^ (prefixWord ++ tailWord_1107896).sum := by decide
  have hdescent : baseEnd_1107896 < baseStart_1107896 := by decide
  rcases family_descends (prefixWord ++ tailWord_1107896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1107909 : List Nat := [1, 3, 1, 1, 1, 1, 1, 6, 2, 2, 4]
def baseStart_1107909 : Nat := 118140960795 + 1107909 * 2 ^ 59
def prefixEnd_1107909 : Nat := 4983230072969 + 3 ^ 40 * 1107909 * 2
def baseEnd_1107909 : Nat := 568889838442211034642325

theorem tailTrace_1107909 : CollatzResearch.WordTrace tailWord_1107909 prefixEnd_1107909 568889838442211034642325 := by
  unfold tailWord_1107909
  simp only [CollatzResearch.WordTrace]
  refine ⟨40408760943242383638070781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26939173962161589092047187 40408760943242383638070781)
  ·
    refine ⟨15153285353715893864276543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40408760943242383638070781 15153285353715893864276543)
    ·
      refine ⟨22729928030573840796414815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15153285353715893864276543 22729928030573840796414815)
      ·
        refine ⟨34094892045860761194622223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22729928030573840796414815 34094892045860761194622223)
        ·
          refine ⟨51142338068791141791933335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34094892045860761194622223 51142338068791141791933335)
          ·
            refine ⟨76713507103186712687900003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51142338068791141791933335 76713507103186712687900003)
            ·
              refine ⟨115070260654780069031850005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76713507103186712687900003 115070260654780069031850005)
              ·
                refine ⟨5393918468192815735867969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 115070260654780069031850005 5393918468192815735867969)
                ·
                  refine ⟨4045438851144611801900977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5393918468192815735867969 4045438851144611801900977)
                  ·
                    refine ⟨3034079138358458851425733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4045438851144611801900977 3034079138358458851425733)
                    ·
                      refine ⟨568889838442211034642325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3034079138358458851425733 568889838442211034642325)
                      ·
                        rfl

theorem cell23_1107909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 6, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 6, 2, 2, 4].length) (baseStart_1107909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1107909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1107909 prefixEnd_1107909 := by exact prefixLift 1107909
  have htrace : WordTrace (prefixWord ++ tailWord_1107909) baseStart_1107909 baseEnd_1107909 := by
    simpa [prefixWord, tailWord_1107909, baseEnd_1107909] using wordTrace_append hprefix tailTrace_1107909
  have hstable : (prefixWord ++ tailWord_1107909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1107909).length < 2 ^ (prefixWord ++ tailWord_1107909).sum := by decide
  have hdescent : baseEnd_1107909 < baseStart_1107909 := by decide
  rcases family_descends (prefixWord ++ tailWord_1107909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1108080 : List Nat := [2, 1, 1, 1, 5, 3, 1, 2, 2, 3, 2]
def baseStart_1108080 : Nat := 118140960795 + 1108080 * 2 ^ 59
def prefixEnd_1108080 : Nat := 4983230072969 + 3 ^ 40 * 1108080 * 2
def baseEnd_1108080 : Nat := 568977643634129865604039

theorem tailTrace_1108080 : CollatzResearch.WordTrace tailWord_1108080 prefixEnd_1108080 568977643634129865604039 := by
  unfold tailWord_1108080
  simp only [CollatzResearch.WordTrace]
  refine ⟨20207498912811439921272847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26943331883748586561697129 20207498912811439921272847)
  ·
    refine ⟨30311248369217159881909271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20207498912811439921272847 30311248369217159881909271)
    ·
      refine ⟨45466872553825739822863907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30311248369217159881909271 45466872553825739822863907)
      ·
        refine ⟨68200308830738609734295861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45466872553825739822863907 68200308830738609734295861)
        ·
          refine ⟨6393778952881744662590237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 68200308830738609734295861 6393778952881744662590237)
          ·
            refine ⟨2397667107330654248471339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6393778952881744662590237 2397667107330654248471339)
            ·
              refine ⟨3596500660995981372707009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2397667107330654248471339 3596500660995981372707009)
              ·
                refine ⟨2697375495746986029530257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3596500660995981372707009 2697375495746986029530257)
                ·
                  refine ⟨2023031621810239522147693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2697375495746986029530257 2023031621810239522147693)
                  ·
                    refine ⟨758636858178839820805385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2023031621810239522147693 758636858178839820805385)
                    ·
                      refine ⟨568977643634129865604039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 758636858178839820805385 568977643634129865604039)
                      ·
                        rfl

theorem cell23_1108080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 1, 2, 2, 3, 2].length) (baseStart_1108080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1108080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1108080 prefixEnd_1108080 := by exact prefixLift 1108080
  have htrace : WordTrace (prefixWord ++ tailWord_1108080) baseStart_1108080 baseEnd_1108080 := by
    simpa [prefixWord, tailWord_1108080, baseEnd_1108080] using wordTrace_append hprefix tailTrace_1108080
  have hstable : (prefixWord ++ tailWord_1108080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1108080).length < 2 ^ (prefixWord ++ tailWord_1108080).sum := by decide
  have hdescent : baseEnd_1108080 < baseStart_1108080 := by decide
  rcases family_descends (prefixWord ++ tailWord_1108080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1108096 : List Nat := [2, 1, 1, 2, 1, 3, 1, 1, 2, 6, 3]
def baseStart_1108096 : Nat := 118140960795 + 1108096 * 2 ^ 59
def prefixEnd_1108096 : Nat := 4983230072969 + 3 ^ 40 * 1108096 * 2
def baseEnd_1108096 : Nat := 568985859324601803003965

theorem tailTrace_1108096 : CollatzResearch.WordTrace tailWord_1108096 prefixEnd_1108096 568985859324601803003965 := by
  unfold tailWord_1108096
  simp only [CollatzResearch.WordTrace]
  refine ⟨20207790696782457287564071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26943720929043276383418761 20207790696782457287564071)
  ·
    refine ⟨30311686045173685931346107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20207790696782457287564071 30311686045173685931346107)
    ·
      refine ⟨45467529067760528897019161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30311686045173685931346107 45467529067760528897019161)
      ·
        refine ⟨34100646800820396672764371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45467529067760528897019161 34100646800820396672764371)
        ·
          refine ⟨51150970201230595009146557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34100646800820396672764371 51150970201230595009146557)
          ·
            refine ⟨19181613825461473128429959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51150970201230595009146557 19181613825461473128429959)
            ·
              refine ⟨28772420738192209692644939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19181613825461473128429959 28772420738192209692644939)
              ·
                refine ⟨43158631107288314538967409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28772420738192209692644939 43158631107288314538967409)
                ·
                  refine ⟨32368973330466235904225557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43158631107288314538967409 32368973330466235904225557)
                  ·
                    refine ⟨1517295624865604808010573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 32368973330466235904225557 1517295624865604808010573)
                    ·
                      refine ⟨568985859324601803003965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1517295624865604808010573 568985859324601803003965)
                      ·
                        rfl

theorem cell23_1108096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 1, 2, 6, 3].length) (baseStart_1108096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1108096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1108096 prefixEnd_1108096 := by exact prefixLift 1108096
  have htrace : WordTrace (prefixWord ++ tailWord_1108096) baseStart_1108096 baseEnd_1108096 := by
    simpa [prefixWord, tailWord_1108096, baseEnd_1108096] using wordTrace_append hprefix tailTrace_1108096
  have hstable : (prefixWord ++ tailWord_1108096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1108096).length < 2 ^ (prefixWord ++ tailWord_1108096).sum := by decide
  have hdescent : baseEnd_1108096 < baseStart_1108096 := by decide
  rcases family_descends (prefixWord ++ tailWord_1108096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1108110 : List Nat := [4, 1, 1, 3, 3, 1, 1, 1, 3, 1, 4]
def baseStart_1108110 : Nat := 118140960795 + 1108110 * 2 ^ 59
def prefixEnd_1108110 : Nat := 4983230072969 + 3 ^ 40 * 1108110 * 2
def baseEnd_1108110 : Nat := 568993048053764748228901

theorem tailTrace_1108110 : CollatzResearch.WordTrace tailWord_1108110 prefixEnd_1108110 568993048053764748228901 := by
  unfold tailWord_1108110
  simp only [CollatzResearch.WordTrace]
  refine ⟨5052011501939274370767223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26944061343676129977425189 5052011501939274370767223)
  ·
    refine ⟨7578017252908911556150835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5052011501939274370767223 7578017252908911556150835)
    ·
      refine ⟨11367025879363367334226253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7578017252908911556150835 11367025879363367334226253)
      ·
        refine ⟨4262634704761262750334845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11367025879363367334226253 4262634704761262750334845)
        ·
          refine ⟨1598488014285473531375567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4262634704761262750334845 1598488014285473531375567)
          ·
            refine ⟨2397732021428210297063351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1598488014285473531375567 2397732021428210297063351)
            ·
              refine ⟨3596598032142315445595027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2397732021428210297063351 3596598032142315445595027)
              ·
                refine ⟨5394897048213473168392541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3596598032142315445595027 5394897048213473168392541)
                ·
                  refine ⟨2023086393080052438147203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5394897048213473168392541 2023086393080052438147203)
                  ·
                    refine ⟨3034629589620078657220805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2023086393080052438147203 3034629589620078657220805)
                    ·
                      refine ⟨568993048053764748228901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3034629589620078657220805 568993048053764748228901)
                      ·
                        rfl

theorem cell23_1108110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 1, 1, 3, 1, 4].length) (baseStart_1108110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1108110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1108110 prefixEnd_1108110 := by exact prefixLift 1108110
  have htrace : WordTrace (prefixWord ++ tailWord_1108110) baseStart_1108110 baseEnd_1108110 := by
    simpa [prefixWord, tailWord_1108110, baseEnd_1108110] using wordTrace_append hprefix tailTrace_1108110
  have hstable : (prefixWord ++ tailWord_1108110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1108110).length < 2 ^ (prefixWord ++ tailWord_1108110).sum := by decide
  have hdescent : baseEnd_1108110 < baseStart_1108110 := by decide
  rcases family_descends (prefixWord ++ tailWord_1108110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1108127 : List Nat := [1, 1, 2, 6, 1, 2, 3, 1, 1, 1, 4]
def baseStart_1108127 : Nat := 118140960795 + 1108127 * 2 ^ 59
def prefixEnd_1108127 : Nat := 4983230072969 + 3 ^ 40 * 1108127 * 2
def baseEnd_1108127 : Nat := 569001777224891181716323

theorem tailTrace_1108127 : CollatzResearch.WordTrace tailWord_1108127 prefixEnd_1108127 569001777224891181716323 := by
  unfold tailWord_1108127
  simp only [CollatzResearch.WordTrace]
  refine ⟨40416712056452606869506635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26944474704301737913004423 40416712056452606869506635)
  ·
    refine ⟨60625068084678910304259953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40416712056452606869506635 60625068084678910304259953)
    ·
      refine ⟨45468801063509182728194965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60625068084678910304259953 45468801063509182728194965)
      ·
        refine ⟨2131350049851992940384139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 45468801063509182728194965 2131350049851992940384139)
        ·
          refine ⟨3197025074777989410576209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2131350049851992940384139 3197025074777989410576209)
          ·
            refine ⟨2397768806083492057932157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3197025074777989410576209 2397768806083492057932157)
            ·
              refine ⟨899163302281309521724559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2397768806083492057932157 899163302281309521724559)
              ·
                refine ⟨1348744953421964282586839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 899163302281309521724559 1348744953421964282586839)
                ·
                  refine ⟨2023117430132946423880259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1348744953421964282586839 2023117430132946423880259)
                  ·
                    refine ⟨3034676145199419635820389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2023117430132946423880259 3034676145199419635820389)
                    ·
                      refine ⟨569001777224891181716323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3034676145199419635820389 569001777224891181716323)
                      ·
                        rfl

theorem cell23_1108127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 3, 1, 1, 1, 4].length) (baseStart_1108127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1108127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1108127 prefixEnd_1108127 := by exact prefixLift 1108127
  have htrace : WordTrace (prefixWord ++ tailWord_1108127) baseStart_1108127 baseEnd_1108127 := by
    simpa [prefixWord, tailWord_1108127, baseEnd_1108127] using wordTrace_append hprefix tailTrace_1108127
  have hstable : (prefixWord ++ tailWord_1108127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1108127).length < 2 ^ (prefixWord ++ tailWord_1108127).sum := by decide
  have hdescent : baseEnd_1108127 < baseStart_1108127 := by decide
  rcases family_descends (prefixWord ++ tailWord_1108127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1108130 : List Nat := [3, 3, 1, 3, 1, 1, 3, 1, 1, 1, 5]
def baseStart_1108130 : Nat := 118140960795 + 1108130 * 2 ^ 59
def prefixEnd_1108130 : Nat := 4983230072969 + 3 ^ 40 * 1108130 * 2
def baseEnd_1108130 : Nat := 569003317666854669978809

theorem tailTrace_1108130 : CollatzResearch.WordTrace tailWord_1108130 prefixEnd_1108130 569003317666854669978809 := by
  unfold tailWord_1108130
  simp only [CollatzResearch.WordTrace]
  refine ⟨10104205368860434595466461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26944547650294492254577229 10104205368860434595466461)
  ·
    refine ⟨3789077013322662973299923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10104205368860434595466461 3789077013322662973299923)
    ·
      refine ⟨5683615519983994459949885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3789077013322662973299923 5683615519983994459949885)
      ·
        refine ⟨2131355819993997922481207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5683615519983994459949885 2131355819993997922481207)
        ·
          refine ⟨3197033729990996883721811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2131355819993997922481207 3197033729990996883721811)
          ·
            refine ⟨4795550594986495325582717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3197033729990996883721811 4795550594986495325582717)
            ·
              refine ⟨1798331473119935747093519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4795550594986495325582717 1798331473119935747093519)
              ·
                refine ⟨2697497209679903620640279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1798331473119935747093519 2697497209679903620640279)
                ·
                  refine ⟨4046245814519855430960419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2697497209679903620640279 4046245814519855430960419)
                  ·
                    refine ⟨6069368721779783146440629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4046245814519855430960419 6069368721779783146440629)
                    ·
                      refine ⟨569003317666854669978809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6069368721779783146440629 569003317666854669978809)
                      ·
                        rfl

theorem cell23_1108130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 3, 1, 1, 1, 5].length) (baseStart_1108130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1108130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1108130 prefixEnd_1108130 := by exact prefixLift 1108130
  have htrace : WordTrace (prefixWord ++ tailWord_1108130) baseStart_1108130 baseEnd_1108130 := by
    simpa [prefixWord, tailWord_1108130, baseEnd_1108130] using wordTrace_append hprefix tailTrace_1108130
  have hstable : (prefixWord ++ tailWord_1108130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1108130).length < 2 ^ (prefixWord ++ tailWord_1108130).sum := by decide
  have hdescent : baseEnd_1108130 < baseStart_1108130 := by decide
  rcases family_descends (prefixWord ++ tailWord_1108130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1108138 : List Nat := [3, 1, 5, 1, 2, 2, 2, 2, 1, 1, 3]
def baseStart_1108138 : Nat := 118140960795 + 1108138 * 2 ^ 59
def prefixEnd_1108138 : Nat := 4983230072969 + 3 ^ 40 * 1108138 * 2
def baseEnd_1108138 : Nat := 569007425512090638678773

theorem tailTrace_1108138 : CollatzResearch.WordTrace tailWord_1108138 prefixEnd_1108138 569007425512090638678773 := by
  unfold tailWord_1108138
  simp only [CollatzResearch.WordTrace]
  refine ⟨10104278314853188937039267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26944742172941837165438045 10104278314853188937039267)
  ·
    refine ⟨15156417472279783405558901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10104278314853188937039267 15156417472279783405558901)
    ·
      refine ⟨1420914138026229694271147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 15156417472279783405558901 1420914138026229694271147)
      ·
        refine ⟨2131371207039344541406721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1420914138026229694271147 2131371207039344541406721)
        ·
          refine ⟨1598528405279508406055041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2131371207039344541406721 1598528405279508406055041)
          ·
            refine ⟨1198896303959631304541281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1598528405279508406055041 1198896303959631304541281)
            ·
              refine ⟨899172227969723478405961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1198896303959631304541281 899172227969723478405961)
              ·
                refine ⟨674379170977292608804471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 899172227969723478405961 674379170977292608804471)
                ·
                  refine ⟨1011568756465938913206707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 674379170977292608804471 1011568756465938913206707)
                  ·
                    refine ⟨1517353134698908369810061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1011568756465938913206707 1517353134698908369810061)
                    ·
                      refine ⟨569007425512090638678773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1517353134698908369810061 569007425512090638678773)
                      ·
                        rfl

theorem cell23_1108138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 2, 2, 2, 1, 1, 3].length) (baseStart_1108138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1108138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1108138 prefixEnd_1108138 := by exact prefixLift 1108138
  have htrace : WordTrace (prefixWord ++ tailWord_1108138) baseStart_1108138 baseEnd_1108138 := by
    simpa [prefixWord, tailWord_1108138, baseEnd_1108138] using wordTrace_append hprefix tailTrace_1108138
  have hstable : (prefixWord ++ tailWord_1108138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1108138).length < 2 ^ (prefixWord ++ tailWord_1108138).sum := by decide
  have hdescent : baseEnd_1108138 < baseStart_1108138 := by decide
  rcases family_descends (prefixWord ++ tailWord_1108138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1108146 : List Nat := [3, 2, 1, 1, 1, 3, 1, 1, 1, 9]
def baseStart_1108146 : Nat := 118140960795 + 1108146 * 2 ^ 59
def prefixEnd_1108146 : Nat := 4983230072969 + 3 ^ 40 * 1108146 * 2
def baseEnd_1108146 : Nat := 189670511119108869126245

theorem tailTrace_1108146 : CollatzResearch.WordTrace tailWord_1108146 prefixEnd_1108146 189670511119108869126245 := by
  unfold tailWord_1108146
  simp only [CollatzResearch.WordTrace]
  refine ⟨10104351260845943278612073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26944936695589182076298861 10104351260845943278612073)
  ·
    refine ⟨7578263445634457458959055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10104351260845943278612073 7578263445634457458959055)
    ·
      refine ⟨11367395168451686188438583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7578263445634457458959055 11367395168451686188438583)
      ·
        refine ⟨17051092752677529282657875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11367395168451686188438583 17051092752677529282657875)
        ·
          refine ⟨25576639129016293923986813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17051092752677529282657875 25576639129016293923986813)
          ·
            refine ⟨9591239673381110221495055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25576639129016293923986813 9591239673381110221495055)
            ·
              refine ⟨14386859510071665332242583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9591239673381110221495055 14386859510071665332242583)
              ·
                refine ⟨21580289265107497998363875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14386859510071665332242583 21580289265107497998363875)
                ·
                  refine ⟨32370433897661246997545813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21580289265107497998363875 32370433897661246997545813)
                  ·
                    refine ⟨189670511119108869126245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 32370433897661246997545813 189670511119108869126245)
                    ·
                      rfl

theorem cell23_1108146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 1, 1, 9].length) (baseStart_1108146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1108146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1108146 prefixEnd_1108146 := by exact prefixLift 1108146
  have htrace : WordTrace (prefixWord ++ tailWord_1108146) baseStart_1108146 baseEnd_1108146 := by
    simpa [prefixWord, tailWord_1108146, baseEnd_1108146] using wordTrace_append hprefix tailTrace_1108146
  have hstable : (prefixWord ++ tailWord_1108146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1108146).length < 2 ^ (prefixWord ++ tailWord_1108146).sum := by decide
  have hdescent : baseEnd_1108146 < baseStart_1108146 := by decide
  rcases family_descends (prefixWord ++ tailWord_1108146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1108160 : List Nat := [2, 1, 1, 2, 5, 2, 2, 1, 1, 3, 3]
def baseStart_1108160 : Nat := 118140960795 + 1108160 * 2 ^ 59
def prefixEnd_1108160 : Nat := 4983230072969 + 3 ^ 40 * 1108160 * 2
def baseEnd_1108160 : Nat := 569018722086489552603671

theorem tailTrace_1108160 : CollatzResearch.WordTrace tailWord_1108160 prefixEnd_1108160 569018722086489552603671 := by
  unfold tailWord_1108160
  simp only [CollatzResearch.WordTrace]
  refine ⟨20208957832666526752728967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26945277110222035670305289 20208957832666526752728967)
  ·
    refine ⟨30313436748999790129093451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20208957832666526752728967 30313436748999790129093451)
    ·
      refine ⟨45470155123499685193640177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30313436748999790129093451 45470155123499685193640177)
      ·
        refine ⟨34102616342624763895230133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45470155123499685193640177 34102616342624763895230133)
        ·
          refine ⟨3197120282121071615177825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 34102616342624763895230133 3197120282121071615177825)
          ·
            refine ⟨2397840211590803711383369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3197120282121071615177825 2397840211590803711383369)
            ·
              refine ⟨1798380158693102783537527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2397840211590803711383369 1798380158693102783537527)
              ·
                refine ⟨2697570238039654175306291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1798380158693102783537527 2697570238039654175306291)
                ·
                  refine ⟨4046355357059481262959437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2697570238039654175306291 4046355357059481262959437)
                  ·
                    refine ⟨1517383258897305473609789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4046355357059481262959437 1517383258897305473609789)
                    ·
                      refine ⟨569018722086489552603671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1517383258897305473609789 569018722086489552603671)
                      ·
                        rfl

theorem cell23_1108160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 2, 1, 1, 3, 3].length) (baseStart_1108160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1108160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1108160 prefixEnd_1108160 := by exact prefixLift 1108160
  have htrace : WordTrace (prefixWord ++ tailWord_1108160) baseStart_1108160 baseEnd_1108160 := by
    simpa [prefixWord, tailWord_1108160, baseEnd_1108160] using wordTrace_append hprefix tailTrace_1108160
  have hstable : (prefixWord ++ tailWord_1108160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1108160).length < 2 ^ (prefixWord ++ tailWord_1108160).sum := by decide
  have hdescent : baseEnd_1108160 < baseStart_1108160 := by decide
  rcases family_descends (prefixWord ++ tailWord_1108160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1108170 : List Nat := [3, 1, 2, 1, 3, 1, 1, 3, 3, 3, 2]
def baseStart_1108170 : Nat := 118140960795 + 1108170 * 2 ^ 59
def prefixEnd_1108170 : Nat := 4983230072969 + 3 ^ 40 * 1108170 * 2
def baseEnd_1108170 : Nat := 569023856893034513478625

theorem tailTrace_1108170 : CollatzResearch.WordTrace tailWord_1108170 prefixEnd_1108170 569023856893034513478625 := by
  unfold tailWord_1108170
  simp only [CollatzResearch.WordTrace]
  refine ⟨10104570098824206303330491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26945520263531216808881309 10104570098824206303330491)
  ·
    refine ⟨15156855148236309454995737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10104570098824206303330491 15156855148236309454995737)
    ·
      refine ⟨11367641361177232091246803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15156855148236309454995737 11367641361177232091246803)
      ·
        refine ⟨17051462041765848136870205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11367641361177232091246803 17051462041765848136870205)
        ·
          refine ⟨6394298265662193051326327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17051462041765848136870205 6394298265662193051326327)
          ·
            refine ⟨9591447398493289576989491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6394298265662193051326327 9591447398493289576989491)
            ·
              refine ⟨14387171097739934365484237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9591447398493289576989491 14387171097739934365484237)
              ·
                refine ⟨5395189161652475387056589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14387171097739934365484237 5395189161652475387056589)
                ·
                  refine ⟨2023195935619678270146221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5395189161652475387056589 2023195935619678270146221)
                  ·
                    refine ⟨758698475857379351304833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2023195935619678270146221 758698475857379351304833)
                    ·
                      refine ⟨569023856893034513478625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 758698475857379351304833 569023856893034513478625)
                      ·
                        rfl

theorem cell23_1108170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 3, 3, 3, 2].length) (baseStart_1108170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1108170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1108170 prefixEnd_1108170 := by exact prefixLift 1108170
  have htrace : WordTrace (prefixWord ++ tailWord_1108170) baseStart_1108170 baseEnd_1108170 := by
    simpa [prefixWord, tailWord_1108170, baseEnd_1108170] using wordTrace_append hprefix tailTrace_1108170
  have hstable : (prefixWord ++ tailWord_1108170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1108170).length < 2 ^ (prefixWord ++ tailWord_1108170).sum := by decide
  have hdescent : baseEnd_1108170 < baseStart_1108170 := by decide
  rcases family_descends (prefixWord ++ tailWord_1108170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1108181 : List Nat := [1, 3, 2, 4, 3, 1, 2, 1, 1, 2, 3]
def baseStart_1108181 : Nat := 118140960795 + 1108181 * 2 ^ 59
def prefixEnd_1108181 : Nat := 4983230072969 + 3 ^ 40 * 1108181 * 2
def baseEnd_1108181 : Nat := 569029505180233970441075

theorem tailTrace_1108181 : CollatzResearch.WordTrace tailWord_1108181 prefixEnd_1108181 569029505180233970441075 := by
  unfold tailWord_1108181
  simp only [CollatzResearch.WordTrace]
  refine ⟨40418681598256974091972397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26945787732171316061314931 40418681598256974091972397)
  ·
    refine ⟨15157005599346365284489649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40418681598256974091972397 15157005599346365284489649)
    ·
      refine ⟨11367754199509773963367237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15157005599346365284489649 11367754199509773963367237)
      ·
        refine ⟨2131453912408082618131357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11367754199509773963367237 2131453912408082618131357)
        ·
          refine ⟨799295217153030981799259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2131453912408082618131357 799295217153030981799259)
          ·
            refine ⟨1198942825729546472698889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 799295217153030981799259 1198942825729546472698889)
            ·
              refine ⟨899207119297159854524167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1198942825729546472698889 899207119297159854524167)
              ·
                refine ⟨1348810678945739781786251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 899207119297159854524167 1348810678945739781786251)
                ·
                  refine ⟨2023216018418609672679377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1348810678945739781786251 2023216018418609672679377)
                  ·
                    refine ⟨1517412013813957254509533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2023216018418609672679377 1517412013813957254509533)
                    ·
                      refine ⟨569029505180233970441075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1517412013813957254509533 569029505180233970441075)
                      ·
                        rfl

theorem cell23_1108181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 3, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 3, 1, 2, 1, 1, 2, 3].length) (baseStart_1108181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1108181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1108181 prefixEnd_1108181 := by exact prefixLift 1108181
  have htrace : WordTrace (prefixWord ++ tailWord_1108181) baseStart_1108181 baseEnd_1108181 := by
    simpa [prefixWord, tailWord_1108181, baseEnd_1108181] using wordTrace_append hprefix tailTrace_1108181
  have hstable : (prefixWord ++ tailWord_1108181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1108181).length < 2 ^ (prefixWord ++ tailWord_1108181).sum := by decide
  have hdescent : baseEnd_1108181 < baseStart_1108181 := by decide
  rcases family_descends (prefixWord ++ tailWord_1108181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1108216 : List Nat := [2, 1, 2, 1, 1, 2, 1, 2, 1, 1, 9]
def baseStart_1108216 : Nat := 118140960795 + 1108216 * 2 ^ 59
def prefixEnd_1108216 : Nat := 4983230072969 + 3 ^ 40 * 1108216 * 2
def baseEnd_1108216 : Nat := 569047477003141333503413

theorem tailTrace_1108216 : CollatzResearch.WordTrace tailWord_1108216 prefixEnd_1108216 569047477003141333503413 := by
  unfold tailWord_1108216
  simp only [CollatzResearch.WordTrace]
  refine ⟨20209979076565087534748251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26946638768753450046331001 20209979076565087534748251)
  ·
    refine ⟨30314968614847631302122377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20209979076565087534748251 30314968614847631302122377)
    ·
      refine ⟨22736226461135723476591783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30314968614847631302122377 22736226461135723476591783)
      ·
        refine ⟨34104339691703585214887675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22736226461135723476591783 34104339691703585214887675)
        ·
          refine ⟨51156509537555377822331513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34104339691703585214887675 51156509537555377822331513)
          ·
            refine ⟨38367382153166533366748635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51156509537555377822331513 38367382153166533366748635)
            ·
              refine ⟨57551073229749800050122953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38367382153166533366748635 57551073229749800050122953)
              ·
                refine ⟨43163304922312350037592215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 57551073229749800050122953 43163304922312350037592215)
                ·
                  refine ⟨64744957383468525056388323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43163304922312350037592215 64744957383468525056388323)
                  ·
                    refine ⟨97117436075202787584582485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 64744957383468525056388323 97117436075202787584582485)
                    ·
                      refine ⟨569047477003141333503413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 97117436075202787584582485 569047477003141333503413)
                      ·
                        rfl

theorem cell23_1108216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 2, 1, 1, 9].length) (baseStart_1108216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1108216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1108216 prefixEnd_1108216 := by exact prefixLift 1108216
  have htrace : WordTrace (prefixWord ++ tailWord_1108216) baseStart_1108216 baseEnd_1108216 := by
    simpa [prefixWord, tailWord_1108216, baseEnd_1108216] using wordTrace_append hprefix tailTrace_1108216
  have hstable : (prefixWord ++ tailWord_1108216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1108216).length < 2 ^ (prefixWord ++ tailWord_1108216).sum := by decide
  have hdescent : baseEnd_1108216 < baseStart_1108216 := by decide
  rcases family_descends (prefixWord ++ tailWord_1108216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1108318 : List Nat := [4, 4, 2, 1, 1, 1, 1, 1, 2, 3, 3]
def baseStart_1108318 : Nat := 118140960795 + 1108318 * 2 ^ 59
def prefixEnd_1108318 : Nat := 4983230072969 + 3 ^ 40 * 1108318 * 2
def baseEnd_1108318 : Nat := 569099852029899934427945

theorem tailTrace_1108318 : CollatzResearch.WordTrace tailWord_1108318 prefixEnd_1108318 569099852029899934427945 := by
  unfold tailWord_1108318
  simp only [CollatzResearch.WordTrace]
  refine ⟨5052959799845080811213701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26949118932507097659806405 5052959799845080811213701)
  ·
    refine ⟨947429962470952652102569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5052959799845080811213701 947429962470952652102569)
    ·
      refine ⟨710572471853214489076927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 947429962470952652102569 710572471853214489076927)
      ·
        refine ⟨1065858707779821733615391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 710572471853214489076927 1065858707779821733615391)
        ·
          refine ⟨1598788061669732600423087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1065858707779821733615391 1598788061669732600423087)
          ·
            refine ⟨2398182092504598900634631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1598788061669732600423087 2398182092504598900634631)
            ·
              refine ⟨3597273138756898350951947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2398182092504598900634631 3597273138756898350951947)
              ·
                refine ⟨5395909708135347526427921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3597273138756898350951947 5395909708135347526427921)
                ·
                  refine ⟨4046932281101510644820941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5395909708135347526427921 4046932281101510644820941)
                  ·
                    refine ⟨1517599605413066491807853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4046932281101510644820941 1517599605413066491807853)
                    ·
                      refine ⟨569099852029899934427945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1517599605413066491807853 569099852029899934427945)
                      ·
                        rfl

theorem cell23_1108318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 1, 1, 2, 3, 3].length) (baseStart_1108318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1108318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1108318 prefixEnd_1108318 := by exact prefixLift 1108318
  have htrace : WordTrace (prefixWord ++ tailWord_1108318) baseStart_1108318 baseEnd_1108318 := by
    simpa [prefixWord, tailWord_1108318, baseEnd_1108318] using wordTrace_append hprefix tailTrace_1108318
  have hstable : (prefixWord ++ tailWord_1108318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1108318).length < 2 ^ (prefixWord ++ tailWord_1108318).sum := by decide
  have hdescent : baseEnd_1108318 < baseStart_1108318 := by decide
  rcases family_descends (prefixWord ++ tailWord_1108318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1108400 : List Nat := [2, 1, 1, 1, 2, 1, 1, 2, 7, 2, 3]
def baseStart_1108400 : Nat := 118140960795 + 1108400 * 2 ^ 59
def prefixEnd_1108400 : Nat := 4983230072969 + 3 ^ 40 * 1108400 * 2
def baseEnd_1108400 : Nat := 569141957443568613602567

theorem tailTrace_1108400 : CollatzResearch.WordTrace tailWord_1108400 prefixEnd_1108400 569141957443568613602567 := by
  unfold tailWord_1108400
  simp only [CollatzResearch.WordTrace]
  refine ⟨20213334592231787247097327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26951112789642382996129769 20213334592231787247097327)
  ·
    refine ⟨30320001888347680870645991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20213334592231787247097327 30320001888347680870645991)
    ·
      refine ⟨45480002832521521305968987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30320001888347680870645991 45480002832521521305968987)
      ·
        refine ⟨68220004248782281958953481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45480002832521521305968987 68220004248782281958953481)
        ·
          refine ⟨51165003186586711469215111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68220004248782281958953481 51165003186586711469215111)
          ·
            refine ⟨76747504779880067203822667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51165003186586711469215111 76747504779880067203822667)
            ·
              refine ⟨115121257169820100805734001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76747504779880067203822667 115121257169820100805734001)
              ·
                refine ⟨86340942877365075604300501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 115121257169820100805734001 86340942877365075604300501)
                ·
                  refine ⟨2023615848688243959475793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 86340942877365075604300501 2023615848688243959475793)
                  ·
                    refine ⟨1517711886516182969606845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2023615848688243959475793 1517711886516182969606845)
                    ·
                      refine ⟨569141957443568613602567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1517711886516182969606845 569141957443568613602567)
                      ·
                        rfl

theorem cell23_1108400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 7, 2, 3].length) (baseStart_1108400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1108400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1108400 prefixEnd_1108400 := by exact prefixLift 1108400
  have htrace : WordTrace (prefixWord ++ tailWord_1108400) baseStart_1108400 baseEnd_1108400 := by
    simpa [prefixWord, tailWord_1108400, baseEnd_1108400] using wordTrace_append hprefix tailTrace_1108400
  have hstable : (prefixWord ++ tailWord_1108400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1108400).length < 2 ^ (prefixWord ++ tailWord_1108400).sum := by decide
  have hdescent : baseEnd_1108400 < baseStart_1108400 := by decide
  rcases family_descends (prefixWord ++ tailWord_1108400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1108410 : List Nat := [3, 1, 1, 1, 2, 1, 1, 6, 1, 2, 4]
def baseStart_1108410 : Nat := 118140960795 + 1108410 * 2 ^ 59
def prefixEnd_1108410 : Nat := 4983230072969 + 3 ^ 40 * 1108410 * 2
def baseEnd_1108410 : Nat := 569147092250113574477521

theorem tailTrace_1108410 : CollatzResearch.WordTrace tailWord_1108410 prefixEnd_1108410 569147092250113574477521 := by
  unfold tailWord_1108410
  simp only [CollatzResearch.WordTrace]
  refine ⟨10106758478606836550514671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26951355942951564134705789 10106758478606836550514671)
  ·
    refine ⟨15160137717910254825772007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10106758478606836550514671 15160137717910254825772007)
    ·
      refine ⟨22740206576865382238658011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15160137717910254825772007 22740206576865382238658011)
      ·
        refine ⟨34110309865298073357987017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22740206576865382238658011 34110309865298073357987017)
        ·
          refine ⟨25582732398973555018490263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34110309865298073357987017 25582732398973555018490263)
          ·
            refine ⟨38374098598460332527735395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25582732398973555018490263 38374098598460332527735395)
            ·
              refine ⟨57561147897690498791603093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38374098598460332527735395 57561147897690498791603093)
              ·
                refine ⟨2698178807704242130856395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 57561147897690498791603093 2698178807704242130856395)
                ·
                  refine ⟨4047268211556363196284593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2698178807704242130856395 4047268211556363196284593)
                  ·
                    refine ⟨3035451158667272397213445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4047268211556363196284593 3035451158667272397213445)
                    ·
                      refine ⟨569147092250113574477521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3035451158667272397213445 569147092250113574477521)
                      ·
                        rfl

theorem cell23_1108410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 6, 1, 2, 4].length) (baseStart_1108410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1108410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1108410 prefixEnd_1108410 := by exact prefixLift 1108410
  have htrace : WordTrace (prefixWord ++ tailWord_1108410) baseStart_1108410 baseEnd_1108410 := by
    simpa [prefixWord, tailWord_1108410, baseEnd_1108410] using wordTrace_append hprefix tailTrace_1108410
  have hstable : (prefixWord ++ tailWord_1108410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1108410).length < 2 ^ (prefixWord ++ tailWord_1108410).sum := by decide
  have hdescent : baseEnd_1108410 < baseStart_1108410 := by decide
  rcases family_descends (prefixWord ++ tailWord_1108410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1108414 : List Nat := [4, 2, 1, 1, 1, 1, 2, 2, 5, 2, 2]
def baseStart_1108414 : Nat := 118140960795 + 1108414 * 2 ^ 59
def prefixEnd_1108414 : Nat := 4983230072969 + 3 ^ 40 * 1108414 * 2
def baseEnd_1108414 : Nat := 569149146172731558827503

theorem tailTrace_1108414 : CollatzResearch.WordTrace tailWord_1108414 prefixEnd_1108414 569149146172731558827503 := by
  unfold tailWord_1108414
  simp only [CollatzResearch.WordTrace]
  refine ⟨5053397475801606860650537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26951453204275236590136197 5053397475801606860650537)
  ·
    refine ⟨3790048106851205145487903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5053397475801606860650537 3790048106851205145487903)
    ·
      refine ⟨5685072160276807718231855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3790048106851205145487903 5685072160276807718231855)
      ·
        refine ⟨8527608240415211577347783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5685072160276807718231855 8527608240415211577347783)
        ·
          refine ⟨12791412360622817366021675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8527608240415211577347783 12791412360622817366021675)
          ·
            refine ⟨19187118540934226049032513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12791412360622817366021675 19187118540934226049032513)
            ·
              refine ⟨14390338905700669536774385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19187118540934226049032513 14390338905700669536774385)
              ·
                refine ⟨10792754179275502152580789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14390338905700669536774385 10792754179275502152580789)
                ·
                  refine ⟨1011820704307078326804449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 10792754179275502152580789 1011820704307078326804449)
                  ·
                    refine ⟨758865528230308745103337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1011820704307078326804449 758865528230308745103337)
                    ·
                      refine ⟨569149146172731558827503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 758865528230308745103337 569149146172731558827503)
                      ·
                        rfl

theorem cell23_1108414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 2, 5, 2, 2].length) (baseStart_1108414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1108414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1108414 prefixEnd_1108414 := by exact prefixLift 1108414
  have htrace : WordTrace (prefixWord ++ tailWord_1108414) baseStart_1108414 baseEnd_1108414 := by
    simpa [prefixWord, tailWord_1108414, baseEnd_1108414] using wordTrace_append hprefix tailTrace_1108414
  have hstable : (prefixWord ++ tailWord_1108414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1108414).length < 2 ^ (prefixWord ++ tailWord_1108414).sum := by decide
  have hdescent : baseEnd_1108414 < baseStart_1108414 := by decide
  rcases family_descends (prefixWord ++ tailWord_1108414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1108451 : List Nat := [1, 1, 1, 6, 3, 2, 1, 2, 1, 2, 3]
def baseStart_1108451 : Nat := 118140960795 + 1108451 * 2 ^ 59
def prefixEnd_1108451 : Nat := 4983230072969 + 3 ^ 40 * 1108451 * 2
def baseEnd_1108451 : Nat := 569168144956947914064833

theorem tailTrace_1108451 : CollatzResearch.WordTrace tailWord_1108451 prefixEnd_1108451 569168144956947914064833 := by
  unfold tailWord_1108451
  simp only [CollatzResearch.WordTrace]
  refine ⟨40428529307278810204301207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26952352871519206802867471 40428529307278810204301207)
  ·
    refine ⟨60642793960918215306451811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40428529307278810204301207 60642793960918215306451811)
    ·
      refine ⟨90964190941377322959677717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60642793960918215306451811 90964190941377322959677717)
      ·
        refine ⟨4263946450377062013734893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 90964190941377322959677717 4263946450377062013734893)
        ·
          refine ⟨1598979918891398255150585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4263946450377062013734893 1598979918891398255150585)
          ·
            refine ⟨1199234939168548691362939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1598979918891398255150585 1199234939168548691362939)
            ·
              refine ⟨1798852408752823037044409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1199234939168548691362939 1798852408752823037044409)
              ·
                refine ⟨1349139306564617277783307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1798852408752823037044409 1349139306564617277783307)
                ·
                  refine ⟨2023708959846925916674961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1349139306564617277783307 2023708959846925916674961)
                  ·
                    refine ⟨1517781719885194437506221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2023708959846925916674961 1517781719885194437506221)
                    ·
                      refine ⟨569168144956947914064833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1517781719885194437506221 569168144956947914064833)
                      ·
                        rfl

theorem cell23_1108451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 2, 1, 2, 1, 2, 3].length) (baseStart_1108451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1108451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1108451 prefixEnd_1108451 := by exact prefixLift 1108451
  have htrace : WordTrace (prefixWord ++ tailWord_1108451) baseStart_1108451 baseEnd_1108451 := by
    simpa [prefixWord, tailWord_1108451, baseEnd_1108451] using wordTrace_append hprefix tailTrace_1108451
  have hstable : (prefixWord ++ tailWord_1108451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1108451).length < 2 ^ (prefixWord ++ tailWord_1108451).sum := by decide
  have hdescent : baseEnd_1108451 < baseStart_1108451 := by decide
  rcases family_descends (prefixWord ++ tailWord_1108451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1108481 : List Nat := [1, 2, 4, 1, 3, 2, 2, 2, 2, 1, 3]
def baseStart_1108481 : Nat := 118140960795 + 1108481 * 2 ^ 59
def prefixEnd_1108481 : Nat := 4983230072969 + 3 ^ 40 * 1108481 * 2
def baseEnd_1108481 : Nat := 569183549376582796689695

theorem tailTrace_1108481 : CollatzResearch.WordTrace tailWord_1108481 prefixEnd_1108481 569183549376582796689695 := by
  unfold tailWord_1108481
  simp only [CollatzResearch.WordTrace]
  refine ⟨40429623497170125327893297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26953082331446750218595531 40429623497170125327893297)
  ·
    refine ⟨30322217622877593995919973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40429623497170125327893297 30322217622877593995919973)
    ·
      refine ⟨5685415804289548874234995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30322217622877593995919973 5685415804289548874234995)
      ·
        refine ⟨8528123706434323311352493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5685415804289548874234995 8528123706434323311352493)
        ·
          refine ⟨3198046389912871241757185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8528123706434323311352493 3198046389912871241757185)
          ·
            refine ⟨2398534792434653431317889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3198046389912871241757185 2398534792434653431317889)
            ·
              refine ⟨1798901094325990073488417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2398534792434653431317889 1798901094325990073488417)
              ·
                refine ⟨1349175820744492555116313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1798901094325990073488417 1349175820744492555116313)
                ·
                  refine ⟨1011881865558369416337235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1349175820744492555116313 1011881865558369416337235)
                  ·
                    refine ⟨1517822798337554124505853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1011881865558369416337235 1517822798337554124505853)
                    ·
                      refine ⟨569183549376582796689695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1517822798337554124505853 569183549376582796689695)
                      ·
                        rfl

theorem cell23_1108481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 2, 2, 2, 1, 3].length) (baseStart_1108481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1108481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1108481 prefixEnd_1108481 := by exact prefixLift 1108481
  have htrace : WordTrace (prefixWord ++ tailWord_1108481) baseStart_1108481 baseEnd_1108481 := by
    simpa [prefixWord, tailWord_1108481, baseEnd_1108481] using wordTrace_append hprefix tailTrace_1108481
  have hstable : (prefixWord ++ tailWord_1108481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1108481).length < 2 ^ (prefixWord ++ tailWord_1108481).sum := by decide
  have hdescent : baseEnd_1108481 < baseStart_1108481 := by decide
  rcases family_descends (prefixWord ++ tailWord_1108481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1108504 : List Nat := [2, 1, 2, 3, 3, 1, 1, 3, 1, 4, 2]
def baseStart_1108504 : Nat := 118140960795 + 1108504 * 2 ^ 59
def prefixEnd_1108504 : Nat := 4983230072969 + 3 ^ 40 * 1108504 * 2
def baseEnd_1108504 : Nat := 569195359431636206702089

theorem tailTrace_1108504 : CollatzResearch.WordTrace tailWord_1108504 prefixEnd_1108504 569195359431636206702089 := by
  unfold tailWord_1108504
  simp only [CollatzResearch.WordTrace]
  refine ⟨20215231188043400127990283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26953641584057866837320377 20215231188043400127990283)
  ·
    refine ⟨30322846782065100191985425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20215231188043400127990283 30322846782065100191985425)
    ·
      refine ⟨22742135086548825143989069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30322846782065100191985425 22742135086548825143989069)
      ·
        refine ⟨8528300657455809428995901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22742135086548825143989069 8528300657455809428995901)
        ·
          refine ⟨3198112746545928535873463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8528300657455809428995901 3198112746545928535873463)
          ·
            refine ⟨4797169119818892803810195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3198112746545928535873463 4797169119818892803810195)
            ·
              refine ⟨7195753679728339205715293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4797169119818892803810195 7195753679728339205715293)
              ·
                refine ⟨2698407629898127202143235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7195753679728339205715293 2698407629898127202143235)
                ·
                  refine ⟨4047611444847190803214853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2698407629898127202143235 4047611444847190803214853)
                  ·
                    refine ⟨758927145908848275602785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4047611444847190803214853 758927145908848275602785)
                    ·
                      refine ⟨569195359431636206702089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 758927145908848275602785 569195359431636206702089)
                      ·
                        rfl

theorem cell23_1108504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 3, 1, 4, 2].length) (baseStart_1108504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1108504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1108504 prefixEnd_1108504 := by exact prefixLift 1108504
  have htrace : WordTrace (prefixWord ++ tailWord_1108504) baseStart_1108504 baseEnd_1108504 := by
    simpa [prefixWord, tailWord_1108504, baseEnd_1108504] using wordTrace_append hprefix tailTrace_1108504
  have hstable : (prefixWord ++ tailWord_1108504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1108504).length < 2 ^ (prefixWord ++ tailWord_1108504).sum := by decide
  have hdescent : baseEnd_1108504 < baseStart_1108504 := by decide
  rcases family_descends (prefixWord ++ tailWord_1108504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1108532 : List Nat := [2, 5, 1, 3, 2, 1, 1, 2, 2, 1, 3]
def baseStart_1108532 : Nat := 118140960795 + 1108532 * 2 ^ 59
def prefixEnd_1108532 : Nat := 4983230072969 + 3 ^ 40 * 1108532 * 2
def baseEnd_1108532 : Nat := 569209736889962097151961

theorem tailTrace_1108532 : CollatzResearch.WordTrace tailWord_1108532 prefixEnd_1108532 569209736889962097151961 := by
  unfold tailWord_1108532
  simp only [CollatzResearch.WordTrace]
  refine ⟨20215741809992680518999925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26954322413323574025333233 20215741809992680518999925)
  ·
    refine ⟨1895225794686813798656243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 20215741809992680518999925 1895225794686813798656243)
    ·
      refine ⟨2842838692030220697984365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1895225794686813798656243 2842838692030220697984365)
      ·
        refine ⟨1066064509511332761744137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2842838692030220697984365 1066064509511332761744137)
        ·
          refine ⟨799548382133499571308103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1066064509511332761744137 799548382133499571308103)
          ·
            refine ⟨1199322573200249356962155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 799548382133499571308103 1199322573200249356962155)
            ·
              refine ⟨1798983859800374035443233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1199322573200249356962155 1798983859800374035443233)
              ·
                refine ⟨1349237894850280526582425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1798983859800374035443233 1349237894850280526582425)
                ·
                  refine ⟨1011928421137710394936819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1349237894850280526582425 1011928421137710394936819)
                  ·
                    refine ⟨1517892631706565592405229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1011928421137710394936819 1517892631706565592405229)
                    ·
                      refine ⟨569209736889962097151961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1517892631706565592405229 569209736889962097151961)
                      ·
                        rfl

theorem cell23_1108532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 2, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 2, 1, 1, 2, 2, 1, 3].length) (baseStart_1108532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1108532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1108532 prefixEnd_1108532 := by exact prefixLift 1108532
  have htrace : WordTrace (prefixWord ++ tailWord_1108532) baseStart_1108532 baseEnd_1108532 := by
    simpa [prefixWord, tailWord_1108532, baseEnd_1108532] using wordTrace_append hprefix tailTrace_1108532
  have hstable : (prefixWord ++ tailWord_1108532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1108532).length < 2 ^ (prefixWord ++ tailWord_1108532).sum := by decide
  have hdescent : baseEnd_1108532 < baseStart_1108532 := by decide
  rcases family_descends (prefixWord ++ tailWord_1108532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1108534 : List Nat := [5, 1, 2, 1, 2, 1, 1, 2, 2, 2, 4]
def baseStart_1108534 : Nat := 118140960795 + 1108534 * 2 ^ 59
def prefixEnd_1108534 : Nat := 4983230072969 + 3 ^ 40 * 1108534 * 2
def baseEnd_1108534 : Nat := 569210763851271089326951

theorem tailTrace_1108534 : CollatzResearch.WordTrace tailWord_1108534 prefixEnd_1108534 569210763851271089326951 := by
  unfold tailWord_1108534
  simp only [CollatzResearch.WordTrace]
  refine ⟨2526972285373632211223291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 26954371043985410253048437 2526972285373632211223291)
  ·
    refine ⟨3790458428060448316834937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2526972285373632211223291 3790458428060448316834937)
    ·
      refine ⟨2842843821045336237626203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3790458428060448316834937 2842843821045336237626203)
      ·
        refine ⟨4264265731568004356439305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2842843821045336237626203 4264265731568004356439305)
        ·
          refine ⟨3198199298676003267329479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4264265731568004356439305 3198199298676003267329479)
          ·
            refine ⟨4797298948014004900994219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3198199298676003267329479 4797298948014004900994219)
            ·
              refine ⟨7195948422021007351491329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4797298948014004900994219 7195948422021007351491329)
              ·
                refine ⟨5396961316515755513618497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7195948422021007351491329 5396961316515755513618497)
                ·
                  refine ⟨4047720987386816635213873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5396961316515755513618497 4047720987386816635213873)
                  ·
                    refine ⟨3035790740540112476410405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4047720987386816635213873 3035790740540112476410405)
                    ·
                      refine ⟨569210763851271089326951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3035790740540112476410405 569210763851271089326951)
                      ·
                        rfl

theorem cell23_1108534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 2, 2, 2, 4].length) (baseStart_1108534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1108534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1108534 prefixEnd_1108534 := by exact prefixLift 1108534
  have htrace : WordTrace (prefixWord ++ tailWord_1108534) baseStart_1108534 baseEnd_1108534 := by
    simpa [prefixWord, tailWord_1108534, baseEnd_1108534] using wordTrace_append hprefix tailTrace_1108534
  have hstable : (prefixWord ++ tailWord_1108534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1108534).length < 2 ^ (prefixWord ++ tailWord_1108534).sum := by decide
  have hdescent : baseEnd_1108534 < baseStart_1108534 := by decide
  rcases family_descends (prefixWord ++ tailWord_1108534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1108537 : List Nat := [1, 2, 1, 5, 1, 1, 1, 1, 4, 3, 3]
def baseStart_1108537 : Nat := 118140960795 + 1108537 * 2 ^ 59
def prefixEnd_1108537 : Nat := 4983230072969 + 3 ^ 40 * 1108537 * 2
def baseEnd_1108537 : Nat := 569212304293234577589437

theorem tailTrace_1108537 : CollatzResearch.WordTrace tailWord_1108537 prefixEnd_1108537 569212304293234577589437 := by
  unfold tailWord_1108537
  simp only [CollatzResearch.WordTrace]
  refine ⟨40431665984967246891931865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26954443989978164594621243 40431665984967246891931865)
  ·
    refine ⟨30323749488725435168948899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40431665984967246891931865 30323749488725435168948899)
    ·
      refine ⟨45485624233088152753423349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30323749488725435168948899 45485624233088152753423349)
      ·
        refine ⟨4264277271852014320633439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 45485624233088152753423349 4264277271852014320633439)
        ·
          refine ⟨6396415907778021480950159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4264277271852014320633439 6396415907778021480950159)
          ·
            refine ⟨9594623861667032221425239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6396415907778021480950159 9594623861667032221425239)
            ·
              refine ⟨14391935792500548332137859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9594623861667032221425239 14391935792500548332137859)
              ·
                refine ⟨21587903688750822498206789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14391935792500548332137859 21587903688750822498206789)
                ·
                  refine ⟨4047731941640779218413773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21587903688750822498206789 4047731941640779218413773)
                  ·
                    refine ⟨1517899478115292206905165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4047731941640779218413773 1517899478115292206905165)
                    ·
                      refine ⟨569212304293234577589437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1517899478115292206905165 569212304293234577589437)
                      ·
                        rfl

theorem cell23_1108537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 1, 4, 3, 3].length) (baseStart_1108537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1108537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1108537 prefixEnd_1108537 := by exact prefixLift 1108537
  have htrace : WordTrace (prefixWord ++ tailWord_1108537) baseStart_1108537 baseEnd_1108537 := by
    simpa [prefixWord, tailWord_1108537, baseEnd_1108537] using wordTrace_append hprefix tailTrace_1108537
  have hstable : (prefixWord ++ tailWord_1108537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1108537).length < 2 ^ (prefixWord ++ tailWord_1108537).sum := by decide
  have hdescent : baseEnd_1108537 < baseStart_1108537 := by decide
  rcases family_descends (prefixWord ++ tailWord_1108537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1108538 : List Nat := [3, 1, 1, 1, 3, 5, 1, 2, 2, 2, 2]
def baseStart_1108538 : Nat := 118140960795 + 1108538 * 2 ^ 59
def prefixEnd_1108538 : Nat := 4983230072969 + 3 ^ 40 * 1108538 * 2
def baseEnd_1108538 : Nat := 569212817773889073676933

theorem tailTrace_1108538 : CollatzResearch.WordTrace tailWord_1108538 prefixEnd_1108538 569212817773889073676933 := by
  unfold tailWord_1108538
  simp only [CollatzResearch.WordTrace]
  refine ⟨10107925614490906015679567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26954468305309082708478845 10107925614490906015679567)
  ·
    refine ⟨15161888421736359023519351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10107925614490906015679567 15161888421736359023519351)
    ·
      refine ⟨22742832632604538535279027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15161888421736359023519351 22742832632604538535279027)
      ·
        refine ⟨34114248948906807802918541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22742832632604538535279027 34114248948906807802918541)
        ·
          refine ⟨12792843355840052926094453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34114248948906807802918541 12792843355840052926094453)
          ·
            refine ⟨1199329064610004961821355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 12792843355840052926094453 1199329064610004961821355)
            ·
              refine ⟨1798993596915007442732033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1199329064610004961821355 1798993596915007442732033)
              ·
                refine ⟨1349245197686255582049025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1798993596915007442732033 1349245197686255582049025)
                ·
                  refine ⟨1011933898264691686536769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1349245197686255582049025 1011933898264691686536769)
                  ·
                    refine ⟨758950423698518764902577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1011933898264691686536769 758950423698518764902577)
                    ·
                      refine ⟨569212817773889073676933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 758950423698518764902577 569212817773889073676933)
                      ·
                        rfl

theorem cell23_1108538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 5, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 5, 1, 2, 2, 2, 2].length) (baseStart_1108538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1108538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1108538 prefixEnd_1108538 := by exact prefixLift 1108538
  have htrace : WordTrace (prefixWord ++ tailWord_1108538) baseStart_1108538 baseEnd_1108538 := by
    simpa [prefixWord, tailWord_1108538, baseEnd_1108538] using wordTrace_append hprefix tailTrace_1108538
  have hstable : (prefixWord ++ tailWord_1108538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1108538).length < 2 ^ (prefixWord ++ tailWord_1108538).sum := by decide
  have hdescent : baseEnd_1108538 < baseStart_1108538 := by decide
  rcases family_descends (prefixWord ++ tailWord_1108538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1108547 : List Nat := [1, 1, 1, 3, 1, 2, 1, 3, 1, 7, 2]
def baseStart_1108547 : Nat := 118140960795 + 1108547 * 2 ^ 59
def prefixEnd_1108547 : Nat := 4983230072969 + 3 ^ 40 * 1108547 * 2
def baseEnd_1108547 : Nat := 569217439099779538464391

theorem tailTrace_1108547 : CollatzResearch.WordTrace tailWord_1108547 prefixEnd_1108547 569217439099779538464391 := by
  unfold tailWord_1108547
  simp only [CollatzResearch.WordTrace]
  refine ⟨40432030714931018599795895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26954687143287345733197263 40432030714931018599795895)
  ·
    refine ⟨60648046072396527899693843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40432030714931018599795895 60648046072396527899693843)
    ·
      refine ⟨90972069108594791849540765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60648046072396527899693843 90972069108594791849540765)
      ·
        refine ⟨34114525915723046943577787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 90972069108594791849540765 34114525915723046943577787)
        ·
          refine ⟨51171788873584570415366681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34114525915723046943577787 51171788873584570415366681)
          ·
            refine ⟨38378841655188427811525011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51171788873584570415366681 38378841655188427811525011)
            ·
              refine ⟨57568262482782641717287517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38378841655188427811525011 57568262482782641717287517)
              ·
                refine ⟨21588098431043490643982819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 57568262482782641717287517 21588098431043490643982819)
                ·
                  refine ⟨32382147646565235965974229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21588098431043490643982819 32382147646565235965974229)
                  ·
                    refine ⟨758956585466372717952521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 32382147646565235965974229 758956585466372717952521)
                    ·
                      refine ⟨569217439099779538464391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 758956585466372717952521 569217439099779538464391)
                      ·
                        rfl

theorem cell23_1108547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 3, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 3, 1, 7, 2].length) (baseStart_1108547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1108547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1108547 prefixEnd_1108547 := by exact prefixLift 1108547
  have htrace : WordTrace (prefixWord ++ tailWord_1108547) baseStart_1108547 baseEnd_1108547 := by
    simpa [prefixWord, tailWord_1108547, baseEnd_1108547] using wordTrace_append hprefix tailTrace_1108547
  have hstable : (prefixWord ++ tailWord_1108547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1108547).length < 2 ^ (prefixWord ++ tailWord_1108547).sum := by decide
  have hdescent : baseEnd_1108547 < baseStart_1108547 := by decide
  rcases family_descends (prefixWord ++ tailWord_1108547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1108577 : List Nat := [1, 2, 3, 1, 1, 4, 2, 1, 1, 3, 4]
def baseStart_1108577 : Nat := 118140960795 + 1108577 * 2 ^ 59
def prefixEnd_1108577 : Nat := 4983230072969 + 3 ^ 40 * 1108577 * 2
def baseEnd_1108577 : Nat := 569232843519414421089253

theorem tailTrace_1108577 : CollatzResearch.WordTrace tailWord_1108577 prefixEnd_1108577 569232843519414421089253 := by
  unfold tailWord_1108577
  simp only [CollatzResearch.WordTrace]
  refine ⟨40433124904822333723387985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26955416603214889148925323 40433124904822333723387985)
  ·
    refine ⟨30324843678616750292540989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40433124904822333723387985 30324843678616750292540989)
    ·
      refine ⟨11371816379481281359702871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30324843678616750292540989 11371816379481281359702871)
      ·
        refine ⟨17057724569221922039554307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11371816379481281359702871 17057724569221922039554307)
        ·
          refine ⟨25586586853832883059331461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17057724569221922039554307 25586586853832883059331461)
          ·
            refine ⟨4797485035093665573624649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25586586853832883059331461 4797485035093665573624649)
            ·
              refine ⟨3598113776320249180218487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4797485035093665573624649 3598113776320249180218487)
              ·
                refine ⟨5397170664480373770327731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3598113776320249180218487 5397170664480373770327731)
                ·
                  refine ⟨8095755996720560655491597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5397170664480373770327731 8095755996720560655491597)
                  ·
                    refine ⟨3035908498770210245809349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8095755996720560655491597 3035908498770210245809349)
                    ·
                      refine ⟨569232843519414421089253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3035908498770210245809349 569232843519414421089253)
                      ·
                        rfl

theorem cell23_1108577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 2, 1, 1, 3, 4].length) (baseStart_1108577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1108577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1108577 prefixEnd_1108577 := by exact prefixLift 1108577
  have htrace : WordTrace (prefixWord ++ tailWord_1108577) baseStart_1108577 baseEnd_1108577 := by
    simpa [prefixWord, tailWord_1108577, baseEnd_1108577] using wordTrace_append hprefix tailTrace_1108577
  have hstable : (prefixWord ++ tailWord_1108577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1108577).length < 2 ^ (prefixWord ++ tailWord_1108577).sum := by decide
  have hdescent : baseEnd_1108577 < baseStart_1108577 := by decide
  rcases family_descends (prefixWord ++ tailWord_1108577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1108604 : List Nat := [2, 2, 2, 1, 1, 2, 5, 1, 3, 4]
def baseStart_1108604 : Nat := 118140960795 + 1108604 * 2 ^ 59
def prefixEnd_1108604 : Nat := 4983230072969 + 3 ^ 40 * 1108604 * 2
def baseEnd_1108604 : Nat := 189748902499028605150543

theorem tailTrace_1108604 : CollatzResearch.WordTrace tailWord_1108604 prefixEnd_1108604 189748902499028605150543 := by
  unfold tailWord_1108604
  simp only [CollatzResearch.WordTrace]
  refine ⟨20217054837862258667310433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26956073117149678223080577 20217054837862258667310433)
  ·
    refine ⟨15162791128396694000482825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20217054837862258667310433 15162791128396694000482825)
    ·
      refine ⟨11372093346297520500362119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15162791128396694000482825 11372093346297520500362119)
      ·
        refine ⟨17058140019446280750543179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11372093346297520500362119 17058140019446280750543179)
        ·
          refine ⟨25587210029169421125814769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17058140019446280750543179 25587210029169421125814769)
          ·
            refine ⟨19190407521877065844361077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25587210029169421125814769 19190407521877065844361077)
            ·
              refine ⟨1799100705175974922908851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 19190407521877065844361077 1799100705175974922908851)
              ·
                refine ⟨2698651057763962384363277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1799100705175974922908851 2698651057763962384363277)
                ·
                  refine ⟨1011994146661485894136229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2698651057763962384363277 1011994146661485894136229)
                  ·
                    refine ⟨189748902499028605150543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1011994146661485894136229 189748902499028605150543)
                    ·
                      rfl

theorem cell23_1108604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 5, 1, 3, 4].length) (baseStart_1108604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1108604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1108604 prefixEnd_1108604 := by exact prefixLift 1108604
  have htrace : WordTrace (prefixWord ++ tailWord_1108604) baseStart_1108604 baseEnd_1108604 := by
    simpa [prefixWord, tailWord_1108604, baseEnd_1108604] using wordTrace_append hprefix tailTrace_1108604
  have hstable : (prefixWord ++ tailWord_1108604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1108604).length < 2 ^ (prefixWord ++ tailWord_1108604).sum := by decide
  have hdescent : baseEnd_1108604 < baseStart_1108604 := by decide
  rcases family_descends (prefixWord ++ tailWord_1108604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1108638 : List Nat := [4, 3, 1, 1, 1, 1, 2, 5, 1, 4]
def baseStart_1108638 : Nat := 118140960795 + 1108638 * 2 ^ 59
def prefixEnd_1108638 : Nat := 4983230072969 + 3 ^ 40 * 1108638 * 2
def baseEnd_1108638 : Nat := 189754721946446227475491

theorem tailTrace_1108638 : CollatzResearch.WordTrace tailWord_1108638 prefixEnd_1108638 189754721946446227475491 := by
  unfold tailWord_1108638
  simp only [CollatzResearch.WordTrace]
  refine ⟨5054418719700167642669821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26956899838400894094239045 5054418719700167642669821)
  ·
    refine ⟨1895407019887562866001183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5054418719700167642669821 1895407019887562866001183)
    ·
      refine ⟨2843110529831344299001775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1895407019887562866001183 2843110529831344299001775)
      ·
        refine ⟨4264665794747016448502663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2843110529831344299001775 4264665794747016448502663)
        ·
          refine ⟨6396998692120524672753995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4264665794747016448502663 6396998692120524672753995)
          ·
            refine ⟨9595498038180787009130993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6396998692120524672753995 9595498038180787009130993)
            ·
              refine ⟨7196623528635590256848245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9595498038180787009130993 7196623528635590256848245)
              ·
                refine ⟨674683455809586586579523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7196623528635590256848245 674683455809586586579523)
                ·
                  refine ⟨1012025183714379879869285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 674683455809586586579523 1012025183714379879869285)
                  ·
                    refine ⟨189754721946446227475491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1012025183714379879869285 189754721946446227475491)
                    ·
                      rfl

theorem cell23_1108638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 5, 1, 4].length) (baseStart_1108638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1108638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1108638 prefixEnd_1108638 := by exact prefixLift 1108638
  have htrace : WordTrace (prefixWord ++ tailWord_1108638) baseStart_1108638 baseEnd_1108638 := by
    simpa [prefixWord, tailWord_1108638, baseEnd_1108638] using wordTrace_append hprefix tailTrace_1108638
  have hstable : (prefixWord ++ tailWord_1108638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1108638).length < 2 ^ (prefixWord ++ tailWord_1108638).sum := by decide
  have hdescent : baseEnd_1108638 < baseStart_1108638 := by decide
  rcases family_descends (prefixWord ++ tailWord_1108638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1108718 : List Nat := [4, 1, 2, 1, 1, 3, 1, 3, 3, 2, 2]
def baseStart_1108718 : Nat := 118140960795 + 1108718 * 2 ^ 59
def prefixEnd_1108718 : Nat := 4983230072969 + 3 ^ 40 * 1108718 * 2
def baseEnd_1108718 : Nat := 569305244291698369426105

theorem tailTrace_1108718 : CollatzResearch.WordTrace tailWord_1108718 prefixEnd_1108718 569305244291698369426105 := by
  unfold tailWord_1108718
  simp only [CollatzResearch.WordTrace]
  refine ⟨5054783449663939350533851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26958845064874343202847205 5054783449663939350533851)
  ·
    refine ⟨7582175174495909025800777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5054783449663939350533851 7582175174495909025800777)
    ·
      refine ⟨5686631380871931769350583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7582175174495909025800777 5686631380871931769350583)
      ·
        refine ⟨8529947071307897654025875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5686631380871931769350583 8529947071307897654025875)
        ·
          refine ⟨12794920606961846481038813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8529947071307897654025875 12794920606961846481038813)
          ·
            refine ⟨4798095227610692430389555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12794920606961846481038813 4798095227610692430389555)
            ·
              refine ⟨7197142841416038645584333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4798095227610692430389555 7197142841416038645584333)
              ·
                refine ⟨2698928565531014492094125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7197142841416038645584333 2698928565531014492094125)
                ·
                  refine ⟨1012098212074130434535297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2698928565531014492094125 1012098212074130434535297)
                  ·
                    refine ⟨759073659055597825901473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1012098212074130434535297 759073659055597825901473)
                    ·
                      refine ⟨569305244291698369426105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 759073659055597825901473 569305244291698369426105)
                      ·
                        rfl

theorem cell23_1108718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 3, 3, 2, 2].length) (baseStart_1108718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1108718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1108718 prefixEnd_1108718 := by exact prefixLift 1108718
  have htrace : WordTrace (prefixWord ++ tailWord_1108718) baseStart_1108718 baseEnd_1108718 := by
    simpa [prefixWord, tailWord_1108718, baseEnd_1108718] using wordTrace_append hprefix tailTrace_1108718
  have hstable : (prefixWord ++ tailWord_1108718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1108718).length < 2 ^ (prefixWord ++ tailWord_1108718).sum := by decide
  have hdescent : baseEnd_1108718 < baseStart_1108718 := by decide
  rcases family_descends (prefixWord ++ tailWord_1108718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1108738 : List Nat := [3, 4, 1, 1, 1, 2, 1, 4, 1, 2, 3]
def baseStart_1108738 : Nat := 118140960795 + 1108738 * 2 ^ 59
def prefixEnd_1108738 : Nat := 4983230072969 + 3 ^ 40 * 1108738 * 2
def baseEnd_1108738 : Nat := 569315513904788291176013

theorem tailTrace_1108738 : CollatzResearch.WordTrace tailWord_1108738 prefixEnd_1108738 569315513904788291176013 := by
  unfold tailWord_1108738
  simp only [CollatzResearch.WordTrace]
  refine ⟨10109749264309764554999717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26959331371492705479999245 10109749264309764554999717)
  ·
    refine ⟨1895577987058080854062447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10109749264309764554999717 1895577987058080854062447)
    ·
      refine ⟨2843366980587121281093671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1895577987058080854062447 2843366980587121281093671)
      ·
        refine ⟨4265050470880681921640507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2843366980587121281093671 4265050470880681921640507)
        ·
          refine ⟨6397575706321022882460761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4265050470880681921640507 6397575706321022882460761)
          ·
            refine ⟨4798181779740767161845571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6397575706321022882460761 4798181779740767161845571)
            ·
              refine ⟨7197272669611150742768357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4798181779740767161845571 7197272669611150742768357)
              ·
                refine ⟨1349488625552090764269067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7197272669611150742768357 1349488625552090764269067)
                ·
                  refine ⟨2024232938328136146403601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1349488625552090764269067 2024232938328136146403601)
                  ·
                    refine ⟨1518174703746102109802701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2024232938328136146403601 1518174703746102109802701)
                    ·
                      refine ⟨569315513904788291176013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1518174703746102109802701 569315513904788291176013)
                      ·
                        rfl

theorem cell23_1108738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 4, 1, 2, 3].length) (baseStart_1108738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1108738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1108738 prefixEnd_1108738 := by exact prefixLift 1108738
  have htrace : WordTrace (prefixWord ++ tailWord_1108738) baseStart_1108738 baseEnd_1108738 := by
    simpa [prefixWord, tailWord_1108738, baseEnd_1108738] using wordTrace_append hprefix tailTrace_1108738
  have hstable : (prefixWord ++ tailWord_1108738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1108738).length < 2 ^ (prefixWord ++ tailWord_1108738).sum := by decide
  have hdescent : baseEnd_1108738 < baseStart_1108738 := by decide
  rcases family_descends (prefixWord ++ tailWord_1108738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1108791 : List Nat := [1, 1, 3, 1, 2, 1, 4, 3, 1, 4, 2]
def baseStart_1108791 : Nat := 118140960795 + 1108791 * 2 ^ 59
def prefixEnd_1108791 : Nat := 4983230072969 + 3 ^ 40 * 1108791 * 2
def baseEnd_1108791 : Nat := 569342728379476583813269

theorem tailTrace_1108791 : CollatzResearch.WordTrace tailWord_1108791 prefixEnd_1108791 569342728379476583813269 := by
  unfold tailWord_1108791
  simp only [CollatzResearch.WordTrace]
  refine ⟨40440930126047048271678227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26960620084031365514452151 40440930126047048271678227)
  ·
    refine ⟨60661395189070572407517341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40440930126047048271678227 60661395189070572407517341)
    ·
      refine ⟨22748023195901464652819003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60661395189070572407517341 22748023195901464652819003)
      ·
        refine ⟨34122034793852196979228505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22748023195901464652819003 34122034793852196979228505)
        ·
          refine ⟨25591526095389147734421379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34122034793852196979228505 25591526095389147734421379)
          ·
            refine ⟨38387289143083721601632069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25591526095389147734421379 38387289143083721601632069)
            ·
              refine ⟨7197616714328197800306013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38387289143083721601632069 7197616714328197800306013)
              ·
                refine ⟨2699106267873074175114755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7197616714328197800306013 2699106267873074175114755)
                ·
                  refine ⟨4048659401809611262672133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2699106267873074175114755 4048659401809611262672133)
                  ·
                    refine ⟨759123637839302111751025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4048659401809611262672133 759123637839302111751025)
                    ·
                      refine ⟨569342728379476583813269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 759123637839302111751025 569342728379476583813269)
                      ·
                        rfl

theorem cell23_1108791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 3, 1, 4, 2].length) (baseStart_1108791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1108791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1108791 prefixEnd_1108791 := by exact prefixLift 1108791
  have htrace : WordTrace (prefixWord ++ tailWord_1108791) baseStart_1108791 baseEnd_1108791 := by
    simpa [prefixWord, tailWord_1108791, baseEnd_1108791] using wordTrace_append hprefix tailTrace_1108791
  have hstable : (prefixWord ++ tailWord_1108791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1108791).length < 2 ^ (prefixWord ++ tailWord_1108791).sum := by decide
  have hdescent : baseEnd_1108791 < baseStart_1108791 := by decide
  rcases family_descends (prefixWord ++ tailWord_1108791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1108824 : List Nat := [2, 1, 2, 2, 1, 1, 1, 2, 3, 5, 3]
def baseStart_1108824 : Nat := 118140960795 + 1108824 * 2 ^ 59
def prefixEnd_1108824 : Nat := 4983230072969 + 3 ^ 40 * 1108824 * 2
def baseEnd_1108824 : Nat := 569359673241074954700617

theorem tailTrace_1108824 : CollatzResearch.WordTrace tailWord_1108824 prefixEnd_1108824 569359673241074954700617 := by
  unfold tailWord_1108824
  simp only [CollatzResearch.WordTrace]
  refine ⟨20221066867463747453814763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26961422489951663271753017 20221066867463747453814763)
  ·
    refine ⟨30331600301195621180722145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20221066867463747453814763 30331600301195621180722145)
    ·
      refine ⟨22748700225896715885541609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30331600301195621180722145 22748700225896715885541609)
      ·
        refine ⟨17061525169422536914156207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22748700225896715885541609 17061525169422536914156207)
        ·
          refine ⟨25592287754133805371234311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17061525169422536914156207 25592287754133805371234311)
          ·
            refine ⟨38388431631200708056851467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25592287754133805371234311 38388431631200708056851467)
            ·
              refine ⟨57582647446801062085277201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38388431631200708056851467 57582647446801062085277201)
              ·
                refine ⟨43186985585100796563957901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 57582647446801062085277201 43186985585100796563957901)
                ·
                  refine ⟨16195119594412798711484213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 43186985585100796563957901 16195119594412798711484213)
                  ·
                    refine ⟨1518292461976199879201645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 16195119594412798711484213 1518292461976199879201645)
                    ·
                      refine ⟨569359673241074954700617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1518292461976199879201645 569359673241074954700617)
                      ·
                        rfl

theorem cell23_1108824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 2, 3, 5, 3].length) (baseStart_1108824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1108824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1108824 prefixEnd_1108824 := by exact prefixLift 1108824
  have htrace : WordTrace (prefixWord ++ tailWord_1108824) baseStart_1108824 baseEnd_1108824 := by
    simpa [prefixWord, tailWord_1108824, baseEnd_1108824] using wordTrace_append hprefix tailTrace_1108824
  have hstable : (prefixWord ++ tailWord_1108824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1108824).length < 2 ^ (prefixWord ++ tailWord_1108824).sum := by decide
  have hdescent : baseEnd_1108824 < baseStart_1108824 := by decide
  rcases family_descends (prefixWord ++ tailWord_1108824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1108825 : List Nat := [1, 2, 1, 2, 2, 5, 2, 2, 2, 2, 2]
def baseStart_1108825 : Nat := 118140960795 + 1108825 * 2 ^ 59
def prefixEnd_1108825 : Nat := 4983230072969 + 3 ^ 40 * 1108825 * 2
def baseEnd_1108825 : Nat := 569360186721729450788113

theorem tailTrace_1108825 : CollatzResearch.WordTrace tailWord_1108825 prefixEnd_1108825 569360186721729450788113 := by
  unfold tailWord_1108825
  simp only [CollatzResearch.WordTrace]
  refine ⟨40442170207923872078415929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26961446805282581385610619 40442170207923872078415929)
  ·
    refine ⟨30331627655942904058811947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40442170207923872078415929 30331627655942904058811947)
    ·
      refine ⟨45497441483914356088217921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30331627655942904058811947 45497441483914356088217921)
      ·
        refine ⟨34123081112935767066163441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45497441483914356088217921 34123081112935767066163441)
        ·
          refine ⟨25592310834701825299622581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34123081112935767066163441 25592310834701825299622581)
          ·
            refine ⟨2399279140753296121839617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 25592310834701825299622581 2399279140753296121839617)
            ·
              refine ⟨1799459355564972091379713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2399279140753296121839617 1799459355564972091379713)
              ·
                refine ⟨1349594516673729068534785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1799459355564972091379713 1349594516673729068534785)
                ·
                  refine ⟨1012195887505296801401089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1349594516673729068534785 1012195887505296801401089)
                  ·
                    refine ⟨759146915628972601050817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1012195887505296801401089 759146915628972601050817)
                    ·
                      refine ⟨569360186721729450788113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 759146915628972601050817 569360186721729450788113)
                      ·
                        rfl

theorem cell23_1108825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 2, 2, 2, 2, 2].length) (baseStart_1108825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1108825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1108825 prefixEnd_1108825 := by exact prefixLift 1108825
  have htrace : WordTrace (prefixWord ++ tailWord_1108825) baseStart_1108825 baseEnd_1108825 := by
    simpa [prefixWord, tailWord_1108825, baseEnd_1108825] using wordTrace_append hprefix tailTrace_1108825
  have hstable : (prefixWord ++ tailWord_1108825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1108825).length < 2 ^ (prefixWord ++ tailWord_1108825).sum := by decide
  have hdescent : baseEnd_1108825 < baseStart_1108825 := by decide
  rcases family_descends (prefixWord ++ tailWord_1108825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1108831 : List Nat := [1, 1, 2, 3, 1, 3, 3, 4, 5]
def baseStart_1108831 : Nat := 118140960795 + 1108831 * 2 ^ 59
def prefixEnd_1108831 : Nat := 4983230072969 + 3 ^ 40 * 1108831 * 2
def baseEnd_1108831 : Nat := 63262585289517380812565

theorem tailTrace_1108831 : CollatzResearch.WordTrace tailWord_1108831 prefixEnd_1108831 63262585289517380812565 := by
  unfold tailWord_1108831
  simp only [CollatzResearch.WordTrace]
  refine ⟨40442389045902135103134347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26961592697268090068756231 40442389045902135103134347)
  ·
    refine ⟨60663583568853202654701521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40442389045902135103134347 60663583568853202654701521)
    ·
      refine ⟨45497687676639901991026141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60663583568853202654701521 45497687676639901991026141)
      ·
        refine ⟨17061632878739963246634803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45497687676639901991026141 17061632878739963246634803)
        ·
          refine ⟨25592449318109944869952205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17061632878739963246634803 25592449318109944869952205)
          ·
            refine ⟨9597168494291229326232077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25592449318109944869952205 9597168494291229326232077)
            ·
              refine ⟨3598938185359210997337029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9597168494291229326232077 3598938185359210997337029)
              ·
                refine ⟨674800909754852062000693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3598938185359210997337029 674800909754852062000693)
                ·
                  refine ⟨63262585289517380812565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 674800909754852062000693 63262585289517380812565)
                  ·
                    rfl

theorem cell23_1108831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 3, 4, 5].length) (baseStart_1108831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1108831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1108831 prefixEnd_1108831 := by exact prefixLift 1108831
  have htrace : WordTrace (prefixWord ++ tailWord_1108831) baseStart_1108831 baseEnd_1108831 := by
    simpa [prefixWord, tailWord_1108831, baseEnd_1108831] using wordTrace_append hprefix tailTrace_1108831
  have hstable : (prefixWord ++ tailWord_1108831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1108831).length < 2 ^ (prefixWord ++ tailWord_1108831).sum := by decide
  have hdescent : baseEnd_1108831 < baseStart_1108831 := by decide
  rcases family_descends (prefixWord ++ tailWord_1108831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1108844 : List Nat := [2, 2, 1, 1, 4, 1, 2, 2, 1, 7]
def baseStart_1108844 : Nat := 118140960795 + 1108844 * 2 ^ 59
def prefixEnd_1108844 : Nat := 4983230072969 + 3 ^ 40 * 1108844 * 2
def baseEnd_1108844 : Nat := 189789980951388292150175

theorem tailTrace_1108844 : CollatzResearch.WordTrace tailWord_1108844 prefixEnd_1108844 189789980951388292150175 := by
  unfold tailWord_1108844
  simp only [CollatzResearch.WordTrace]
  refine ⟨20221431597427519161678793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26961908796570025548905057 20221431597427519161678793)
  ·
    refine ⟨15166073698070639371259095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20221431597427519161678793 15166073698070639371259095)
    ·
      refine ⟨22749110547105959056888643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15166073698070639371259095 22749110547105959056888643)
      ·
        refine ⟨34123665820658938585332965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22749110547105959056888643 34123665820658938585332965)
        ·
          refine ⟨6398187341373550984749931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34123665820658938585332965 6398187341373550984749931)
          ·
            refine ⟨9597281012060326477124897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6398187341373550984749931 9597281012060326477124897)
            ·
              refine ⟨7197960759045244857843673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9597281012060326477124897 7197960759045244857843673)
              ·
                refine ⟨5398470569283933643382755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7197960759045244857843673 5398470569283933643382755)
                ·
                  refine ⟨8097705853925900465074133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5398470569283933643382755 8097705853925900465074133)
                  ·
                    refine ⟨189789980951388292150175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 8097705853925900465074133 189789980951388292150175)
                    ·
                      rfl

theorem cell23_1108844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 7].length) (baseStart_1108844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1108844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1108844 prefixEnd_1108844 := by exact prefixLift 1108844
  have htrace : WordTrace (prefixWord ++ tailWord_1108844) baseStart_1108844 baseEnd_1108844 := by
    simpa [prefixWord, tailWord_1108844, baseEnd_1108844] using wordTrace_append hprefix tailTrace_1108844
  have hstable : (prefixWord ++ tailWord_1108844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1108844).length < 2 ^ (prefixWord ++ tailWord_1108844).sum := by decide
  have hdescent : baseEnd_1108844 < baseStart_1108844 := by decide
  rcases family_descends (prefixWord ++ tailWord_1108844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1108861 : List Nat := [1, 4, 1, 1, 2, 1, 5, 1, 2, 5]
def baseStart_1108861 : Nat := 118140960795 + 1108861 * 2 ^ 59
def prefixEnd_1108861 : Nat := 4983230072969 + 3 ^ 40 * 1108861 * 2
def baseEnd_1108861 : Nat := 189792890675097103312649

theorem tailTrace_1108861 : CollatzResearch.WordTrace tailWord_1108861 prefixEnd_1108861 189792890675097103312649 := by
  unfold tailWord_1108861
  simp only [CollatzResearch.WordTrace]
  refine ⟨40443483235793450226726437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26962322157195633484484291 40443483235793450226726437)
  ·
    refine ⟨7583153106711271917511207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 40443483235793450226726437 7583153106711271917511207)
    ·
      refine ⟨11374729660066907876266811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7583153106711271917511207 11374729660066907876266811)
      ·
        refine ⟨17062094490100361814400217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11374729660066907876266811 17062094490100361814400217)
        ·
          refine ⟨12796570867575271360800163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17062094490100361814400217 12796570867575271360800163)
          ·
            refine ⟨19194856301362907041200245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12796570867575271360800163 19194856301362907041200245)
            ·
              refine ⟨1799517778252772535112523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 19194856301362907041200245 1799517778252772535112523)
              ·
                refine ⟨2699276667379158802668785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1799517778252772535112523 2699276667379158802668785)
                ·
                  refine ⟨2024457500534369102001589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2699276667379158802668785 2024457500534369102001589)
                  ·
                    refine ⟨189792890675097103312649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2024457500534369102001589 189792890675097103312649)
                    ·
                      rfl

theorem cell23_1108861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 5, 1, 2, 5].length) (baseStart_1108861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1108861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1108861 prefixEnd_1108861 := by exact prefixLift 1108861
  have htrace : WordTrace (prefixWord ++ tailWord_1108861) baseStart_1108861 baseEnd_1108861 := by
    simpa [prefixWord, tailWord_1108861, baseEnd_1108861] using wordTrace_append hprefix tailTrace_1108861
  have hstable : (prefixWord ++ tailWord_1108861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1108861).length < 2 ^ (prefixWord ++ tailWord_1108861).sum := by decide
  have hdescent : baseEnd_1108861 < baseStart_1108861 := by decide
  rcases family_descends (prefixWord ++ tailWord_1108861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1108914 : List Nat := [3, 2, 1, 1, 1, 1, 1, 1, 2, 1, 9]
def baseStart_1108914 : Nat := 118140960795 + 1108914 * 2 ^ 59
def prefixEnd_1108914 : Nat := 4983230072969 + 3 ^ 40 * 1108914 * 2
def baseEnd_1108914 : Nat := 569405886499979602575203

theorem tailTrace_1108914 : CollatzResearch.WordTrace tailWord_1108914 prefixEnd_1108914 569405886499979602575203 := by
  unfold tailWord_1108914
  simp only [CollatzResearch.WordTrace]
  refine ⟨10111354076150360069601449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26963610869734293518937197 10111354076150360069601449)
  ·
    refine ⟨7583515557112770052201087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10111354076150360069601449 7583515557112770052201087)
    ·
      refine ⟨11375273335669155078301631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7583515557112770052201087 11375273335669155078301631)
      ·
        refine ⟨17062910003503732617452447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11375273335669155078301631 17062910003503732617452447)
        ·
          refine ⟨25594365005255598926178671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17062910003503732617452447 25594365005255598926178671)
          ·
            refine ⟨38391547507883398389268007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25594365005255598926178671 38391547507883398389268007)
            ·
              refine ⟨57587321261825097583902011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38391547507883398389268007 57587321261825097583902011)
              ·
                refine ⟨86380981892737646375853017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57587321261825097583902011 86380981892737646375853017)
                ·
                  refine ⟨64785736419553234781889763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 86380981892737646375853017 64785736419553234781889763)
                  ·
                    refine ⟨97178604629329852172834645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 64785736419553234781889763 97178604629329852172834645)
                    ·
                      refine ⟨569405886499979602575203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 97178604629329852172834645 569405886499979602575203)
                      ·
                        rfl

theorem cell23_1108914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 1, 2, 1, 9].length) (baseStart_1108914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1108914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1108914 prefixEnd_1108914 := by exact prefixLift 1108914
  have htrace : WordTrace (prefixWord ++ tailWord_1108914) baseStart_1108914 baseEnd_1108914 := by
    simpa [prefixWord, tailWord_1108914, baseEnd_1108914] using wordTrace_append hprefix tailTrace_1108914
  have hstable : (prefixWord ++ tailWord_1108914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1108914).length < 2 ^ (prefixWord ++ tailWord_1108914).sum := by decide
  have hdescent : baseEnd_1108914 < baseStart_1108914 := by decide
  rcases family_descends (prefixWord ++ tailWord_1108914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1108942 : List Nat := [4, 1, 1, 1, 2, 4, 3, 2, 1, 4]
def baseStart_1108942 : Nat := 118140960795 + 1108942 * 2 ^ 59
def prefixEnd_1108942 : Nat := 4983230072969 + 3 ^ 40 * 1108942 * 2
def baseEnd_1108942 : Nat := 189806754652768497675025

theorem tailTrace_1108942 : CollatzResearch.WordTrace tailWord_1108942 prefixEnd_1108942 189806754652768497675025 := by
  unfold tailWord_1108942
  simp only [CollatzResearch.WordTrace]
  refine ⟨5055804693562500132553135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26964291699000000706950053 5055804693562500132553135)
  ·
    refine ⟨7583707040343750198829703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5055804693562500132553135 7583707040343750198829703)
    ·
      refine ⟨11375560560515625298244555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7583707040343750198829703 11375560560515625298244555)
      ·
        refine ⟨17063340840773437947366833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11375560560515625298244555 17063340840773437947366833)
        ·
          refine ⟨12797505630580078460525125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17063340840773437947366833 12797505630580078460525125)
          ·
            refine ⟨2399532305733764711348461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12797505630580078460525125 2399532305733764711348461)
            ·
              refine ⟨899824614650161766755673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2399532305733764711348461 899824614650161766755673)
              ·
                refine ⟨674868460987621325066755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 899824614650161766755673 674868460987621325066755)
                ·
                  refine ⟨1012302691481431987600133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 674868460987621325066755 1012302691481431987600133)
                  ·
                    refine ⟨189806754652768497675025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1012302691481431987600133 189806754652768497675025)
                    ·
                      rfl

theorem cell23_1108942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 3, 2, 1, 4].length) (baseStart_1108942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1108942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1108942 prefixEnd_1108942 := by exact prefixLift 1108942
  have htrace : WordTrace (prefixWord ++ tailWord_1108942) baseStart_1108942 baseEnd_1108942 := by
    simpa [prefixWord, tailWord_1108942, baseEnd_1108942] using wordTrace_append hprefix tailTrace_1108942
  have hstable : (prefixWord ++ tailWord_1108942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1108942).length < 2 ^ (prefixWord ++ tailWord_1108942).sum := by decide
  have hdescent : baseEnd_1108942 < baseStart_1108942 := by decide
  rcases family_descends (prefixWord ++ tailWord_1108942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1108944 : List Nat := [2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 7]
def baseStart_1108944 : Nat := 118140960795 + 1108944 * 2 ^ 59
def prefixEnd_1108944 : Nat := 4983230072969 + 3 ^ 40 * 1108944 * 2
def baseEnd_1108944 : Nat := 569421290919614485200065

theorem tailTrace_1108944 : CollatzResearch.WordTrace tailWord_1108944 prefixEnd_1108944 569421290919614485200065 := by
  unfold tailWord_1108944
  simp only [CollatzResearch.WordTrace]
  refine ⟨20223255247246377700998943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26964340329661836934665257 20223255247246377700998943)
  ·
    refine ⟨30334882870869566551498415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20223255247246377700998943 30334882870869566551498415)
    ·
      refine ⟨45502324306304349827247623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30334882870869566551498415 45502324306304349827247623)
      ·
        refine ⟨68253486459456524740871435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45502324306304349827247623 68253486459456524740871435)
        ·
          refine ⟨102380229689184787111307153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68253486459456524740871435 102380229689184787111307153)
          ·
            refine ⟨76785172266888590333480365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 102380229689184787111307153 76785172266888590333480365)
            ·
              refine ⟨28794439600083221375055137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 76785172266888590333480365 28794439600083221375055137)
              ·
                refine ⟨21595829700062416031291353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28794439600083221375055137 21595829700062416031291353)
                ·
                  refine ⟨16196872275046812023468515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21595829700062416031291353 16196872275046812023468515)
                  ·
                    refine ⟨24295308412570218035202773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16196872275046812023468515 24295308412570218035202773)
                    ·
                      refine ⟨569421290919614485200065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 24295308412570218035202773 569421290919614485200065)
                      ·
                        rfl

theorem cell23_1108944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 7].length) (baseStart_1108944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1108944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1108944 prefixEnd_1108944 := by exact prefixLift 1108944
  have htrace : WordTrace (prefixWord ++ tailWord_1108944) baseStart_1108944 baseEnd_1108944 := by
    simpa [prefixWord, tailWord_1108944, baseEnd_1108944] using wordTrace_append hprefix tailTrace_1108944
  have hstable : (prefixWord ++ tailWord_1108944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1108944).length < 2 ^ (prefixWord ++ tailWord_1108944).sum := by decide
  have hdescent : baseEnd_1108944 < baseStart_1108944 := by decide
  rcases family_descends (prefixWord ++ tailWord_1108944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1108968 : List Nat := [2, 1, 4, 1, 1, 1, 5, 2, 1, 5]
def baseStart_1108968 : Nat := 118140960795 + 1108968 * 2 ^ 59
def prefixEnd_1108968 : Nat := 4983230072969 + 3 ^ 40 * 1108968 * 2
def baseEnd_1108968 : Nat := 189811204818440797099985

theorem tailTrace_1108968 : CollatzResearch.WordTrace tailWord_1108968 prefixEnd_1108968 189811204818440797099985 := by
  unfold tailWord_1108968
  simp only [CollatzResearch.WordTrace]
  refine ⟨20223692923202903750435779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26964923897603871667247705 20223692923202903750435779)
  ·
    refine ⟨30335539384804355625653669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20223692923202903750435779 30335539384804355625653669)
    ·
      refine ⟨5687913634650816679810063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30335539384804355625653669 5687913634650816679810063)
      ·
        refine ⟨8531870451976225019715095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5687913634650816679810063 8531870451976225019715095)
        ·
          refine ⟨12797805677964337529572643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8531870451976225019715095 12797805677964337529572643)
          ·
            refine ⟨19196708516946506294358965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12797805677964337529572643 19196708516946506294358965)
            ·
              refine ⟨1799691423463734965096153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 19196708516946506294358965 1799691423463734965096153)
              ·
                refine ⟨1349768567597801223822115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1799691423463734965096153 1349768567597801223822115)
                ·
                  refine ⟨2024652851396701835733173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1349768567597801223822115 2024652851396701835733173)
                  ·
                    refine ⟨189811204818440797099985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2024652851396701835733173 189811204818440797099985)
                    ·
                      rfl

theorem cell23_1108968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 5, 2, 1, 5].length) (baseStart_1108968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1108968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1108968 prefixEnd_1108968 := by exact prefixLift 1108968
  have htrace : WordTrace (prefixWord ++ tailWord_1108968) baseStart_1108968 baseEnd_1108968 := by
    simpa [prefixWord, tailWord_1108968, baseEnd_1108968] using wordTrace_append hprefix tailTrace_1108968
  have hstable : (prefixWord ++ tailWord_1108968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1108968).length < 2 ^ (prefixWord ++ tailWord_1108968).sum := by decide
  have hdescent : baseEnd_1108968 < baseStart_1108968 := by decide
  rcases family_descends (prefixWord ++ tailWord_1108968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1108975 : List Nat := [1, 1, 2, 1, 4, 4, 2, 1, 2, 3, 2]
def baseStart_1108975 : Nat := 118140960795 + 1108975 * 2 ^ 59
def prefixEnd_1108975 : Nat := 4983230072969 + 3 ^ 40 * 1108975 * 2
def baseEnd_1108975 : Nat := 569437208819903863912423

theorem tailTrace_1108975 : CollatzResearch.WordTrace tailWord_1108975 prefixEnd_1108975 569437208819903863912423 := by
  unfold tailWord_1108975
  simp only [CollatzResearch.WordTrace]
  refine ⟨40447641157380447696376379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26965094104920298464250919 40447641157380447696376379)
  ·
    refine ⟨60671461736070671544564569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40447641157380447696376379 60671461736070671544564569)
    ·
      refine ⟨45503596302053003658423427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60671461736070671544564569 45503596302053003658423427)
      ·
        refine ⟨68255394453079505487635141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45503596302053003658423427 68255394453079505487635141)
        ·
          refine ⟨12797886459952407278931589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 68255394453079505487635141 12797886459952407278931589)
          ·
            refine ⟨2399603711241076364799673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12797886459952407278931589 2399603711241076364799673)
            ·
              refine ⟨1799702783430807273599755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2399603711241076364799673 1799702783430807273599755)
              ·
                refine ⟨2699554175146210910399633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1799702783430807273599755 2699554175146210910399633)
                ·
                  refine ⟨2024665631359658182799725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2699554175146210910399633 2024665631359658182799725)
                  ·
                    refine ⟨759249611759871818549897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2024665631359658182799725 759249611759871818549897)
                    ·
                      refine ⟨569437208819903863912423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 759249611759871818549897 569437208819903863912423)
                      ·
                        rfl

theorem cell23_1108975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 2, 1, 2, 3, 2].length) (baseStart_1108975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1108975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1108975 prefixEnd_1108975 := by exact prefixLift 1108975
  have htrace : WordTrace (prefixWord ++ tailWord_1108975) baseStart_1108975 baseEnd_1108975 := by
    simpa [prefixWord, tailWord_1108975, baseEnd_1108975] using wordTrace_append hprefix tailTrace_1108975
  have hstable : (prefixWord ++ tailWord_1108975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1108975).length < 2 ^ (prefixWord ++ tailWord_1108975).sum := by decide
  have hdescent : baseEnd_1108975 < baseStart_1108975 := by decide
  rcases family_descends (prefixWord ++ tailWord_1108975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1109015 : List Nat := [1, 1, 3, 5, 1, 1, 2, 3, 2, 4]
def baseStart_1109015 : Nat := 118140960795 + 1109015 * 2 ^ 59
def prefixEnd_1109015 : Nat := 4983230072969 + 3 ^ 40 * 1109015 * 2
def baseEnd_1109015 : Nat := 189819249348694569137413

theorem tailTrace_1109015 : CollatzResearch.WordTrace tailWord_1109015 prefixEnd_1109015 189819249348694569137413 := by
  unfold tailWord_1109015
  simp only [CollatzResearch.WordTrace]
  refine ⟨40449100077235534527832499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26966066718157023018554999 40449100077235534527832499)
  ·
    refine ⟨60673650115853301791748749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40449100077235534527832499 60673650115853301791748749)
    ·
      refine ⟨22752618793444988171905781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60673650115853301791748749 22752618793444988171905781)
      ·
        refine ⟨2133058011885467641116167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 22752618793444988171905781 2133058011885467641116167)
        ·
          refine ⟨3199587017828201461674251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2133058011885467641116167 3199587017828201461674251)
          ·
            refine ⟨4799380526742302192511377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3199587017828201461674251 4799380526742302192511377)
            ·
              refine ⟨3599535395056726644383533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4799380526742302192511377 3599535395056726644383533)
              ·
                refine ⟨1349825773146272491643825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3599535395056726644383533 1349825773146272491643825)
                ·
                  refine ⟨1012369329859704368732869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1349825773146272491643825 1012369329859704368732869)
                  ·
                    refine ⟨189819249348694569137413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1012369329859704368732869 189819249348694569137413)
                    ·
                      rfl

theorem cell23_1109015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 2, 3, 2, 4].length) (baseStart_1109015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1109015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1109015 prefixEnd_1109015 := by exact prefixLift 1109015
  have htrace : WordTrace (prefixWord ++ tailWord_1109015) baseStart_1109015 baseEnd_1109015 := by
    simpa [prefixWord, tailWord_1109015, baseEnd_1109015] using wordTrace_append hprefix tailTrace_1109015
  have hstable : (prefixWord ++ tailWord_1109015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1109015).length < 2 ^ (prefixWord ++ tailWord_1109015).sum := by decide
  have hdescent : baseEnd_1109015 < baseStart_1109015 := by decide
  rcases family_descends (prefixWord ++ tailWord_1109015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1109018 : List Nat := [3, 1, 1, 3, 1, 2, 4, 1, 1, 2, 4]
def baseStart_1109018 : Nat := 118140960795 + 1109018 * 2 ^ 59
def prefixEnd_1109018 : Nat := 4983230072969 + 3 ^ 40 * 1109018 * 2
def baseEnd_1109018 : Nat := 569459288488047195674725

theorem tailTrace_1109018 : CollatzResearch.WordTrace tailWord_1109018 prefixEnd_1109018 569459288488047195674725 := by
  unfold tailWord_1109018
  simp only [CollatzResearch.WordTrace]
  refine ⟨10112302374056166510047927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26966139664149777360127805 10112302374056166510047927)
  ·
    refine ⟨15168453561084249765071891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10112302374056166510047927 15168453561084249765071891)
    ·
      refine ⟨22752680341626374647607837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15168453561084249765071891 22752680341626374647607837)
      ·
        refine ⟨8532255128109890492852939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22752680341626374647607837 8532255128109890492852939)
        ·
          refine ⟨12798382692164835739279409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8532255128109890492852939 12798382692164835739279409)
          ·
            refine ⟨9598787019123626804459557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12798382692164835739279409 9598787019123626804459557)
            ·
              refine ⟨1799772566085680025836167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9598787019123626804459557 1799772566085680025836167)
              ·
                refine ⟨2699658849128520038754251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1799772566085680025836167 2699658849128520038754251)
                ·
                  refine ⟨4049488273692780058131377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2699658849128520038754251 4049488273692780058131377)
                  ·
                    refine ⟨3037116205269585043598533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4049488273692780058131377 3037116205269585043598533)
                    ·
                      refine ⟨569459288488047195674725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3037116205269585043598533 569459288488047195674725)
                      ·
                        rfl

theorem cell23_1109018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 4, 1, 1, 2, 4].length) (baseStart_1109018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1109018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1109018 prefixEnd_1109018 := by exact prefixLift 1109018
  have htrace : WordTrace (prefixWord ++ tailWord_1109018) baseStart_1109018 baseEnd_1109018 := by
    simpa [prefixWord, tailWord_1109018, baseEnd_1109018] using wordTrace_append hprefix tailTrace_1109018
  have hstable : (prefixWord ++ tailWord_1109018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1109018).length < 2 ^ (prefixWord ++ tailWord_1109018).sum := by decide
  have hdescent : baseEnd_1109018 < baseStart_1109018 := by decide
  rcases family_descends (prefixWord ++ tailWord_1109018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1109061 : List Nat := [1, 3, 1, 1, 1, 3, 2, 1, 1, 5, 4]
def baseStart_1109061 : Nat := 118140960795 + 1109061 * 2 ^ 59
def prefixEnd_1109061 : Nat := 4983230072969 + 3 ^ 40 * 1109061 * 2
def baseEnd_1109061 : Nat := 569481368156190527437027

theorem tailTrace_1109061 : CollatzResearch.WordTrace tailWord_1109061 prefixEnd_1109061 569481368156190527437027 := by
  unfold tailWord_1109061
  simp only [CollatzResearch.WordTrace]
  refine ⟨40450777835068884384007037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26967185223379256256004691 40450777835068884384007037)
  ·
    refine ⟨15169041688150831644002639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40450777835068884384007037 15169041688150831644002639)
    ·
      refine ⟨22753562532226247466003959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15169041688150831644002639 22753562532226247466003959)
      ·
        refine ⟨34130343798339371199005939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22753562532226247466003959 34130343798339371199005939)
        ·
          refine ⟨51195515697509056798508909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34130343798339371199005939 51195515697509056798508909)
          ·
            refine ⟨19198318386565896299440841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51195515697509056798508909 19198318386565896299440841)
            ·
              refine ⟨14398738789924422224580631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19198318386565896299440841 14398738789924422224580631)
              ·
                refine ⟨21598108184886633336870947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14398738789924422224580631 21598108184886633336870947)
                ·
                  refine ⟨32397162277329950005306421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21598108184886633336870947 32397162277329950005306421)
                  ·
                    refine ⟨3037233963499682812997477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 32397162277329950005306421 3037233963499682812997477)
                    ·
                      refine ⟨569481368156190527437027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3037233963499682812997477 569481368156190527437027)
                      ·
                        rfl

theorem cell23_1109061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 1, 1, 5, 4].length) (baseStart_1109061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1109061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1109061 prefixEnd_1109061 := by exact prefixLift 1109061
  have htrace : WordTrace (prefixWord ++ tailWord_1109061) baseStart_1109061 baseEnd_1109061 := by
    simpa [prefixWord, tailWord_1109061, baseEnd_1109061] using wordTrace_append hprefix tailTrace_1109061
  have hstable : (prefixWord ++ tailWord_1109061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1109061).length < 2 ^ (prefixWord ++ tailWord_1109061).sum := by decide
  have hdescent : baseEnd_1109061 < baseStart_1109061 := by decide
  rcases family_descends (prefixWord ++ tailWord_1109061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1109098 : List Nat := [3, 1, 3, 2, 2, 1, 1, 1, 1, 3, 5]
def baseStart_1109098 : Nat := 118140960795 + 1109098 * 2 ^ 59
def prefixEnd_1109098 : Nat := 4983230072969 + 3 ^ 40 * 1109098 * 2
def baseEnd_1109098 : Nat := 569500366940406882674357

theorem tailTrace_1109098 : CollatzResearch.WordTrace tailWord_1109098 prefixEnd_1109098 569500366940406882674357 := by
  unfold tailWord_1109098
  simp only [CollatzResearch.WordTrace]
  refine ⟨10113031833983709925775987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26968084890623226468735965 10113031833983709925775987)
  ·
    refine ⟨15169547750975564888663981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10113031833983709925775987 15169547750975564888663981)
    ·
      refine ⟨5688580406615836833248993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15169547750975564888663981 5688580406615836833248993)
      ·
        refine ⟨4266435304961877624936745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5688580406615836833248993 4266435304961877624936745)
        ·
          refine ⟨3199826478721408218702559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4266435304961877624936745 3199826478721408218702559)
          ·
            refine ⟨4799739718082112328053839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3199826478721408218702559 4799739718082112328053839)
            ·
              refine ⟨7199609577123168492080759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4799739718082112328053839 7199609577123168492080759)
              ·
                refine ⟨10799414365684752738121139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7199609577123168492080759 10799414365684752738121139)
                ·
                  refine ⟨16199121548527129107181709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10799414365684752738121139 16199121548527129107181709)
                  ·
                    refine ⟨6074670580697673415193141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16199121548527129107181709 6074670580697673415193141)
                    ·
                      refine ⟨569500366940406882674357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6074670580697673415193141 569500366940406882674357)
                      ·
                        rfl

theorem cell23_1109098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 1, 1, 3, 5].length) (baseStart_1109098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1109098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1109098 prefixEnd_1109098 := by exact prefixLift 1109098
  have htrace : WordTrace (prefixWord ++ tailWord_1109098) baseStart_1109098 baseEnd_1109098 := by
    simpa [prefixWord, tailWord_1109098, baseEnd_1109098] using wordTrace_append hprefix tailTrace_1109098
  have hstable : (prefixWord ++ tailWord_1109098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1109098).length < 2 ^ (prefixWord ++ tailWord_1109098).sum := by decide
  have hdescent : baseEnd_1109098 < baseStart_1109098 := by decide
  rcases family_descends (prefixWord ++ tailWord_1109098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1109111 : List Nat := [1, 1, 3, 1, 1, 4, 1, 1, 1, 2, 7]
def baseStart_1109111 : Nat := 118140960795 + 1109111 * 2 ^ 59
def prefixEnd_1109111 : Nat := 4983230072969 + 3 ^ 40 * 1109111 * 2
def baseEnd_1109111 : Nat := 569507042188915331811797

theorem tailTrace_1109111 : CollatzResearch.WordTrace tailWord_1109111 prefixEnd_1109111 569507042188915331811797 := by
  unfold tailWord_1109111
  simp only [CollatzResearch.WordTrace]
  refine ⟨40452601484887742923327187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26968400989925161948884791 40452601484887742923327187)
  ·
    refine ⟨60678902227331614384990781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40452601484887742923327187 60678902227331614384990781)
    ·
      refine ⟨22754588335249355394371543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60678902227331614384990781 22754588335249355394371543)
      ·
        refine ⟨34131882502874033091557315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22754588335249355394371543 34131882502874033091557315)
        ·
          refine ⟨51197823754311049637335973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34131882502874033091557315 51197823754311049637335973)
          ·
            refine ⟨9599591953933321807000495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 51197823754311049637335973 9599591953933321807000495)
            ·
              refine ⟨14399387930899982710500743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9599591953933321807000495 14399387930899982710500743)
              ·
                refine ⟨21599081896349974065751115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14399387930899982710500743 21599081896349974065751115)
                ·
                  refine ⟨32398622844524961098626673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21599081896349974065751115 32398622844524961098626673)
                  ·
                    refine ⟨24298967133393720823970005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 32398622844524961098626673 24298967133393720823970005)
                    ·
                      refine ⟨569507042188915331811797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 24298967133393720823970005 569507042188915331811797)
                      ·
                        rfl

theorem cell23_1109111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 1, 1, 2, 7].length) (baseStart_1109111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1109111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1109111 prefixEnd_1109111 := by exact prefixLift 1109111
  have htrace : WordTrace (prefixWord ++ tailWord_1109111) baseStart_1109111 baseEnd_1109111 := by
    simpa [prefixWord, tailWord_1109111, baseEnd_1109111] using wordTrace_append hprefix tailTrace_1109111
  have hstable : (prefixWord ++ tailWord_1109111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1109111).length < 2 ^ (prefixWord ++ tailWord_1109111).sum := by decide
  have hdescent : baseEnd_1109111 < baseStart_1109111 := by decide
  rcases family_descends (prefixWord ++ tailWord_1109111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1109129 : List Nat := [1, 2, 1, 1, 4, 3, 4, 1, 2, 2, 2]
def baseStart_1109129 : Nat := 118140960795 + 1109129 * 2 ^ 59
def prefixEnd_1109129 : Nat := 4983230072969 + 3 ^ 40 * 1109129 * 2
def baseEnd_1109129 : Nat := 569516284840696261386715

theorem tailTrace_1109129 : CollatzResearch.WordTrace tailWord_1109129 prefixEnd_1109129 569516284840696261386715 := by
  unfold tailWord_1109129
  simp only [CollatzResearch.WordTrace]
  refine ⟨40453257998822531997482441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26968838665881687998321627 40453257998822531997482441)
  ·
    refine ⟨30339943499116898998111831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40453257998822531997482441 30339943499116898998111831)
    ·
      refine ⟨45509915248675348497167747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30339943499116898998111831 45509915248675348497167747)
      ·
        refine ⟨68264872873013022745751621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45509915248675348497167747 68264872873013022745751621)
        ·
          refine ⟨12799663663689941764828429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 68264872873013022745751621 12799663663689941764828429)
          ·
            refine ⟨4799873873883728161810661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12799663663689941764828429 4799873873883728161810661)
            ·
              refine ⟨899976351353199030339499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4799873873883728161810661 899976351353199030339499)
              ·
                refine ⟨1349964527029798545509249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 899976351353199030339499 1349964527029798545509249)
                ·
                  refine ⟨1012473395272348909131937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1349964527029798545509249 1012473395272348909131937)
                  ·
                    refine ⟨759355046454261681848953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1012473395272348909131937 759355046454261681848953)
                    ·
                      refine ⟨569516284840696261386715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 759355046454261681848953 569516284840696261386715)
                      ·
                        rfl

theorem cell23_1109129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 4, 1, 2, 2, 2].length) (baseStart_1109129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1109129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1109129 prefixEnd_1109129 := by exact prefixLift 1109129
  have htrace : WordTrace (prefixWord ++ tailWord_1109129) baseStart_1109129 baseEnd_1109129 := by
    simpa [prefixWord, tailWord_1109129, baseEnd_1109129] using wordTrace_append hprefix tailTrace_1109129
  have hstable : (prefixWord ++ tailWord_1109129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1109129).length < 2 ^ (prefixWord ++ tailWord_1109129).sum := by decide
  have hdescent : baseEnd_1109129 < baseStart_1109129 := by decide
  rcases family_descends (prefixWord ++ tailWord_1109129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1109131 : List Nat := [1, 1, 1, 1, 4, 1, 1, 3, 3, 7]
def baseStart_1109131 : Nat := 118140960795 + 1109131 * 2 ^ 59
def prefixEnd_1109131 : Nat := 4983230072969 + 3 ^ 40 * 1109131 * 2
def baseEnd_1109131 : Nat := 189839103934001751187235

theorem tailTrace_1109131 : CollatzResearch.WordTrace tailWord_1109131 prefixEnd_1109131 189839103934001751187235 := by
  unfold tailWord_1109131
  simp only [CollatzResearch.WordTrace]
  refine ⟨40453330944815286339055247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26968887296543524226036831 40453330944815286339055247)
  ·
    refine ⟨60679996417222929508582871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40453330944815286339055247 60679996417222929508582871)
    ·
      refine ⟨91019994625834394262874307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60679996417222929508582871 91019994625834394262874307)
      ·
        refine ⟨136529991938751591394311461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91019994625834394262874307 136529991938751591394311461)
        ·
          refine ⟨25599373488515923386433399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 136529991938751591394311461 25599373488515923386433399)
          ·
            refine ⟨38399060232773885079650099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25599373488515923386433399 38399060232773885079650099)
            ·
              refine ⟨57598590349160827619475149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38399060232773885079650099 57598590349160827619475149)
              ·
                refine ⟨21599471380935310357303181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 57598590349160827619475149 21599471380935310357303181)
                ·
                  refine ⟨8099801767850741383988693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21599471380935310357303181 8099801767850741383988693)
                  ·
                    refine ⟨189839103934001751187235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 8099801767850741383988693 189839103934001751187235)
                    ·
                      rfl

theorem cell23_1109131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 3, 3, 7].length) (baseStart_1109131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1109131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1109131 prefixEnd_1109131 := by exact prefixLift 1109131
  have htrace : WordTrace (prefixWord ++ tailWord_1109131) baseStart_1109131 baseEnd_1109131 := by
    simpa [prefixWord, tailWord_1109131, baseEnd_1109131] using wordTrace_append hprefix tailTrace_1109131
  have hstable : (prefixWord ++ tailWord_1109131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1109131).length < 2 ^ (prefixWord ++ tailWord_1109131).sum := by decide
  have hdescent : baseEnd_1109131 < baseStart_1109131 := by decide
  rcases family_descends (prefixWord ++ tailWord_1109131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1109161 : List Nat := [1, 2, 1, 1, 1, 1, 2, 1, 3, 10]
def baseStart_1109161 : Nat := 118140960795 + 1109161 * 2 ^ 59
def prefixEnd_1109161 : Nat := 4983230072969 + 3 ^ 40 * 1109161 * 2
def baseEnd_1109161 : Nat := 189844238740546712062189

theorem tailTrace_1109161 : CollatzResearch.WordTrace tailWord_1109161 prefixEnd_1109161 189844238740546712062189 := by
  unfold tailWord_1109161
  simp only [CollatzResearch.WordTrace]
  refine ⟨40454425134706601462647337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26969616756471067641764891 40454425134706601462647337)
  ·
    refine ⟨30340818851029951096985503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40454425134706601462647337 30340818851029951096985503)
    ·
      refine ⟨45511228276544926645478255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30340818851029951096985503 45511228276544926645478255)
      ·
        refine ⟨68266842414817389968217383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45511228276544926645478255 68266842414817389968217383)
        ·
          refine ⟨102400263622226084952326075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68266842414817389968217383 102400263622226084952326075)
          ·
            refine ⟨153600395433339127428489113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 102400263622226084952326075 153600395433339127428489113)
            ·
              refine ⟨115200296575004345571366835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 153600395433339127428489113 115200296575004345571366835)
              ·
                refine ⟨172800444862506518357050253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 115200296575004345571366835 172800444862506518357050253)
                ·
                  refine ⟨64800166823439944383893845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 172800444862506518357050253 64800166823439944383893845)
                  ·
                    refine ⟨189844238740546712062189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 64800166823439944383893845 189844238740546712062189)
                    ·
                      rfl

theorem cell23_1109161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 3, 10].length) (baseStart_1109161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1109161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1109161 prefixEnd_1109161 := by exact prefixLift 1109161
  have htrace : WordTrace (prefixWord ++ tailWord_1109161) baseStart_1109161 baseEnd_1109161 := by
    simpa [prefixWord, tailWord_1109161, baseEnd_1109161] using wordTrace_append hprefix tailTrace_1109161
  have hstable : (prefixWord ++ tailWord_1109161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1109161).length < 2 ^ (prefixWord ++ tailWord_1109161).sum := by decide
  have hdescent : baseEnd_1109161 < baseStart_1109161 := by decide
  rcases family_descends (prefixWord ++ tailWord_1109161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1109169 : List Nat := [1, 2, 2, 5, 1, 3, 2, 2, 5]
def baseStart_1109169 : Nat := 118140960795 + 1109169 * 2 ^ 59
def prefixEnd_1109169 : Nat := 4983230072969 + 3 ^ 40 * 1109169 * 2
def baseEnd_1109169 : Nat := 63281869340764011654059

theorem tailTrace_1109169 : CollatzResearch.WordTrace tailWord_1109169 prefixEnd_1109169 63281869340764011654059 := by
  unfold tailWord_1109169
  simp only [CollatzResearch.WordTrace]
  refine ⟨40454716918677618828938561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26969811279118412552625707 40454716918677618828938561)
  ·
    refine ⟨30341037689008214121703921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40454716918677618828938561 30341037689008214121703921)
    ·
      refine ⟨22755778266756160591277941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30341037689008214121703921 22755778266756160591277941)
      ·
        refine ⟨2133354212508390055432307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 22755778266756160591277941 2133354212508390055432307)
        ·
          refine ⟨3200031318762585083148461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2133354212508390055432307 3200031318762585083148461)
          ·
            refine ⟨1200011744535969406180673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3200031318762585083148461 1200011744535969406180673)
            ·
              refine ⟨900008808401977054635505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1200011744535969406180673 900008808401977054635505)
              ·
                refine ⟨675006606301482790976629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 900008808401977054635505 675006606301482790976629)
                ·
                  refine ⟨63281869340764011654059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 675006606301482790976629 63281869340764011654059)
                  ·
                    rfl

theorem cell23_1109169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 3, 2, 2, 5].length) (baseStart_1109169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1109169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1109169 prefixEnd_1109169 := by exact prefixLift 1109169
  have htrace : WordTrace (prefixWord ++ tailWord_1109169) baseStart_1109169 baseEnd_1109169 := by
    simpa [prefixWord, tailWord_1109169, baseEnd_1109169] using wordTrace_append hprefix tailTrace_1109169
  have hstable : (prefixWord ++ tailWord_1109169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1109169).length < 2 ^ (prefixWord ++ tailWord_1109169).sum := by decide
  have hdescent : baseEnd_1109169 < baseStart_1109169 := by decide
  rcases family_descends (prefixWord ++ tailWord_1109169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1109228 : List Nat := [2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 6]
def baseStart_1109228 : Nat := 118140960795 + 1109228 * 2 ^ 59
def prefixEnd_1109228 : Nat := 4983230072969 + 3 ^ 40 * 1109228 * 2
def baseEnd_1109228 : Nat := 569567119425491374048759

theorem tailTrace_1109228 : CollatzResearch.WordTrace tailWord_1109228 prefixEnd_1109228 569567119425491374048759 := by
  unfold tailWord_1109228
  simp only [CollatzResearch.WordTrace]
  refine ⟨20228434412731935952668169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26971245883642581270224225 20228434412731935952668169)
  ·
    refine ⟨15171325809548951964501127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20228434412731935952668169 15171325809548951964501127)
    ·
      refine ⟨22756988714323427946751691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15171325809548951964501127 22756988714323427946751691)
      ·
        refine ⟨34135483071485141920127537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22756988714323427946751691 34135483071485141920127537)
        ·
          refine ⟨25601612303613856440095653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34135483071485141920127537 25601612303613856440095653)
          ·
            refine ⟨4800302306927598082517935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25601612303613856440095653 4800302306927598082517935)
            ·
              refine ⟨7200453460391397123776903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4800302306927598082517935 7200453460391397123776903)
              ·
                refine ⟨10800680190587095685665355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7200453460391397123776903 10800680190587095685665355)
                ·
                  refine ⟨16201020285880643528498033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10800680190587095685665355 16201020285880643528498033)
                  ·
                    refine ⟨12150765214410482646373525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16201020285880643528498033 12150765214410482646373525)
                    ·
                      refine ⟨569567119425491374048759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 12150765214410482646373525 569567119425491374048759)
                      ·
                        rfl

theorem cell23_1109228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 6].length) (baseStart_1109228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1109228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1109228 prefixEnd_1109228 := by exact prefixLift 1109228
  have htrace : WordTrace (prefixWord ++ tailWord_1109228) baseStart_1109228 baseEnd_1109228 := by
    simpa [prefixWord, tailWord_1109228, baseEnd_1109228] using wordTrace_append hprefix tailTrace_1109228
  have hstable : (prefixWord ++ tailWord_1109228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1109228).length < 2 ^ (prefixWord ++ tailWord_1109228).sum := by decide
  have hdescent : baseEnd_1109228 < baseStart_1109228 := by decide
  rcases family_descends (prefixWord ++ tailWord_1109228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1109229 : List Nat := [1, 5, 1, 2, 2, 1, 2, 4, 1, 4]
def baseStart_1109229 : Nat := 118140960795 + 1109229 * 2 ^ 59
def prefixEnd_1109229 : Nat := 4983230072969 + 3 ^ 40 * 1109229 * 2
def baseEnd_1109229 : Nat := 189855877635381956712085

theorem tailTrace_1109229 : CollatzResearch.WordTrace tailWord_1109229 prefixEnd_1109229 189855877635381956712085 := by
  unfold tailWord_1109229
  simp only [CollatzResearch.WordTrace]
  refine ⟨40456905298460249076122741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26971270198973499384081827 40456905298460249076122741)
  ·
    refine ⟨3792834871730648350886507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 40456905298460249076122741 3792834871730648350886507)
    ·
      refine ⟨5689252307595972526329761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3792834871730648350886507 5689252307595972526329761)
      ·
        refine ⟨4266939230696979394747321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5689252307595972526329761 4266939230696979394747321)
        ·
          refine ⟨3200204423022734546060491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4266939230696979394747321 3200204423022734546060491)
          ·
            refine ⟨4800306634534101819090737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3200204423022734546060491 4800306634534101819090737)
            ·
              refine ⟨3600229975900576364318053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4800306634534101819090737 3600229975900576364318053)
              ·
                refine ⟨675043120481358068309635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3600229975900576364318053 675043120481358068309635)
                ·
                  refine ⟨1012564680722037102464453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 675043120481358068309635 1012564680722037102464453)
                  ·
                    refine ⟨189855877635381956712085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1012564680722037102464453 189855877635381956712085)
                    ·
                      rfl

theorem cell23_1109229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 2, 4, 1, 4].length) (baseStart_1109229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1109229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1109229 prefixEnd_1109229 := by exact prefixLift 1109229
  have htrace : WordTrace (prefixWord ++ tailWord_1109229) baseStart_1109229 baseEnd_1109229 := by
    simpa [prefixWord, tailWord_1109229, baseEnd_1109229] using wordTrace_append hprefix tailTrace_1109229
  have hstable : (prefixWord ++ tailWord_1109229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1109229).length < 2 ^ (prefixWord ++ tailWord_1109229).sum := by decide
  have hdescent : baseEnd_1109229 < baseStart_1109229 := by decide
  rcases family_descends (prefixWord ++ tailWord_1109229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1109262 : List Nat := [4, 1, 1, 2, 1, 3, 2, 1, 1, 5, 2]
def baseStart_1109262 : Nat := 118140960795 + 1109262 * 2 ^ 59
def prefixEnd_1109262 : Nat := 4983230072969 + 3 ^ 40 * 1109262 * 2
def baseEnd_1109262 : Nat := 569584577767744241023603

theorem tailTrace_1109262 : CollatzResearch.WordTrace tailWord_1109262 prefixEnd_1109262 569584577767744241023603 := by
  unfold tailWord_1109262
  simp only [CollatzResearch.WordTrace]
  refine ⟨5057263613417586964009255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26972072604893797141382693 5057263613417586964009255)
  ·
    refine ⟨7585895420126380446013883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5057263613417586964009255 7585895420126380446013883)
    ·
      refine ⟨11378843130189570669020825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7585895420126380446013883 11378843130189570669020825)
      ·
        refine ⟨8534132347642178001765619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11378843130189570669020825 8534132347642178001765619)
        ·
          refine ⟨12801198521463267002648429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8534132347642178001765619 12801198521463267002648429)
          ·
            refine ⟨4800449445548725125993161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12801198521463267002648429 4800449445548725125993161)
            ·
              refine ⟨3600337084161543844494871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4800449445548725125993161 3600337084161543844494871)
              ·
                refine ⟨5400505626242315766742307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3600337084161543844494871 5400505626242315766742307)
                ·
                  refine ⟨8100758439363473650113461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5400505626242315766742307 8100758439363473650113461)
                  ·
                    refine ⟨759446103690325654698137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8100758439363473650113461 759446103690325654698137)
                    ·
                      refine ⟨569584577767744241023603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 759446103690325654698137 569584577767744241023603)
                      ·
                        rfl

theorem cell23_1109262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 2, 1, 1, 5, 2].length) (baseStart_1109262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1109262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1109262 prefixEnd_1109262 := by exact prefixLift 1109262
  have htrace : WordTrace (prefixWord ++ tailWord_1109262) baseStart_1109262 baseEnd_1109262 := by
    simpa [prefixWord, tailWord_1109262, baseEnd_1109262] using wordTrace_append hprefix tailTrace_1109262
  have hstable : (prefixWord ++ tailWord_1109262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1109262).length < 2 ^ (prefixWord ++ tailWord_1109262).sum := by decide
  have hdescent : baseEnd_1109262 < baseStart_1109262 := by decide
  rcases family_descends (prefixWord ++ tailWord_1109262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1109279 : List Nat := [1, 1, 2, 4, 4, 1, 1, 2, 2, 3, 2]
def baseStart_1109279 : Nat := 118140960795 + 1109279 * 2 ^ 59
def prefixEnd_1109279 : Nat := 4983230072969 + 3 ^ 40 * 1109279 * 2
def baseEnd_1109279 : Nat := 569593306938870674511025

theorem tailTrace_1109279 : CollatzResearch.WordTrace tailWord_1109279 prefixEnd_1109279 569593306938870674511025 := by
  unfold tailWord_1109279
  simp only [CollatzResearch.WordTrace]
  refine ⟨40458728948279107615442891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26972485965519405076961927 40458728948279107615442891)
  ·
    refine ⟨60688093422418661423164337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40458728948279107615442891 60688093422418661423164337)
    ·
      refine ⟨45516070066813996067373253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60688093422418661423164337 45516070066813996067373253)
      ·
        refine ⟨8534263137527624262632485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 45516070066813996067373253 8534263137527624262632485)
        ·
          refine ⟨1600174338286429549243591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8534263137527624262632485 1600174338286429549243591)
          ·
            refine ⟨2400261507429644323865387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1600174338286429549243591 2400261507429644323865387)
            ·
              refine ⟨3600392261144466485798081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2400261507429644323865387 3600392261144466485798081)
              ·
                refine ⟨2700294195858349864348561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3600392261144466485798081 2700294195858349864348561)
                ·
                  refine ⟨2025220646893762398261421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2700294195858349864348561 2025220646893762398261421)
                  ·
                    refine ⟨759457742585160899348033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2025220646893762398261421 759457742585160899348033)
                    ·
                      refine ⟨569593306938870674511025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 759457742585160899348033 569593306938870674511025)
                      ·
                        rfl

theorem cell23_1109279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 1, 2, 2, 3, 2].length) (baseStart_1109279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1109279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1109279 prefixEnd_1109279 := by exact prefixLift 1109279
  have htrace : WordTrace (prefixWord ++ tailWord_1109279) baseStart_1109279 baseEnd_1109279 := by
    simpa [prefixWord, tailWord_1109279, baseEnd_1109279] using wordTrace_append hprefix tailTrace_1109279
  have hstable : (prefixWord ++ tailWord_1109279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1109279).length < 2 ^ (prefixWord ++ tailWord_1109279).sum := by decide
  have hdescent : baseEnd_1109279 < baseStart_1109279 := by decide
  rcases family_descends (prefixWord ++ tailWord_1109279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1109295 : List Nat := [1, 1, 2, 1, 2, 1, 3, 4, 3, 2, 3]
def baseStart_1109295 : Nat := 118140960795 + 1109295 * 2 ^ 59
def prefixEnd_1109295 : Nat := 4983230072969 + 3 ^ 40 * 1109295 * 2
def baseEnd_1109295 : Nat := 569601522629342611910951

theorem tailTrace_1109295 : CollatzResearch.WordTrace tailWord_1109295 prefixEnd_1109295 569601522629342611910951 := by
  unfold tailWord_1109295
  simp only [CollatzResearch.WordTrace]
  refine ⟨40459312516221142348025339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26972875010814094898683559 40459312516221142348025339)
  ·
    refine ⟨60688968774331713522038009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40459312516221142348025339 60688968774331713522038009)
    ·
      refine ⟨45516726580748785141528507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60688968774331713522038009 45516726580748785141528507)
      ·
        refine ⟨68275089871123177712292761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45516726580748785141528507 68275089871123177712292761)
        ·
          refine ⟨51206317403342383284219571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68275089871123177712292761 51206317403342383284219571)
          ·
            refine ⟨76809476105013574926329357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51206317403342383284219571 76809476105013574926329357)
            ·
              refine ⟨28803553539380090597373509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 76809476105013574926329357 28803553539380090597373509)
              ·
                refine ⟨5400666288633766987007533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28803553539380090597373509 5400666288633766987007533)
                ·
                  refine ⟨2025249858237662620127825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5400666288633766987007533 2025249858237662620127825)
                  ·
                    refine ⟨1518937393678246965095869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2025249858237662620127825 1518937393678246965095869)
                    ·
                      refine ⟨569601522629342611910951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1518937393678246965095869 569601522629342611910951)
                      ·
                        rfl

theorem cell23_1109295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 4, 3, 2, 3].length) (baseStart_1109295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1109295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1109295 prefixEnd_1109295 := by exact prefixLift 1109295
  have htrace : WordTrace (prefixWord ++ tailWord_1109295) baseStart_1109295 baseEnd_1109295 := by
    simpa [prefixWord, tailWord_1109295, baseEnd_1109295] using wordTrace_append hprefix tailTrace_1109295
  have hstable : (prefixWord ++ tailWord_1109295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1109295).length < 2 ^ (prefixWord ++ tailWord_1109295).sum := by decide
  have hdescent : baseEnd_1109295 < baseStart_1109295 := by decide
  rcases family_descends (prefixWord ++ tailWord_1109295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1109309 : List Nat := [1, 4, 1, 5, 1, 1, 1, 1, 3, 1, 4]
def baseStart_1109309 : Nat := 118140960795 + 1109309 * 2 ^ 59
def prefixEnd_1109309 : Nat := 4983230072969 + 3 ^ 40 * 1109309 * 2
def baseEnd_1109309 : Nat := 569608711358505557135887

theorem tailTrace_1109309 : CollatzResearch.WordTrace tailWord_1109309 prefixEnd_1109309 569608711358505557135887 := by
  unfold tailWord_1109309
  simp only [CollatzResearch.WordTrace]
  refine ⟨40459823138170422739034981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26973215425446948492689987 40459823138170422739034981)
  ·
    refine ⟨7586216838406954263569059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 40459823138170422739034981 7586216838406954263569059)
    ·
      refine ⟨11379325257610431395353589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7586216838406954263569059 11379325257610431395353589)
      ·
        refine ⟨1066811742900977943314399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 11379325257610431395353589 1066811742900977943314399)
        ·
          refine ⟨1600217614351466914971599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1066811742900977943314399 1600217614351466914971599)
          ·
            refine ⟨2400326421527200372457399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1600217614351466914971599 2400326421527200372457399)
            ·
              refine ⟨3600489632290800558686099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2400326421527200372457399 3600489632290800558686099)
              ·
                refine ⟨5400734448436200838029149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3600489632290800558686099 5400734448436200838029149)
                ·
                  refine ⟨2025275418163575314260931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5400734448436200838029149 2025275418163575314260931)
                  ·
                    refine ⟨3037913127245362971391397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2025275418163575314260931 3037913127245362971391397)
                    ·
                      refine ⟨569608711358505557135887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3037913127245362971391397 569608711358505557135887)
                      ·
                        rfl

theorem cell23_1109309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 1, 1, 3, 1, 4].length) (baseStart_1109309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1109309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1109309 prefixEnd_1109309 := by exact prefixLift 1109309
  have htrace : WordTrace (prefixWord ++ tailWord_1109309) baseStart_1109309 baseEnd_1109309 := by
    simpa [prefixWord, tailWord_1109309, baseEnd_1109309] using wordTrace_append hprefix tailTrace_1109309
  have hstable : (prefixWord ++ tailWord_1109309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1109309).length < 2 ^ (prefixWord ++ tailWord_1109309).sum := by decide
  have hdescent : baseEnd_1109309 < baseStart_1109309 := by decide
  rcases family_descends (prefixWord ++ tailWord_1109309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1109326 : List Nat := [4, 1, 1, 1, 1, 1, 4, 5, 1, 2, 2]
def baseStart_1109326 : Nat := 118140960795 + 1109326 * 2 ^ 59
def prefixEnd_1109326 : Nat := 4983230072969 + 3 ^ 40 * 1109326 * 2
def baseEnd_1109326 : Nat := 569617440529631990623309

theorem tailTrace_1109326 : CollatzResearch.WordTrace tailWord_1109326 prefixEnd_1109326 569617440529631990623309 := by
  unfold tailWord_1109326
  simp only [CollatzResearch.WordTrace]
  refine ⟨5057555397388604330300479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26973628786072556428269221 5057555397388604330300479)
  ·
    refine ⟨7586333096082906495450719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5057555397388604330300479 7586333096082906495450719)
    ·
      refine ⟨11379499644124359743176079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7586333096082906495450719 11379499644124359743176079)
      ·
        refine ⟨17069249466186539614764119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11379499644124359743176079 17069249466186539614764119)
        ·
          refine ⟨25603874199279809422146179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17069249466186539614764119 25603874199279809422146179)
          ·
            refine ⟨38405811298919714133219269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25603874199279809422146179 38405811298919714133219269)
            ·
              refine ⟨7201089618547446399978613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38405811298919714133219269 7201089618547446399978613)
              ·
                refine ⟨675102151738823099997995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7201089618547446399978613 675102151738823099997995)
                ·
                  refine ⟨1012653227608234649996993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 675102151738823099997995 1012653227608234649996993)
                  ·
                    refine ⟨759489920706175987497745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1012653227608234649996993 759489920706175987497745)
                    ·
                      refine ⟨569617440529631990623309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 759489920706175987497745 569617440529631990623309)
                      ·
                        rfl

theorem cell23_1109326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 5, 1, 2, 2].length) (baseStart_1109326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1109326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1109326 prefixEnd_1109326 := by exact prefixLift 1109326
  have htrace : WordTrace (prefixWord ++ tailWord_1109326) baseStart_1109326 baseEnd_1109326 := by
    simpa [prefixWord, tailWord_1109326, baseEnd_1109326] using wordTrace_append hprefix tailTrace_1109326
  have hstable : (prefixWord ++ tailWord_1109326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1109326).length < 2 ^ (prefixWord ++ tailWord_1109326).sum := by decide
  have hdescent : baseEnd_1109326 < baseStart_1109326 := by decide
  rcases family_descends (prefixWord ++ tailWord_1109326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1109329 : List Nat := [1, 2, 2, 1, 4, 1, 5, 1, 1, 2, 3]
def baseStart_1109329 : Nat := 118140960795 + 1109329 * 2 ^ 59
def prefixEnd_1109329 : Nat := 4983230072969 + 3 ^ 40 * 1109329 * 2
def baseEnd_1109329 : Nat := 569618980971595478885795

theorem tailTrace_1109329 : CollatzResearch.WordTrace tailWord_1109329 prefixEnd_1109329 569618980971595478885795 := by
  unfold tailWord_1109329
  simp only [CollatzResearch.WordTrace]
  refine ⟨40460552598097966154763041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26973701732065310769842027 40460552598097966154763041)
  ·
    refine ⟨30345414448573474616072281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40460552598097966154763041 30345414448573474616072281)
    ·
      refine ⟨22759060836430105962054211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30345414448573474616072281 22759060836430105962054211)
      ·
        refine ⟨34138591254645158943081317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22759060836430105962054211 34138591254645158943081317)
        ·
          refine ⟨6400985860245967301827747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34138591254645158943081317 6400985860245967301827747)
          ·
            refine ⟨9601478790368950952741621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6400985860245967301827747 9601478790368950952741621)
            ·
              refine ⟨900138636597089151819527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9601478790368950952741621 900138636597089151819527)
              ·
                refine ⟨1350207954895633727729291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 900138636597089151819527 1350207954895633727729291)
                ·
                  refine ⟨2025311932343450591593937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1350207954895633727729291 2025311932343450591593937)
                  ·
                    refine ⟨1518983949257587943695453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2025311932343450591593937 1518983949257587943695453)
                    ·
                      refine ⟨569618980971595478885795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1518983949257587943695453 569618980971595478885795)
                      ·
                        rfl

theorem cell23_1109329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 5, 1, 1, 2, 3].length) (baseStart_1109329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1109329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1109329 prefixEnd_1109329 := by exact prefixLift 1109329
  have htrace : WordTrace (prefixWord ++ tailWord_1109329) baseStart_1109329 baseEnd_1109329 := by
    simpa [prefixWord, tailWord_1109329, baseEnd_1109329] using wordTrace_append hprefix tailTrace_1109329
  have hstable : (prefixWord ++ tailWord_1109329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1109329).length < 2 ^ (prefixWord ++ tailWord_1109329).sum := by decide
  have hdescent : baseEnd_1109329 < baseStart_1109329 := by decide
  rcases family_descends (prefixWord ++ tailWord_1109329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1109452 : List Nat := [2, 2, 1, 4, 2, 1, 1, 1, 4, 5]
def baseStart_1109452 : Nat := 118140960795 + 1109452 * 2 ^ 59
def prefixEnd_1109452 : Nat := 4983230072969 + 3 ^ 40 * 1109452 * 2
def baseEnd_1109452 : Nat := 189894046364032832549243

theorem tailTrace_1109452 : CollatzResearch.WordTrace tailWord_1109452 prefixEnd_1109452 189894046364032832549243 := by
  unfold tailWord_1109452
  simp only [CollatzResearch.WordTrace]
  refine ⟨20232519388326179080745305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26976692517768238774327073 20232519388326179080745305)
  ·
    refine ⟨15174389541244634310558979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20232519388326179080745305 15174389541244634310558979)
    ·
      refine ⟨22761584311866951465838469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15174389541244634310558979 22761584311866951465838469)
      ·
        refine ⟨4267797058475053399844713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22761584311866951465838469 4267797058475053399844713)
        ·
          refine ⟨3200847793856290049883535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4267797058475053399844713 3200847793856290049883535)
          ·
            refine ⟨4801271690784435074825303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3200847793856290049883535 4801271690784435074825303)
            ·
              refine ⟨7201907536176652612237955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4801271690784435074825303 7201907536176652612237955)
              ·
                refine ⟨10802861304264978918356933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7201907536176652612237955 10802861304264978918356933)
                ·
                  refine ⟨2025536494549683547191925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10802861304264978918356933 2025536494549683547191925)
                  ·
                    refine ⟨189894046364032832549243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2025536494549683547191925 189894046364032832549243)
                    ·
                      rfl

theorem cell23_1109452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 1, 4, 5].length) (baseStart_1109452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1109452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1109452 prefixEnd_1109452 := by exact prefixLift 1109452
  have htrace : WordTrace (prefixWord ++ tailWord_1109452) baseStart_1109452 baseEnd_1109452 := by
    simpa [prefixWord, tailWord_1109452, baseEnd_1109452] using wordTrace_append hprefix tailTrace_1109452
  have hstable : (prefixWord ++ tailWord_1109452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1109452).length < 2 ^ (prefixWord ++ tailWord_1109452).sum := by decide
  have hdescent : baseEnd_1109452 < baseStart_1109452 := by decide
  rcases family_descends (prefixWord ++ tailWord_1109452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1109489 : List Nat := [1, 2, 2, 2, 3, 3, 2, 1, 2, 1, 4]
def baseStart_1109489 : Nat := 118140960795 + 1109489 * 2 ^ 59
def prefixEnd_1109489 : Nat := 4983230072969 + 3 ^ 40 * 1109489 * 2
def baseEnd_1109489 : Nat := 569701137876314852885059

theorem tailTrace_1109489 : CollatzResearch.WordTrace tailWord_1109489 prefixEnd_1109489 569701137876314852885059 := by
  unfold tailWord_1109489
  simp only [CollatzResearch.WordTrace]
  refine ⟨40466388277518313480587521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26977592185012208987058347 40466388277518313480587521)
  ·
    refine ⟨30349791208138735110440641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40466388277518313480587521 30349791208138735110440641)
    ·
      refine ⟨22762343406104051332830481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30349791208138735110440641 22762343406104051332830481)
      ·
        refine ⟨17071757554578038499622861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22762343406104051332830481 17071757554578038499622861)
        ·
          refine ⟨6401909082966764437358573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17071757554578038499622861 6401909082966764437358573)
          ·
            refine ⟨2400715906112536664009465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6401909082966764437358573 2400715906112536664009465)
            ·
              refine ⟨1800536929584402498007099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2400715906112536664009465 1800536929584402498007099)
              ·
                refine ⟨2700805394376603747010649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1800536929584402498007099 2700805394376603747010649)
                ·
                  refine ⟨2025604045782452810257987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2700805394376603747010649 2025604045782452810257987)
                  ·
                    refine ⟨3038406068673679215386981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2025604045782452810257987 3038406068673679215386981)
                    ·
                      refine ⟨569701137876314852885059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3038406068673679215386981 569701137876314852885059)
                      ·
                        rfl

theorem cell23_1109489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 2, 1, 2, 1, 4].length) (baseStart_1109489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1109489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1109489 prefixEnd_1109489 := by exact prefixLift 1109489
  have htrace : WordTrace (prefixWord ++ tailWord_1109489) baseStart_1109489 baseEnd_1109489 := by
    simpa [prefixWord, tailWord_1109489, baseEnd_1109489] using wordTrace_append hprefix tailTrace_1109489
  have hstable : (prefixWord ++ tailWord_1109489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1109489).length < 2 ^ (prefixWord ++ tailWord_1109489).sum := by decide
  have hdescent : baseEnd_1109489 < baseStart_1109489 := by decide
  rcases family_descends (prefixWord ++ tailWord_1109489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1109495 : List Nat := [1, 1, 3, 1, 1, 1, 1, 6, 8]
def baseStart_1109495 : Nat := 118140960795 + 1109495 * 2 ^ 59
def prefixEnd_1109495 : Nat := 4983230072969 + 3 ^ 40 * 1109495 * 2
def baseEnd_1109495 : Nat := 63300468751137981045559

theorem tailTrace_1109495 : CollatzResearch.WordTrace tailWord_1109495 prefixEnd_1109495 63300468751137981045559 := by
  unfold tailWord_1109495
  simp only [CollatzResearch.WordTrace]
  refine ⟨40466607115496576505305939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26977738076997717670203959 40466607115496576505305939)
  ·
    refine ⟨60699910673244864757958909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40466607115496576505305939 60699910673244864757958909)
    ·
      refine ⟨22762466502466824284234591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60699910673244864757958909 22762466502466824284234591)
      ·
        refine ⟨34143699753700236426351887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22762466502466824284234591 34143699753700236426351887)
        ·
          refine ⟨51215549630550354639527831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34143699753700236426351887 51215549630550354639527831)
          ·
            refine ⟨76823324445825531959291747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51215549630550354639527831 76823324445825531959291747)
            ·
              refine ⟨115234986668738297938937621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76823324445825531959291747 115234986668738297938937621)
              ·
                refine ⟨5401640000097107715887701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 115234986668738297938937621 5401640000097107715887701)
                ·
                  refine ⟨63300468751137981045559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 5401640000097107715887701 63300468751137981045559)
                  ·
                    rfl

theorem cell23_1109495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 6, 8].length) (baseStart_1109495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1109495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1109495 prefixEnd_1109495 := by exact prefixLift 1109495
  have htrace : WordTrace (prefixWord ++ tailWord_1109495) baseStart_1109495 baseEnd_1109495 := by
    simpa [prefixWord, tailWord_1109495, baseEnd_1109495] using wordTrace_append hprefix tailTrace_1109495
  have hstable : (prefixWord ++ tailWord_1109495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1109495).length < 2 ^ (prefixWord ++ tailWord_1109495).sum := by decide
  have hdescent : baseEnd_1109495 < baseStart_1109495 := by decide
  rcases family_descends (prefixWord ++ tailWord_1109495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1109506 : List Nat := [3, 4, 1, 2, 1, 1, 2, 2, 2, 1, 4]
def baseStart_1109506 : Nat := 118140960795 + 1109506 * 2 ^ 59
def prefixEnd_1109506 : Nat := 4983230072969 + 3 ^ 40 * 1109506 * 2
def baseEnd_1109506 : Nat := 569709867047441286372481

theorem tailTrace_1109506 : CollatzResearch.WordTrace tailWord_1109506 prefixEnd_1109506 569709867047441286372481 := by
  unfold tailWord_1109506
  simp only [CollatzResearch.WordTrace]
  refine ⟨10116752079614181345989093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26978005545637816922637581 10116752079614181345989093)
  ·
    refine ⟨1896891014927659002372955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10116752079614181345989093 1896891014927659002372955)
    ·
      refine ⟨2845336522391488503559433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1896891014927659002372955 2845336522391488503559433)
      ·
        refine ⟨2134002391793616377669575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2845336522391488503559433 2134002391793616377669575)
        ·
          refine ⟨3201003587690424566504363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2134002391793616377669575 3201003587690424566504363)
          ·
            refine ⟨4801505381535636849756545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3201003587690424566504363 4801505381535636849756545)
            ·
              refine ⟨3601129036151727637317409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4801505381535636849756545 3601129036151727637317409)
              ·
                refine ⟨2700846777113795727988057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3601129036151727637317409 2700846777113795727988057)
                ·
                  refine ⟨2025635082835346795991043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2700846777113795727988057 2025635082835346795991043)
                  ·
                    refine ⟨3038452624253020193986565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2025635082835346795991043 3038452624253020193986565)
                    ·
                      refine ⟨569709867047441286372481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3038452624253020193986565 569709867047441286372481)
                      ·
                        rfl

theorem cell23_1109506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 2, 2, 2, 1, 4].length) (baseStart_1109506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1109506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1109506 prefixEnd_1109506 := by exact prefixLift 1109506
  have htrace : WordTrace (prefixWord ++ tailWord_1109506) baseStart_1109506 baseEnd_1109506 := by
    simpa [prefixWord, tailWord_1109506, baseEnd_1109506] using wordTrace_append hprefix tailTrace_1109506
  have hstable : (prefixWord ++ tailWord_1109506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1109506).length < 2 ^ (prefixWord ++ tailWord_1109506).sum := by decide
  have hdescent : baseEnd_1109506 < baseStart_1109506 := by decide
  rcases family_descends (prefixWord ++ tailWord_1109506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1109512 : List Nat := [2, 1, 3, 2, 1, 1, 3, 4, 6]
def baseStart_1109512 : Nat := 118140960795 + 1109512 * 2 ^ 59
def prefixEnd_1109512 : Nat := 4983230072969 + 3 ^ 40 * 1109512 * 2
def baseEnd_1109512 : Nat := 63301438659040918099717

theorem tailTrace_1109512 : CollatzResearch.WordTrace tailWord_1109512 prefixEnd_1109512 63301438659040918099717 := by
  unfold tailWord_1109512
  simp only [CollatzResearch.WordTrace]
  refine ⟨20233613578217494204337395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26978151437623325605783193 20233613578217494204337395)
  ·
    refine ⟨30350420367326241306506093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20233613578217494204337395 30350420367326241306506093)
    ·
      refine ⟨11381407637747340489939785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30350420367326241306506093 11381407637747340489939785)
      ·
        refine ⟨8536055728310505367454839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11381407637747340489939785 8536055728310505367454839)
        ·
          refine ⟨12804083592465758051182259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8536055728310505367454839 12804083592465758051182259)
          ·
            refine ⟨19206125388698637076773389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12804083592465758051182259 19206125388698637076773389)
            ·
              refine ⟨7202297020761988903790021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19206125388698637076773389 7202297020761988903790021)
              ·
                refine ⟨1350430691392872919460629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7202297020761988903790021 1350430691392872919460629)
                ·
                  refine ⟨63301438659040918099717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1350430691392872919460629 63301438659040918099717)
                  ·
                    rfl

theorem cell23_1109512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 4, 6].length) (baseStart_1109512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1109512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1109512 prefixEnd_1109512 := by exact prefixLift 1109512
  have htrace : WordTrace (prefixWord ++ tailWord_1109512) baseStart_1109512 baseEnd_1109512 := by
    simpa [prefixWord, tailWord_1109512, baseEnd_1109512] using wordTrace_append hprefix tailTrace_1109512
  have hstable : (prefixWord ++ tailWord_1109512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1109512).length < 2 ^ (prefixWord ++ tailWord_1109512).sum := by decide
  have hdescent : baseEnd_1109512 < baseStart_1109512 := by decide
  rcases family_descends (prefixWord ++ tailWord_1109512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1109559 : List Nat := [1, 1, 3, 1, 2, 5, 1, 3, 1, 5]
def baseStart_1109559 : Nat := 118140960795 + 1109559 * 2 ^ 59
def prefixEnd_1109559 : Nat := 4983230072969 + 3 ^ 40 * 1109559 * 2
def baseEnd_1109559 : Nat := 189912360507376526336579

theorem tailTrace_1109559 : CollatzResearch.WordTrace tailWord_1109559 prefixEnd_1109559 189912360507376526336579 := by
  unfold tailWord_1109559
  simp only [CollatzResearch.WordTrace]
  refine ⟨40468941387264715435635731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26979294258176476957090487 40468941387264715435635731)
  ·
    refine ⟨60703412080897073153453597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40468941387264715435635731 60703412080897073153453597)
    ·
      refine ⟨22763779530336402432545099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60703412080897073153453597 22763779530336402432545099)
      ·
        refine ⟨34145669295504603648817649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22763779530336402432545099 34145669295504603648817649)
        ·
          refine ⟨25609251971628452736613237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34145669295504603648817649 25609251971628452736613237)
          ·
            refine ⟨2400867372340167444057491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 25609251971628452736613237 2400867372340167444057491)
            ·
              refine ⟨3601301058510251166086237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2400867372340167444057491 3601301058510251166086237)
              ·
                refine ⟨1350487896941344187282339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3601301058510251166086237 1350487896941344187282339)
                ·
                  refine ⟨2025731845412016280923509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1350487896941344187282339 2025731845412016280923509)
                  ·
                    refine ⟨189912360507376526336579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2025731845412016280923509 189912360507376526336579)
                    ·
                      rfl

theorem cell23_1109559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 1, 3, 1, 5].length) (baseStart_1109559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1109559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1109559 prefixEnd_1109559 := by exact prefixLift 1109559
  have htrace : WordTrace (prefixWord ++ tailWord_1109559) baseStart_1109559 baseEnd_1109559 := by
    simpa [prefixWord, tailWord_1109559, baseEnd_1109559] using wordTrace_append hprefix tailTrace_1109559
  have hstable : (prefixWord ++ tailWord_1109559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1109559).length < 2 ^ (prefixWord ++ tailWord_1109559).sum := by decide
  have hdescent : baseEnd_1109559 < baseStart_1109559 := by decide
  rcases family_descends (prefixWord ++ tailWord_1109559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1109596 : List Nat := [2, 2, 4, 1, 2, 1, 1, 4, 1, 1, 4]
def baseStart_1109596 : Nat := 118140960795 + 1109596 * 2 ^ 59
def prefixEnd_1109596 : Nat := 4983230072969 + 3 ^ 40 * 1109596 * 2
def baseEnd_1109596 : Nat := 569756080306345934247067

theorem tailTrace_1109596 : CollatzResearch.WordTrace tailWord_1109596 prefixEnd_1109596 569756080306345934247067 := by
  unfold tailWord_1109596
  simp only [CollatzResearch.WordTrace]
  refine ⟨20235145444065335377366321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26980193925420447169821761 20235145444065335377366321)
  ·
    refine ⟨15176359083049001533024741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20235145444065335377366321 15176359083049001533024741)
    ·
      refine ⟨2845567328071687787442139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15176359083049001533024741 2845567328071687787442139)
      ·
        refine ⟨4268350992107531681163209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2845567328071687787442139 4268350992107531681163209)
        ·
          refine ⟨3201263244080648760872407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4268350992107531681163209 3201263244080648760872407)
          ·
            refine ⟨4801894866120973141308611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3201263244080648760872407 4801894866120973141308611)
            ·
              refine ⟨7202842299181459711962917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4801894866120973141308611 7202842299181459711962917)
              ·
                refine ⟨1350532931096523695993047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7202842299181459711962917 1350532931096523695993047)
                ·
                  refine ⟨2025799396644785543989571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1350532931096523695993047 2025799396644785543989571)
                  ·
                    refine ⟨3038699094967178315984357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2025799396644785543989571 3038699094967178315984357)
                    ·
                      refine ⟨569756080306345934247067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3038699094967178315984357 569756080306345934247067)
                      ·
                        rfl

theorem cell23_1109596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 4, 1, 1, 4].length) (baseStart_1109596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1109596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1109596 prefixEnd_1109596 := by exact prefixLift 1109596
  have htrace : WordTrace (prefixWord ++ tailWord_1109596) baseStart_1109596 baseEnd_1109596 := by
    simpa [prefixWord, tailWord_1109596, baseEnd_1109596] using wordTrace_append hprefix tailTrace_1109596
  have hstable : (prefixWord ++ tailWord_1109596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1109596).length < 2 ^ (prefixWord ++ tailWord_1109596).sum := by decide
  have hdescent : baseEnd_1109596 < baseStart_1109596 := by decide
  rcases family_descends (prefixWord ++ tailWord_1109596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1109616 : List Nat := [2, 1, 1, 1, 6, 1, 2, 3, 1, 2, 3]
def baseStart_1109616 : Nat := 118140960795 + 1109616 * 2 ^ 59
def prefixEnd_1109616 : Nat := 4983230072969 + 3 ^ 40 * 1109616 * 2
def baseEnd_1109616 : Nat := 569766349919435855996975

theorem tailTrace_1109616 : CollatzResearch.WordTrace tailWord_1109616 prefixEnd_1109616 569766349919435855996975 := by
  unfold tailWord_1109616
  simp only [CollatzResearch.WordTrace]
  refine ⟨20235510174029107085230351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26980680232038809446973801 20235510174029107085230351)
  ·
    refine ⟨30353265261043660627845527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20235510174029107085230351 30353265261043660627845527)
    ·
      refine ⟨45529897891565490941768291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30353265261043660627845527 45529897891565490941768291)
      ·
        refine ⟨68294846837348236412652437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45529897891565490941768291 68294846837348236412652437)
        ·
          refine ⟨3201320945500698581843083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 68294846837348236412652437 3201320945500698581843083)
          ·
            refine ⟨4801981418251047872764625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3201320945500698581843083 4801981418251047872764625)
            ·
              refine ⟨3601486063688285904573469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4801981418251047872764625 3601486063688285904573469)
              ·
                refine ⟨1350557273883107214215051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3601486063688285904573469 1350557273883107214215051)
                ·
                  refine ⟨2025835910824660821322577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1350557273883107214215051 2025835910824660821322577)
                  ·
                    refine ⟨1519376933118495615991933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2025835910824660821322577 1519376933118495615991933)
                    ·
                      refine ⟨569766349919435855996975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1519376933118495615991933 569766349919435855996975)
                      ·
                        rfl

theorem cell23_1109616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 2, 3, 1, 2, 3].length) (baseStart_1109616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1109616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1109616 prefixEnd_1109616 := by exact prefixLift 1109616
  have htrace : WordTrace (prefixWord ++ tailWord_1109616) baseStart_1109616 baseEnd_1109616 := by
    simpa [prefixWord, tailWord_1109616, baseEnd_1109616] using wordTrace_append hprefix tailTrace_1109616
  have hstable : (prefixWord ++ tailWord_1109616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1109616).length < 2 ^ (prefixWord ++ tailWord_1109616).sum := by decide
  have hdescent : baseEnd_1109616 < baseStart_1109616 := by decide
  rcases family_descends (prefixWord ++ tailWord_1109616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1109632 : List Nat := [2, 1, 1, 2, 1, 4, 2, 1, 2, 7]
def baseStart_1109632 : Nat := 118140960795 + 1109632 * 2 ^ 59
def prefixEnd_1109632 : Nat := 4983230072969 + 3 ^ 40 * 1109632 * 2
def baseEnd_1109632 : Nat := 189924855203302597798967

theorem tailTrace_1109632 : CollatzResearch.WordTrace tailWord_1109632 prefixEnd_1109632 189924855203302597798967 := by
  unfold tailWord_1109632
  simp only [CollatzResearch.WordTrace]
  refine ⟨20235801958000124451521575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26981069277333499268695433 20235801958000124451521575)
  ·
    refine ⟨30353702937000186677282363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20235801958000124451521575 30353702937000186677282363)
    ·
      refine ⟨45530554405500280015923545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30353702937000186677282363 45530554405500280015923545)
      ·
        refine ⟨34147915804125210011942659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45530554405500280015923545 34147915804125210011942659)
        ·
          refine ⟨51221873706187815017913989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34147915804125210011942659 51221873706187815017913989)
          ·
            refine ⟨9604101319910215315858873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 51221873706187815017913989 9604101319910215315858873)
            ·
              refine ⟨7203075989932661486894155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9604101319910215315858873 7203075989932661486894155)
              ·
                refine ⟨10804613984898992230341233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7203075989932661486894155 10804613984898992230341233)
                ·
                  refine ⟨8103460488674244172755925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10804613984898992230341233 8103460488674244172755925)
                  ·
                    refine ⟨189924855203302597798967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 8103460488674244172755925 189924855203302597798967)
                    ·
                      rfl

theorem cell23_1109632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 1, 2, 7].length) (baseStart_1109632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1109632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1109632 prefixEnd_1109632 := by exact prefixLift 1109632
  have htrace : WordTrace (prefixWord ++ tailWord_1109632) baseStart_1109632 baseEnd_1109632 := by
    simpa [prefixWord, tailWord_1109632, baseEnd_1109632] using wordTrace_append hprefix tailTrace_1109632
  have hstable : (prefixWord ++ tailWord_1109632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1109632).length < 2 ^ (prefixWord ++ tailWord_1109632).sum := by decide
  have hdescent : baseEnd_1109632 < baseStart_1109632 := by decide
  rcases family_descends (prefixWord ++ tailWord_1109632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1109650 : List Nat := [3, 2, 3, 1, 3, 2, 1, 2, 1, 2, 3]
def baseStart_1109650 : Nat := 118140960795 + 1109650 * 2 ^ 59
def prefixEnd_1109650 : Nat := 4983230072969 + 3 ^ 40 * 1109650 * 2
def baseEnd_1109650 : Nat := 569783808261688722971819

theorem tailTrace_1109650 : CollatzResearch.WordTrace tailWord_1109650 prefixEnd_1109650 569783808261688722971819 := by
  unfold tailWord_1109650
  simp only [CollatzResearch.WordTrace]
  refine ⟨10118065107483759494299601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26981506953290025318132269 10118065107483759494299601)
  ·
    refine ⟨7588548830612819620724701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10118065107483759494299601 7588548830612819620724701)
    ·
      refine ⟨2845705811479807357771763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7588548830612819620724701 2845705811479807357771763)
      ·
        refine ⟨4268558717219711036657645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2845705811479807357771763 4268558717219711036657645)
        ·
          refine ⟨1600709518957391638746617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4268558717219711036657645 1600709518957391638746617)
          ·
            refine ⟨1200532139218043729059963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1600709518957391638746617 1200532139218043729059963)
            ·
              refine ⟨1800798208827065593589945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1200532139218043729059963 1800798208827065593589945)
              ·
                refine ⟨1350598656620299195192459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1800798208827065593589945 1350598656620299195192459)
                ·
                  refine ⟨2025897984930448792788689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1350598656620299195192459 2025897984930448792788689)
                  ·
                    refine ⟨1519423488697836594591517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2025897984930448792788689 1519423488697836594591517)
                    ·
                      refine ⟨569783808261688722971819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1519423488697836594591517 569783808261688722971819)
                      ·
                        rfl

theorem cell23_1109650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 2, 1, 2, 1, 2, 3].length) (baseStart_1109650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1109650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1109650 prefixEnd_1109650 := by exact prefixLift 1109650
  have htrace : WordTrace (prefixWord ++ tailWord_1109650) baseStart_1109650 baseEnd_1109650 := by
    simpa [prefixWord, tailWord_1109650, baseEnd_1109650] using wordTrace_append hprefix tailTrace_1109650
  have hstable : (prefixWord ++ tailWord_1109650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1109650).length < 2 ^ (prefixWord ++ tailWord_1109650).sum := by decide
  have hdescent : baseEnd_1109650 < baseStart_1109650 := by decide
  rcases family_descends (prefixWord ++ tailWord_1109650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1109663 : List Nat := [1, 1, 2, 7, 1, 1, 1, 2, 1, 3, 3]
def baseStart_1109663 : Nat := 118140960795 + 1109663 * 2 ^ 59
def prefixEnd_1109663 : Nat := 4983230072969 + 3 ^ 40 * 1109663 * 2
def baseEnd_1109663 : Nat := 569790483510197172109259

theorem tailTrace_1109663 : CollatzResearch.WordTrace tailWord_1109663 prefixEnd_1109663 569790483510197172109259 := by
  unfold tailWord_1109663
  simp only [CollatzResearch.WordTrace]
  refine ⟨40472734578887941197421643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26981823052591960798281095 40472734578887941197421643)
  ·
    refine ⟨60709101868331911796132465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40472734578887941197421643 60709101868331911796132465)
    ·
      refine ⟨45531826401248933847099349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60709101868331911796132465 45531826401248933847099349)
      ·
        refine ⟨1067152181279271887041391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 45531826401248933847099349 1067152181279271887041391)
        ·
          refine ⟨1600728271918907830562087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1067152181279271887041391 1600728271918907830562087)
          ·
            refine ⟨2401092407878361745843131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1600728271918907830562087 2401092407878361745843131)
            ·
              refine ⟨3601638611817542618764697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2401092407878361745843131 3601638611817542618764697)
              ·
                refine ⟨2701228958863156964073523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3601638611817542618764697 2701228958863156964073523)
                ·
                  refine ⟨4051843438294735446110285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2701228958863156964073523 4051843438294735446110285)
                  ·
                    refine ⟨1519441289360525792291357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4051843438294735446110285 1519441289360525792291357)
                    ·
                      refine ⟨569790483510197172109259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1519441289360525792291357 569790483510197172109259)
                      ·
                        rfl

theorem cell23_1109663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 1, 2, 1, 3, 3].length) (baseStart_1109663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1109663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1109663 prefixEnd_1109663 := by exact prefixLift 1109663
  have htrace : WordTrace (prefixWord ++ tailWord_1109663) baseStart_1109663 baseEnd_1109663 := by
    simpa [prefixWord, tailWord_1109663, baseEnd_1109663] using wordTrace_append hprefix tailTrace_1109663
  have hstable : (prefixWord ++ tailWord_1109663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1109663).length < 2 ^ (prefixWord ++ tailWord_1109663).sum := by decide
  have hdescent : baseEnd_1109663 < baseStart_1109663 := by decide
  rcases family_descends (prefixWord ++ tailWord_1109663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1109689 : List Nat := [1, 2, 1, 4, 1, 1, 3, 1, 2, 4, 3]
def baseStart_1109689 : Nat := 118140960795 + 1109689 * 2 ^ 59
def prefixEnd_1109689 : Nat := 4983230072969 + 3 ^ 40 * 1109689 * 2
def baseEnd_1109689 : Nat := 569803834007214070384139

theorem tailTrace_1109689 : CollatzResearch.WordTrace tailWord_1109689 prefixEnd_1109689 569803834007214070384139 := by
  unfold tailWord_1109689
  simp only [CollatzResearch.WordTrace]
  refine ⟨40473682876793747637868121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26982455251195831758578747 40473682876793747637868121)
  ·
    refine ⟨30355262157595310728401091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40473682876793747637868121 30355262157595310728401091)
    ·
      refine ⟨45532893236392966092601637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30355262157595310728401091 45532893236392966092601637)
      ·
        refine ⟨8537417481823681142362807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 45532893236392966092601637 8537417481823681142362807)
        ·
          refine ⟨12806126222735521713544211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8537417481823681142362807 12806126222735521713544211)
          ·
            refine ⟨19209189334103282570316317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12806126222735521713544211 19209189334103282570316317)
            ·
              refine ⟨7203446000288730963868619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19209189334103282570316317 7203446000288730963868619)
              ·
                refine ⟨10805169000433096445802929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7203446000288730963868619 10805169000433096445802929)
                ·
                  refine ⟨8103876750324822334352197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10805169000433096445802929 8103876750324822334352197)
                  ·
                    refine ⟨1519476890685904187691037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8103876750324822334352197 1519476890685904187691037)
                    ·
                      refine ⟨569803834007214070384139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1519476890685904187691037 569803834007214070384139)
                      ·
                        rfl

theorem cell23_1109689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 1, 2, 4, 3].length) (baseStart_1109689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1109689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1109689 prefixEnd_1109689 := by exact prefixLift 1109689
  have htrace : WordTrace (prefixWord ++ tailWord_1109689) baseStart_1109689 baseEnd_1109689 := by
    simpa [prefixWord, tailWord_1109689, baseEnd_1109689] using wordTrace_append hprefix tailTrace_1109689
  have hstable : (prefixWord ++ tailWord_1109689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1109689).length < 2 ^ (prefixWord ++ tailWord_1109689).sum := by decide
  have hdescent : baseEnd_1109689 < baseStart_1109689 := by decide
  rcases family_descends (prefixWord ++ tailWord_1109689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1109703 : List Nat := [1, 1, 4, 1, 1, 1, 3, 5, 2, 2, 2]
def baseStart_1109703 : Nat := 118140960795 + 1109703 * 2 ^ 59
def prefixEnd_1109703 : Nat := 4983230072969 + 3 ^ 40 * 1109703 * 2
def baseEnd_1109703 : Nat := 569811022736377015609075

theorem tailTrace_1109703 : CollatzResearch.WordTrace tailWord_1109703 prefixEnd_1109703 569811022736377015609075 := by
  unfold tailWord_1109703
  simp only [CollatzResearch.WordTrace]
  refine ⟨40474193498743028028877763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26982795665828685352585175 40474193498743028028877763)
  ·
    refine ⟨60711290248114542043316645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40474193498743028028877763 60711290248114542043316645)
    ·
      refine ⟨11383366921521476633121871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 60711290248114542043316645 11383366921521476633121871)
      ·
        refine ⟨17075050382282214949682807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11383366921521476633121871 17075050382282214949682807)
        ·
          refine ⟨25612575573423322424524211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17075050382282214949682807 25612575573423322424524211)
          ·
            refine ⟨38418863360134983636786317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25612575573423322424524211 38418863360134983636786317)
            ·
              refine ⟨14407073760050618863794869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38418863360134983636786317 14407073760050618863794869)
              ·
                refine ⟨1350663165004745518480769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14407073760050618863794869 1350663165004745518480769)
                ·
                  refine ⟨1012997373753559138860577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1350663165004745518480769 1012997373753559138860577)
                  ·
                    refine ⟨759748030315169354145433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1012997373753559138860577 759748030315169354145433)
                    ·
                      refine ⟨569811022736377015609075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 759748030315169354145433 569811022736377015609075)
                      ·
                        rfl

theorem cell23_1109703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 5, 2, 2, 2].length) (baseStart_1109703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1109703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1109703 prefixEnd_1109703 := by exact prefixLift 1109703
  have htrace : WordTrace (prefixWord ++ tailWord_1109703) baseStart_1109703 baseEnd_1109703 := by
    simpa [prefixWord, tailWord_1109703, baseEnd_1109703] using wordTrace_append hprefix tailTrace_1109703
  have hstable : (prefixWord ++ tailWord_1109703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1109703).length < 2 ^ (prefixWord ++ tailWord_1109703).sum := by decide
  have hdescent : baseEnd_1109703 < baseStart_1109703 := by decide
  rcases family_descends (prefixWord ++ tailWord_1109703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1109719 : List Nat := [1, 1, 3, 2, 1, 3, 1, 2, 1, 5, 3]
def baseStart_1109719 : Nat := 118140960795 + 1109719 * 2 ^ 59
def prefixEnd_1109719 : Nat := 4983230072969 + 3 ^ 40 * 1109719 * 2
def baseEnd_1109719 : Nat := 569819238426848953009001

theorem tailTrace_1109719 : CollatzResearch.WordTrace tailWord_1109719 prefixEnd_1109719 569819238426848953009001 := by
  unfold tailWord_1109719
  simp only [CollatzResearch.WordTrace]
  refine ⟨40474777066685062761460211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26983184711123375174306807 40474777066685062761460211)
  ·
    refine ⟨60712165600027594142190317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40474777066685062761460211 60712165600027594142190317)
    ·
      refine ⟨22767062100010347803321369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60712165600027594142190317 22767062100010347803321369)
      ·
        refine ⟨17075296575007760852491027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22767062100010347803321369 17075296575007760852491027)
        ·
          refine ⟨25612944862511641278736541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17075296575007760852491027 25612944862511641278736541)
          ·
            refine ⟨9604854323441865479526203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25612944862511641278736541 9604854323441865479526203)
            ·
              refine ⟨14407281485162798219289305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9604854323441865479526203 14407281485162798219289305)
              ·
                refine ⟨10805461113872098664466979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14407281485162798219289305 10805461113872098664466979)
                ·
                  refine ⟨16208191670808147996700469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10805461113872098664466979 16208191670808147996700469)
                  ·
                    refine ⟨1519517969138263874690669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 16208191670808147996700469 1519517969138263874690669)
                    ·
                      refine ⟨569819238426848953009001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1519517969138263874690669 569819238426848953009001)
                      ·
                        rfl

theorem cell23_1109719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 2, 1, 5, 3].length) (baseStart_1109719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1109719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1109719 prefixEnd_1109719 := by exact prefixLift 1109719
  have htrace : WordTrace (prefixWord ++ tailWord_1109719) baseStart_1109719 baseEnd_1109719 := by
    simpa [prefixWord, tailWord_1109719, baseEnd_1109719] using wordTrace_append hprefix tailTrace_1109719
  have hstable : (prefixWord ++ tailWord_1109719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1109719).length < 2 ^ (prefixWord ++ tailWord_1109719).sum := by decide
  have hdescent : baseEnd_1109719 < baseStart_1109719 := by decide
  rcases family_descends (prefixWord ++ tailWord_1109719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1109724 : List Nat := [2, 2, 5, 1, 2, 2, 2, 1, 1, 3, 2]
def baseStart_1109724 : Nat := 118140960795 + 1109724 * 2 ^ 59
def prefixEnd_1109724 : Nat := 4983230072969 + 3 ^ 40 * 1109724 * 2
def baseEnd_1109724 : Nat := 569821805830121433446479

theorem tailTrace_1109724 : CollatzResearch.WordTrace tailWord_1109724 prefixEnd_1109724 569821805830121433446479 := by
  unfold tailWord_1109724
  simp only [CollatzResearch.WordTrace]
  refine ⟨20237479715833474307696113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26983306287777965743594817 20237479715833474307696113)
  ·
    refine ⟨15178109786875105730772085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20237479715833474307696113 15178109786875105730772085)
    ·
      refine ⟨1422947792519541162259883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 15178109786875105730772085 1422947792519541162259883)
      ·
        refine ⟨2134421688779311743389825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1422947792519541162259883 2134421688779311743389825)
        ·
          refine ⟨1600816266584483807542369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2134421688779311743389825 1600816266584483807542369)
          ·
            refine ⟨1200612199938362855656777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1600816266584483807542369 1200612199938362855656777)
            ·
              refine ⟨900459149953772141742583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1200612199938362855656777 900459149953772141742583)
              ·
                refine ⟨1350688724930658212613875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 900459149953772141742583 1350688724930658212613875)
                ·
                  refine ⟨2026033087395987318920813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1350688724930658212613875 2026033087395987318920813)
                  ·
                    refine ⟨759762407773495244595305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2026033087395987318920813 759762407773495244595305)
                    ·
                      refine ⟨569821805830121433446479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 759762407773495244595305 569821805830121433446479)
                      ·
                        rfl

theorem cell23_1109724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 2, 2, 1, 1, 3, 2].length) (baseStart_1109724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1109724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1109724 prefixEnd_1109724 := by exact prefixLift 1109724
  have htrace : WordTrace (prefixWord ++ tailWord_1109724) baseStart_1109724 baseEnd_1109724 := by
    simpa [prefixWord, tailWord_1109724, baseEnd_1109724] using wordTrace_append hprefix tailTrace_1109724
  have hstable : (prefixWord ++ tailWord_1109724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1109724).length < 2 ^ (prefixWord ++ tailWord_1109724).sum := by decide
  have hdescent : baseEnd_1109724 < baseStart_1109724 := by decide
  rcases family_descends (prefixWord ++ tailWord_1109724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1109736 : List Nat := [2, 1, 4, 1, 3, 1, 1, 2, 2, 3, 3]
def baseStart_1109736 : Nat := 118140960795 + 1109736 * 2 ^ 59
def prefixEnd_1109736 : Nat := 4983230072969 + 3 ^ 40 * 1109736 * 2
def baseEnd_1109736 : Nat := 569827967597975386496423

theorem tailTrace_1109736 : CollatzResearch.WordTrace tailWord_1109736 prefixEnd_1109736 569827967597975386496423 := by
  unfold tailWord_1109736
  simp only [CollatzResearch.WordTrace]
  refine ⟨20237698553811737332414531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26983598071748983109886041 20237698553811737332414531)
  ·
    refine ⟨30356547830717605998621797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20237698553811737332414531 30356547830717605998621797)
    ·
      refine ⟨5691852718259551124741587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30356547830717605998621797 5691852718259551124741587)
      ·
        refine ⟨8537779077389326687112381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5691852718259551124741587 8537779077389326687112381)
        ·
          refine ⟨3201667154020997507667143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8537779077389326687112381 3201667154020997507667143)
          ·
            refine ⟨4802500731031496261500715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3201667154020997507667143 4802500731031496261500715)
            ·
              refine ⟨7203751096547244392251073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4802500731031496261500715 7203751096547244392251073)
              ·
                refine ⟨5402813322410433294188305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7203751096547244392251073 5402813322410433294188305)
                ·
                  refine ⟨4052109991807824970641229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5402813322410433294188305 4052109991807824970641229)
                  ·
                    refine ⟨1519541246927934363990461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4052109991807824970641229 1519541246927934363990461)
                    ·
                      refine ⟨569827967597975386496423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1519541246927934363990461 569827967597975386496423)
                      ·
                        rfl

theorem cell23_1109736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 2, 2, 3, 3].length) (baseStart_1109736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1109736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1109736 prefixEnd_1109736 := by exact prefixLift 1109736
  have htrace : WordTrace (prefixWord ++ tailWord_1109736) baseStart_1109736 baseEnd_1109736 := by
    simpa [prefixWord, tailWord_1109736, baseEnd_1109736] using wordTrace_append hprefix tailTrace_1109736
  have hstable : (prefixWord ++ tailWord_1109736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1109736).length < 2 ^ (prefixWord ++ tailWord_1109736).sum := by decide
  have hdescent : baseEnd_1109736 < baseStart_1109736 := by decide
  rcases family_descends (prefixWord ++ tailWord_1109736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1109739 : List Nat := [1, 1, 1, 1, 2, 4, 2, 4, 2, 5]
def baseStart_1109739 : Nat := 118140960795 + 1109739 * 2 ^ 59
def prefixEnd_1109739 : Nat := 4983230072969 + 3 ^ 40 * 1109739 * 2
def baseEnd_1109739 : Nat := 189943169346646291586303

theorem tailTrace_1109739 : CollatzResearch.WordTrace tailWord_1109739 prefixEnd_1109739 189943169346646291586303 := by
  unfold tailWord_1109739
  simp only [CollatzResearch.WordTrace]
  refine ⟨40475506526612606177188271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26983671017741737451458847 40475506526612606177188271)
  ·
    refine ⟨60713259789918909265782407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40475506526612606177188271 60713259789918909265782407)
    ·
      refine ⟨91069889684878363898673611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60713259789918909265782407 91069889684878363898673611)
      ·
        refine ⟨136604834527317545848010417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91069889684878363898673611 136604834527317545848010417)
        ·
          refine ⟨102453625895488159386007813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 136604834527317545848010417 102453625895488159386007813)
          ·
            refine ⟨19210054855404029884876465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 102453625895488159386007813 19210054855404029884876465)
            ·
              refine ⟨14407541141553022413657349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19210054855404029884876465 14407541141553022413657349)
              ·
                refine ⟨2701413964041191702560753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14407541141553022413657349 2701413964041191702560753)
                ·
                  refine ⟨2026060473030893776920565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2701413964041191702560753 2026060473030893776920565)
                  ·
                    refine ⟨189943169346646291586303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2026060473030893776920565 189943169346646291586303)
                    ·
                      rfl

theorem cell23_1109739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 4, 2, 5].length) (baseStart_1109739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1109739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1109739 prefixEnd_1109739 := by exact prefixLift 1109739
  have htrace : WordTrace (prefixWord ++ tailWord_1109739) baseStart_1109739 baseEnd_1109739 := by
    simpa [prefixWord, tailWord_1109739, baseEnd_1109739] using wordTrace_append hprefix tailTrace_1109739
  have hstable : (prefixWord ++ tailWord_1109739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1109739).length < 2 ^ (prefixWord ++ tailWord_1109739).sum := by decide
  have hdescent : baseEnd_1109739 < baseStart_1109739 := by decide
  rcases family_descends (prefixWord ++ tailWord_1109739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1109759 : List Nat := [1, 1, 2, 2, 1, 3, 3, 2, 1, 3, 4]
def baseStart_1109759 : Nat := 118140960795 + 1109759 * 2 ^ 59
def prefixEnd_1109759 : Nat := 4983230072969 + 3 ^ 40 * 1109759 * 2
def baseEnd_1109759 : Nat := 569839777653028796508817

theorem tailTrace_1109759 : CollatzResearch.WordTrace tailWord_1109759 prefixEnd_1109759 569839777653028796508817 := by
  unfold tailWord_1109759
  simp only [CollatzResearch.WordTrace]
  refine ⟨40476235986540149592916331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26984157324360099728610887 40476235986540149592916331)
  ·
    refine ⟨60714353979810224389374497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40476235986540149592916331 60714353979810224389374497)
    ·
      refine ⟨45535765484857668292030873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60714353979810224389374497 45535765484857668292030873)
      ·
        refine ⟨34151824113643251219023155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45535765484857668292030873 34151824113643251219023155)
        ·
          refine ⟨51227736170464876828534733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34151824113643251219023155 51227736170464876828534733)
          ·
            refine ⟨19210401063924328810700525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51227736170464876828534733 19210401063924328810700525)
            ·
              refine ⟨7203900398971623304012697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19210401063924328810700525 7203900398971623304012697)
              ·
                refine ⟨5402925299228717478009523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7203900398971623304012697 5402925299228717478009523)
                ·
                  refine ⟨8104387948843076217014285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5402925299228717478009523 8104387948843076217014285)
                  ·
                    refine ⟨3039145480816153581380357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8104387948843076217014285 3039145480816153581380357)
                    ·
                      refine ⟨569839777653028796508817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3039145480816153581380357 569839777653028796508817)
                      ·
                        rfl

theorem cell23_1109759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 2, 1, 3, 4].length) (baseStart_1109759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1109759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1109759 prefixEnd_1109759 := by exact prefixLift 1109759
  have htrace : WordTrace (prefixWord ++ tailWord_1109759) baseStart_1109759 baseEnd_1109759 := by
    simpa [prefixWord, tailWord_1109759, baseEnd_1109759] using wordTrace_append hprefix tailTrace_1109759
  have hstable : (prefixWord ++ tailWord_1109759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1109759).length < 2 ^ (prefixWord ++ tailWord_1109759).sum := by decide
  have hdescent : baseEnd_1109759 < baseStart_1109759 := by decide
  rcases family_descends (prefixWord ++ tailWord_1109759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1109816 : List Nat := [2, 1, 2, 1, 3, 4, 1, 3, 6]
def baseStart_1109816 : Nat := 118140960795 + 1109816 * 2 ^ 59
def prefixEnd_1109816 : Nat := 4983230072969 + 3 ^ 40 * 1109816 * 2
def baseEnd_1109816 : Nat := 63318782894481674832895

theorem tailTrace_1109816 : CollatzResearch.WordTrace tailWord_1109816 prefixEnd_1109816 63318782894481674832895 := by
  unfold tailWord_1109816
  simp only [CollatzResearch.WordTrace]
  refine ⟨20239157473666824163870651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26985543298222432218494201 20239157473666824163870651)
  ·
    refine ⟨30358736210500236245805977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20239157473666824163870651 30358736210500236245805977)
    ·
      refine ⟨22769052157875177184354483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30358736210500236245805977 22769052157875177184354483)
      ·
        refine ⟨34153578236812765776531725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22769052157875177184354483 34153578236812765776531725)
        ·
          refine ⟨12807591838804787166199397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34153578236812765776531725 12807591838804787166199397)
          ·
            refine ⟨2401423469775897593662387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12807591838804787166199397 2401423469775897593662387)
            ·
              refine ⟨3602135204663846390493581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2401423469775897593662387 3602135204663846390493581)
              ·
                refine ⟨1350800701748942396435093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3602135204663846390493581 1350800701748942396435093)
                ·
                  refine ⟨63318782894481674832895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1350800701748942396435093 63318782894481674832895)
                  ·
                    rfl

theorem cell23_1109816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 1, 3, 6].length) (baseStart_1109816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1109816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1109816 prefixEnd_1109816 := by exact prefixLift 1109816
  have htrace : WordTrace (prefixWord ++ tailWord_1109816) baseStart_1109816 baseEnd_1109816 := by
    simpa [prefixWord, tailWord_1109816, baseEnd_1109816] using wordTrace_append hprefix tailTrace_1109816
  have hstable : (prefixWord ++ tailWord_1109816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1109816).length < 2 ^ (prefixWord ++ tailWord_1109816).sum := by decide
  have hdescent : baseEnd_1109816 < baseStart_1109816 := by decide
  rcases family_descends (prefixWord ++ tailWord_1109816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1109917 : List Nat := [1, 4, 2, 1, 2, 3, 2, 1, 3, 2, 2]
def baseStart_1109917 : Nat := 118140960795 + 1109917 * 2 ^ 59
def prefixEnd_1109917 : Nat := 4983230072969 + 3 ^ 40 * 1109917 * 2
def baseEnd_1109917 : Nat := 569920907596439178333091

theorem tailTrace_1109917 : CollatzResearch.WordTrace tailWord_1109917 prefixEnd_1109917 569920907596439178333091 := by
  unfold tailWord_1109917
  simp only [CollatzResearch.WordTrace]
  refine ⟨40481998719967742577168005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26987999146645161718112003 40481998719967742577168005)
  ·
    refine ⟨7590374759993951733219001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 40481998719967742577168005 7590374759993951733219001)
    ·
      refine ⟨5692781069995463799914251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7590374759993951733219001 5692781069995463799914251)
      ·
        refine ⟨8539171604993195699871377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5692781069995463799914251 8539171604993195699871377)
        ·
          refine ⟨6404378703744896774903533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8539171604993195699871377 6404378703744896774903533)
          ·
            refine ⟨2401642013904336290588825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6404378703744896774903533 2401642013904336290588825)
            ·
              refine ⟨1801231510428252217941619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2401642013904336290588825 1801231510428252217941619)
              ·
                refine ⟨2701847265642378326912429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1801231510428252217941619 2701847265642378326912429)
                ·
                  refine ⟨1013192724615891872592161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2701847265642378326912429 1013192724615891872592161)
                  ·
                    refine ⟨759894543461918904444121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1013192724615891872592161 759894543461918904444121)
                    ·
                      refine ⟨569920907596439178333091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 759894543461918904444121 569920907596439178333091)
                      ·
                        rfl

theorem cell23_1109917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 2, 1, 3, 2, 2].length) (baseStart_1109917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1109917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1109917 prefixEnd_1109917 := by exact prefixLift 1109917
  have htrace : WordTrace (prefixWord ++ tailWord_1109917) baseStart_1109917 baseEnd_1109917 := by
    simpa [prefixWord, tailWord_1109917, baseEnd_1109917] using wordTrace_append hprefix tailTrace_1109917
  have hstable : (prefixWord ++ tailWord_1109917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1109917).length < 2 ^ (prefixWord ++ tailWord_1109917).sum := by decide
  have hdescent : baseEnd_1109917 < baseStart_1109917 := by decide
  rcases family_descends (prefixWord ++ tailWord_1109917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1109927 : List Nat := [1, 1, 6, 1, 2, 2, 3, 1, 2, 4]
def baseStart_1109927 : Nat := 118140960795 + 1109927 * 2 ^ 59
def prefixEnd_1109927 : Nat := 4983230072969 + 3 ^ 40 * 1109927 * 2
def baseEnd_1109927 : Nat := 189975347467661379736015

theorem tailTrace_1109927 : CollatzResearch.WordTrace tailWord_1109927 prefixEnd_1109927 189975347467661379736015 := by
  unfold tailWord_1109927
  simp only [CollatzResearch.WordTrace]
  refine ⟨40482363449931514285032035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26988242299954342856688023 40482363449931514285032035)
  ·
    refine ⟨60723545174897271427548053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40482363449931514285032035 60723545174897271427548053)
    ·
      refine ⟨2846416180073309598166315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 60723545174897271427548053 2846416180073309598166315)
      ·
        refine ⟨4269624270109964397249473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2846416180073309598166315 4269624270109964397249473)
        ·
          refine ⟨3202218202582473297937105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4269624270109964397249473 3202218202582473297937105)
          ·
            refine ⟨2401663651936854973452829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3202218202582473297937105 2401663651936854973452829)
            ·
              refine ⟨900623869476320615044811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2401663651936854973452829 900623869476320615044811)
              ·
                refine ⟨1350935804214480922567217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 900623869476320615044811 1350935804214480922567217)
                ·
                  refine ⟨1013201853160860691925413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1350935804214480922567217 1013201853160860691925413)
                  ·
                    refine ⟨189975347467661379736015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1013201853160860691925413 189975347467661379736015)
                    ·
                      rfl

theorem cell23_1109927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 3, 1, 2, 4].length) (baseStart_1109927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1109927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1109927 prefixEnd_1109927 := by exact prefixLift 1109927
  have htrace : WordTrace (prefixWord ++ tailWord_1109927) baseStart_1109927 baseEnd_1109927 := by
    simpa [prefixWord, tailWord_1109927, baseEnd_1109927] using wordTrace_append hprefix tailTrace_1109927
  have hstable : (prefixWord ++ tailWord_1109927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1109927).length < 2 ^ (prefixWord ++ tailWord_1109927).sum := by decide
  have hdescent : baseEnd_1109927 < baseStart_1109927 := by decide
  rcases family_descends (prefixWord ++ tailWord_1109927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1109940 : List Nat := [2, 5, 2, 1, 2, 1, 1, 9]
def baseStart_1109940 : Nat := 118140960795 + 1109940 * 2 ^ 59
def prefixEnd_1109940 : Nat := 4983230072969 + 3 ^ 40 * 1109940 * 2
def baseEnd_1109940 : Nat := 21108619172277503272055

theorem tailTrace_1109940 : CollatzResearch.WordTrace tailWord_1109940 prefixEnd_1109940 21108619172277503272055 := by
  unfold tailWord_1109940
  simp only [CollatzResearch.WordTrace]
  refine ⟨20241418799442208752627637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26988558399256278336836849 20241418799442208752627637)
  ·
    refine ⟨1897633012447707070558841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 20241418799442208752627637 1897633012447707070558841)
    ·
      refine ⟨1423224759335780302919131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1897633012447707070558841 1423224759335780302919131)
      ·
        refine ⟨2134837139003670454378697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1423224759335780302919131 2134837139003670454378697)
        ·
          refine ⟨1601127854252752840784023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2134837139003670454378697 1601127854252752840784023)
          ·
            refine ⟨2401691781379129261176035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1601127854252752840784023 2401691781379129261176035)
            ·
              refine ⟨3602537672068693891764053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2401691781379129261176035 3602537672068693891764053)
              ·
                refine ⟨21108619172277503272055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 3602537672068693891764053 21108619172277503272055)
                ·
                  rfl

theorem cell23_1109940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 1, 9].length) (baseStart_1109940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1109940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1109940 prefixEnd_1109940 := by exact prefixLift 1109940
  have htrace : WordTrace (prefixWord ++ tailWord_1109940) baseStart_1109940 baseEnd_1109940 := by
    simpa [prefixWord, tailWord_1109940, baseEnd_1109940] using wordTrace_append hprefix tailTrace_1109940
  have hstable : (prefixWord ++ tailWord_1109940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1109940).length < 2 ^ (prefixWord ++ tailWord_1109940).sum := by decide
  have hdescent : baseEnd_1109940 < baseStart_1109940 := by decide
  rcases family_descends (prefixWord ++ tailWord_1109940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1109950 : List Nat := [4, 2, 1, 1, 1, 3, 1, 2, 4, 1, 3]
def baseStart_1109950 : Nat := 118140960795 + 1109950 * 2 ^ 59
def prefixEnd_1109950 : Nat := 4983230072969 + 3 ^ 40 * 1109950 * 2
def baseEnd_1109950 : Nat := 569937852458037549220439

theorem tailTrace_1109950 : CollatzResearch.WordTrace tailWord_1109950 prefixEnd_1109950 569937852458037549220439 := by
  unfold tailWord_1109950
  simp only [CollatzResearch.WordTrace]
  refine ⟨5060400291106023651639913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26988801552565459475412869 5060400291106023651639913)
  ·
    refine ⟨3795300218329517738729935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5060400291106023651639913 3795300218329517738729935)
    ·
      refine ⟨5692950327494276608094903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3795300218329517738729935 5692950327494276608094903)
      ·
        refine ⟨8539425491241414912142355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5692950327494276608094903 8539425491241414912142355)
        ·
          refine ⟨12809138236862122368213533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8539425491241414912142355 12809138236862122368213533)
          ·
            refine ⟨4803426838823295888080075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12809138236862122368213533 4803426838823295888080075)
            ·
              refine ⟨7205140258234943832120113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4803426838823295888080075 7205140258234943832120113)
              ·
                refine ⟨5403855193676207874090085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7205140258234943832120113 5403855193676207874090085)
                ·
                  refine ⟨1013222848814288976391891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5403855193676207874090085 1013222848814288976391891)
                  ·
                    refine ⟨1519834273221433464587837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1013222848814288976391891 1519834273221433464587837)
                    ·
                      refine ⟨569937852458037549220439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1519834273221433464587837 569937852458037549220439)
                      ·
                        rfl

theorem cell23_1109950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 2, 4, 1, 3].length) (baseStart_1109950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1109950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1109950 prefixEnd_1109950 := by exact prefixLift 1109950
  have htrace : WordTrace (prefixWord ++ tailWord_1109950) baseStart_1109950 baseEnd_1109950 := by
    simpa [prefixWord, tailWord_1109950, baseEnd_1109950] using wordTrace_append hprefix tailTrace_1109950
  have hstable : (prefixWord ++ tailWord_1109950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1109950).length < 2 ^ (prefixWord ++ tailWord_1109950).sum := by decide
  have hdescent : baseEnd_1109950 < baseStart_1109950 := by decide
  rcases family_descends (prefixWord ++ tailWord_1109950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1109976 : List Nat := [2, 1, 2, 2, 2, 2, 1, 2, 1, 3, 5]
def baseStart_1109976 : Nat := 118140960795 + 1109976 * 2 ^ 59
def prefixEnd_1109976 : Nat := 4983230072969 + 3 ^ 40 * 1109976 * 2
def baseEnd_1109976 : Nat := 569951202955054447495319

theorem tailTrace_1109976 : CollatzResearch.WordTrace tailWord_1109976 prefixEnd_1109976 569951202955054447495319 := by
  unfold tailWord_1109976
  simp only [CollatzResearch.WordTrace]
  refine ⟨20242075313376997826782891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26989433751169330435710521 20242075313376997826782891)
  ·
    refine ⟨30363112970065496740174337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20242075313376997826782891 30363112970065496740174337)
    ·
      refine ⟨22772334727549122555130753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30363112970065496740174337 22772334727549122555130753)
      ·
        refine ⟨17079251045661841916348065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22772334727549122555130753 17079251045661841916348065)
        ·
          refine ⟨12809438284246381437261049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17079251045661841916348065 12809438284246381437261049)
          ·
            refine ⟨9607078713184786077945787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12809438284246381437261049 9607078713184786077945787)
            ·
              refine ⟨14410618069777179116918681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9607078713184786077945787 14410618069777179116918681)
              ·
                refine ⟨10807963552332884337689011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14410618069777179116918681 10807963552332884337689011)
                ·
                  refine ⟨16211945328499326506533517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10807963552332884337689011 16211945328499326506533517)
                  ·
                    refine ⟨6079479498187247439950069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16211945328499326506533517 6079479498187247439950069)
                    ·
                      refine ⟨569951202955054447495319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6079479498187247439950069 569951202955054447495319)
                      ·
                        rfl

theorem cell23_1109976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 2, 1, 3, 5].length) (baseStart_1109976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1109976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1109976 prefixEnd_1109976 := by exact prefixLift 1109976
  have htrace : WordTrace (prefixWord ++ tailWord_1109976) baseStart_1109976 baseEnd_1109976 := by
    simpa [prefixWord, tailWord_1109976, baseEnd_1109976] using wordTrace_append hprefix tailTrace_1109976
  have hstable : (prefixWord ++ tailWord_1109976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1109976).length < 2 ^ (prefixWord ++ tailWord_1109976).sum := by decide
  have hdescent : baseEnd_1109976 < baseStart_1109976 := by decide
  rcases family_descends (prefixWord ++ tailWord_1109976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1109996 : List Nat := [2, 2, 1, 1, 2, 1, 1, 6, 7]
def baseStart_1109996 : Nat := 118140960795 + 1109996 * 2 ^ 59
def prefixEnd_1109996 : Nat := 4983230072969 + 3 ^ 40 * 1109996 * 2
def baseEnd_1109996 : Nat := 63329052507571596582803

theorem tailTrace_1109996 : CollatzResearch.WordTrace tailWord_1109996 prefixEnd_1109996 63329052507571596582803 := by
  unfold tailWord_1109996
  simp only [CollatzResearch.WordTrace]
  refine ⟨20242440043340769534646921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26989920057787692712862561 20242440043340769534646921)
  ·
    refine ⟨15181830032505577150985191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20242440043340769534646921 15181830032505577150985191)
    ·
      refine ⟨22772745048758365726477787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15181830032505577150985191 22772745048758365726477787)
      ·
        refine ⟨34159117573137548589716681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22772745048758365726477787 34159117573137548589716681)
        ·
          refine ⟨25619338179853161442287511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34159117573137548589716681 25619338179853161442287511)
          ·
            refine ⟨38429007269779742163431267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25619338179853161442287511 38429007269779742163431267)
            ·
              refine ⟨57643510904669613245146901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38429007269779742163431267 57643510904669613245146901)
              ·
                refine ⟨2702039573656388120866261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 57643510904669613245146901 2702039573656388120866261)
                ·
                  refine ⟨63329052507571596582803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2702039573656388120866261 63329052507571596582803)
                  ·
                    rfl

theorem cell23_1109996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 7].length) (baseStart_1109996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1109996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1109996 prefixEnd_1109996 := by exact prefixLift 1109996
  have htrace : WordTrace (prefixWord ++ tailWord_1109996) baseStart_1109996 baseEnd_1109996 := by
    simpa [prefixWord, tailWord_1109996, baseEnd_1109996] using wordTrace_append hprefix tailTrace_1109996
  have hstable : (prefixWord ++ tailWord_1109996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1109996).length < 2 ^ (prefixWord ++ tailWord_1109996).sum := by decide
  have hdescent : baseEnd_1109996 < baseStart_1109996 := by decide
  rcases family_descends (prefixWord ++ tailWord_1109996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1110030 : List Nat := [4, 1, 1, 2, 2, 1, 3, 4, 5]
def baseStart_1110030 : Nat := 118140960795 + 1110030 * 2 ^ 59
def prefixEnd_1110030 : Nat := 4983230072969 + 3 ^ 40 * 1110030 * 2
def baseEnd_1110030 : Nat := 63330992323377470691119

theorem tailTrace_1110030 : CollatzResearch.WordTrace tailWord_1110030 prefixEnd_1110030 63330992323377470691119 := by
  unfold tailWord_1110030
  simp only [CollatzResearch.WordTrace]
  refine ⟨5060765021069795359503943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26990746779038908584021029 5060765021069795359503943)
  ·
    refine ⟨7591147531604693039255915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5060765021069795359503943 7591147531604693039255915)
    ·
      refine ⟨11386721297407039558883873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7591147531604693039255915 11386721297407039558883873)
      ·
        refine ⟨8540040973055279669162905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11386721297407039558883873 8540040973055279669162905)
        ·
          refine ⟨6405030729791459751872179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8540040973055279669162905 6405030729791459751872179)
          ·
            refine ⟨9607546094687189627808269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6405030729791459751872179 9607546094687189627808269)
            ·
              refine ⟨3602829785507696110428101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9607546094687189627808269 3602829785507696110428101)
              ·
                refine ⟨675530584782693020705269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3602829785507696110428101 675530584782693020705269)
                ·
                  refine ⟨63330992323377470691119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 675530584782693020705269 63330992323377470691119)
                  ·
                    rfl

theorem cell23_1110030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 3, 4, 5].length) (baseStart_1110030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1110030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1110030 prefixEnd_1110030 := by exact prefixLift 1110030
  have htrace : WordTrace (prefixWord ++ tailWord_1110030) baseStart_1110030 baseEnd_1110030 := by
    simpa [prefixWord, tailWord_1110030, baseEnd_1110030] using wordTrace_append hprefix tailTrace_1110030
  have hstable : (prefixWord ++ tailWord_1110030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1110030).length < 2 ^ (prefixWord ++ tailWord_1110030).sum := by decide
  have hdescent : baseEnd_1110030 < baseStart_1110030 := by decide
  rcases family_descends (prefixWord ++ tailWord_1110030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1110050 : List Nat := [3, 3, 1, 1, 1, 2, 1, 2, 2, 5, 2]
def baseStart_1110050 : Nat := 118140960795 + 1110050 * 2 ^ 59
def prefixEnd_1110050 : Nat := 4983230072969 + 3 ^ 40 * 1110050 * 2
def baseEnd_1110050 : Nat := 569989200523487157969979

theorem tailTrace_1110050 : CollatzResearch.WordTrace tailWord_1110050 prefixEnd_1110050 569989200523487157969979 := by
  unfold tailWord_1110050
  simp only [CollatzResearch.WordTrace]
  refine ⟨10121712407121476572939901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26991233085657270861173069 10121712407121476572939901)
  ·
    refine ⟨3795642152670553714852463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10121712407121476572939901 3795642152670553714852463)
    ·
      refine ⟨5693463229005830572278695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3795642152670553714852463 5693463229005830572278695)
      ·
        refine ⟨8540194843508745858418043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5693463229005830572278695 8540194843508745858418043)
        ·
          refine ⟨12810292265263118787627065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8540194843508745858418043 12810292265263118787627065)
          ·
            refine ⟨9607719198947339090720299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12810292265263118787627065 9607719198947339090720299)
            ·
              refine ⟨14411578798421008636080449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9607719198947339090720299 14411578798421008636080449)
              ·
                refine ⟨10808684098815756477060337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14411578798421008636080449 10808684098815756477060337)
                ·
                  refine ⟨8106513074111817357795253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10808684098815756477060337 8106513074111817357795253)
                  ·
                    refine ⟨759985600697982877293305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8106513074111817357795253 759985600697982877293305)
                    ·
                      refine ⟨569989200523487157969979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 759985600697982877293305 569989200523487157969979)
                      ·
                        rfl

theorem cell23_1110050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 2, 2, 5, 2].length) (baseStart_1110050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1110050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1110050 prefixEnd_1110050 := by exact prefixLift 1110050
  have htrace : WordTrace (prefixWord ++ tailWord_1110050) baseStart_1110050 baseEnd_1110050 := by
    simpa [prefixWord, tailWord_1110050, baseEnd_1110050] using wordTrace_append hprefix tailTrace_1110050
  have hstable : (prefixWord ++ tailWord_1110050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1110050).length < 2 ^ (prefixWord ++ tailWord_1110050).sum := by decide
  have hdescent : baseEnd_1110050 < baseStart_1110050 := by decide
  rcases family_descends (prefixWord ++ tailWord_1110050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1110063 : List Nat := [1, 1, 2, 1, 2, 1, 1, 7, 2, 1, 4]
def baseStart_1110063 : Nat := 118140960795 + 1110063 * 2 ^ 59
def prefixEnd_1110063 : Nat := 4983230072969 + 3 ^ 40 * 1110063 * 2
def baseEnd_1110063 : Nat := 569995875771995607107419

theorem tailTrace_1110063 : CollatzResearch.WordTrace tailWord_1110063 prefixEnd_1110063 569995875771995607107419 := by
  unfold tailWord_1110063
  simp only [CollatzResearch.WordTrace]
  refine ⟨40487323777438809511982843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26991549184959206341321895 40487323777438809511982843)
  ·
    refine ⟨60730985666158214267974265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40487323777438809511982843 60730985666158214267974265)
    ·
      refine ⟨45548239249618660700980699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60730985666158214267974265 45548239249618660700980699)
      ·
        refine ⟨68322358874427991051471049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45548239249618660700980699 68322358874427991051471049)
        ·
          refine ⟨51241769155820993288603287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68322358874427991051471049 51241769155820993288603287)
          ·
            refine ⟨76862653733731489932904931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51241769155820993288603287 76862653733731489932904931)
            ·
              refine ⟨115293980600597234899357397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76862653733731489932904931 115293980600597234899357397)
              ·
                refine ⟨2702202670326497692953689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 115293980600597234899357397 2702202670326497692953689)
                ·
                  refine ⟨2026652002744873269715267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2702202670326497692953689 2026652002744873269715267)
                  ·
                    refine ⟨3039978004117309904572901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2026652002744873269715267 3039978004117309904572901)
                    ·
                      refine ⟨569995875771995607107419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3039978004117309904572901 569995875771995607107419)
                      ·
                        rfl

theorem cell23_1110063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 7, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 7, 2, 1, 4].length) (baseStart_1110063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1110063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1110063 prefixEnd_1110063 := by exact prefixLift 1110063
  have htrace : WordTrace (prefixWord ++ tailWord_1110063) baseStart_1110063 baseEnd_1110063 := by
    simpa [prefixWord, tailWord_1110063, baseEnd_1110063] using wordTrace_append hprefix tailTrace_1110063
  have hstable : (prefixWord ++ tailWord_1110063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1110063).length < 2 ^ (prefixWord ++ tailWord_1110063).sum := by decide
  have hdescent : baseEnd_1110063 < baseStart_1110063 := by decide
  rcases family_descends (prefixWord ++ tailWord_1110063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1110080 : List Nat := [2, 1, 1, 2, 2, 4, 1, 2, 2, 4, 2]
def baseStart_1110080 : Nat := 118140960795 + 1110080 * 2 ^ 59
def prefixEnd_1110080 : Nat := 4983230072969 + 3 ^ 40 * 1110080 * 2
def baseEnd_1110080 : Nat := 570004604943122040594841

theorem tailTrace_1110080 : CollatzResearch.WordTrace tailWord_1110080 prefixEnd_1110080 570004604943122040594841 := by
  unfold tailWord_1110080
  simp only [CollatzResearch.WordTrace]
  refine ⟨20243971909188610707675847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26991962545584814276901129 20243971909188610707675847)
  ·
    refine ⟨30365957863782916061513771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20243971909188610707675847 30365957863782916061513771)
    ·
      refine ⟨45548936795674374092270657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30365957863782916061513771 45548936795674374092270657)
      ·
        refine ⟨34161702596755780569202993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45548936795674374092270657 34161702596755780569202993)
        ·
          refine ⟨25621276947566835426902245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34161702596755780569202993 25621276947566835426902245)
          ·
            refine ⟨4803989427668781642544171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25621276947566835426902245 4803989427668781642544171)
            ·
              refine ⟨7205984141503172463816257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4803989427668781642544171 7205984141503172463816257)
              ·
                refine ⟨5404488106127379347862193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7205984141503172463816257 5404488106127379347862193)
                ·
                  refine ⟨4053366079595534510896645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5404488106127379347862193 4053366079595534510896645)
                  ·
                    refine ⟨760006139924162720793121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4053366079595534510896645 760006139924162720793121)
                    ·
                      refine ⟨570004604943122040594841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 760006139924162720793121 570004604943122040594841)
                      ·
                        rfl

theorem cell23_1110080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 2, 2, 4, 2].length) (baseStart_1110080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1110080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1110080 prefixEnd_1110080 := by exact prefixLift 1110080
  have htrace : WordTrace (prefixWord ++ tailWord_1110080) baseStart_1110080 baseEnd_1110080 := by
    simpa [prefixWord, tailWord_1110080, baseEnd_1110080] using wordTrace_append hprefix tailTrace_1110080
  have hstable : (prefixWord ++ tailWord_1110080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1110080).length < 2 ^ (prefixWord ++ tailWord_1110080).sum := by decide
  have hdescent : baseEnd_1110080 < baseStart_1110080 := by decide
  rcases family_descends (prefixWord ++ tailWord_1110080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1110103 : List Nat := [1, 1, 3, 2, 2, 1, 2, 5, 6]
def baseStart_1110103 : Nat := 118140960795 + 1110103 * 2 ^ 59
def prefixEnd_1110103 : Nat := 4983230072969 + 3 ^ 40 * 1110103 * 2
def baseEnd_1110103 : Nat := 63335157222019494511915

theorem tailTrace_1110103 : CollatzResearch.WordTrace tailWord_1110103 prefixEnd_1110103 63335157222019494511915 := by
  unfold tailWord_1110103
  simp only [CollatzResearch.WordTrace]
  refine ⟨40488782697293896343438963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26992521798195930895625975 40488782697293896343438963)
  ·
    refine ⟨60733174045940844515158445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40488782697293896343438963 60733174045940844515158445)
    ·
      refine ⟨22774940267227816693184417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60733174045940844515158445 22774940267227816693184417)
      ·
        refine ⟨17081205200420862519888313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22774940267227816693184417 17081205200420862519888313)
        ·
          refine ⟨12810903900315646889916235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17081205200420862519888313 12810903900315646889916235)
          ·
            refine ⟨19216355850473470334874353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12810903900315646889916235 19216355850473470334874353)
            ·
              refine ⟨14412266887855102751155765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19216355850473470334874353 14412266887855102751155765)
              ·
                refine ⟨1351150020736415882920853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14412266887855102751155765 1351150020736415882920853)
                ·
                  refine ⟨63335157222019494511915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1351150020736415882920853 63335157222019494511915)
                  ·
                    rfl

theorem cell23_1110103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 5, 6].length) (baseStart_1110103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1110103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1110103 prefixEnd_1110103 := by exact prefixLift 1110103
  have htrace : WordTrace (prefixWord ++ tailWord_1110103) baseStart_1110103 baseEnd_1110103 := by
    simpa [prefixWord, tailWord_1110103, baseEnd_1110103] using wordTrace_append hprefix tailTrace_1110103
  have hstable : (prefixWord ++ tailWord_1110103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1110103).length < 2 ^ (prefixWord ++ tailWord_1110103).sum := by decide
  have hdescent : baseEnd_1110103 < baseStart_1110103 := by decide
  rcases family_descends (prefixWord ++ tailWord_1110103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1110113 : List Nat := [1, 2, 3, 1, 1, 2, 1, 1, 1, 7, 3]
def baseStart_1110113 : Nat := 118140960795 + 1110113 * 2 ^ 59
def prefixEnd_1110113 : Nat := 4983230072969 + 3 ^ 40 * 1110113 * 2
def baseEnd_1110113 : Nat := 570021549804720411482189

theorem tailTrace_1110113 : CollatzResearch.WordTrace tailWord_1110113 prefixEnd_1110113 570021549804720411482189 := by
  unfold tailWord_1110113
  simp only [CollatzResearch.WordTrace]
  refine ⟨40489147427257668051302993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26992764951505112034201995 40489147427257668051302993)
  ·
    refine ⟨30366860570443251038477245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40489147427257668051302993 30366860570443251038477245)
    ·
      refine ⟨11387572713916219139428967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30366860570443251038477245 11387572713916219139428967)
      ·
        refine ⟨17081359070874328709143451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11387572713916219139428967 17081359070874328709143451)
        ·
          refine ⟨25622038606311493063715177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17081359070874328709143451 25622038606311493063715177)
          ·
            refine ⟨19216528954733619797786383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25622038606311493063715177 19216528954733619797786383)
            ·
              refine ⟨28824793432100429696679575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19216528954733619797786383 28824793432100429696679575)
              ·
                refine ⟨43237190148150644545019363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28824793432100429696679575 43237190148150644545019363)
                ·
                  refine ⟨64855785222225966817529045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43237190148150644545019363 64855785222225966817529045)
                  ·
                    refine ⟨1520057466145921097285837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 64855785222225966817529045 1520057466145921097285837)
                    ·
                      refine ⟨570021549804720411482189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1520057466145921097285837 570021549804720411482189)
                      ·
                        rfl

theorem cell23_1110113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 1, 1, 7, 3].length) (baseStart_1110113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1110113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1110113 prefixEnd_1110113 := by exact prefixLift 1110113
  have htrace : WordTrace (prefixWord ++ tailWord_1110113) baseStart_1110113 baseEnd_1110113 := by
    simpa [prefixWord, tailWord_1110113, baseEnd_1110113] using wordTrace_append hprefix tailTrace_1110113
  have hstable : (prefixWord ++ tailWord_1110113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1110113).length < 2 ^ (prefixWord ++ tailWord_1110113).sum := by decide
  have hdescent : baseEnd_1110113 < baseStart_1110113 := by decide
  rcases family_descends (prefixWord ++ tailWord_1110113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1110124 : List Nat := [2, 2, 1, 1, 3, 5, 1, 3, 1, 4]
def baseStart_1110124 : Nat := 118140960795 + 1110124 * 2 ^ 59
def prefixEnd_1110124 : Nat := 4983230072969 + 3 ^ 40 * 1110124 * 2
def baseEnd_1110124 : Nat := 190009066030639956148213

theorem tailTrace_1110124 : CollatzResearch.WordTrace tailWord_1110124 prefixEnd_1110124 190009066030639956148213 := by
  unfold tailWord_1110124
  simp only [CollatzResearch.WordTrace]
  refine ⟨20244774315108908464976713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26993032420145211286635617 20244774315108908464976713)
  ·
    refine ⟨15183580736331681348732535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20244774315108908464976713 15183580736331681348732535)
    ·
      refine ⟨22775371104497522023098803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15183580736331681348732535 22775371104497522023098803)
      ·
        refine ⟨34163056656746283034648205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22775371104497522023098803 34163056656746283034648205)
        ·
          refine ⟨12811146246279856137993077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34163056656746283034648205 12811146246279856137993077)
          ·
            refine ⟨1201044960588736512936851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 12811146246279856137993077 1201044960588736512936851)
            ·
              refine ⟨1801567440883104769405277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1201044960588736512936851 1801567440883104769405277)
              ·
                refine ⟨675587790331164288526979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1801567440883104769405277 675587790331164288526979)
                ·
                  refine ⟨1013381685496746432790469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 675587790331164288526979 1013381685496746432790469)
                  ·
                    refine ⟨190009066030639956148213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1013381685496746432790469 190009066030639956148213)
                    ·
                      rfl

theorem cell23_1110124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 5, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 5, 1, 3, 1, 4].length) (baseStart_1110124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1110124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1110124 prefixEnd_1110124 := by exact prefixLift 1110124
  have htrace : WordTrace (prefixWord ++ tailWord_1110124) baseStart_1110124 baseEnd_1110124 := by
    simpa [prefixWord, tailWord_1110124, baseEnd_1110124] using wordTrace_append hprefix tailTrace_1110124
  have hstable : (prefixWord ++ tailWord_1110124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1110124).length < 2 ^ (prefixWord ++ tailWord_1110124).sum := by decide
  have hdescent : baseEnd_1110124 < baseStart_1110124 := by decide
  rcases family_descends (prefixWord ++ tailWord_1110124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1110147 : List Nat := [1, 1, 1, 3, 3, 3, 3, 1, 3, 1, 3]
def baseStart_1110147 : Nat := 118140960795 + 1110147 * 2 ^ 59
def prefixEnd_1110147 : Nat := 4983230072969 + 3 ^ 40 * 1110147 * 2
def baseEnd_1110147 : Nat := 570039008146973278457033

theorem tailTrace_1110147 : CollatzResearch.WordTrace tailWord_1110147 prefixEnd_1110147 570039008146973278457033 := by
  unfold tailWord_1110147
  simp only [CollatzResearch.WordTrace]
  refine ⟨40490387509134491858040695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26993591672756327905360463 40490387509134491858040695)
  ·
    refine ⟨60735581263701737787061043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40490387509134491858040695 60735581263701737787061043)
    ·
      refine ⟨91103371895552606680591565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60735581263701737787061043 91103371895552606680591565)
      ·
        refine ⟨34163764460832227505221837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 91103371895552606680591565 34163764460832227505221837)
        ·
          refine ⟨12811411672812085314458189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34163764460832227505221837 12811411672812085314458189)
          ·
            refine ⟨4804279377304531992921821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12811411672812085314458189 4804279377304531992921821)
            ·
              refine ⟨1801604766489199497345683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4804279377304531992921821 1801604766489199497345683)
              ·
                refine ⟨2702407149733799246018525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1801604766489199497345683 2702407149733799246018525)
                ·
                  refine ⟨1013402681150174717256947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2702407149733799246018525 1013402681150174717256947)
                  ·
                    refine ⟨1520104021725262075885421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1013402681150174717256947 1520104021725262075885421)
                    ·
                      refine ⟨570039008146973278457033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1520104021725262075885421 570039008146973278457033)
                      ·
                        rfl

theorem cell23_1110147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 3, 1, 3, 1, 3].length) (baseStart_1110147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1110147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1110147 prefixEnd_1110147 := by exact prefixLift 1110147
  have htrace : WordTrace (prefixWord ++ tailWord_1110147) baseStart_1110147 baseEnd_1110147 := by
    simpa [prefixWord, tailWord_1110147, baseEnd_1110147] using wordTrace_append hprefix tailTrace_1110147
  have hstable : (prefixWord ++ tailWord_1110147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1110147).length < 2 ^ (prefixWord ++ tailWord_1110147).sum := by decide
  have hdescent : baseEnd_1110147 < baseStart_1110147 := by decide
  rcases family_descends (prefixWord ++ tailWord_1110147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1110163 : List Nat := [1, 1, 1, 2, 1, 2, 3, 5, 1, 6]
def baseStart_1110163 : Nat := 118140960795 + 1110163 * 2 ^ 59
def prefixEnd_1110163 : Nat := 4983230072969 + 3 ^ 40 * 1110163 * 2
def baseEnd_1110163 : Nat := 190015741279148405285653

theorem tailTrace_1110163 : CollatzResearch.WordTrace tailWord_1110163 prefixEnd_1110163 190015741279148405285653 := by
  unfold tailWord_1110163
  simp only [CollatzResearch.WordTrace]
  refine ⟨40490971077076526590623143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26993980718051017727082095 40490971077076526590623143)
  ·
    refine ⟨60736456615614789885934715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40490971077076526590623143 60736456615614789885934715)
    ·
      refine ⟨91104684923422184828902073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60736456615614789885934715 91104684923422184828902073)
      ·
        refine ⟨68328513692566638621676555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91104684923422184828902073 68328513692566638621676555)
        ·
          refine ⟨102492770538849957932514833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68328513692566638621676555 102492770538849957932514833)
          ·
            refine ⟨76869577904137468449386125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 102492770538849957932514833 76869577904137468449386125)
            ·
              refine ⟨28826091714051550668519797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 76869577904137468449386125 28826091714051550668519797)
              ·
                refine ⟨2702446098192332875173731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 28826091714051550668519797 2702446098192332875173731)
                ·
                  refine ⟨4053669147288499312760597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2702446098192332875173731 4053669147288499312760597)
                  ·
                    refine ⟨190015741279148405285653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4053669147288499312760597 190015741279148405285653)
                    ·
                      rfl

theorem cell23_1110163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 5, 1, 6].length) (baseStart_1110163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1110163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1110163 prefixEnd_1110163 := by exact prefixLift 1110163
  have htrace : WordTrace (prefixWord ++ tailWord_1110163) baseStart_1110163 baseEnd_1110163 := by
    simpa [prefixWord, tailWord_1110163, baseEnd_1110163] using wordTrace_append hprefix tailTrace_1110163
  have hstable : (prefixWord ++ tailWord_1110163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1110163).length < 2 ^ (prefixWord ++ tailWord_1110163).sum := by decide
  have hdescent : baseEnd_1110163 < baseStart_1110163 := by decide
  rcases family_descends (prefixWord ++ tailWord_1110163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1110193 : List Nat := [1, 2, 2, 5, 13]
def baseStart_1110193 : Nat := 118140960795 + 1110193 * 2 ^ 59
def prefixEnd_1110193 : Nat := 4983230072969 + 3 ^ 40 * 1110193 * 2
def baseEnd_1110193 : Nat := 781978913932894510949

theorem tailTrace_1110193 : CollatzResearch.WordTrace tailWord_1110193 prefixEnd_1110193 781978913932894510949 := by
  unfold tailWord_1110193
  simp only [CollatzResearch.WordTrace]
  refine ⟨40492065266967841714215233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26994710177978561142810155 40492065266967841714215233)
  ·
    refine ⟨30369048950225881285661425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40492065266967841714215233 30369048950225881285661425)
    ·
      refine ⟨22776786712669410964246069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30369048950225881285661425 22776786712669410964246069)
      ·
        refine ⟨2135323754312757277898069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 22776786712669410964246069 2135323754312757277898069)
        ·
          refine ⟨781978913932894510949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 2135323754312757277898069 781978913932894510949)
          ·
            rfl

theorem cell23_1110193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 13].length) (baseStart_1110193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1110193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1110193 prefixEnd_1110193 := by exact prefixLift 1110193
  have htrace : WordTrace (prefixWord ++ tailWord_1110193) baseStart_1110193 baseEnd_1110193 := by
    simpa [prefixWord, tailWord_1110193, baseEnd_1110193] using wordTrace_append hprefix tailTrace_1110193
  have hstable : (prefixWord ++ tailWord_1110193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1110193).length < 2 ^ (prefixWord ++ tailWord_1110193).sum := by decide
  have hdescent : baseEnd_1110193 < baseStart_1110193 := by decide
  rcases family_descends (prefixWord ++ tailWord_1110193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1110213 : List Nat := [1, 3, 1, 1, 1, 1, 4, 1, 2, 2, 6]
def baseStart_1110213 : Nat := 118140960795 + 1110213 * 2 ^ 59
def prefixEnd_1110213 : Nat := 4983230072969 + 3 ^ 40 * 1110213 * 2
def baseEnd_1110213 : Nat := 570072897870170020231729

theorem tailTrace_1110213 : CollatzResearch.WordTrace tailWord_1110213 prefixEnd_1110213 570072897870170020231729 := by
  unfold tailWord_1110213
  simp only [CollatzResearch.WordTrace]
  refine ⟨40492794726895385129943293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26995196484596923419962195 40492794726895385129943293)
  ·
    refine ⟨15184798022585769423728735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40492794726895385129943293 15184798022585769423728735)
    ·
      refine ⟨22777197033878654135593103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15184798022585769423728735 22777197033878654135593103)
      ·
        refine ⟨34165795550817981203389655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22777197033878654135593103 34165795550817981203389655)
        ·
          refine ⟨51248693326226971805084483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34165795550817981203389655 51248693326226971805084483)
          ·
            refine ⟨76873039989340457707626725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51248693326226971805084483 76873039989340457707626725)
            ·
              refine ⟨14413694998001335820180011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 76873039989340457707626725 14413694998001335820180011)
              ·
                refine ⟨21620542497002003730270017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14413694998001335820180011 21620542497002003730270017)
                ·
                  refine ⟨16215406872751502797702513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21620542497002003730270017 16215406872751502797702513)
                  ·
                    refine ⟨12161555154563627098276885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16215406872751502797702513 12161555154563627098276885)
                    ·
                      refine ⟨570072897870170020231729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 12161555154563627098276885 570072897870170020231729)
                      ·
                        rfl

theorem cell23_1110213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 1, 2, 2, 6].length) (baseStart_1110213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1110213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1110213 prefixEnd_1110213 := by exact prefixLift 1110213
  have htrace : WordTrace (prefixWord ++ tailWord_1110213) baseStart_1110213 baseEnd_1110213 := by
    simpa [prefixWord, tailWord_1110213, baseEnd_1110213] using wordTrace_append hprefix tailTrace_1110213
  have hstable : (prefixWord ++ tailWord_1110213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1110213).length < 2 ^ (prefixWord ++ tailWord_1110213).sum := by decide
  have hdescent : baseEnd_1110213 < baseStart_1110213 := by decide
  rcases family_descends (prefixWord ++ tailWord_1110213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1110223 : List Nat := [1, 1, 2, 1, 1, 3, 3, 2, 2, 7]
def baseStart_1110223 : Nat := 118140960795 + 1110223 * 2 ^ 59
def prefixEnd_1110223 : Nat := 4983230072969 + 3 ^ 40 * 1110223 * 2
def baseEnd_1110223 : Nat := 190026010892238327035561

theorem tailTrace_1110223 : CollatzResearch.WordTrace tailWord_1110223 prefixEnd_1110223 190026010892238327035561 := by
  unfold tailWord_1110223
  simp only [CollatzResearch.WordTrace]
  refine ⟨40493159456859156837807323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26995439637906104558538215 40493159456859156837807323)
  ·
    refine ⟨60739739185288735256710985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40493159456859156837807323 60739739185288735256710985)
    ·
      refine ⟨45554804388966551442533239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60739739185288735256710985 45554804388966551442533239)
      ·
        refine ⟨68332206583449827163799859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45554804388966551442533239 68332206583449827163799859)
        ·
          refine ⟨102498309875174740745699789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68332206583449827163799859 102498309875174740745699789)
          ·
            refine ⟨38436866203190527779637421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 102498309875174740745699789 38436866203190527779637421)
            ·
              refine ⟨14413824826196447917364033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38436866203190527779637421 14413824826196447917364033)
              ·
                refine ⟨10810368619647335938023025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14413824826196447917364033 10810368619647335938023025)
                ·
                  refine ⟨8107776464735501953517269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10810368619647335938023025 8107776464735501953517269)
                  ·
                    refine ⟨190026010892238327035561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 8107776464735501953517269 190026010892238327035561)
                    ·
                      rfl

theorem cell23_1110223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 2, 2, 7].length) (baseStart_1110223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1110223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1110223 prefixEnd_1110223 := by exact prefixLift 1110223
  have htrace : WordTrace (prefixWord ++ tailWord_1110223) baseStart_1110223 baseEnd_1110223 := by
    simpa [prefixWord, tailWord_1110223, baseEnd_1110223] using wordTrace_append hprefix tailTrace_1110223
  have hstable : (prefixWord ++ tailWord_1110223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1110223).length < 2 ^ (prefixWord ++ tailWord_1110223).sum := by decide
  have hdescent : baseEnd_1110223 < baseStart_1110223 := by decide
  rcases family_descends (prefixWord ++ tailWord_1110223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1110277 : List Nat := [1, 3, 1, 1, 2, 1, 2, 5, 1, 4, 2]
def baseStart_1110277 : Nat := 118140960795 + 1110277 * 2 ^ 59
def prefixEnd_1110277 : Nat := 4983230072969 + 3 ^ 40 * 1110277 * 2
def baseEnd_1110277 : Nat := 570105760632057769831435

theorem tailTrace_1110277 : CollatzResearch.WordTrace tailWord_1110277 prefixEnd_1110277 570105760632057769831435 := by
  unfold tailWord_1110277
  simp only [CollatzResearch.WordTrace]
  refine ⟨40495128998663524060273085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26996752665775682706848723 40495128998663524060273085)
  ·
    refine ⟨15185673374498821522602407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40495128998663524060273085 15185673374498821522602407)
    ·
      refine ⟨22778510061748232283903611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15185673374498821522602407 22778510061748232283903611)
      ·
        refine ⟨34167765092622348425855417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22778510061748232283903611 34167765092622348425855417)
        ·
          refine ⟨25625823819466761319391563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34167765092622348425855417 25625823819466761319391563)
          ·
            refine ⟨38438735729200141979087345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25625823819466761319391563 38438735729200141979087345)
            ·
              refine ⟨28829051796900106484315509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38438735729200141979087345 28829051796900106484315509)
              ·
                refine ⟨2702723605959384982904579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 28829051796900106484315509 2702723605959384982904579)
                ·
                  refine ⟨4054085408939077474356869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2702723605959384982904579 4054085408939077474356869)
                  ·
                    refine ⟨760141014176077026441913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4054085408939077474356869 760141014176077026441913)
                    ·
                      refine ⟨570105760632057769831435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 760141014176077026441913 570105760632057769831435)
                      ·
                        rfl

theorem cell23_1110277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 5, 1, 4, 2].length) (baseStart_1110277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1110277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1110277 prefixEnd_1110277 := by exact prefixLift 1110277
  have htrace : WordTrace (prefixWord ++ tailWord_1110277) baseStart_1110277 baseEnd_1110277 := by
    simpa [prefixWord, tailWord_1110277, baseEnd_1110277] using wordTrace_append hprefix tailTrace_1110277
  have hstable : (prefixWord ++ tailWord_1110277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1110277).length < 2 ^ (prefixWord ++ tailWord_1110277).sum := by decide
  have hdescent : baseEnd_1110277 < baseStart_1110277 := by decide
  rcases family_descends (prefixWord ++ tailWord_1110277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1110367 : List Nat := [1, 1, 2, 3, 1, 2, 4, 2, 2, 1, 4]
def baseStart_1110367 : Nat := 118140960795 + 1110367 * 2 ^ 59
def prefixEnd_1110367 : Nat := 4983230072969 + 3 ^ 40 * 1110367 * 2
def baseEnd_1110367 : Nat := 570151973890962417706021

theorem tailTrace_1110367 : CollatzResearch.WordTrace tailWord_1110367 prefixEnd_1110367 570151973890962417706021 := by
  unfold tailWord_1110367
  simp only [CollatzResearch.WordTrace]
  refine ⟨40498411568337469431049355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26998941045558312954032903 40498411568337469431049355)
  ·
    refine ⟨60747617352506204146574033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40498411568337469431049355 60747617352506204146574033)
    ·
      refine ⟨45560713014379653109930525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60747617352506204146574033 45560713014379653109930525)
      ·
        refine ⟨17085267380392369916223947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45560713014379653109930525 17085267380392369916223947)
        ·
          refine ⟨25627901070588554874335921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17085267380392369916223947 25627901070588554874335921)
          ·
            refine ⟨19220925802941416155751941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25627901070588554874335921 19220925802941416155751941)
            ·
              refine ⟨3603923588051515529203489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19220925802941416155751941 3603923588051515529203489)
              ·
                refine ⟨2702942691038636646902617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3603923588051515529203489 2702942691038636646902617)
                ·
                  refine ⟨2027207018278977485176963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2702942691038636646902617 2027207018278977485176963)
                  ·
                    refine ⟨3040810527418466227765445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2027207018278977485176963 3040810527418466227765445)
                    ·
                      refine ⟨570151973890962417706021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3040810527418466227765445 570151973890962417706021)
                      ·
                        rfl

theorem cell23_1110367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 4, 2, 2, 1, 4].length) (baseStart_1110367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1110367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1110367 prefixEnd_1110367 := by exact prefixLift 1110367
  have htrace : WordTrace (prefixWord ++ tailWord_1110367) baseStart_1110367 baseEnd_1110367 := by
    simpa [prefixWord, tailWord_1110367, baseEnd_1110367] using wordTrace_append hprefix tailTrace_1110367
  have hstable : (prefixWord ++ tailWord_1110367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1110367).length < 2 ^ (prefixWord ++ tailWord_1110367).sum := by decide
  have hdescent : baseEnd_1110367 < baseStart_1110367 := by decide
  rcases family_descends (prefixWord ++ tailWord_1110367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1110368 : List Nat := [2, 1, 1, 3, 6, 1, 2, 2, 5]
def baseStart_1110368 : Nat := 118140960795 + 1110368 * 2 ^ 59
def prefixEnd_1110368 : Nat := 4983230072969 + 3 ^ 40 * 1110368 * 2
def baseEnd_1110368 : Nat := 63350276374624101532613

theorem tailTrace_1110368 : CollatzResearch.WordTrace tailWord_1110368 prefixEnd_1110368 63350276374624101532613 := by
  unfold tailWord_1110368
  simp only [CollatzResearch.WordTrace]
  refine ⟨20249224020666923300917879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26998965360889231067890505 20249224020666923300917879)
  ·
    refine ⟨30373836031000384951376819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20249224020666923300917879 30373836031000384951376819)
    ·
      refine ⟨45560754046500577427065229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30373836031000384951376819 45560754046500577427065229)
      ·
        refine ⟨17085282767437716535149461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45560754046500577427065229 17085282767437716535149461)
        ·
          refine ⟨800872629723642962585131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 17085282767437716535149461 800872629723642962585131)
          ·
            refine ⟨1201308944585464443877697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 800872629723642962585131 1201308944585464443877697)
            ·
              refine ⟨900981708439098332908273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1201308944585464443877697 900981708439098332908273)
              ·
                refine ⟨675736281329323749681205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 900981708439098332908273 675736281329323749681205)
                ·
                  refine ⟨63350276374624101532613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 675736281329323749681205 63350276374624101532613)
                  ·
                    rfl

theorem cell23_1110368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 6, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 6, 1, 2, 2, 5].length) (baseStart_1110368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1110368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1110368 prefixEnd_1110368 := by exact prefixLift 1110368
  have htrace : WordTrace (prefixWord ++ tailWord_1110368) baseStart_1110368 baseEnd_1110368 := by
    simpa [prefixWord, tailWord_1110368, baseEnd_1110368] using wordTrace_append hprefix tailTrace_1110368
  have hstable : (prefixWord ++ tailWord_1110368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1110368).length < 2 ^ (prefixWord ++ tailWord_1110368).sum := by decide
  have hdescent : baseEnd_1110368 < baseStart_1110368 := by decide
  rcases family_descends (prefixWord ++ tailWord_1110368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1110377 : List Nat := [1, 2, 1, 1, 1, 3, 4, 3, 3, 4]
def baseStart_1110377 : Nat := 118140960795 + 1110377 * 2 ^ 59
def prefixEnd_1110377 : Nat := 4983230072969 + 3 ^ 40 * 1110377 * 2
def baseEnd_1110377 : Nat := 190052369565835792860325

theorem tailTrace_1110377 : CollatzResearch.WordTrace tailWord_1110377 prefixEnd_1110377 190052369565835792860325 := by
  unfold tailWord_1110377
  simp only [CollatzResearch.WordTrace]
  refine ⟨40498776298301241138913385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26999184198867494092608923 40498776298301241138913385)
  ·
    refine ⟨30374082223725930854185039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40498776298301241138913385 30374082223725930854185039)
    ·
      refine ⟨45561123335588896281277559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30374082223725930854185039 45561123335588896281277559)
      ·
        refine ⟨68341685003383344421916339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45561123335588896281277559 68341685003383344421916339)
        ·
          refine ⟨102512527505075016632874509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68341685003383344421916339 102512527505075016632874509)
          ·
            refine ⟨38442197814403131237327941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 102512527505075016632874509 38442197814403131237327941)
            ·
              refine ⟨7207912090200587106998989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38442197814403131237327941 7207912090200587106998989)
              ·
                refine ⟨2702967033825220165124621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7207912090200587106998989 2702967033825220165124621)
                ·
                  refine ⟨1013612637684457561921733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2702967033825220165124621 1013612637684457561921733)
                  ·
                    refine ⟨190052369565835792860325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1013612637684457561921733 190052369565835792860325)
                    ·
                      rfl

theorem cell23_1110377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 3, 3, 4].length) (baseStart_1110377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1110377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1110377 prefixEnd_1110377 := by exact prefixLift 1110377
  have htrace : WordTrace (prefixWord ++ tailWord_1110377) baseStart_1110377 baseEnd_1110377 := by
    simpa [prefixWord, tailWord_1110377, baseEnd_1110377] using wordTrace_append hprefix tailTrace_1110377
  have hstable : (prefixWord ++ tailWord_1110377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1110377).length < 2 ^ (prefixWord ++ tailWord_1110377).sum := by decide
  have hdescent : baseEnd_1110377 < baseStart_1110377 := by decide
  rcases family_descends (prefixWord ++ tailWord_1110377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1110384 : List Nat := [2, 1, 1, 1, 4, 4, 1, 1, 2, 4, 2]
def baseStart_1110384 : Nat := 118140960795 + 1110384 * 2 ^ 59
def prefixEnd_1110384 : Nat := 4983230072969 + 3 ^ 40 * 1110384 * 2
def baseEnd_1110384 : Nat := 570160703062088851193443

theorem tailTrace_1110384 : CollatzResearch.WordTrace tailWord_1110384 prefixEnd_1110384 570160703062088851193443 := by
  unfold tailWord_1110384
  simp only [CollatzResearch.WordTrace]
  refine ⟨20249515804637940667209103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26999354406183920889612137 20249515804637940667209103)
  ·
    refine ⟨30374273706956911000813655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20249515804637940667209103 30374273706956911000813655)
    ·
      refine ⟨45561410560435366501220483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30374273706956911000813655 45561410560435366501220483)
      ·
        refine ⟨68342115840653049751830725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45561410560435366501220483 68342115840653049751830725)
        ·
          refine ⟨12814146720122446828468261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 68342115840653049751830725 12814146720122446828468261)
          ·
            refine ⟨2402652510022958780337799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12814146720122446828468261 2402652510022958780337799)
            ·
              refine ⟨3603978765034438170506699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2402652510022958780337799 3603978765034438170506699)
              ·
                refine ⟨5405968147551657255760049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3603978765034438170506699 5405968147551657255760049)
                ·
                  refine ⟨4054476110663742941820037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5405968147551657255760049 4054476110663742941820037)
                  ·
                    refine ⟨760214270749451801591257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4054476110663742941820037 760214270749451801591257)
                    ·
                      refine ⟨570160703062088851193443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 760214270749451801591257 570160703062088851193443)
                      ·
                        rfl

theorem cell23_1110384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 1, 1, 2, 4, 2].length) (baseStart_1110384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1110384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1110384 prefixEnd_1110384 := by exact prefixLift 1110384
  have htrace : WordTrace (prefixWord ++ tailWord_1110384) baseStart_1110384 baseEnd_1110384 := by
    simpa [prefixWord, tailWord_1110384, baseEnd_1110384] using wordTrace_append hprefix tailTrace_1110384
  have hstable : (prefixWord ++ tailWord_1110384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1110384).length < 2 ^ (prefixWord ++ tailWord_1110384).sum := by decide
  have hdescent : baseEnd_1110384 < baseStart_1110384 := by decide
  rcases family_descends (prefixWord ++ tailWord_1110384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1110401 : List Nat := [1, 2, 4, 3, 1, 3, 1, 1, 2, 1, 4]
def baseStart_1110401 : Nat := 118140960795 + 1110401 * 2 ^ 59
def prefixEnd_1110401 : Nat := 4983230072969 + 3 ^ 40 * 1110401 * 2
def baseEnd_1110401 : Nat := 570169432233215284680865

theorem tailTrace_1110401 : CollatzResearch.WordTrace tailWord_1110401 prefixEnd_1110401 570169432233215284680865 := by
  unfold tailWord_1110401
  simp only [CollatzResearch.WordTrace]
  refine ⟨40499651650214293237787057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26999767766809528825191371 40499651650214293237787057)
  ·
    refine ⟨30374738737660719928340293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40499651650214293237787057 30374738737660719928340293)
    ·
      refine ⟨5695263513311384986563805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30374738737660719928340293 5695263513311384986563805)
      ·
        refine ⟨2135723817491769369961427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5695263513311384986563805 2135723817491769369961427)
        ·
          refine ⟨3203585726237654054942141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2135723817491769369961427 3203585726237654054942141)
          ·
            refine ⟨1201344647339120270603303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3203585726237654054942141 1201344647339120270603303)
            ·
              refine ⟨1802016971008680405904955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1201344647339120270603303 1802016971008680405904955)
              ·
                refine ⟨2703025456513020608857433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1802016971008680405904955 2703025456513020608857433)
                ·
                  refine ⟨2027269092384765456643075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2703025456513020608857433 2027269092384765456643075)
                  ·
                    refine ⟨3040903638577148184964613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2027269092384765456643075 3040903638577148184964613)
                    ·
                      refine ⟨570169432233215284680865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3040903638577148184964613 570169432233215284680865)
                      ·
                        rfl

theorem cell23_1110401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 3, 1, 1, 2, 1, 4].length) (baseStart_1110401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1110401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1110401 prefixEnd_1110401 := by exact prefixLift 1110401
  have htrace : WordTrace (prefixWord ++ tailWord_1110401) baseStart_1110401 baseEnd_1110401 := by
    simpa [prefixWord, tailWord_1110401, baseEnd_1110401] using wordTrace_append hprefix tailTrace_1110401
  have hstable : (prefixWord ++ tailWord_1110401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1110401).length < 2 ^ (prefixWord ++ tailWord_1110401).sum := by decide
  have hdescent : baseEnd_1110401 < baseStart_1110401 := by decide
  rcases family_descends (prefixWord ++ tailWord_1110401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1110411 : List Nat := [1, 1, 1, 1, 4, 5, 2, 3, 1, 4]
def baseStart_1110411 : Nat := 118140960795 + 1110411 * 2 ^ 59
def prefixEnd_1110411 : Nat := 4983230072969 + 3 ^ 40 * 1110411 * 2
def baseEnd_1110411 : Nat := 190058189013253415185273

theorem tailTrace_1110411 : CollatzResearch.WordTrace tailWord_1110411 prefixEnd_1110411 190058189013253415185273 := by
  unfold tailWord_1110411
  simp only [CollatzResearch.WordTrace]
  refine ⟨40500016380178064945651087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27000010920118709963767391 40500016380178064945651087)
  ·
    refine ⟨60750024570267097418476631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40500016380178064945651087 60750024570267097418476631)
    ·
      refine ⟨91125036855400646127714947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60750024570267097418476631 91125036855400646127714947)
      ·
        refine ⟨136687555283100969191572421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91125036855400646127714947 136687555283100969191572421)
        ·
          refine ⟨25628916615581431723419829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 136687555283100969191572421 25628916615581431723419829)
          ·
            refine ⟨2402710932710759224070609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 25628916615581431723419829 2402710932710759224070609)
            ·
              refine ⟨1802033199533069418052957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2402710932710759224070609 1802033199533069418052957)
              ·
                refine ⟨675762449824901031769859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1802033199533069418052957 675762449824901031769859)
                ·
                  refine ⟨1013643674737351547654789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 675762449824901031769859 1013643674737351547654789)
                  ·
                    refine ⟨190058189013253415185273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1013643674737351547654789 190058189013253415185273)
                    ·
                      rfl

theorem cell23_1110411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 2, 3, 1, 4].length) (baseStart_1110411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1110411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1110411 prefixEnd_1110411 := by exact prefixLift 1110411
  have htrace : WordTrace (prefixWord ++ tailWord_1110411) baseStart_1110411 baseEnd_1110411 := by
    simpa [prefixWord, tailWord_1110411, baseEnd_1110411] using wordTrace_append hprefix tailTrace_1110411
  have hstable : (prefixWord ++ tailWord_1110411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1110411).length < 2 ^ (prefixWord ++ tailWord_1110411).sum := by decide
  have hdescent : baseEnd_1110411 < baseStart_1110411 := by decide
  rcases family_descends (prefixWord ++ tailWord_1110411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1110424 : List Nat := [2, 1, 2, 5, 1, 1, 3, 2, 6]
def baseStart_1110424 : Nat := 118140960795 + 1110424 * 2 ^ 59
def prefixEnd_1110424 : Nat := 4983230072969 + 3 ^ 40 * 1110424 * 2
def baseEnd_1110424 : Nat := 63353471365363188299251

theorem tailTrace_1110424 : CollatzResearch.WordTrace tailWord_1110424 prefixEnd_1110424 63353471365363188299251 := by
  unfold tailWord_1110424
  simp only [CollatzResearch.WordTrace]
  refine ⟨20250245264565484082937163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27000327019420645443916217 20250245264565484082937163)
  ·
    refine ⟨30375367896848226124405745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20250245264565484082937163 30375367896848226124405745)
    ·
      refine ⟨22781525922636169593304309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30375367896848226124405745 22781525922636169593304309)
      ·
        refine ⟨2135768055247140899372279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 22781525922636169593304309 2135768055247140899372279)
        ·
          refine ⟨3203652082870711349058419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2135768055247140899372279 3203652082870711349058419)
          ·
            refine ⟨4805478124306067023587629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3203652082870711349058419 4805478124306067023587629)
            ·
              refine ⟨1802054296614775133845361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4805478124306067023587629 1802054296614775133845361)
              ·
                refine ⟨1351540722461081350384021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1802054296614775133845361 1351540722461081350384021)
                ·
                  refine ⟨63353471365363188299251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1351540722461081350384021 63353471365363188299251)
                  ·
                    rfl

theorem cell23_1110424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 3, 2, 6].length) (baseStart_1110424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1110424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1110424 prefixEnd_1110424 := by exact prefixLift 1110424
  have htrace : WordTrace (prefixWord ++ tailWord_1110424) baseStart_1110424 baseEnd_1110424 := by
    simpa [prefixWord, tailWord_1110424, baseEnd_1110424] using wordTrace_append hprefix tailTrace_1110424
  have hstable : (prefixWord ++ tailWord_1110424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1110424).length < 2 ^ (prefixWord ++ tailWord_1110424).sum := by decide
  have hdescent : baseEnd_1110424 < baseStart_1110424 := by decide
  rcases family_descends (prefixWord ++ tailWord_1110424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1110474 : List Nat := [3, 1, 2, 1, 2, 2, 1, 5, 1, 1, 4]
def baseStart_1110474 : Nat := 118140960795 + 1110474 * 2 ^ 59
def prefixEnd_1110474 : Nat := 4983230072969 + 3 ^ 40 * 1110474 * 2
def baseEnd_1110474 : Nat := 570206916320993499068029

theorem tailTrace_1110474 : CollatzResearch.WordTrace tailWord_1110474 prefixEnd_1110474 570206916320993499068029 := by
  unfold tailWord_1110474
  simp only [CollatzResearch.WordTrace]
  refine ⟨10125578544737456676298619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27001542785966551136796317 10125578544737456676298619)
  ·
    refine ⟨15188367817106185014447929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10125578544737456676298619 15188367817106185014447929)
    ·
      refine ⟨11391275862829638760835947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15188367817106185014447929 11391275862829638760835947)
      ·
        refine ⟨17086913794244458141253921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11391275862829638760835947 17086913794244458141253921)
        ·
          refine ⟨12815185345683343605940441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17086913794244458141253921 12815185345683343605940441)
          ·
            refine ⟨9611389009262507704455331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12815185345683343605940441 9611389009262507704455331)
            ·
              refine ⟨14417083513893761556682997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9611389009262507704455331 14417083513893761556682997)
              ·
                refine ⟨1351601579427540145939031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14417083513893761556682997 1351601579427540145939031)
                ·
                  refine ⟨2027402369141310218908547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1351601579427540145939031 2027402369141310218908547)
                  ·
                    refine ⟨3041103553711965328362821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2027402369141310218908547 3041103553711965328362821)
                    ·
                      refine ⟨570206916320993499068029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3041103553711965328362821 570206916320993499068029)
                      ·
                        rfl

theorem cell23_1110474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 5, 1, 1, 4].length) (baseStart_1110474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1110474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1110474 prefixEnd_1110474 := by exact prefixLift 1110474
  have htrace : WordTrace (prefixWord ++ tailWord_1110474) baseStart_1110474 baseEnd_1110474 := by
    simpa [prefixWord, tailWord_1110474, baseEnd_1110474] using wordTrace_append hprefix tailTrace_1110474
  have hstable : (prefixWord ++ tailWord_1110474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1110474).length < 2 ^ (prefixWord ++ tailWord_1110474).sum := by decide
  have hdescent : baseEnd_1110474 < baseStart_1110474 := by decide
  rcases family_descends (prefixWord ++ tailWord_1110474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1110485 : List Nat := [1, 3, 2, 3, 1, 3, 3, 2, 1, 1, 3]
def baseStart_1110485 : Nat := 118140960795 + 1110485 * 2 ^ 59
def prefixEnd_1110485 : Nat := 4983230072969 + 3 ^ 40 * 1110485 * 2
def baseEnd_1110485 : Nat := 570212564608192956030479

theorem tailTrace_1110485 : CollatzResearch.WordTrace tailWord_1110485 prefixEnd_1110485 570212564608192956030479 := by
  unfold tailWord_1110485
  simp only [CollatzResearch.WordTrace]
  refine ⟨40502715381909975583844909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27001810254606650389229939 40502715381909975583844909)
  ·
    refine ⟨15188518268216240843941841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40502715381909975583844909 15188518268216240843941841)
    ·
      refine ⟨11391388701162180632956381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15188518268216240843941841 11391388701162180632956381)
      ·
        refine ⟨4271770762935817737358643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11391388701162180632956381 4271770762935817737358643)
        ·
          refine ⟨6407656144403726606037965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4271770762935817737358643 6407656144403726606037965)
          ·
            refine ⟨2402871054151397477264237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6407656144403726606037965 2402871054151397477264237)
            ·
              refine ⟨901076645306774053974089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2402871054151397477264237 901076645306774053974089)
              ·
                refine ⟨675807483980080540480567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 901076645306774053974089 675807483980080540480567)
                ·
                  refine ⟨1013711225970120810720851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 675807483980080540480567 1013711225970120810720851)
                  ·
                    refine ⟨1520566838955181216081277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1013711225970120810720851 1520566838955181216081277)
                    ·
                      refine ⟨570212564608192956030479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1520566838955181216081277 570212564608192956030479)
                      ·
                        rfl

theorem cell23_1110485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 3, 2, 1, 1, 3].length) (baseStart_1110485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1110485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1110485 prefixEnd_1110485 := by exact prefixLift 1110485
  have htrace : WordTrace (prefixWord ++ tailWord_1110485) baseStart_1110485 baseEnd_1110485 := by
    simpa [prefixWord, tailWord_1110485, baseEnd_1110485] using wordTrace_append hprefix tailTrace_1110485
  have hstable : (prefixWord ++ tailWord_1110485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1110485).length < 2 ^ (prefixWord ++ tailWord_1110485).sum := by decide
  have hdescent : baseEnd_1110485 < baseStart_1110485 := by decide
  rcases family_descends (prefixWord ++ tailWord_1110485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1110497 : List Nat := [1, 2, 3, 1, 2, 2, 4, 8]
def baseStart_1110497 : Nat := 118140960795 + 1110497 * 2 ^ 59
def prefixEnd_1110497 : Nat := 4983230072969 + 3 ^ 40 * 1110497 * 2
def baseEnd_1110497 : Nat := 21119212088001737373349

theorem tailTrace_1110497 : CollatzResearch.WordTrace tailWord_1110497 prefixEnd_1110497 21119212088001737373349 := by
  unfold tailWord_1110497
  simp only [CollatzResearch.WordTrace]
  refine ⟨40503153057866501633281745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27002102038577667755521163 40503153057866501633281745)
  ·
    refine ⟨30377364793399876224961309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40503153057866501633281745 30377364793399876224961309)
    ·
      refine ⟨11391511797524953584360491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30377364793399876224961309 11391511797524953584360491)
      ·
        refine ⟨17087267696287430376540737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11391511797524953584360491 17087267696287430376540737)
        ·
          refine ⟨12815450772215572782405553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17087267696287430376540737 12815450772215572782405553)
          ·
            refine ⟨9611588079161679586804165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12815450772215572782405553 9611588079161679586804165)
            ·
              refine ⟨1802172764842814922525781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9611588079161679586804165 1802172764842814922525781)
              ·
                refine ⟨21119212088001737373349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1802172764842814922525781 21119212088001737373349)
                ·
                  rfl

theorem cell23_1110497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 4, 8].length) (baseStart_1110497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1110497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1110497 prefixEnd_1110497 := by exact prefixLift 1110497
  have htrace : WordTrace (prefixWord ++ tailWord_1110497) baseStart_1110497 baseEnd_1110497 := by
    simpa [prefixWord, tailWord_1110497, baseEnd_1110497] using wordTrace_append hprefix tailTrace_1110497
  have hstable : (prefixWord ++ tailWord_1110497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1110497).length < 2 ^ (prefixWord ++ tailWord_1110497).sum := by decide
  have hdescent : baseEnd_1110497 < baseStart_1110497 := by decide
  rcases family_descends (prefixWord ++ tailWord_1110497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1110542 : List Nat := [4, 1, 1, 2, 3, 1, 4, 2, 1, 2, 2]
def baseStart_1110542 : Nat := 118140960795 + 1110542 * 2 ^ 59
def prefixEnd_1110542 : Nat := 4983230072969 + 3 ^ 40 * 1110542 * 2
def baseEnd_1110542 : Nat := 570241833005499233017717

theorem tailTrace_1110542 : CollatzResearch.WordTrace tailWord_1110542 prefixEnd_1110542 570241833005499233017717 := by
  unfold tailWord_1110542
  simp only [CollatzResearch.WordTrace]
  refine ⟨5063099292837934289833735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27003196228468982879113253 5063099292837934289833735)
  ·
    refine ⟨7594648939256901434750603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5063099292837934289833735 7594648939256901434750603)
    ·
      refine ⟨11391973408885352152125905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7594648939256901434750603 11391973408885352152125905)
      ·
        refine ⟨8543980056664014114094429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11391973408885352152125905 8543980056664014114094429)
        ·
          refine ⟨3203992521249005292785411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8543980056664014114094429 3203992521249005292785411)
          ·
            refine ⟨4805988781873507939178117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3203992521249005292785411 4805988781873507939178117)
            ·
              refine ⟨901122896601282738595897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4805988781873507939178117 901122896601282738595897)
              ·
                refine ⟨675842172450962053946923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 901122896601282738595897 675842172450962053946923)
                ·
                  refine ⟨1013763258676443080920385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 675842172450962053946923 1013763258676443080920385)
                  ·
                    refine ⟨760322444007332310690289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1013763258676443080920385 760322444007332310690289)
                    ·
                      refine ⟨570241833005499233017717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 760322444007332310690289 570241833005499233017717)
                      ·
                        rfl

theorem cell23_1110542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 4, 2, 1, 2, 2].length) (baseStart_1110542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1110542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1110542 prefixEnd_1110542 := by exact prefixLift 1110542
  have htrace : WordTrace (prefixWord ++ tailWord_1110542) baseStart_1110542 baseEnd_1110542 := by
    simpa [prefixWord, tailWord_1110542, baseEnd_1110542] using wordTrace_append hprefix tailTrace_1110542
  have hstable : (prefixWord ++ tailWord_1110542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1110542).length < 2 ^ (prefixWord ++ tailWord_1110542).sum := by decide
  have hdescent : baseEnd_1110542 < baseStart_1110542 := by decide
  rcases family_descends (prefixWord ++ tailWord_1110542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1110547 : List Nat := [1, 1, 1, 2, 1, 5, 1, 1, 1, 5, 4]
def baseStart_1110547 : Nat := 118140960795 + 1110547 * 2 ^ 59
def prefixEnd_1110547 : Nat := 4983230072969 + 3 ^ 40 * 1110547 * 2
def baseEnd_1110547 : Nat := 570244400408771713455193

theorem tailTrace_1110547 : CollatzResearch.WordTrace tailWord_1110547 prefixEnd_1110547 570244400408771713455193 := by
  unfold tailWord_1110547
  simp only [CollatzResearch.WordTrace]
  refine ⟨40504976707685360172601895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27003317805123573448401263 40504976707685360172601895)
  ·
    refine ⟨60757465061528040258902843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40504976707685360172601895 60757465061528040258902843)
    ·
      refine ⟨91136197592292060388354265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60757465061528040258902843 91136197592292060388354265)
      ·
        refine ⟨68352148194219045291265699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91136197592292060388354265 68352148194219045291265699)
        ·
          refine ⟨102528222291328567936898549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68352148194219045291265699 102528222291328567936898549)
          ·
            refine ⟨9612020839812053244084239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 102528222291328567936898549 9612020839812053244084239)
            ·
              refine ⟨14418031259718079866126359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9612020839812053244084239 14418031259718079866126359)
              ·
                refine ⟨21627046889577119799189539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14418031259718079866126359 21627046889577119799189539)
                ·
                  refine ⟨32440570334365679698784309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21627046889577119799189539 32440570334365679698784309)
                  ·
                    refine ⟨3041303468846782471761029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 32440570334365679698784309 3041303468846782471761029)
                    ·
                      refine ⟨570244400408771713455193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3041303468846782471761029 570244400408771713455193)
                      ·
                        rfl

theorem cell23_1110547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 1, 1, 5, 4].length) (baseStart_1110547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1110547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1110547 prefixEnd_1110547 := by exact prefixLift 1110547
  have htrace : WordTrace (prefixWord ++ tailWord_1110547) baseStart_1110547 baseEnd_1110547 := by
    simpa [prefixWord, tailWord_1110547, baseEnd_1110547] using wordTrace_append hprefix tailTrace_1110547
  have hstable : (prefixWord ++ tailWord_1110547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1110547).length < 2 ^ (prefixWord ++ tailWord_1110547).sum := by decide
  have hdescent : baseEnd_1110547 < baseStart_1110547 := by decide
  rcases family_descends (prefixWord ++ tailWord_1110547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1110568 : List Nat := [2, 1, 5, 2, 1, 1, 2, 1, 3, 3, 2]
def baseStart_1110568 : Nat := 118140960795 + 1110568 * 2 ^ 59
def prefixEnd_1110568 : Nat := 4983230072969 + 3 ^ 40 * 1110568 * 2
def baseEnd_1110568 : Nat := 570255183502516131292597

theorem tailTrace_1110568 : CollatzResearch.WordTrace tailWord_1110568 prefixEnd_1110568 570255183502516131292597 := by
  unfold tailWord_1110568
  simp only [CollatzResearch.WordTrace]
  refine ⟨20252871320304640379558179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27003828427072853839410905 20252871320304640379558179)
  ·
    refine ⟨30379306980456960569337269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20252871320304640379558179 30379306980456960569337269)
    ·
      refine ⟨2848060029417840053375369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 30379306980456960569337269 2848060029417840053375369)
      ·
        refine ⟨2136045022063380040031527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2848060029417840053375369 2136045022063380040031527)
        ·
          refine ⟨3204067533095070060047291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2136045022063380040031527 3204067533095070060047291)
          ·
            refine ⟨4806101299642605090070937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3204067533095070060047291 4806101299642605090070937)
            ·
              refine ⟨3604575974731953817553203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4806101299642605090070937 3604575974731953817553203)
              ·
                refine ⟨5406863962097930726329805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3604575974731953817553203 5406863962097930726329805)
                ·
                  refine ⟨2027573985786724022373677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5406863962097930726329805 2027573985786724022373677)
                  ·
                    refine ⟨760340244670021508390129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2027573985786724022373677 760340244670021508390129)
                    ·
                      refine ⟨570255183502516131292597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 760340244670021508390129 570255183502516131292597)
                      ·
                        rfl

theorem cell23_1110568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 2, 1, 3, 3, 2].length) (baseStart_1110568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1110568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1110568 prefixEnd_1110568 := by exact prefixLift 1110568
  have htrace : WordTrace (prefixWord ++ tailWord_1110568) baseStart_1110568 baseEnd_1110568 := by
    simpa [prefixWord, tailWord_1110568, baseEnd_1110568] using wordTrace_append hprefix tailTrace_1110568
  have hstable : (prefixWord ++ tailWord_1110568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1110568).length < 2 ^ (prefixWord ++ tailWord_1110568).sum := by decide
  have hdescent : baseEnd_1110568 < baseStart_1110568 := by decide
  rcases family_descends (prefixWord ++ tailWord_1110568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1110581 : List Nat := [1, 3, 3, 1, 1, 2, 1, 4, 1, 4, 2]
def baseStart_1110581 : Nat := 118140960795 + 1110581 * 2 ^ 59
def prefixEnd_1110581 : Nat := 4983230072969 + 3 ^ 40 * 1110581 * 2
def baseEnd_1110581 : Nat := 570261858751024580430037

theorem tailTrace_1110581 : CollatzResearch.WordTrace tailWord_1110581 prefixEnd_1110581 570261858751024580430037 := by
  unfold tailWord_1110581
  simp only [CollatzResearch.WordTrace]
  refine ⟨40506216789562183979339597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27004144526374789319559731 40506216789562183979339597)
  ·
    refine ⟨15189831296085818992252349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40506216789562183979339597 15189831296085818992252349)
    ·
      refine ⟨5696186736032182122094631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15189831296085818992252349 5696186736032182122094631)
      ·
        refine ⟨8544280104048273183141947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5696186736032182122094631 8544280104048273183141947)
        ·
          refine ⟨12816420156072409774712921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8544280104048273183141947 12816420156072409774712921)
          ·
            refine ⟨9612315117054307331034691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12816420156072409774712921 9612315117054307331034691)
            ·
              refine ⟨14418472675581460996552037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9612315117054307331034691 14418472675581460996552037)
              ·
                refine ⟨2703463626671523936853507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14418472675581460996552037 2703463626671523936853507)
                ·
                  refine ⟨4055195440007285905280261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2703463626671523936853507 4055195440007285905280261)
                  ·
                    refine ⟨760349145001366107240049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4055195440007285905280261 760349145001366107240049)
                    ·
                      refine ⟨570261858751024580430037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 760349145001366107240049 570261858751024580430037)
                      ·
                        rfl

theorem cell23_1110581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 4, 1, 4, 2].length) (baseStart_1110581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1110581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1110581 prefixEnd_1110581 := by exact prefixLift 1110581
  have htrace : WordTrace (prefixWord ++ tailWord_1110581) baseStart_1110581 baseEnd_1110581 := by
    simpa [prefixWord, tailWord_1110581, baseEnd_1110581] using wordTrace_append hprefix tailTrace_1110581
  have hstable : (prefixWord ++ tailWord_1110581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1110581).length < 2 ^ (prefixWord ++ tailWord_1110581).sum := by decide
  have hdescent : baseEnd_1110581 < baseStart_1110581 := by decide
  rcases family_descends (prefixWord ++ tailWord_1110581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1110604 : List Nat := [2, 2, 1, 3, 1, 2, 4, 1, 7]
def baseStart_1110604 : Nat := 118140960795 + 1110604 * 2 ^ 59
def prefixEnd_1110604 : Nat := 4983230072969 + 3 ^ 40 * 1110604 * 2
def baseEnd_1110604 : Nat := 63363740978453110049159

theorem tailTrace_1110604 : CollatzResearch.WordTrace tailWord_1110604 prefixEnd_1110604 63363740978453110049159 := by
  unfold tailWord_1110604
  simp only [CollatzResearch.WordTrace]
  refine ⟨20253527834239429453713433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27004703778985905938284577 20253527834239429453713433)
  ·
    refine ⟨15190145875679572090285075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20253527834239429453713433 15190145875679572090285075)
    ·
      refine ⟨22785218813519358135427613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15190145875679572090285075 22785218813519358135427613)
      ·
        refine ⟨8544457055069759300785355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22785218813519358135427613 8544457055069759300785355)
        ·
          refine ⟨12816685582604638951178033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8544457055069759300785355 12816685582604638951178033)
          ·
            refine ⟨9612514186953479213383525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12816685582604638951178033 9612514186953479213383525)
            ·
              refine ⟨1802346410053777352509411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9612514186953479213383525 1802346410053777352509411)
              ·
                refine ⟨2703519615080666028764117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1802346410053777352509411 2703519615080666028764117)
                ·
                  refine ⟨63363740978453110049159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2703519615080666028764117 63363740978453110049159)
                  ·
                    rfl

theorem cell23_1110604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 4, 1, 7].length) (baseStart_1110604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1110604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1110604 prefixEnd_1110604 := by exact prefixLift 1110604
  have htrace : WordTrace (prefixWord ++ tailWord_1110604) baseStart_1110604 baseEnd_1110604 := by
    simpa [prefixWord, tailWord_1110604, baseEnd_1110604] using wordTrace_append hprefix tailTrace_1110604
  have hstable : (prefixWord ++ tailWord_1110604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1110604).length < 2 ^ (prefixWord ++ tailWord_1110604).sum := by decide
  have hdescent : baseEnd_1110604 < baseStart_1110604 := by decide
  rcases family_descends (prefixWord ++ tailWord_1110604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1110615 : List Nat := [1, 1, 3, 2, 2, 2, 5, 1, 2, 2, 2]
def baseStart_1110615 : Nat := 118140960795 + 1110615 * 2 ^ 59
def prefixEnd_1110615 : Nat := 4983230072969 + 3 ^ 40 * 1110615 * 2
def baseEnd_1110615 : Nat := 570279317093277447404881

theorem tailTrace_1110615 : CollatzResearch.WordTrace tailWord_1110615 prefixEnd_1110615 570279317093277447404881 := by
  unfold tailWord_1110615
  simp only [CollatzResearch.WordTrace]
  refine ⟨40507456871439007786077299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27004971247626005190718199 40507456871439007786077299)
  ·
    refine ⟨60761185307158511679115949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40507456871439007786077299 60761185307158511679115949)
    ·
      refine ⟨22785444490184441879668481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60761185307158511679115949 22785444490184441879668481)
      ·
        refine ⟨17089083367638331409751361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22785444490184441879668481 17089083367638331409751361)
        ·
          refine ⟨12816812525728748557313521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17089083367638331409751361 12816812525728748557313521)
          ·
            refine ⟨9612609394296561417985141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12816812525728748557313521 9612609394296561417985141)
            ·
              refine ⟨901182130715302632936107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9612609394296561417985141 901182130715302632936107)
              ·
                refine ⟨1351773196072953949404161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 901182130715302632936107 1351773196072953949404161)
                ·
                  refine ⟨1013829897054715462053121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1351773196072953949404161 1013829897054715462053121)
                  ·
                    refine ⟨760372422791036596539841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1013829897054715462053121 760372422791036596539841)
                    ·
                      refine ⟨570279317093277447404881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 760372422791036596539841 570279317093277447404881)
                      ·
                        rfl

theorem cell23_1110615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 5, 1, 2, 2, 2].length) (baseStart_1110615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1110615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1110615 prefixEnd_1110615 := by exact prefixLift 1110615
  have htrace : WordTrace (prefixWord ++ tailWord_1110615) baseStart_1110615 baseEnd_1110615 := by
    simpa [prefixWord, tailWord_1110615, baseEnd_1110615] using wordTrace_append hprefix tailTrace_1110615
  have hstable : (prefixWord ++ tailWord_1110615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1110615).length < 2 ^ (prefixWord ++ tailWord_1110615).sum := by decide
  have hdescent : baseEnd_1110615 < baseStart_1110615 := by decide
  rcases family_descends (prefixWord ++ tailWord_1110615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1110634 : List Nat := [3, 1, 3, 2, 1, 1, 1, 3, 1, 7]
def baseStart_1110634 : Nat := 118140960795 + 1110634 * 2 ^ 59
def prefixEnd_1110634 : Nat := 4983230072969 + 3 ^ 40 * 1110634 * 2
def baseEnd_1110634 : Nat := 190096357741904291022431

theorem tailTrace_1110634 : CollatzResearch.WordTrace tailWord_1110634 prefixEnd_1110634 190096357741904291022431 := by
  unfold tailWord_1110634
  simp only [CollatzResearch.WordTrace]
  refine ⟨10127037464592543507754739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27005433238913449354012637 10127037464592543507754739)
  ·
    refine ⟨15190556196888815261632109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10127037464592543507754739 15190556196888815261632109)
    ·
      refine ⟨5696458573833305723112041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15190556196888815261632109 5696458573833305723112041)
      ·
        refine ⟨4272343930374979292334031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5696458573833305723112041 4272343930374979292334031)
        ·
          refine ⟨6408515895562468938501047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4272343930374979292334031 6408515895562468938501047)
          ·
            refine ⟨9612773843343703407751571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6408515895562468938501047 9612773843343703407751571)
            ·
              refine ⟨14419160765015555111627357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9612773843343703407751571 14419160765015555111627357)
              ·
                refine ⟨5407185286880833166860259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14419160765015555111627357 5407185286880833166860259)
                ·
                  refine ⟨8110777930321249750290389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5407185286880833166860259 8110777930321249750290389)
                  ·
                    refine ⟨190096357741904291022431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 8110777930321249750290389 190096357741904291022431)
                    ·
                      rfl

theorem cell23_1110634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 3, 1, 7].length) (baseStart_1110634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1110634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1110634 prefixEnd_1110634 := by exact prefixLift 1110634
  have htrace : WordTrace (prefixWord ++ tailWord_1110634) baseStart_1110634 baseEnd_1110634 := by
    simpa [prefixWord, tailWord_1110634, baseEnd_1110634] using wordTrace_append hprefix tailTrace_1110634
  have hstable : (prefixWord ++ tailWord_1110634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1110634).length < 2 ^ (prefixWord ++ tailWord_1110634).sum := by decide
  have hdescent : baseEnd_1110634 < baseStart_1110634 := by decide
  rcases family_descends (prefixWord ++ tailWord_1110634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1110638 : List Nat := [4, 1, 2, 2, 2, 1, 3, 3, 5]
def baseStart_1110638 : Nat := 118140960795 + 1110638 * 2 ^ 59
def prefixEnd_1110638 : Nat := 4983230072969 + 3 ^ 40 * 1110638 * 2
def baseEnd_1110638 : Nat := 63365680794258984157475

theorem tailTrace_1110638 : CollatzResearch.WordTrace tailWord_1110638 prefixEnd_1110638 63365680794258984157475 := by
  unfold tailWord_1110638
  simp only [CollatzResearch.WordTrace]
  refine ⟨5063536968794460339270571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27005530500237121809443045 5063536968794460339270571)
  ·
    refine ⟨7595305453191690508905857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5063536968794460339270571 7595305453191690508905857)
    ·
      refine ⟨5696479089893767881679393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7595305453191690508905857 5696479089893767881679393)
      ·
        refine ⟨4272359317420325911259545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5696479089893767881679393 4272359317420325911259545)
        ·
          refine ⟨3204269488065244433444659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4272359317420325911259545 3204269488065244433444659)
          ·
            refine ⟨4806404232097866650166989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3204269488065244433444659 4806404232097866650166989)
            ·
              refine ⟨1802401587036699993812621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4806404232097866650166989 1802401587036699993812621)
              ·
                refine ⟨675900595138762497679733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1802401587036699993812621 675900595138762497679733)
                ·
                  refine ⟨63365680794258984157475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 675900595138762497679733 63365680794258984157475)
                  ·
                    rfl

theorem cell23_1110638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 3, 3, 5].length) (baseStart_1110638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1110638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1110638 prefixEnd_1110638 := by exact prefixLift 1110638
  have htrace : WordTrace (prefixWord ++ tailWord_1110638) baseStart_1110638 baseEnd_1110638 := by
    simpa [prefixWord, tailWord_1110638, baseEnd_1110638] using wordTrace_append hprefix tailTrace_1110638
  have hstable : (prefixWord ++ tailWord_1110638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1110638).length < 2 ^ (prefixWord ++ tailWord_1110638).sum := by decide
  have hdescent : baseEnd_1110638 < baseStart_1110638 := by decide
  rcases family_descends (prefixWord ++ tailWord_1110638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1110688 : List Nat := [2, 1, 1, 4, 4, 1, 2, 1, 2, 1, 4]
def baseStart_1110688 : Nat := 118140960795 + 1110688 * 2 ^ 59
def prefixEnd_1110688 : Nat := 4983230072969 + 3 ^ 40 * 1110688 * 2
def baseEnd_1110688 : Nat := 570316801181055661792045

theorem tailTrace_1110688 : CollatzResearch.WordTrace tailWord_1110688 prefixEnd_1110688 570316801181055661792045 := by
  unfold tailWord_1110688
  simp only [CollatzResearch.WordTrace]
  refine ⟨20255059700087270626742359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27006746266783027502323145 20255059700087270626742359)
  ·
    refine ⟨30382589550130905940113539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20255059700087270626742359 30382589550130905940113539)
    ·
      refine ⟨45573884325196358910170309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30382589550130905940113539 45573884325196358910170309)
      ·
        refine ⟨8545103310974317295656933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 45573884325196358910170309 8545103310974317295656933)
        ·
          refine ⟨1602206870807684492935675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8545103310974317295656933 1602206870807684492935675)
          ·
            refine ⟨2403310306211526739403513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1602206870807684492935675 2403310306211526739403513)
            ·
              refine ⟨1802482729658645054552635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2403310306211526739403513 1802482729658645054552635)
              ·
                refine ⟨2703724094487967581828953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1802482729658645054552635 2703724094487967581828953)
                ·
                  refine ⟨2027793070865975686371715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2703724094487967581828953 2027793070865975686371715)
                  ·
                    refine ⟨3041689606298963529557573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2027793070865975686371715 3041689606298963529557573)
                    ·
                      refine ⟨570316801181055661792045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3041689606298963529557573 570316801181055661792045)
                      ·
                        rfl

theorem cell23_1110688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 2, 1, 2, 1, 4].length) (baseStart_1110688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1110688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1110688 prefixEnd_1110688 := by exact prefixLift 1110688
  have htrace : WordTrace (prefixWord ++ tailWord_1110688) baseStart_1110688 baseEnd_1110688 := by
    simpa [prefixWord, tailWord_1110688, baseEnd_1110688] using wordTrace_append hprefix tailTrace_1110688
  have hstable : (prefixWord ++ tailWord_1110688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1110688).length < 2 ^ (prefixWord ++ tailWord_1110688).sum := by decide
  have hdescent : baseEnd_1110688 < baseStart_1110688 := by decide
  rcases family_descends (prefixWord ++ tailWord_1110688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1110714 : List Nat := [3, 1, 1, 1, 2, 3, 2, 1, 1, 2, 6]
def baseStart_1110714 : Nat := 118140960795 + 1110714 * 2 ^ 59
def prefixEnd_1110714 : Nat := 4983230072969 + 3 ^ 40 * 1110714 * 2
def baseEnd_1110714 : Nat := 570330151678072560066925

theorem tailTrace_1110714 : CollatzResearch.WordTrace tailWord_1110714 prefixEnd_1110714 570330151678072560066925 := by
  unfold tailWord_1110714
  simp only [CollatzResearch.WordTrace]
  refine ⟨10127766924520086923482799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27007378465386898462620797 10127766924520086923482799)
  ·
    refine ⟨15191650386780130385224199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10127766924520086923482799 15191650386780130385224199)
    ·
      refine ⟨22787475580170195577836299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15191650386780130385224199 22787475580170195577836299)
      ·
        refine ⟨34181213370255293366754449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22787475580170195577836299 34181213370255293366754449)
        ·
          refine ⟨25635910027691470025065837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34181213370255293366754449 25635910027691470025065837)
          ·
            refine ⟨9613466260384301259399689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25635910027691470025065837 9613466260384301259399689)
            ·
              refine ⟨7210099695288225944549767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9613466260384301259399689 7210099695288225944549767)
              ·
                refine ⟨10815149542932338916824651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7210099695288225944549767 10815149542932338916824651)
                ·
                  refine ⟨16222724314398508375236977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10815149542932338916824651 16222724314398508375236977)
                  ·
                    refine ⟨12167043235798881281427733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16222724314398508375236977 12167043235798881281427733)
                    ·
                      refine ⟨570330151678072560066925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 12167043235798881281427733 570330151678072560066925)
                      ·
                        rfl

theorem cell23_1110714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 1, 1, 2, 6].length) (baseStart_1110714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1110714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1110714 prefixEnd_1110714 := by exact prefixLift 1110714
  have htrace : WordTrace (prefixWord ++ tailWord_1110714) baseStart_1110714 baseEnd_1110714 := by
    simpa [prefixWord, tailWord_1110714, baseEnd_1110714] using wordTrace_append hprefix tailTrace_1110714
  have hstable : (prefixWord ++ tailWord_1110714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1110714).length < 2 ^ (prefixWord ++ tailWord_1110714).sum := by decide
  have hdescent : baseEnd_1110714 < baseStart_1110714 := by decide
  rcases family_descends (prefixWord ++ tailWord_1110714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1110781 : List Nat := [1, 4, 1, 1, 1, 1, 5, 2, 1, 1, 5]
def baseStart_1110781 : Nat := 118140960795 + 1110781 * 2 ^ 59
def prefixEnd_1110781 : Nat := 4983230072969 + 3 ^ 40 * 1110781 * 2
def baseEnd_1110781 : Nat := 570364554881923797929117

theorem tailTrace_1110781 : CollatzResearch.WordTrace tailWord_1110781 prefixEnd_1110781 570364554881923797929117 := by
  unfold tailWord_1110781
  simp only [CollatzResearch.WordTrace]
  refine ⟨40513511388837618136620197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27009007592558412091080131 40513511388837618136620197)
  ·
    refine ⟨7596283385407053400616287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 40513511388837618136620197 7596283385407053400616287)
    ·
      refine ⟨11394425078110580100924431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7596283385407053400616287 11394425078110580100924431)
      ·
        refine ⟨17091637617165870151386647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11394425078110580100924431 17091637617165870151386647)
        ·
          refine ⟨25637456425748805227079971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17091637617165870151386647 25637456425748805227079971)
          ·
            refine ⟨38456184638623207840619957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25637456425748805227079971 38456184638623207840619957)
            ·
              refine ⟨3605267309870925735058121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 38456184638623207840619957 3605267309870925735058121)
              ·
                refine ⟨2703950482403194301293591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3605267309870925735058121 2703950482403194301293591)
                ·
                  refine ⟨4055925723604791451940387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2703950482403194301293591 4055925723604791451940387)
                  ·
                    refine ⟨6083888585407187177910581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4055925723604791451940387 6083888585407187177910581)
                    ·
                      refine ⟨570364554881923797929117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6083888585407187177910581 570364554881923797929117)
                      ·
                        rfl

theorem cell23_1110781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 5, 2, 1, 1, 5].length) (baseStart_1110781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1110781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1110781 prefixEnd_1110781 := by exact prefixLift 1110781
  have htrace : WordTrace (prefixWord ++ tailWord_1110781) baseStart_1110781 baseEnd_1110781 := by
    simpa [prefixWord, tailWord_1110781, baseEnd_1110781] using wordTrace_append hprefix tailTrace_1110781
  have hstable : (prefixWord ++ tailWord_1110781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1110781).length < 2 ^ (prefixWord ++ tailWord_1110781).sum := by decide
  have hdescent : baseEnd_1110781 < baseStart_1110781 := by decide
  rcases family_descends (prefixWord ++ tailWord_1110781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1110801 : List Nat := [1, 2, 2, 1, 1, 3, 6, 7]
def baseStart_1110801 : Nat := 118140960795 + 1110801 * 2 ^ 59
def prefixEnd_1110801 : Nat := 4983230072969 + 3 ^ 40 * 1110801 * 2
def baseEnd_1110801 : Nat := 21124993499815322951075

theorem tailTrace_1110801 : CollatzResearch.WordTrace tailWord_1110801 prefixEnd_1110801 21124993499815322951075 := by
  unfold tailWord_1110801
  simp only [CollatzResearch.WordTrace]
  refine ⟨40514240848765161552348257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27009493899176774368232171 40514240848765161552348257)
  ·
    refine ⟨30385680636573871164261193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40514240848765161552348257 30385680636573871164261193)
    ·
      refine ⟨22789260477430403373195895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30385680636573871164261193 22789260477430403373195895)
      ·
        refine ⟨34183890716145605059793843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22789260477430403373195895 34183890716145605059793843)
        ·
          refine ⟨51275836074218407589690765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34183890716145605059793843 51275836074218407589690765)
          ·
            refine ⟨19228438527831902846134037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51275836074218407589690765 19228438527831902846134037)
            ·
              refine ⟨901333055992120445912533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 19228438527831902846134037 901333055992120445912533)
              ·
                refine ⟨21124993499815322951075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 901333055992120445912533 21124993499815322951075)
                ·
                  rfl

theorem cell23_1110801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 6, 7].length) (baseStart_1110801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1110801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1110801 prefixEnd_1110801 := by exact prefixLift 1110801
  have htrace : WordTrace (prefixWord ++ tailWord_1110801) baseStart_1110801 baseEnd_1110801 := by
    simpa [prefixWord, tailWord_1110801, baseEnd_1110801] using wordTrace_append hprefix tailTrace_1110801
  have hstable : (prefixWord ++ tailWord_1110801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1110801).length < 2 ^ (prefixWord ++ tailWord_1110801).sum := by decide
  have hdescent : baseEnd_1110801 < baseStart_1110801 := by decide
  rcases family_descends (prefixWord ++ tailWord_1110801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1110828 : List Nat := [2, 2, 1, 1, 1, 4, 1, 3, 4, 1, 3]
def baseStart_1110828 : Nat := 118140960795 + 1110828 * 2 ^ 59
def prefixEnd_1110828 : Nat := 4983230072969 + 3 ^ 40 * 1110828 * 2
def baseEnd_1110828 : Nat := 570388688472685114041401

theorem tailTrace_1110828 : CollatzResearch.WordTrace tailWord_1110828 prefixEnd_1110828 570388688472685114041401 := by
  unfold tailWord_1110828
  simp only [CollatzResearch.WordTrace]
  refine ⟨20257612809833672581790569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27010150413111563442387425 20257612809833672581790569)
  ·
    refine ⟨15193209607375254436342927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20257612809833672581790569 15193209607375254436342927)
    ·
      refine ⟨22789814411062881654514391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15193209607375254436342927 22789814411062881654514391)
      ·
        refine ⟨34184721616594322481771587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22789814411062881654514391 34184721616594322481771587)
        ·
          refine ⟨51277082424891483722657381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34184721616594322481771587 51277082424891483722657381)
          ·
            refine ⟨9614452954667153197998259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 51277082424891483722657381 9614452954667153197998259)
            ·
              refine ⟨14421679432000729796997389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9614452954667153197998259 14421679432000729796997389)
              ·
                refine ⟨5408129787000273673874021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14421679432000729796997389 5408129787000273673874021)
                ·
                  refine ⟨1014024335062551313851379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5408129787000273673874021 1014024335062551313851379)
                  ·
                    refine ⟨1521036502593826970777069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1014024335062551313851379 1521036502593826970777069)
                    ·
                      refine ⟨570388688472685114041401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1521036502593826970777069 570388688472685114041401)
                      ·
                        rfl

theorem cell23_1110828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 4, 1, 3].length) (baseStart_1110828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1110828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1110828 prefixEnd_1110828 := by exact prefixLift 1110828
  have htrace : WordTrace (prefixWord ++ tailWord_1110828) baseStart_1110828 baseEnd_1110828 := by
    simpa [prefixWord, tailWord_1110828, baseEnd_1110828] using wordTrace_append hprefix tailTrace_1110828
  have hstable : (prefixWord ++ tailWord_1110828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1110828).length < 2 ^ (prefixWord ++ tailWord_1110828).sum := by decide
  have hdescent : baseEnd_1110828 < baseStart_1110828 := by decide
  rcases family_descends (prefixWord ++ tailWord_1110828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1110849 : List Nat := [1, 2, 5, 3, 1, 2, 1, 2, 1, 2, 3]
def baseStart_1110849 : Nat := 118140960795 + 1110849 * 2 ^ 59
def prefixEnd_1110849 : Nat := 4983230072969 + 3 ^ 40 * 1110849 * 2
def baseEnd_1110849 : Nat := 570399471566429531878805

theorem tailTrace_1110849 : CollatzResearch.WordTrace tailWord_1110849 prefixEnd_1110849 570399471566429531878805 := by
  unfold tailWord_1110849
  simp only [CollatzResearch.WordTrace]
  refine ⟨40515991552591265750095601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27010661035060843833397067 40515991552591265750095601)
  ·
    refine ⟨30386993664443449312571701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40515991552591265750095601 30386993664443449312571701)
    ·
      refine ⟨2848780656041573373053597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 30386993664443449312571701 2848780656041573373053597)
      ·
        refine ⟨1068292746015590014895099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2848780656041573373053597 1068292746015590014895099)
        ·
          refine ⟨1602439119023385022342649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1068292746015590014895099 1602439119023385022342649)
          ·
            refine ⟨1201829339267538766756987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1602439119023385022342649 1201829339267538766756987)
            ·
              refine ⟨1802744008901308150135481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1201829339267538766756987 1802744008901308150135481)
              ·
                refine ⟨1352058006675981112601611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1802744008901308150135481 1352058006675981112601611)
                ·
                  refine ⟨2028087010013971668902417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1352058006675981112601611 2028087010013971668902417)
                  ·
                    refine ⟨1521065257510478751676813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2028087010013971668902417 1521065257510478751676813)
                    ·
                      refine ⟨570399471566429531878805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1521065257510478751676813 570399471566429531878805)
                      ·
                        rfl

theorem cell23_1110849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 2, 1, 2, 1, 2, 3].length) (baseStart_1110849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1110849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1110849 prefixEnd_1110849 := by exact prefixLift 1110849
  have htrace : WordTrace (prefixWord ++ tailWord_1110849) baseStart_1110849 baseEnd_1110849 := by
    simpa [prefixWord, tailWord_1110849, baseEnd_1110849] using wordTrace_append hprefix tailTrace_1110849
  have hstable : (prefixWord ++ tailWord_1110849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1110849).length < 2 ^ (prefixWord ++ tailWord_1110849).sum := by decide
  have hdescent : baseEnd_1110849 < baseStart_1110849 := by decide
  rcases family_descends (prefixWord ++ tailWord_1110849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1110885 : List Nat := [1, 3, 1, 3, 1, 1, 2, 3, 4, 2, 2]
def baseStart_1110885 : Nat := 118140960795 + 1110885 * 2 ^ 59
def prefixEnd_1110885 : Nat := 4983230072969 + 3 ^ 40 * 1110885 * 2
def baseEnd_1110885 : Nat := 570417956869991391028639

theorem tailTrace_1110885 : CollatzResearch.WordTrace tailWord_1110885 prefixEnd_1110885 570417956869991391028639 := by
  unfold tailWord_1110885
  simp only [CollatzResearch.WordTrace]
  refine ⟨40517304580460843898406109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27011536386973895932270739 40517304580460843898406109)
  ·
    refine ⟨15193989217672816461902291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40517304580460843898406109 15193989217672816461902291)
    ·
      refine ⟨22790983826509224692853437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15193989217672816461902291 22790983826509224692853437)
      ·
        refine ⟨8546618934940959259820039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22790983826509224692853437 8546618934940959259820039)
        ·
          refine ⟨12819928402411438889730059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8546618934940959259820039 12819928402411438889730059)
          ·
            refine ⟨19229892603617158334595089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12819928402411438889730059 19229892603617158334595089)
            ·
              refine ⟨14422419452712868750946317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19229892603617158334595089 14422419452712868750946317)
              ·
                refine ⟨5408407294767325781604869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14422419452712868750946317 5408407294767325781604869)
                ·
                  refine ⟨1014076367768873584050913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5408407294767325781604869 1014076367768873584050913)
                  ·
                    refine ⟨760557275826655188038185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1014076367768873584050913 760557275826655188038185)
                    ·
                      refine ⟨570417956869991391028639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 760557275826655188038185 570417956869991391028639)
                      ·
                        rfl

theorem cell23_1110885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 3, 4, 2, 2].length) (baseStart_1110885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1110885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1110885 prefixEnd_1110885 := by exact prefixLift 1110885
  have htrace : WordTrace (prefixWord ++ tailWord_1110885) baseStart_1110885 baseEnd_1110885 := by
    simpa [prefixWord, tailWord_1110885, baseEnd_1110885] using wordTrace_append hprefix tailTrace_1110885
  have hstable : (prefixWord ++ tailWord_1110885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1110885).length < 2 ^ (prefixWord ++ tailWord_1110885).sum := by decide
  have hdescent : baseEnd_1110885 < baseStart_1110885 := by decide
  rcases family_descends (prefixWord ++ tailWord_1110885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1110888 : List Nat := [2, 1, 4, 2, 1, 2, 1, 1, 2, 4, 3]
def baseStart_1110888 : Nat := 118140960795 + 1110888 * 2 ^ 59
def prefixEnd_1110888 : Nat := 4983230072969 + 3 ^ 40 * 1110888 * 2
def baseEnd_1110888 : Nat := 570419497311954879291125

theorem tailTrace_1110888 : CollatzResearch.WordTrace tailWord_1110888 prefixEnd_1110888 570419497311954879291125 := by
  unfold tailWord_1110888
  simp only [CollatzResearch.WordTrace]
  refine ⟨20258706999724987705382659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27011609332966650273843545 20258706999724987705382659)
  ·
    refine ⟨30388060499587481558073989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20258706999724987705382659 30388060499587481558073989)
    ·
      refine ⟨5697761343672652792138873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30388060499587481558073989 5697761343672652792138873)
      ·
        refine ⟨4273321007754489594104155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5697761343672652792138873 4273321007754489594104155)
        ·
          refine ⟨6409981511631734391156233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4273321007754489594104155 6409981511631734391156233)
          ·
            refine ⟨4807486133723800793367175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6409981511631734391156233 4807486133723800793367175)
            ·
              refine ⟨7211229200585701190050763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4807486133723800793367175 7211229200585701190050763)
              ·
                refine ⟨10816843800878551785076145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7211229200585701190050763 10816843800878551785076145)
                ·
                  refine ⟨8112632850658913838807109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10816843800878551785076145 8112632850658913838807109)
                  ·
                    refine ⟨1521118659498546344776333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8112632850658913838807109 1521118659498546344776333)
                    ·
                      refine ⟨570419497311954879291125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1521118659498546344776333 570419497311954879291125)
                      ·
                        rfl

theorem cell23_1110888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 1, 2, 4, 3].length) (baseStart_1110888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1110888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1110888 prefixEnd_1110888 := by exact prefixLift 1110888
  have htrace : WordTrace (prefixWord ++ tailWord_1110888) baseStart_1110888 baseEnd_1110888 := by
    simpa [prefixWord, tailWord_1110888, baseEnd_1110888] using wordTrace_append hprefix tailTrace_1110888
  have hstable : (prefixWord ++ tailWord_1110888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1110888).length < 2 ^ (prefixWord ++ tailWord_1110888).sum := by decide
  have hdescent : baseEnd_1110888 < baseStart_1110888 := by decide
  rcases family_descends (prefixWord ++ tailWord_1110888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1110902 : List Nat := [5, 1, 1, 3, 1, 1, 1, 3, 1, 4, 2]
def baseStart_1110902 : Nat := 118140960795 + 1110902 * 2 ^ 59
def prefixEnd_1110902 : Nat := 4983230072969 + 3 ^ 40 * 1110902 * 2
def baseEnd_1110902 : Nat := 570426686041117824516061

theorem tailTrace_1110902 : CollatzResearch.WordTrace tailWord_1110902 prefixEnd_1110902 570426686041117824516061 := by
  unfold tailWord_1110902
  simp only [CollatzResearch.WordTrace]
  refine ⟨2532370288837453487610935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 27011949747599503867849973 2532370288837453487610935)
  ·
    refine ⟨3798555433256180231416403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2532370288837453487610935 3798555433256180231416403)
    ·
      refine ⟨5697833149884270347124605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3798555433256180231416403 5697833149884270347124605)
      ·
        refine ⟨2136687431206601380171727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5697833149884270347124605 2136687431206601380171727)
        ·
          refine ⟨3205031146809902070257591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2136687431206601380171727 3205031146809902070257591)
          ·
            refine ⟨4807546720214853105386387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3205031146809902070257591 4807546720214853105386387)
            ·
              refine ⟨7211320080322279658079581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4807546720214853105386387 7211320080322279658079581)
              ·
                refine ⟨2704245030120854871779843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7211320080322279658079581 2704245030120854871779843)
                ·
                  refine ⟨4056367545181282307669765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2704245030120854871779843 4056367545181282307669765)
                  ·
                    refine ⟨760568914721490432688081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4056367545181282307669765 760568914721490432688081)
                    ·
                      refine ⟨570426686041117824516061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 760568914721490432688081 570426686041117824516061)
                      ·
                        rfl

theorem cell23_1110902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 3, 1, 4, 2].length) (baseStart_1110902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1110902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1110902 prefixEnd_1110902 := by exact prefixLift 1110902
  have htrace : WordTrace (prefixWord ++ tailWord_1110902) baseStart_1110902 baseEnd_1110902 := by
    simpa [prefixWord, tailWord_1110902, baseEnd_1110902] using wordTrace_append hprefix tailTrace_1110902
  have hstable : (prefixWord ++ tailWord_1110902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1110902).length < 2 ^ (prefixWord ++ tailWord_1110902).sum := by decide
  have hdescent : baseEnd_1110902 < baseStart_1110902 := by decide
  rcases family_descends (prefixWord ++ tailWord_1110902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1110931 : List Nat := [1, 1, 1, 2, 1, 2, 1, 6, 1, 2, 5]
def baseStart_1110931 : Nat := 118140960795 + 1110931 * 2 ^ 59
def prefixEnd_1110931 : Nat := 4983230072969 + 3 ^ 40 * 1110931 * 2
def baseEnd_1110931 : Nat := 570441576980098211053427

theorem tailTrace_1110931 : CollatzResearch.WordTrace tailWord_1110931 prefixEnd_1110931 570441576980098211053427 := by
  unfold tailWord_1110931
  simp only [CollatzResearch.WordTrace]
  refine ⟨40518982338294193754580647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27012654892196129169720431 40518982338294193754580647)
  ·
    refine ⟨60778473507441290631870971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40518982338294193754580647 60778473507441290631870971)
    ·
      refine ⟨91167710261161935947806457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60778473507441290631870971 91167710261161935947806457)
      ·
        refine ⟨68375782695871451960854843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91167710261161935947806457 68375782695871451960854843)
        ·
          refine ⟨102563674043807177941282265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68375782695871451960854843 102563674043807177941282265)
          ·
            refine ⟨76922755532855383455961699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 102563674043807177941282265 76922755532855383455961699)
            ·
              refine ⟨115384133299283075183942549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76922755532855383455961699 115384133299283075183942549)
              ·
                refine ⟨5408631248403894149247307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 115384133299283075183942549 5408631248403894149247307)
                ·
                  refine ⟨8112946872605841223870961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5408631248403894149247307 8112946872605841223870961)
                  ·
                    refine ⟨6084710154454380917903221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8112946872605841223870961 6084710154454380917903221)
                    ·
                      refine ⟨570441576980098211053427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6084710154454380917903221 570441576980098211053427)
                      ·
                        rfl

theorem cell23_1110931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 6, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 6, 1, 2, 5].length) (baseStart_1110931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1110931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1110931 prefixEnd_1110931 := by exact prefixLift 1110931
  have htrace : WordTrace (prefixWord ++ tailWord_1110931) baseStart_1110931 baseEnd_1110931 := by
    simpa [prefixWord, tailWord_1110931, baseEnd_1110931] using wordTrace_append hprefix tailTrace_1110931
  have hstable : (prefixWord ++ tailWord_1110931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1110931).length < 2 ^ (prefixWord ++ tailWord_1110931).sum := by decide
  have hdescent : baseEnd_1110931 < baseStart_1110931 := by decide
  rcases family_descends (prefixWord ++ tailWord_1110931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1111002 : List Nat := [3, 1, 1, 2, 4, 3, 1, 1, 3, 4]
def baseStart_1111002 : Nat := 118140960795 + 1111002 * 2 ^ 59
def prefixEnd_1111002 : Nat := 4983230072969 + 3 ^ 40 * 1111002 * 2
def baseEnd_1111002 : Nat := 190159344702189144421867

theorem tailTrace_1111002 : CollatzResearch.WordTrace tailWord_1111002 prefixEnd_1111002 190159344702189144421867 := by
  unfold tailWord_1111002
  simp only [CollatzResearch.WordTrace]
  refine ⟨10130392980259243220103815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27014381280691315253610173 10130392980259243220103815)
  ·
    refine ⟨15195589470388864830155723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10130392980259243220103815 15195589470388864830155723)
    ·
      refine ⟨22793384205583297245233585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15195589470388864830155723 22793384205583297245233585)
      ·
        refine ⟨17095038154187472933925189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22793384205583297245233585 17095038154187472933925189)
        ·
          refine ⟨3205319653910151175110973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17095038154187472933925189 3205319653910151175110973)
          ·
            refine ⟨1201994870216306690666615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3205319653910151175110973 1201994870216306690666615)
            ·
              refine ⟨1802992305324460035999923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1201994870216306690666615 1802992305324460035999923)
              ·
                refine ⟨2704488457986690053999885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1802992305324460035999923 2704488457986690053999885)
                ·
                  refine ⟨1014183171745008770249957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2704488457986690053999885 1014183171745008770249957)
                  ·
                    refine ⟨190159344702189144421867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1014183171745008770249957 190159344702189144421867)
                    ·
                      rfl

theorem cell23_1111002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 3, 4].length) (baseStart_1111002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1111002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1111002 prefixEnd_1111002 := by exact prefixLift 1111002
  have htrace : WordTrace (prefixWord ++ tailWord_1111002) baseStart_1111002 baseEnd_1111002 := by
    simpa [prefixWord, tailWord_1111002, baseEnd_1111002] using wordTrace_append hprefix tailTrace_1111002
  have hstable : (prefixWord ++ tailWord_1111002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1111002).length < 2 ^ (prefixWord ++ tailWord_1111002).sum := by decide
  have hdescent : baseEnd_1111002 < baseStart_1111002 := by decide
  rcases family_descends (prefixWord ++ tailWord_1111002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1111015 : List Nat := [1, 1, 5, 2, 2, 2, 1, 3, 6]
def baseStart_1111015 : Nat := 118140960795 + 1111015 * 2 ^ 59
def prefixEnd_1111015 : Nat := 4983230072969 + 3 ^ 40 * 1111015 * 2
def baseEnd_1111015 : Nat := 63387189928341764711449

theorem tailTrace_1111015 : CollatzResearch.WordTrace tailWord_1111015 prefixEnd_1111015 63387189928341764711449 := by
  unfold tailWord_1111015
  simp only [CollatzResearch.WordTrace]
  refine ⟨40522046069989876100638499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27014697379993250733758999 40522046069989876100638499)
  ·
    refine ⟨60783069104984814150957749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40522046069989876100638499 60783069104984814150957749)
    ·
      refine ⟨5698412728592326326652289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 60783069104984814150957749 5698412728592326326652289)
      ·
        refine ⟨4273809546444244744989217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5698412728592326326652289 4273809546444244744989217)
        ·
          refine ⟨3205357159833183558741913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4273809546444244744989217 3205357159833183558741913)
          ·
            refine ⟨2404017869874887669056435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3205357159833183558741913 2404017869874887669056435)
            ·
              refine ⟨3606026804812331503584653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2404017869874887669056435 3606026804812331503584653)
              ·
                refine ⟨1352260051804624313844245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3606026804812331503584653 1352260051804624313844245)
                ·
                  refine ⟨63387189928341764711449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1352260051804624313844245 63387189928341764711449)
                  ·
                    rfl

theorem cell23_1111015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 1, 3, 6].length) (baseStart_1111015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1111015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1111015 prefixEnd_1111015 := by exact prefixLift 1111015
  have htrace : WordTrace (prefixWord ++ tailWord_1111015) baseStart_1111015 baseEnd_1111015 := by
    simpa [prefixWord, tailWord_1111015, baseEnd_1111015] using wordTrace_append hprefix tailTrace_1111015
  have hstable : (prefixWord ++ tailWord_1111015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1111015).length < 2 ^ (prefixWord ++ tailWord_1111015).sum := by decide
  have hdescent : baseEnd_1111015 < baseStart_1111015 := by decide
  rcases family_descends (prefixWord ++ tailWord_1111015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1111052 : List Nat := [2, 2, 1, 2, 3, 2, 2, 2, 2, 3, 2]
def baseStart_1111052 : Nat := 118140960795 + 1111052 * 2 ^ 59
def prefixEnd_1111052 : Nat := 4983230072969 + 3 ^ 40 * 1111052 * 2
def baseEnd_1111052 : Nat := 570503708139292237640371

theorem tailTrace_1111052 : CollatzResearch.WordTrace tailWord_1111052 prefixEnd_1111052 570503708139292237640371 := by
  unfold tailWord_1111052
  simp only [CollatzResearch.WordTrace]
  refine ⟨20261697785427915709867705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27015597047237220946490273 20261697785427915709867705)
  ·
    refine ⟨15196273339070936782400779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20261697785427915709867705 15196273339070936782400779)
    ·
      refine ⟨22794410008606405173601169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15196273339070936782400779 22794410008606405173601169)
      ·
        refine ⟨17095807506454803880200877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22794410008606405173601169 17095807506454803880200877)
        ·
          refine ⟨6410927814920551455075329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17095807506454803880200877 6410927814920551455075329)
          ·
            refine ⟨4808195861190413591306497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6410927814920551455075329 4808195861190413591306497)
            ·
              refine ⟨3606146895892810193479873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4808195861190413591306497 3606146895892810193479873)
              ·
                refine ⟨2704610171919607645109905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3606146895892810193479873 2704610171919607645109905)
                ·
                  refine ⟨2028457628939705733832429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2704610171919607645109905 2028457628939705733832429)
                  ·
                    refine ⟨760671610852389650187161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2028457628939705733832429 760671610852389650187161)
                    ·
                      refine ⟨570503708139292237640371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 760671610852389650187161 570503708139292237640371)
                      ·
                        rfl

theorem cell23_1111052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 2, 2, 2, 3, 2].length) (baseStart_1111052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1111052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1111052 prefixEnd_1111052 := by exact prefixLift 1111052
  have htrace : WordTrace (prefixWord ++ tailWord_1111052) baseStart_1111052 baseEnd_1111052 := by
    simpa [prefixWord, tailWord_1111052, baseEnd_1111052] using wordTrace_append hprefix tailTrace_1111052
  have hstable : (prefixWord ++ tailWord_1111052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1111052).length < 2 ^ (prefixWord ++ tailWord_1111052).sum := by decide
  have hdescent : baseEnd_1111052 < baseStart_1111052 := by decide
  rcases family_descends (prefixWord ++ tailWord_1111052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1111075 : List Nat := [1, 1, 1, 4, 3, 3, 2, 1, 1, 6]
def baseStart_1111075 : Nat := 118140960795 + 1111075 * 2 ^ 59
def prefixEnd_1111075 : Nat := 4983230072969 + 3 ^ 40 * 1111075 * 2
def baseEnd_1111075 : Nat := 190171839398115215884255

theorem tailTrace_1111075 : CollatzResearch.WordTrace tailWord_1111075 prefixEnd_1111075 190171839398115215884255 := by
  unfold tailWord_1111075
  simp only [CollatzResearch.WordTrace]
  refine ⟨40524234449772506347822679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27016156299848337565215119 40524234449772506347822679)
  ·
    refine ⟨60786351674658759521734019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40524234449772506347822679 60786351674658759521734019)
    ·
      refine ⟨91179527511988139282601029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60786351674658759521734019 91179527511988139282601029)
      ·
        refine ⟨17096161408497776115487693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 91179527511988139282601029 17096161408497776115487693)
        ·
          refine ⟨6411060528186666043307885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17096161408497776115487693 6411060528186666043307885)
          ·
            refine ⟨2404147698069999766240457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6411060528186666043307885 2404147698069999766240457)
            ·
              refine ⟨1803110773552499824680343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2404147698069999766240457 1803110773552499824680343)
              ·
                refine ⟨2704666160328749737020515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1803110773552499824680343 2704666160328749737020515)
                ·
                  refine ⟨4056999240493124605530773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2704666160328749737020515 4056999240493124605530773)
                  ·
                    refine ⟨190171839398115215884255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4056999240493124605530773 190171839398115215884255)
                    ·
                      rfl

theorem cell23_1111075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 2, 1, 1, 6].length) (baseStart_1111075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1111075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1111075 prefixEnd_1111075 := by exact prefixLift 1111075
  have htrace : WordTrace (prefixWord ++ tailWord_1111075) baseStart_1111075 baseEnd_1111075 := by
    simpa [prefixWord, tailWord_1111075, baseEnd_1111075] using wordTrace_append hprefix tailTrace_1111075
  have hstable : (prefixWord ++ tailWord_1111075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1111075).length < 2 ^ (prefixWord ++ tailWord_1111075).sum := by decide
  have hdescent : baseEnd_1111075 < baseStart_1111075 := by decide
  rcases family_descends (prefixWord ++ tailWord_1111075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1111092 : List Nat := [2, 5, 1, 2, 1, 1, 2, 2, 1, 6]
def baseStart_1111092 : Nat := 118140960795 + 1111092 * 2 ^ 59
def prefixEnd_1111092 : Nat := 4983230072969 + 3 ^ 40 * 1111092 * 2
def baseEnd_1111092 : Nat := 190174749121824027046729

theorem tailTrace_1111092 : CollatzResearch.WordTrace tailWord_1111092 prefixEnd_1111092 190174749121824027046729 := by
  unfold tailWord_1111092
  simp only [CollatzResearch.WordTrace]
  refine ⟨20262427245355459125595765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27016569660473945500794353 20262427245355459125595765)
  ·
    refine ⟨1899602554252074293024603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 20262427245355459125595765 1899602554252074293024603)
    ·
      refine ⟨2849403831378111439536905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1899602554252074293024603 2849403831378111439536905)
      ·
        refine ⟨2137052873533583579652679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2849403831378111439536905 2137052873533583579652679)
        ·
          refine ⟨3205579310300375369479019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2137052873533583579652679 3205579310300375369479019)
          ·
            refine ⟨4808368965450563054218529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3205579310300375369479019 4808368965450563054218529)
            ·
              refine ⟨3606276724087922290663897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4808368965450563054218529 3606276724087922290663897)
              ·
                refine ⟨2704707543065941717997923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3606276724087922290663897 2704707543065941717997923)
                ·
                  refine ⟨4057061314598912576996885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2704707543065941717997923 4057061314598912576996885)
                  ·
                    refine ⟨190174749121824027046729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4057061314598912576996885 190174749121824027046729)
                    ·
                      rfl

theorem cell23_1111092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 2, 2, 1, 6].length) (baseStart_1111092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1111092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1111092 prefixEnd_1111092 := by exact prefixLift 1111092
  have htrace : WordTrace (prefixWord ++ tailWord_1111092) baseStart_1111092 baseEnd_1111092 := by
    simpa [prefixWord, tailWord_1111092, baseEnd_1111092] using wordTrace_append hprefix tailTrace_1111092
  have hstable : (prefixWord ++ tailWord_1111092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1111092).length < 2 ^ (prefixWord ++ tailWord_1111092).sum := by decide
  have hdescent : baseEnd_1111092 < baseStart_1111092 := by decide
  rcases family_descends (prefixWord ++ tailWord_1111092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1111105 : List Nat := [1, 2, 5, 1, 3, 1, 10]
def baseStart_1111105 : Nat := 118140960795 + 1111105 * 2 ^ 59
def prefixEnd_1111105 : Nat := 4983230072969 + 3 ^ 40 * 1111105 * 2
def baseEnd_1111105 : Nat := 7043591637209636176267

theorem tailTrace_1111105 : CollatzResearch.WordTrace tailWord_1111105 prefixEnd_1111105 7043591637209636176267 := by
  unfold tailWord_1111105
  simp only [CollatzResearch.WordTrace]
  refine ⟨40525328639663821471414769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27016885759775880980943179 40525328639663821471414769)
  ·
    refine ⟨30393996479747866103561077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40525328639663821471414769 30393996479747866103561077)
    ·
      refine ⟨2849437169976362447208851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 30393996479747866103561077 2849437169976362447208851)
      ·
        refine ⟨4274155754964543670813277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2849437169976362447208851 4274155754964543670813277)
        ·
          refine ⟨1602808408111703876554979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4274155754964543670813277 1602808408111703876554979)
          ·
            refine ⟨2404212612167555814832469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1602808408111703876554979 2404212612167555814832469)
            ·
              refine ⟨7043591637209636176267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 2404212612167555814832469 7043591637209636176267)
              ·
                rfl

theorem cell23_1111105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 10].length) (baseStart_1111105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1111105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1111105 prefixEnd_1111105 := by exact prefixLift 1111105
  have htrace : WordTrace (prefixWord ++ tailWord_1111105) baseStart_1111105 baseEnd_1111105 := by
    simpa [prefixWord, tailWord_1111105, baseEnd_1111105] using wordTrace_append hprefix tailTrace_1111105
  have hstable : (prefixWord ++ tailWord_1111105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1111105).length < 2 ^ (prefixWord ++ tailWord_1111105).sum := by decide
  have hdescent : baseEnd_1111105 < baseStart_1111105 := by decide
  rcases family_descends (prefixWord ++ tailWord_1111105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1111126 : List Nat := [5, 2, 2, 1, 2, 2, 1, 1, 1, 6]
def baseStart_1111126 : Nat := 118140960795 + 1111126 * 2 ^ 59
def prefixEnd_1111126 : Nat := 4983230072969 + 3 ^ 40 * 1111126 * 2
def baseEnd_1111126 : Nat := 190180568569241649371677

theorem tailTrace_1111126 : CollatzResearch.WordTrace tailWord_1111126 prefixEnd_1111126 190180568569241649371677 := by
  unfold tailWord_1111126
  simp only [CollatzResearch.WordTrace]
  refine ⟨2532880910786733878620577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 27017396381725161371952821 2532880910786733878620577)
  ·
    refine ⟨1899660683090050408965433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2532880910786733878620577 1899660683090050408965433)
    ·
      refine ⟨1424745512317537806724075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1899660683090050408965433 1424745512317537806724075)
      ·
        refine ⟨2137118268476306710086113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1424745512317537806724075 2137118268476306710086113)
        ·
          refine ⟨1602838701357230032564585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2137118268476306710086113 1602838701357230032564585)
          ·
            refine ⟨1202129026017922524423439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1602838701357230032564585 1202129026017922524423439)
            ·
              refine ⟨1803193539026883786635159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1202129026017922524423439 1803193539026883786635159)
              ·
                refine ⟨2704790308540325679952739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1803193539026883786635159 2704790308540325679952739)
                ·
                  refine ⟨4057185462810488519929109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2704790308540325679952739 4057185462810488519929109)
                  ·
                    refine ⟨190180568569241649371677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4057185462810488519929109 190180568569241649371677)
                    ·
                      rfl

theorem cell23_1111126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 2, 1, 1, 1, 6].length) (baseStart_1111126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1111126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1111126 prefixEnd_1111126 := by exact prefixLift 1111126
  have htrace : WordTrace (prefixWord ++ tailWord_1111126) baseStart_1111126 baseEnd_1111126 := by
    simpa [prefixWord, tailWord_1111126, baseEnd_1111126] using wordTrace_append hprefix tailTrace_1111126
  have hstable : (prefixWord ++ tailWord_1111126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1111126).length < 2 ^ (prefixWord ++ tailWord_1111126).sum := by decide
  have hdescent : baseEnd_1111126 < baseStart_1111126 := by decide
  rcases family_descends (prefixWord ++ tailWord_1111126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1111175 : List Nat := [1, 1, 4, 2, 1, 1, 1, 3, 2, 4, 3]
def baseStart_1111175 : Nat := 118140960795 + 1111175 * 2 ^ 59
def prefixEnd_1111175 : Nat := 4983230072969 + 3 ^ 40 * 1111175 * 2
def baseEnd_1111175 : Nat := 570566866259795256402305

theorem tailTrace_1111175 : CollatzResearch.WordTrace tailWord_1111175 prefixEnd_1111175 570566866259795256402305 := by
  unfold tailWord_1111175
  simp only [CollatzResearch.WordTrace]
  refine ⟨40527881749410223426462979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27018587832940148950975319 40527881749410223426462979)
  ·
    refine ⟨60791822624115335139694469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40527881749410223426462979 60791822624115335139694469)
    ·
      refine ⟨11398466742021625338692713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 60791822624115335139694469 11398466742021625338692713)
      ·
        refine ⟨8548850056516219004019535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11398466742021625338692713 8548850056516219004019535)
        ·
          refine ⟨12823275084774328506029303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8548850056516219004019535 12823275084774328506029303)
          ·
            refine ⟨19234912627161492759043955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12823275084774328506029303 19234912627161492759043955)
            ·
              refine ⟨28852368940742239138565933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19234912627161492759043955 28852368940742239138565933)
              ·
                refine ⟨10819638352778339676962225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28852368940742239138565933 10819638352778339676962225)
                ·
                  refine ⟨8114728764583754757721669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10819638352778339676962225 8114728764583754757721669)
                  ·
                    refine ⟨1521511643359454017072813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8114728764583754757721669 1521511643359454017072813)
                    ·
                      refine ⟨570566866259795256402305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1521511643359454017072813 570566866259795256402305)
                      ·
                        rfl

theorem cell23_1111175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 3, 2, 4, 3].length) (baseStart_1111175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1111175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1111175 prefixEnd_1111175 := by exact prefixLift 1111175
  have htrace : WordTrace (prefixWord ++ tailWord_1111175) baseStart_1111175 baseEnd_1111175 := by
    simpa [prefixWord, tailWord_1111175, baseEnd_1111175] using wordTrace_append hprefix tailTrace_1111175
  have hstable : (prefixWord ++ tailWord_1111175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1111175).length < 2 ^ (prefixWord ++ tailWord_1111175).sum := by decide
  have hdescent : baseEnd_1111175 < baseStart_1111175 := by decide
  rcases family_descends (prefixWord ++ tailWord_1111175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1111229 : List Nat := [1, 4, 1, 2, 1, 1, 6, 2, 5]
def baseStart_1111229 : Nat := 118140960795 + 1111229 * 2 ^ 59
def prefixEnd_1111229 : Nat := 4983230072969 + 3 ^ 40 * 1111229 * 2
def baseEnd_1111229 : Nat := 63399399357237560569673

theorem tailTrace_1111229 : CollatzResearch.WordTrace tailWord_1111229 prefixEnd_1111229 63399399357237560569673 := by
  unfold tailWord_1111229
  simp only [CollatzResearch.WordTrace]
  refine ⟨40529851291214590648928741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27019900860809727099285827 40529851291214590648928741)
  ·
    refine ⟨7599347117102735746674139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 40529851291214590648928741 7599347117102735746674139)
    ·
      refine ⟨11399020675654103620011209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7599347117102735746674139 11399020675654103620011209)
      ·
        refine ⟨8549265506740577715008407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11399020675654103620011209 8549265506740577715008407)
        ·
          refine ⟨12823898260110866572512611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8549265506740577715008407 12823898260110866572512611)
          ·
            refine ⟨19235847390166299858768917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12823898260110866572512611 19235847390166299858768917)
            ·
              refine ⟨901680346414045305879793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 19235847390166299858768917 901680346414045305879793)
              ·
                refine ⟨676260259810533979409845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 901680346414045305879793 676260259810533979409845)
                ·
                  refine ⟨63399399357237560569673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 676260259810533979409845 63399399357237560569673)
                  ·
                    rfl

theorem cell23_1111229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 6, 2, 5].length) (baseStart_1111229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1111229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1111229 prefixEnd_1111229 := by exact prefixLift 1111229
  have htrace : WordTrace (prefixWord ++ tailWord_1111229) baseStart_1111229 baseEnd_1111229 := by
    simpa [prefixWord, tailWord_1111229, baseEnd_1111229] using wordTrace_append hprefix tailTrace_1111229
  have hstable : (prefixWord ++ tailWord_1111229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1111229).length < 2 ^ (prefixWord ++ tailWord_1111229).sum := by decide
  have hdescent : baseEnd_1111229 < baseStart_1111229 := by decide
  rcases family_descends (prefixWord ++ tailWord_1111229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1111272 : List Nat := [2, 1, 4, 1, 2, 1, 1, 2, 5, 4]
def baseStart_1111272 : Nat := 118140960795 + 1111272 * 2 ^ 59
def prefixEnd_1111272 : Nat := 4983230072969 + 3 ^ 40 * 1111272 * 2
def baseEnd_1111272 : Nat := 190205557961093792296453

theorem tailTrace_1111272 : CollatzResearch.WordTrace tailWord_1111272 prefixEnd_1111272 190205557961093792296453 := by
  unfold tailWord_1111272
  simp only [CollatzResearch.WordTrace]
  refine ⟨20265709815029404496372035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27020946420039205995162713 20265709815029404496372035)
  ·
    refine ⟨30398564722544106744558053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20265709815029404496372035 30398564722544106744558053)
    ·
      refine ⟨5699730885477020014604635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30398564722544106744558053 5699730885477020014604635)
      ·
        refine ⟨8549596328215530021906953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5699730885477020014604635 8549596328215530021906953)
        ·
          refine ⟨6412197246161647516430215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8549596328215530021906953 6412197246161647516430215)
          ·
            refine ⟨9618295869242471274645323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6412197246161647516430215 9618295869242471274645323)
            ·
              refine ⟨14427443803863706911967985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9618295869242471274645323 14427443803863706911967985)
              ·
                refine ⟨10820582852897780183975989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14427443803863706911967985 10820582852897780183975989)
                ·
                  refine ⟨1014429642459166892247749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 10820582852897780183975989 1014429642459166892247749)
                  ·
                    refine ⟨190205557961093792296453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1014429642459166892247749 190205557961093792296453)
                    ·
                      rfl

theorem cell23_1111272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 2, 5, 4].length) (baseStart_1111272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1111272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1111272 prefixEnd_1111272 := by exact prefixLift 1111272
  have htrace : WordTrace (prefixWord ++ tailWord_1111272) baseStart_1111272 baseEnd_1111272 := by
    simpa [prefixWord, tailWord_1111272, baseEnd_1111272] using wordTrace_append hprefix tailTrace_1111272
  have hstable : (prefixWord ++ tailWord_1111272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1111272).length < 2 ^ (prefixWord ++ tailWord_1111272).sum := by decide
  have hdescent : baseEnd_1111272 < baseStart_1111272 := by decide
  rcases family_descends (prefixWord ++ tailWord_1111272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1111275 : List Nat := [1, 1, 1, 1, 2, 6, 1, 1, 2, 1, 6]
def baseStart_1111275 : Nat := 118140960795 + 1111275 * 2 ^ 59
def prefixEnd_1111275 : Nat := 4983230072969 + 3 ^ 40 * 1111275 * 2
def baseEnd_1111275 : Nat := 570618214325244865151845

theorem tailTrace_1111275 : CollatzResearch.WordTrace tailWord_1111275 prefixEnd_1111275 570618214325244865151845 := by
  unfold tailWord_1111275
  simp only [CollatzResearch.WordTrace]
  refine ⟨40531529049047940505103279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27021019366031960336735519 40531529049047940505103279)
  ·
    refine ⟨60797293573571910757654919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40531529049047940505103279 60797293573571910757654919)
    ·
      refine ⟨91195940360357866136482379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60797293573571910757654919 91195940360357866136482379)
      ·
        refine ⟨136793910540536799204723569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91195940360357866136482379 136793910540536799204723569)
        ·
          refine ⟨102595432905402599403542677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 136793910540536799204723569 102595432905402599403542677)
          ·
            refine ⟨4809160917440746847041063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 102595432905402599403542677 4809160917440746847041063)
            ·
              refine ⟨7213741376161120270561595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4809160917440746847041063 7213741376161120270561595)
              ·
                refine ⟨10820612064241680405842393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7213741376161120270561595 10820612064241680405842393)
                ·
                  refine ⟨8115459048181260304381795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10820612064241680405842393 8115459048181260304381795)
                  ·
                    refine ⟨12173188572271890456572693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8115459048181260304381795 12173188572271890456572693)
                    ·
                      refine ⟨570618214325244865151845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 12173188572271890456572693 570618214325244865151845)
                      ·
                        rfl

theorem cell23_1111275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 1, 2, 1, 6].length) (baseStart_1111275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1111275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1111275 prefixEnd_1111275 := by exact prefixLift 1111275
  have htrace : WordTrace (prefixWord ++ tailWord_1111275) baseStart_1111275 baseEnd_1111275 := by
    simpa [prefixWord, tailWord_1111275, baseEnd_1111275] using wordTrace_append hprefix tailTrace_1111275
  have hstable : (prefixWord ++ tailWord_1111275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1111275).length < 2 ^ (prefixWord ++ tailWord_1111275).sum := by decide
  have hdescent : baseEnd_1111275 < baseStart_1111275 := by decide
  rcases family_descends (prefixWord ++ tailWord_1111275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1111289 : List Nat := [1, 2, 1, 3, 1, 1, 3, 6, 1, 4]
def baseStart_1111289 : Nat := 118140960795 + 1111289 * 2 ^ 59
def prefixEnd_1111289 : Nat := 4983230072969 + 3 ^ 40 * 1111289 * 2
def baseEnd_1111289 : Nat := 190208467684802603458927

theorem tailTrace_1111289 : CollatzResearch.WordTrace tailWord_1111289 prefixEnd_1111289 190208467684802603458927 := by
  unfold tailWord_1111289
  simp only [CollatzResearch.WordTrace]
  refine ⟨40532039670997220896112921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27021359780664813930741947 40532039670997220896112921)
  ·
    refine ⟨30399029753247915672084691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40532039670997220896112921 30399029753247915672084691)
    ·
      refine ⟨45598544629871873508127037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30399029753247915672084691 45598544629871873508127037)
      ·
        refine ⟨17099454236201952565547639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45598544629871873508127037 17099454236201952565547639)
        ·
          refine ⟨25649181354302928848321459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17099454236201952565547639 25649181354302928848321459)
          ·
            refine ⟨38473772031454393272482189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25649181354302928848321459 38473772031454393272482189)
            ·
              refine ⟨14427664511795397477180821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38473772031454393272482189 14427664511795397477180821)
              ·
                refine ⟨676296773990409256742851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 14427664511795397477180821 676296773990409256742851)
                ·
                  refine ⟨1014445160985613885114277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 676296773990409256742851 1014445160985613885114277)
                  ·
                    refine ⟨190208467684802603458927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1014445160985613885114277 190208467684802603458927)
                    ·
                      rfl

theorem cell23_1111289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 6, 1, 4].length) (baseStart_1111289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1111289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1111289 prefixEnd_1111289 := by exact prefixLift 1111289
  have htrace : WordTrace (prefixWord ++ tailWord_1111289) baseStart_1111289 baseEnd_1111289 := by
    simpa [prefixWord, tailWord_1111289, baseEnd_1111289] using wordTrace_append hprefix tailTrace_1111289
  have hstable : (prefixWord ++ tailWord_1111289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1111289).length < 2 ^ (prefixWord ++ tailWord_1111289).sum := by decide
  have hdescent : baseEnd_1111289 < baseStart_1111289 := by decide
  rcases family_descends (prefixWord ++ tailWord_1111289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1111305 : List Nat := [1, 2, 1, 1, 3, 3, 1, 2, 1, 2, 6]
def baseStart_1111305 : Nat := 118140960795 + 1111305 * 2 ^ 59
def prefixEnd_1111305 : Nat := 4983230072969 + 3 ^ 40 * 1111305 * 2
def baseEnd_1111305 : Nat := 570633618744879747776707

theorem tailTrace_1111305 : CollatzResearch.WordTrace tailWord_1111305 prefixEnd_1111305 570633618744879747776707 := by
  unfold tailWord_1111305
  simp only [CollatzResearch.WordTrace]
  refine ⟨40532623238939255628695369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27021748825959503752463579 40532623238939255628695369)
  ·
    refine ⟨30399467429204441721521527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40532623238939255628695369 30399467429204441721521527)
    ·
      refine ⟨45599201143806662582282291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30399467429204441721521527 45599201143806662582282291)
      ·
        refine ⟨68398801715709993873423437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45599201143806662582282291 68398801715709993873423437)
        ·
          refine ⟨25649550643391247702533789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 68398801715709993873423437 25649550643391247702533789)
          ·
            refine ⟨9618581491271717888450171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25649550643391247702533789 9618581491271717888450171)
            ·
              refine ⟨14427872236907576832675257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9618581491271717888450171 14427872236907576832675257)
              ·
                refine ⟨10820904177680682624506443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14427872236907576832675257 10820904177680682624506443)
                ·
                  refine ⟨16231356266521023936759665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10820904177680682624506443 16231356266521023936759665)
                  ·
                    refine ⟨12173517199890767952569749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16231356266521023936759665 12173517199890767952569749)
                    ·
                      refine ⟨570633618744879747776707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 12173517199890767952569749 570633618744879747776707)
                      ·
                        rfl

theorem cell23_1111305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 2, 1, 2, 6].length) (baseStart_1111305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1111305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1111305 prefixEnd_1111305 := by exact prefixLift 1111305
  have htrace : WordTrace (prefixWord ++ tailWord_1111305) baseStart_1111305 baseEnd_1111305 := by
    simpa [prefixWord, tailWord_1111305, baseEnd_1111305] using wordTrace_append hprefix tailTrace_1111305
  have hstable : (prefixWord ++ tailWord_1111305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1111305).length < 2 ^ (prefixWord ++ tailWord_1111305).sum := by decide
  have hdescent : baseEnd_1111305 < baseStart_1111305 := by decide
  rcases family_descends (prefixWord ++ tailWord_1111305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1111346 : List Nat := [3, 2, 1, 1, 4, 1, 3, 1, 3, 1, 3]
def baseStart_1111346 : Nat := 118140960795 + 1111346 * 2 ^ 59
def prefixEnd_1111346 : Nat := 4983230072969 + 3 ^ 40 * 1111346 * 2
def baseEnd_1111346 : Nat := 570654671451714087364019

theorem tailTrace_1111346 : CollatzResearch.WordTrace tailWord_1111346 prefixEnd_1111346 570654671451714087364019 := by
  unfold tailWord_1111346
  simp only [CollatzResearch.WordTrace]
  refine ⟨10133529657947679907734473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27022745754527146420625261 10133529657947679907734473)
  ·
    refine ⟨7600147243460759930800855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10133529657947679907734473 7600147243460759930800855)
    ·
      refine ⟨11400220865191139896201283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7600147243460759930800855 11400220865191139896201283)
      ·
        refine ⟨17100331297786709844301925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11400220865191139896201283 17100331297786709844301925)
        ·
          refine ⟨3206312118335008095806611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17100331297786709844301925 3206312118335008095806611)
          ·
            refine ⟨4809468177502512143709917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3206312118335008095806611 4809468177502512143709917)
            ·
              refine ⟨1803550566563442053891219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4809468177502512143709917 1803550566563442053891219)
              ·
                refine ⟨2705325849845163080836829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1803550566563442053891219 2705325849845163080836829)
                ·
                  refine ⟨1014497193691936155313811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2705325849845163080836829 1014497193691936155313811)
                  ·
                    refine ⟨1521745790537904232970717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1014497193691936155313811 1521745790537904232970717)
                    ·
                      refine ⟨570654671451714087364019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1521745790537904232970717 570654671451714087364019)
                      ·
                        rfl

theorem cell23_1111346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 3, 1, 3, 1, 3].length) (baseStart_1111346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1111346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1111346 prefixEnd_1111346 := by exact prefixLift 1111346
  have htrace : WordTrace (prefixWord ++ tailWord_1111346) baseStart_1111346 baseEnd_1111346 := by
    simpa [prefixWord, tailWord_1111346, baseEnd_1111346] using wordTrace_append hprefix tailTrace_1111346
  have hstable : (prefixWord ++ tailWord_1111346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1111346).length < 2 ^ (prefixWord ++ tailWord_1111346).sum := by decide
  have hdescent : baseEnd_1111346 < baseStart_1111346 := by decide
  rcases family_descends (prefixWord ++ tailWord_1111346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1111352 : List Nat := [2, 1, 2, 1, 3, 1, 1, 4, 3, 1, 4]
def baseStart_1111352 : Nat := 118140960795 + 1111352 * 2 ^ 59
def prefixEnd_1111352 : Nat := 4983230072969 + 3 ^ 40 * 1111352 * 2
def baseEnd_1111352 : Nat := 570657752335641063888991

theorem tailTrace_1111352 : CollatzResearch.WordTrace tailWord_1111352 prefixEnd_1111352 570657752335641063888991 := by
  unfold tailWord_1111352
  simp only [CollatzResearch.WordTrace]
  refine ⟨20267168734884491327828155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27022891646512655103770873 20267168734884491327828155)
  ·
    refine ⟨30400753102326736991742233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20267168734884491327828155 30400753102326736991742233)
    ·
      refine ⟨22800564826745052743806675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30400753102326736991742233 22800564826745052743806675)
      ·
        refine ⟨34200847240117579115710013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22800564826745052743806675 34200847240117579115710013)
        ·
          refine ⟨12825317715044092168391255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34200847240117579115710013 12825317715044092168391255)
          ·
            refine ⟨19237976572566138252586883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12825317715044092168391255 19237976572566138252586883)
            ·
              refine ⟨28856964858849207378880325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19237976572566138252586883 28856964858849207378880325)
              ·
                refine ⟨5410680911034226383540061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28856964858849207378880325 5410680911034226383540061)
                ·
                  refine ⟨2029005341637834893827523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5410680911034226383540061 2029005341637834893827523)
                  ·
                    refine ⟨3043508012456752340741285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2029005341637834893827523 3043508012456752340741285)
                    ·
                      refine ⟨570657752335641063888991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3043508012456752340741285 570657752335641063888991)
                      ·
                        rfl

theorem cell23_1111352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 4, 3, 1, 4].length) (baseStart_1111352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1111352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1111352 prefixEnd_1111352 := by exact prefixLift 1111352
  have htrace : WordTrace (prefixWord ++ tailWord_1111352) baseStart_1111352 baseEnd_1111352 := by
    simpa [prefixWord, tailWord_1111352, baseEnd_1111352] using wordTrace_append hprefix tailTrace_1111352
  have hstable : (prefixWord ++ tailWord_1111352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1111352).length < 2 ^ (prefixWord ++ tailWord_1111352).sum := by decide
  have hdescent : baseEnd_1111352 < baseStart_1111352 := by decide
  rcases family_descends (prefixWord ++ tailWord_1111352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1111353 : List Nat := [1, 2, 1, 6, 3, 1, 2, 1, 6]
def baseStart_1111353 : Nat := 118140960795 + 1111353 * 2 ^ 59
def prefixEnd_1111353 : Nat := 4983230072969 + 3 ^ 40 * 1111353 * 2
def baseEnd_1111353 : Nat := 63406473979588395552943

theorem tailTrace_1111353 : CollatzResearch.WordTrace tailWord_1111353 prefixEnd_1111353 63406473979588395552943 := by
  unfold tailWord_1111353
  simp only [CollatzResearch.WordTrace]
  refine ⟨40534373942765359826442713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27022915961843573217628475 40534373942765359826442713)
  ·
    refine ⟨30400780457074019869832035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40534373942765359826442713 30400780457074019869832035)
    ·
      refine ⟨45601170685611029804748053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30400780457074019869832035 45601170685611029804748053)
      ·
        refine ⟨2137554875888017022097565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 45601170685611029804748053 2137554875888017022097565)
        ·
          refine ⟨801583078458006383286587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2137554875888017022097565 801583078458006383286587)
          ·
            refine ⟨1202374617687009574929881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 801583078458006383286587 1202374617687009574929881)
            ·
              refine ⟨901780963265257181197411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1202374617687009574929881 901780963265257181197411)
              ·
                refine ⟨1352671444897885771796117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 901780963265257181197411 1352671444897885771796117)
                ·
                  refine ⟨63406473979588395552943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1352671444897885771796117 63406473979588395552943)
                  ·
                    rfl

theorem cell23_1111353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 3, 1, 2, 1, 6].length) (baseStart_1111353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1111353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1111353 prefixEnd_1111353 := by exact prefixLift 1111353
  have htrace : WordTrace (prefixWord ++ tailWord_1111353) baseStart_1111353 baseEnd_1111353 := by
    simpa [prefixWord, tailWord_1111353, baseEnd_1111353] using wordTrace_append hprefix tailTrace_1111353
  have hstable : (prefixWord ++ tailWord_1111353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1111353).length < 2 ^ (prefixWord ++ tailWord_1111353).sum := by decide
  have hdescent : baseEnd_1111353 < baseStart_1111353 := by decide
  rcases family_descends (prefixWord ++ tailWord_1111353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1111355 : List Nat := [1, 1, 1, 1, 1, 2, 1, 1, 4, 5, 5]
def baseStart_1111355 : Nat := 118140960795 + 1111355 * 2 ^ 59
def prefixEnd_1111355 : Nat := 4983230072969 + 3 ^ 40 * 1111355 * 2
def baseEnd_1111355 : Nat := 570659292777604552151477

theorem tailTrace_1111355 : CollatzResearch.WordTrace tailWord_1111355 prefixEnd_1111355 570659292777604552151477 := by
  unfold tailWord_1111355
  simp only [CollatzResearch.WordTrace]
  refine ⟨40534446888758114168015519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27022964592505409445343679 40534446888758114168015519)
  ·
    refine ⟨60801670333137171252023279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40534446888758114168015519 60801670333137171252023279)
    ·
      refine ⟨91202505499705756878034919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60801670333137171252023279 91202505499705756878034919)
      ·
        refine ⟨136803758249558635317052379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91202505499705756878034919 136803758249558635317052379)
        ·
          refine ⟨205205637374337952975578569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 136803758249558635317052379 205205637374337952975578569)
          ·
            refine ⟨153904228030753464731683927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 205205637374337952975578569 153904228030753464731683927)
            ·
              refine ⟨230856342046130197097525891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 153904228030753464731683927 230856342046130197097525891)
              ·
                refine ⟨346284513069195295646288837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 230856342046130197097525891 346284513069195295646288837)
                ·
                  refine ⟨64928346200474117933679157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 346284513069195295646288837 64928346200474117933679157)
                  ·
                    refine ⟨6087032456294448556282421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 64928346200474117933679157 6087032456294448556282421)
                    ·
                      refine ⟨570659292777604552151477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6087032456294448556282421 570659292777604552151477)
                      ·
                        rfl

theorem cell23_1111355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 4, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 4, 5, 5].length) (baseStart_1111355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1111355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1111355 prefixEnd_1111355 := by exact prefixLift 1111355
  have htrace : WordTrace (prefixWord ++ tailWord_1111355) baseStart_1111355 baseEnd_1111355 := by
    simpa [prefixWord, tailWord_1111355, baseEnd_1111355] using wordTrace_append hprefix tailTrace_1111355
  have hstable : (prefixWord ++ tailWord_1111355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1111355).length < 2 ^ (prefixWord ++ tailWord_1111355).sum := by decide
  have hdescent : baseEnd_1111355 < baseStart_1111355 := by decide
  rcases family_descends (prefixWord ++ tailWord_1111355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1111369 : List Nat := [1, 2, 1, 1, 2, 3, 5, 2, 1, 1, 4]
def baseStart_1111369 : Nat := 118140960795 + 1111369 * 2 ^ 59
def prefixEnd_1111369 : Nat := 4983230072969 + 3 ^ 40 * 1111369 * 2
def baseEnd_1111369 : Nat := 570666481506767497376413

theorem tailTrace_1111369 : CollatzResearch.WordTrace tailWord_1111369 prefixEnd_1111369 570666481506767497376413 := by
  unfold tailWord_1111369
  simp only [CollatzResearch.WordTrace]
  refine ⟨40534957510707394559025161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27023305007138263039350107 40534957510707394559025161)
  ·
    refine ⟨30401218133030545919268871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40534957510707394559025161 30401218133030545919268871)
    ·
      refine ⟨45601827199545818878903307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30401218133030545919268871 45601827199545818878903307)
      ·
        refine ⟨68402740799318728318354961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45601827199545818878903307 68402740799318728318354961)
        ·
          refine ⟨51302055599489046238766221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68402740799318728318354961 51302055599489046238766221)
          ·
            refine ⟨19238270849808392339537333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51302055599489046238766221 19238270849808392339537333)
            ·
              refine ⟨1803587892169536781831625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 19238270849808392339537333 1803587892169536781831625)
              ·
                refine ⟨1352690919127152586373719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1803587892169536781831625 1352690919127152586373719)
                ·
                  refine ⟨2029036378690728879560579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1352690919127152586373719 2029036378690728879560579)
                  ·
                    refine ⟨3043554568036093319340869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2029036378690728879560579 3043554568036093319340869)
                    ·
                      refine ⟨570666481506767497376413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3043554568036093319340869 570666481506767497376413)
                      ·
                        rfl

theorem cell23_1111369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 5, 2, 1, 1, 4].length) (baseStart_1111369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1111369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1111369 prefixEnd_1111369 := by exact prefixLift 1111369
  have htrace : WordTrace (prefixWord ++ tailWord_1111369) baseStart_1111369 baseEnd_1111369 := by
    simpa [prefixWord, tailWord_1111369, baseEnd_1111369] using wordTrace_append hprefix tailTrace_1111369
  have hstable : (prefixWord ++ tailWord_1111369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1111369).length < 2 ^ (prefixWord ++ tailWord_1111369).sum := by decide
  have hdescent : baseEnd_1111369 < baseStart_1111369 := by decide
  rcases family_descends (prefixWord ++ tailWord_1111369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1111396 : List Nat := [2, 3, 1, 1, 3, 3, 2, 2, 2, 4]
def baseStart_1111396 : Nat := 118140960795 + 1111396 * 2 ^ 59
def prefixEnd_1111396 : Nat := 4983230072969 + 3 ^ 40 * 1111396 * 2
def baseEnd_1111396 : Nat := 190226781828146297246263

theorem tailTrace_1111396 : CollatzResearch.WordTrace tailWord_1111396 prefixEnd_1111396 190226781828146297246263 := by
  unfold tailWord_1111396
  simp only [CollatzResearch.WordTrace]
  refine ⟨20267971140804789085129021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27023961521073052113505361 20267971140804789085129021)
  ·
    refine ⟨7600489177801795906923383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20267971140804789085129021 7600489177801795906923383)
    ·
      refine ⟨11400733766702693860385075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7600489177801795906923383 11400733766702693860385075)
      ·
        refine ⟨17101100650054040790577613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11400733766702693860385075 17101100650054040790577613)
        ·
          refine ⟨6412912743770265296466605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17101100650054040790577613 6412912743770265296466605)
          ·
            refine ⟨2404842278913849486174977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6412912743770265296466605 2404842278913849486174977)
            ·
              refine ⟨1803631709185387114631233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2404842278913849486174977 1803631709185387114631233)
              ·
                refine ⟨1352723781889040335973425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1803631709185387114631233 1352723781889040335973425)
                ·
                  refine ⟨1014542836416780251980069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1352723781889040335973425 1014542836416780251980069)
                  ·
                    refine ⟨190226781828146297246263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1014542836416780251980069 190226781828146297246263)
                    ·
                      rfl

theorem cell23_1111396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 2, 2, 2, 4].length) (baseStart_1111396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1111396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1111396 prefixEnd_1111396 := by exact prefixLift 1111396
  have htrace : WordTrace (prefixWord ++ tailWord_1111396) baseStart_1111396 baseEnd_1111396 := by
    simpa [prefixWord, tailWord_1111396, baseEnd_1111396] using wordTrace_append hprefix tailTrace_1111396
  have hstable : (prefixWord ++ tailWord_1111396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1111396).length < 2 ^ (prefixWord ++ tailWord_1111396).sum := by decide
  have hdescent : baseEnd_1111396 < baseStart_1111396 := by decide
  rcases family_descends (prefixWord ++ tailWord_1111396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1111419 : List Nat := [1, 1, 1, 1, 1, 6, 4, 1, 1, 3, 3]
def baseStart_1111419 : Nat := 118140960795 + 1111419 * 2 ^ 59
def prefixEnd_1111419 : Nat := 4983230072969 + 3 ^ 40 * 1111419 * 2
def baseEnd_1111419 : Nat := 570692155539492301751183

theorem tailTrace_1111419 : CollatzResearch.WordTrace tailWord_1111419 prefixEnd_1111419 570692155539492301751183 := by
  unfold tailWord_1111419
  simp only [CollatzResearch.WordTrace]
  refine ⟨40536781160526253098345311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27024520773684168732230207 40536781160526253098345311)
  ·
    refine ⟨60805171740789379647517967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40536781160526253098345311 60805171740789379647517967)
    ·
      refine ⟨91207757611184069471276951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60805171740789379647517967 91207757611184069471276951)
      ·
        refine ⟨136811636416776104206915427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91207757611184069471276951 136811636416776104206915427)
        ·
          refine ⟨205217454625164156310373141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 136811636416776104206915427 205217454625164156310373141)
          ·
            refine ⟨9619568185554569827048741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 205217454625164156310373141 9619568185554569827048741)
            ·
              refine ⟨1803669034791481842571639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9619568185554569827048741 1803669034791481842571639)
              ·
                refine ⟨2705503552187222763857459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1803669034791481842571639 2705503552187222763857459)
                ·
                  refine ⟨4058255328280834145786189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2705503552187222763857459 4058255328280834145786189)
                  ·
                    refine ⟨1521845748105312804669821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4058255328280834145786189 1521845748105312804669821)
                    ·
                      refine ⟨570692155539492301751183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1521845748105312804669821 570692155539492301751183)
                      ·
                        rfl

theorem cell23_1111419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 4, 1, 1, 3, 3].length) (baseStart_1111419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1111419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1111419 prefixEnd_1111419 := by exact prefixLift 1111419
  have htrace : WordTrace (prefixWord ++ tailWord_1111419) baseStart_1111419 baseEnd_1111419 := by
    simpa [prefixWord, tailWord_1111419, baseEnd_1111419] using wordTrace_append hprefix tailTrace_1111419
  have hstable : (prefixWord ++ tailWord_1111419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1111419).length < 2 ^ (prefixWord ++ tailWord_1111419).sum := by decide
  have hdescent : baseEnd_1111419 < baseStart_1111419 := by decide
  rcases family_descends (prefixWord ++ tailWord_1111419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1111453 : List Nat := [1, 4, 2, 1, 3, 1, 3, 2, 2, 1, 3]
def baseStart_1111453 : Nat := 118140960795 + 1111453 * 2 ^ 59
def prefixEnd_1111453 : Nat := 4983230072969 + 3 ^ 40 * 1111453 * 2
def baseEnd_1111453 : Nat := 570709613881745168726027

theorem tailTrace_1111453 : CollatzResearch.WordTrace tailWord_1111453 prefixEnd_1111453 570709613881745168726027 := by
  unfold tailWord_1111453
  simp only [CollatzResearch.WordTrace]
  refine ⟨40538021242403076905083013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27025347494935384603388675 40538021242403076905083013)
  ·
    refine ⟨7600878982950576919703065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 40538021242403076905083013 7600878982950576919703065)
    ·
      refine ⟨5700659237212932689777299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7600878982950576919703065 5700659237212932689777299)
      ·
        refine ⟨8550988855819399034665949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5700659237212932689777299 8550988855819399034665949)
        ·
          refine ⟨3206620820932274637999731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8550988855819399034665949 3206620820932274637999731)
          ·
            refine ⟨4809931231398411956999597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3206620820932274637999731 4809931231398411956999597)
            ·
              refine ⟨1803724211774404483874849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4809931231398411956999597 1803724211774404483874849)
              ·
                refine ⟨1352793158830803362906137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1803724211774404483874849 1352793158830803362906137)
                ·
                  refine ⟨1014594869123102522179603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1352793158830803362906137 1014594869123102522179603)
                  ·
                    refine ⟨1521892303684653783269405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1014594869123102522179603 1521892303684653783269405)
                    ·
                      refine ⟨570709613881745168726027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1521892303684653783269405 570709613881745168726027)
                      ·
                        rfl

theorem cell23_1111453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 3, 2, 2, 1, 3].length) (baseStart_1111453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1111453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1111453 prefixEnd_1111453 := by exact prefixLift 1111453
  have htrace : WordTrace (prefixWord ++ tailWord_1111453) baseStart_1111453 baseEnd_1111453 := by
    simpa [prefixWord, tailWord_1111453, baseEnd_1111453] using wordTrace_append hprefix tailTrace_1111453
  have hstable : (prefixWord ++ tailWord_1111453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1111453).length < 2 ^ (prefixWord ++ tailWord_1111453).sum := by decide
  have hdescent : baseEnd_1111453 < baseStart_1111453 := by decide
  rcases family_descends (prefixWord ++ tailWord_1111453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1111472 : List Nat := [2, 1, 1, 1, 2, 1, 1, 5, 1, 4, 4]
def baseStart_1111472 : Nat := 118140960795 + 1111472 * 2 ^ 59
def prefixEnd_1111472 : Nat := 4983230072969 + 3 ^ 40 * 1111472 * 2
def baseEnd_1111472 : Nat := 570719370014180594388439

theorem tailTrace_1111472 : CollatzResearch.WordTrace tailWord_1111472 prefixEnd_1111472 570719370014180594388439 := by
  unfold tailWord_1111472
  simp only [CollatzResearch.WordTrace]
  refine ⟨20269357114667121575012335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27025809486222828766683113 20269357114667121575012335)
  ·
    refine ⟨30404035672000682362518503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20269357114667121575012335 30404035672000682362518503)
    ·
      refine ⟨45606053508001023543777755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30404035672000682362518503 45606053508001023543777755)
      ·
        refine ⟨68409080262001535315666633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45606053508001023543777755 68409080262001535315666633)
        ·
          refine ⟨51306810196501151486749975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68409080262001535315666633 51306810196501151486749975)
          ·
            refine ⟨76960215294751727230124963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51306810196501151486749975 76960215294751727230124963)
            ·
              refine ⟨115440322942127590845187445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76960215294751727230124963 115440322942127590845187445)
              ·
                refine ⟨10822530275824461641736323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 115440322942127590845187445 10822530275824461641736323)
                ·
                  refine ⟨16233795413736692462604485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10822530275824461641736323 16233795413736692462604485)
                  ·
                    refine ⟨3043836640075629836738341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16233795413736692462604485 3043836640075629836738341)
                    ·
                      refine ⟨570719370014180594388439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3043836640075629836738341 570719370014180594388439)
                      ·
                        rfl

theorem cell23_1111472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 5, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 5, 1, 4, 4].length) (baseStart_1111472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1111472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1111472 prefixEnd_1111472 := by exact prefixLift 1111472
  have htrace : WordTrace (prefixWord ++ tailWord_1111472) baseStart_1111472 baseEnd_1111472 := by
    simpa [prefixWord, tailWord_1111472, baseEnd_1111472] using wordTrace_append hprefix tailTrace_1111472
  have hstable : (prefixWord ++ tailWord_1111472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1111472).length < 2 ^ (prefixWord ++ tailWord_1111472).sum := by decide
  have hdescent : baseEnd_1111472 < baseStart_1111472 := by decide
  rcases family_descends (prefixWord ++ tailWord_1111472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1111510 : List Nat := [5, 2, 1, 1, 1, 2, 2, 1, 4, 2, 2]
def baseStart_1111510 : Nat := 118140960795 + 1111510 * 2 ^ 59
def prefixEnd_1111510 : Nat := 4983230072969 + 3 ^ 40 * 1111510 * 2
def baseEnd_1111510 : Nat := 570738882279051445713265

theorem tailTrace_1111510 : CollatzResearch.WordTrace tailWord_1111510 prefixEnd_1111510 570738882279051445713265 := by
  unfold tailWord_1111510
  simp only [CollatzResearch.WordTrace]
  refine ⟨2533756262699785977494249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 27026733468797717093271989 2533756262699785977494249)
  ·
    refine ⟨1900317197024839483120687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2533756262699785977494249 1900317197024839483120687)
    ·
      refine ⟨2850475795537259224681031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1900317197024839483120687 2850475795537259224681031)
      ·
        refine ⟨4275713693305888837021547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2850475795537259224681031 4275713693305888837021547)
        ·
          refine ⟨6413570539958833255532321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4275713693305888837021547 6413570539958833255532321)
          ·
            refine ⟨4810177904969124941649241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6413570539958833255532321 4810177904969124941649241)
            ·
              refine ⟨3607633428726843706236931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4810177904969124941649241 3607633428726843706236931)
              ·
                refine ⟨5411450143090265559355397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3607633428726843706236931 5411450143090265559355397)
                ·
                  refine ⟨1014646901829424792379137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5411450143090265559355397 1014646901829424792379137)
                  ·
                    refine ⟨760985176372068594284353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1014646901829424792379137 760985176372068594284353)
                    ·
                      refine ⟨570738882279051445713265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 760985176372068594284353 570738882279051445713265)
                      ·
                        rfl

theorem cell23_1111510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 2, 1, 4, 2, 2].length) (baseStart_1111510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1111510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1111510 prefixEnd_1111510 := by exact prefixLift 1111510
  have htrace : WordTrace (prefixWord ++ tailWord_1111510) baseStart_1111510 baseEnd_1111510 := by
    simpa [prefixWord, tailWord_1111510, baseEnd_1111510] using wordTrace_append hprefix tailTrace_1111510
  have hstable : (prefixWord ++ tailWord_1111510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1111510).length < 2 ^ (prefixWord ++ tailWord_1111510).sum := by decide
  have hdescent : baseEnd_1111510 < baseStart_1111510 := by decide
  rcases family_descends (prefixWord ++ tailWord_1111510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1111527 : List Nat := [1, 1, 5, 2, 1, 4, 2, 1, 2, 2, 2]
def baseStart_1111527 : Nat := 118140960795 + 1111527 * 2 ^ 59
def prefixEnd_1111527 : Nat := 4983230072969 + 3 ^ 40 * 1111527 * 2
def baseEnd_1111527 : Nat := 570747611450177879200687

theorem tailTrace_1111527 : CollatzResearch.WordTrace tailWord_1111527 prefixEnd_1111527 570747611450177879200687 := by
  unfold tailWord_1111527
  simp only [CollatzResearch.WordTrace]
  refine ⟨40540720244134987543276835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27027146829423325028851223 40540720244134987543276835)
  ·
    refine ⟨60811080366202481314915253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40540720244134987543276835 60811080366202481314915253)
    ·
      refine ⟨5701038784331482623273305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 60811080366202481314915253 5701038784331482623273305)
      ·
        refine ⟨4275779088248611967454979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5701038784331482623273305 4275779088248611967454979)
        ·
          refine ⟨6413668632372917951182469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4275779088248611967454979 6413668632372917951182469)
          ·
            refine ⟨1202562868569922115846713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6413668632372917951182469 1202562868569922115846713)
            ·
              refine ⟨901922151427441586885035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1202562868569922115846713 901922151427441586885035)
              ·
                refine ⟨1352883227141162380327553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 901922151427441586885035 1352883227141162380327553)
                ·
                  refine ⟨1014662420355871785245665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1352883227141162380327553 1014662420355871785245665)
                  ·
                    refine ⟨760996815266903838934249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1014662420355871785245665 760996815266903838934249)
                    ·
                      refine ⟨570747611450177879200687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 760996815266903838934249 570747611450177879200687)
                      ·
                        rfl

theorem cell23_1111527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 4, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 4, 2, 1, 2, 2, 2].length) (baseStart_1111527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1111527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1111527 prefixEnd_1111527 := by exact prefixLift 1111527
  have htrace : WordTrace (prefixWord ++ tailWord_1111527) baseStart_1111527 baseEnd_1111527 := by
    simpa [prefixWord, tailWord_1111527, baseEnd_1111527] using wordTrace_append hprefix tailTrace_1111527
  have hstable : (prefixWord ++ tailWord_1111527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1111527).length < 2 ^ (prefixWord ++ tailWord_1111527).sum := by decide
  have hdescent : baseEnd_1111527 < baseStart_1111527 := by decide
  rcases family_descends (prefixWord ++ tailWord_1111527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1111552 : List Nat := [2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 11]
def baseStart_1111552 : Nat := 118140960795 + 1111552 * 2 ^ 59
def prefixEnd_1111552 : Nat := 4983230072969 + 3 ^ 40 * 1111552 * 2
def baseEnd_1111552 : Nat := 570760448466540281388071

theorem tailTrace_1111552 : CollatzResearch.WordTrace tailWord_1111552 prefixEnd_1111552 570760448466540281388071 := by
  unfold tailWord_1111552
  simp only [CollatzResearch.WordTrace]
  refine ⟨20270816034522208406468455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27027754712696277875291273 20270816034522208406468455)
  ·
    refine ⟨30406224051783312609702683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20270816034522208406468455 30406224051783312609702683)
    ·
      refine ⟨45609336077674968914554025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30406224051783312609702683 45609336077674968914554025)
      ·
        refine ⟨34207002058256226685915519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45609336077674968914554025 34207002058256226685915519)
        ·
          refine ⟨51310503087384340028873279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34207002058256226685915519 51310503087384340028873279)
          ·
            refine ⟨76965754631076510043309919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51310503087384340028873279 76965754631076510043309919)
            ·
              refine ⟨115448631946614765064964879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76965754631076510043309919 115448631946614765064964879)
              ·
                refine ⟨173172947919922147597447319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 115448631946614765064964879 173172947919922147597447319)
                ·
                  refine ⟨259759421879883221396170979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 173172947919922147597447319 259759421879883221396170979)
                  ·
                    refine ⟨389639132819824832094256469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 259759421879883221396170979 389639132819824832094256469)
                    ·
                      refine ⟨570760448466540281388071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 11 389639132819824832094256469 570760448466540281388071)
                      ·
                        rfl

theorem cell23_1111552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 11].length) (baseStart_1111552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1111552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1111552 prefixEnd_1111552 := by exact prefixLift 1111552
  have htrace : WordTrace (prefixWord ++ tailWord_1111552) baseStart_1111552 baseEnd_1111552 := by
    simpa [prefixWord, tailWord_1111552, baseEnd_1111552] using wordTrace_append hprefix tailTrace_1111552
  have hstable : (prefixWord ++ tailWord_1111552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1111552).length < 2 ^ (prefixWord ++ tailWord_1111552).sum := by decide
  have hdescent : baseEnd_1111552 < baseStart_1111552 := by decide
  rcases family_descends (prefixWord ++ tailWord_1111552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1111586 : List Nat := [3, 3, 1, 1, 1, 1, 2, 2, 4, 2, 3]
def baseStart_1111586 : Nat := 118140960795 + 1111586 * 2 ^ 59
def prefixEnd_1111586 : Nat := 4983230072969 + 3 ^ 40 * 1111586 * 2
def baseEnd_1111586 : Nat := 570777906808793148362915

theorem tailTrace_1111586 : CollatzResearch.WordTrace tailWord_1111586 prefixEnd_1111586 570777906808793148362915 := by
  unfold tailWord_1111586
  simp only [CollatzResearch.WordTrace]
  refine ⟨10135718037730310154918653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27028581433947493746449741 10135718037730310154918653)
  ·
    refine ⟨3800894264148866308094495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10135718037730310154918653 3800894264148866308094495)
    ·
      refine ⟨5701341396223299462141743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3800894264148866308094495 5701341396223299462141743)
      ·
        refine ⟨8552012094334949193212615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5701341396223299462141743 8552012094334949193212615)
        ·
          refine ⟨12828018141502423789818923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8552012094334949193212615 12828018141502423789818923)
          ·
            refine ⟨19242027212253635684728385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12828018141502423789818923 19242027212253635684728385)
            ·
              refine ⟨14431520409190226763546289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19242027212253635684728385 14431520409190226763546289)
              ·
                refine ⟨10823640306892670072659717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14431520409190226763546289 10823640306892670072659717)
                ·
                  refine ⟨2029432557542375638623697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10823640306892670072659717 2029432557542375638623697)
                  ·
                    refine ⟨1522074418156781728967773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2029432557542375638623697 1522074418156781728967773)
                    ·
                      refine ⟨570777906808793148362915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1522074418156781728967773 570777906808793148362915)
                      ·
                        rfl

theorem cell23_1111586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 2, 4, 2, 3].length) (baseStart_1111586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1111586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1111586 prefixEnd_1111586 := by exact prefixLift 1111586
  have htrace : WordTrace (prefixWord ++ tailWord_1111586) baseStart_1111586 baseEnd_1111586 := by
    simpa [prefixWord, tailWord_1111586, baseEnd_1111586] using wordTrace_append hprefix tailTrace_1111586
  have hstable : (prefixWord ++ tailWord_1111586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1111586).length < 2 ^ (prefixWord ++ tailWord_1111586).sum := by decide
  have hdescent : baseEnd_1111586 < baseStart_1111586 := by decide
  rcases family_descends (prefixWord ++ tailWord_1111586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1111603 : List Nat := [1, 1, 1, 2, 4, 5, 1, 1, 2, 2, 3]
def baseStart_1111603 : Nat := 118140960795 + 1111603 * 2 ^ 59
def prefixEnd_1111603 : Nat := 4983230072969 + 3 ^ 40 * 1111603 * 2
def baseEnd_1111603 : Nat := 570786635979919581850337

theorem tailTrace_1111603 : CollatzResearch.WordTrace tailWord_1111603 prefixEnd_1111603 570786635979919581850337 := by
  unfold tailWord_1111603
  simp only [CollatzResearch.WordTrace]
  refine ⟨40543492191859652523043463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27028994794573101682028975 40543492191859652523043463)
  ·
    refine ⟨60815238287789478784565195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40543492191859652523043463 60815238287789478784565195)
    ·
      refine ⟨91222857431684218176847793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60815238287789478784565195 91222857431684218176847793)
      ·
        refine ⟨68417143073763163632635845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91222857431684218176847793 68417143073763163632635845)
        ·
          refine ⟨12828214326330593181119221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 68417143073763163632635845 12828214326330593181119221)
          ·
            refine ⟨1202645093093493110729927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 12828214326330593181119221 1202645093093493110729927)
            ·
              refine ⟨1803967639640239666094891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1202645093093493110729927 1803967639640239666094891)
              ·
                refine ⟨2705951459460359499142337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1803967639640239666094891 2705951459460359499142337)
                ·
                  refine ⟨2029463594595269624356753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2705951459460359499142337 2029463594595269624356753)
                  ·
                    refine ⟨1522097695946452218267565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2029463594595269624356753 1522097695946452218267565)
                    ·
                      refine ⟨570786635979919581850337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1522097695946452218267565 570786635979919581850337)
                      ·
                        rfl

theorem cell23_1111603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 5, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 5, 1, 1, 2, 2, 3].length) (baseStart_1111603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1111603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1111603 prefixEnd_1111603 := by exact prefixLift 1111603
  have htrace : WordTrace (prefixWord ++ tailWord_1111603) baseStart_1111603 baseEnd_1111603 := by
    simpa [prefixWord, tailWord_1111603, baseEnd_1111603] using wordTrace_append hprefix tailTrace_1111603
  have hstable : (prefixWord ++ tailWord_1111603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1111603).length < 2 ^ (prefixWord ++ tailWord_1111603).sum := by decide
  have hdescent : baseEnd_1111603 < baseStart_1111603 := by decide
  rcases family_descends (prefixWord ++ tailWord_1111603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1111616 : List Nat := [2, 1, 1, 2, 2, 2, 1, 1, 7, 1, 3]
def baseStart_1111616 : Nat := 118140960795 + 1111616 * 2 ^ 59
def prefixEnd_1111616 : Nat := 4983230072969 + 3 ^ 40 * 1111616 * 2
def baseEnd_1111616 : Nat := 570793311228428030987777

theorem tailTrace_1111616 : CollatzResearch.WordTrace tailWord_1111616 prefixEnd_1111616 570793311228428030987777 := by
  unfold tailWord_1111616
  simp only [CollatzResearch.WordTrace]
  refine ⟨20271983170406277871633351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27029310893875037162177801 20271983170406277871633351)
  ·
    refine ⟨30407974755609416807450027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20271983170406277871633351 30407974755609416807450027)
    ·
      refine ⟨45611962133414125211175041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30407974755609416807450027 45611962133414125211175041)
      ·
        refine ⟨34208971600060593908381281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45611962133414125211175041 34208971600060593908381281)
        ·
          refine ⟨25656728700045445431285961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34208971600060593908381281 25656728700045445431285961)
          ·
            refine ⟨19242546525034084073464471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25656728700045445431285961 19242546525034084073464471)
            ·
              refine ⟨28863819787551126110196707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19242546525034084073464471 28863819787551126110196707)
              ·
                refine ⟨43295729681326689165295061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28863819787551126110196707 43295729681326689165295061)
                ·
                  refine ⟨1014743664406094277311603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 43295729681326689165295061 1014743664406094277311603)
                  ·
                    refine ⟨1522115496609141415967405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1014743664406094277311603 1522115496609141415967405)
                    ·
                      refine ⟨570793311228428030987777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1522115496609141415967405 570793311228428030987777)
                      ·
                        rfl

theorem cell23_1111616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 1, 7, 1, 3].length) (baseStart_1111616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1111616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1111616 prefixEnd_1111616 := by exact prefixLift 1111616
  have htrace : WordTrace (prefixWord ++ tailWord_1111616) baseStart_1111616 baseEnd_1111616 := by
    simpa [prefixWord, tailWord_1111616, baseEnd_1111616] using wordTrace_append hprefix tailTrace_1111616
  have hstable : (prefixWord ++ tailWord_1111616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1111616).length < 2 ^ (prefixWord ++ tailWord_1111616).sum := by decide
  have hdescent : baseEnd_1111616 < baseStart_1111616 := by decide
  rcases family_descends (prefixWord ++ tailWord_1111616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1111623 : List Nat := [1, 1, 4, 1, 5, 2, 1, 2, 6]
def baseStart_1111623 : Nat := 118140960795 + 1111623 * 2 ^ 59
def prefixEnd_1111623 : Nat := 4983230072969 + 3 ^ 40 * 1111623 * 2
def baseEnd_1111623 : Nat := 63421878399223278177805

theorem tailTrace_1111623 : CollatzResearch.WordTrace tailWord_1111623 prefixEnd_1111623 63421878399223278177805 := by
  unfold tailWord_1111623
  simp only [CollatzResearch.WordTrace]
  refine ⟨40544221651787195938771523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27029481101191463959181015 40544221651787195938771523)
  ·
    refine ⟨60816332477680793908157285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40544221651787195938771523 60816332477680793908157285)
    ·
      refine ⟨11403062339565148857779491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 60816332477680793908157285 11403062339565148857779491)
      ·
        refine ⟨17104593509347723286669237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11403062339565148857779491 17104593509347723286669237)
        ·
          refine ⟨1603555641501349058125241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 17104593509347723286669237 1603555641501349058125241)
          ·
            refine ⟨1202666731126011793593931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1603555641501349058125241 1202666731126011793593931)
            ·
              refine ⟨1804000096689017690390897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1202666731126011793593931 1804000096689017690390897)
              ·
                refine ⟨1353000072516763267793173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1804000096689017690390897 1353000072516763267793173)
                ·
                  refine ⟨63421878399223278177805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1353000072516763267793173 63421878399223278177805)
                  ·
                    rfl

theorem cell23_1111623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 2, 1, 2, 6].length) (baseStart_1111623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1111623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1111623 prefixEnd_1111623 := by exact prefixLift 1111623
  have htrace : WordTrace (prefixWord ++ tailWord_1111623) baseStart_1111623 baseEnd_1111623 := by
    simpa [prefixWord, tailWord_1111623, baseEnd_1111623] using wordTrace_append hprefix tailTrace_1111623
  have hstable : (prefixWord ++ tailWord_1111623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1111623).length < 2 ^ (prefixWord ++ tailWord_1111623).sum := by decide
  have hdescent : baseEnd_1111623 < baseStart_1111623 := by decide
  rcases family_descends (prefixWord ++ tailWord_1111623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1111633 : List Nat := [1, 2, 2, 1, 3, 2, 4, 1, 3, 1, 3]
def baseStart_1111633 : Nat := 118140960795 + 1111633 * 2 ^ 59
def prefixEnd_1111633 : Nat := 4983230072969 + 3 ^ 40 * 1111633 * 2
def baseEnd_1111633 : Nat := 570802040399554464475199

theorem tailTrace_1111633 : CollatzResearch.WordTrace tailWord_1111633 prefixEnd_1111633 570802040399554464475199 := by
  unfold tailWord_1111633
  simp only [CollatzResearch.WordTrace]
  refine ⟨40544586381750967646635553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27029724254500645097757035 40544586381750967646635553)
  ·
    refine ⟨30408439786313225734976665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40544586381750967646635553 30408439786313225734976665)
    ·
      refine ⟨22806329839734919301232499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30408439786313225734976665 22806329839734919301232499)
      ·
        refine ⟨34209494759602378951848749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22806329839734919301232499 34209494759602378951848749)
        ·
          refine ⟨12828560534850892106943281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34209494759602378951848749 12828560534850892106943281)
          ·
            refine ⟨9621420401138169080207461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12828560534850892106943281 9621420401138169080207461)
            ·
              refine ⟨1804016325213406702538899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9621420401138169080207461 1804016325213406702538899)
              ·
                refine ⟨2706024487820110053808349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1804016325213406702538899 2706024487820110053808349)
                ·
                  refine ⟨1014759182932541270178131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2706024487820110053808349 1014759182932541270178131)
                  ·
                    refine ⟨1522138774398811905267197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1014759182932541270178131 1522138774398811905267197)
                    ·
                      refine ⟨570802040399554464475199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1522138774398811905267197 570802040399554464475199)
                      ·
                        rfl

theorem cell23_1111633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 4, 1, 3, 1, 3].length) (baseStart_1111633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1111633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1111633 prefixEnd_1111633 := by exact prefixLift 1111633
  have htrace : WordTrace (prefixWord ++ tailWord_1111633) baseStart_1111633 baseEnd_1111633 := by
    simpa [prefixWord, tailWord_1111633, baseEnd_1111633] using wordTrace_append hprefix tailTrace_1111633
  have hstable : (prefixWord ++ tailWord_1111633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1111633).length < 2 ^ (prefixWord ++ tailWord_1111633).sum := by decide
  have hdescent : baseEnd_1111633 < baseStart_1111633 := by decide
  rcases family_descends (prefixWord ++ tailWord_1111633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1111653 : List Nat := [1, 3, 1, 3, 3, 2, 2, 2, 1, 5]
def baseStart_1111653 : Nat := 118140960795 + 1111653 * 2 ^ 59
def prefixEnd_1111653 : Nat := 4983230072969 + 3 ^ 40 * 1111653 * 2
def baseEnd_1111653 : Nat := 190270770004214795408369

theorem tailTrace_1111653 : CollatzResearch.WordTrace tailWord_1111653 prefixEnd_1111653 190270770004214795408369 := by
  unfold tailWord_1111653
  simp only [CollatzResearch.WordTrace]
  refine ⟨40545315841678511062363613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27030210561119007374909075 40545315841678511062363613)
  ·
    refine ⟨15204493440629441648386355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40545315841678511062363613 15204493440629441648386355)
    ·
      refine ⟨22806740160944162472579533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15204493440629441648386355 22806740160944162472579533)
      ·
        refine ⟨8552527560354060927217325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22806740160944162472579533 8552527560354060927217325)
        ·
          refine ⟨3207197835132772847706497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8552527560354060927217325 3207197835132772847706497)
          ·
            refine ⟨2405398376349579635779873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3207197835132772847706497 2405398376349579635779873)
            ·
              refine ⟨1804048782262184726834905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2405398376349579635779873 1804048782262184726834905)
              ·
                refine ⟨1353036586696638545126179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1804048782262184726834905 1353036586696638545126179)
                ·
                  refine ⟨2029554880044957817689269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1353036586696638545126179 2029554880044957817689269)
                  ·
                    refine ⟨190270770004214795408369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2029554880044957817689269 190270770004214795408369)
                    ·
                      rfl

theorem cell23_1111653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 2, 2, 1, 5].length) (baseStart_1111653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1111653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1111653 prefixEnd_1111653 := by exact prefixLift 1111653
  have htrace : WordTrace (prefixWord ++ tailWord_1111653) baseStart_1111653 baseEnd_1111653 := by
    simpa [prefixWord, tailWord_1111653, baseEnd_1111653] using wordTrace_append hprefix tailTrace_1111653
  have hstable : (prefixWord ++ tailWord_1111653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1111653).length < 2 ^ (prefixWord ++ tailWord_1111653).sum := by decide
  have hdescent : baseEnd_1111653 < baseStart_1111653 := by decide
  rcases family_descends (prefixWord ++ tailWord_1111653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1111676 : List Nat := [2, 2, 2, 1, 1, 2, 1, 2, 5, 2, 3]
def baseStart_1111676 : Nat := 118140960795 + 1111676 * 2 ^ 59
def prefixEnd_1111676 : Nat := 4983230072969 + 3 ^ 40 * 1111676 * 2
def baseEnd_1111676 : Nat := 570824120067697796237501

theorem tailTrace_1111676 : CollatzResearch.WordTrace tailWord_1111676 prefixEnd_1111676 570824120067697796237501 := by
  unfold tailWord_1111676
  simp only [CollatzResearch.WordTrace]
  refine ⟨20273077360297592995225441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27030769813730123993633921 20273077360297592995225441)
  ·
    refine ⟨15204808020223194746419081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20273077360297592995225441 15204808020223194746419081)
    ·
      refine ⟨11403606015167396059814311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15204808020223194746419081 11403606015167396059814311)
      ·
        refine ⟨17105409022751094089721467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11403606015167396059814311 17105409022751094089721467)
        ·
          refine ⟨25658113534126641134582201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17105409022751094089721467 25658113534126641134582201)
          ·
            refine ⟨19243585150594980850936651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25658113534126641134582201 19243585150594980850936651)
            ·
              refine ⟨28865377725892471276404977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19243585150594980850936651 28865377725892471276404977)
              ·
                refine ⟨21649033294419353457303733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28865377725892471276404977 21649033294419353457303733)
                ·
                  refine ⟨2029596871351814386622225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 21649033294419353457303733 2029596871351814386622225)
                  ·
                    refine ⟨1522197653513860789966669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2029596871351814386622225 1522197653513860789966669)
                    ·
                      refine ⟨570824120067697796237501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1522197653513860789966669 570824120067697796237501)
                      ·
                        rfl

theorem cell23_1111676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 2, 5, 2, 3].length) (baseStart_1111676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1111676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1111676 prefixEnd_1111676 := by exact prefixLift 1111676
  have htrace : WordTrace (prefixWord ++ tailWord_1111676) baseStart_1111676 baseEnd_1111676 := by
    simpa [prefixWord, tailWord_1111676, baseEnd_1111676] using wordTrace_append hprefix tailTrace_1111676
  have hstable : (prefixWord ++ tailWord_1111676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1111676).length < 2 ^ (prefixWord ++ tailWord_1111676).sum := by decide
  have hdescent : baseEnd_1111676 < baseStart_1111676 := by decide
  rcases family_descends (prefixWord ++ tailWord_1111676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1111684 : List Nat := [2, 3, 2, 1, 4, 1, 3, 2, 1, 1, 3]
def baseStart_1111684 : Nat := 118140960795 + 1111684 * 2 ^ 59
def prefixEnd_1111684 : Nat := 4983230072969 + 3 ^ 40 * 1111684 * 2
def baseEnd_1111684 : Nat := 570828227912933764937465

theorem tailTrace_1111684 : CollatzResearch.WordTrace tailWord_1111684 prefixEnd_1111684 570828227912933764937465 := by
  unfold tailWord_1111684
  simp only [CollatzResearch.WordTrace]
  refine ⟨20273223252283101678371053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27030964336377468904494737 20273223252283101678371053)
  ·
    refine ⟨7602458719606163129389145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20273223252283101678371053 7602458719606163129389145)
    ·
      refine ⟨5701844039704622347041859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7602458719606163129389145 5701844039704622347041859)
      ·
        refine ⟨8552766059556933520562789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5701844039704622347041859 8552766059556933520562789)
        ·
          refine ⟨1603643636166925035105523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8552766059556933520562789 1603643636166925035105523)
          ·
            refine ⟨2405465454250387552658285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1603643636166925035105523 2405465454250387552658285)
            ·
              refine ⟨902049545343895332246857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2405465454250387552658285 902049545343895332246857)
              ·
                refine ⟨676537159007921499185143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 902049545343895332246857 676537159007921499185143)
                ·
                  refine ⟨1014805738511882248777715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 676537159007921499185143 1014805738511882248777715)
                  ·
                    refine ⟨1522208607767823373166573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1014805738511882248777715 1522208607767823373166573)
                    ·
                      refine ⟨570828227912933764937465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1522208607767823373166573 570828227912933764937465)
                      ·
                        rfl

theorem cell23_1111684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 3, 2, 1, 1, 3].length) (baseStart_1111684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1111684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1111684 prefixEnd_1111684 := by exact prefixLift 1111684
  have htrace : WordTrace (prefixWord ++ tailWord_1111684) baseStart_1111684 baseEnd_1111684 := by
    simpa [prefixWord, tailWord_1111684, baseEnd_1111684] using wordTrace_append hprefix tailTrace_1111684
  have hstable : (prefixWord ++ tailWord_1111684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1111684).length < 2 ^ (prefixWord ++ tailWord_1111684).sum := by decide
  have hdescent : baseEnd_1111684 < baseStart_1111684 := by decide
  rcases family_descends (prefixWord ++ tailWord_1111684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1111710 : List Nat := [4, 3, 1, 1, 1, 3, 1, 1, 3, 2, 3]
def baseStart_1111710 : Nat := 118140960795 + 1111710 * 2 ^ 59
def prefixEnd_1111710 : Nat := 4983230072969 + 3 ^ 40 * 1111710 * 2
def baseEnd_1111710 : Nat := 570841578409950663212345

theorem tailTrace_1111710 : CollatzResearch.WordTrace tailWord_1111710 prefixEnd_1111710 570841578409950663212345 := by
  unfold tailWord_1111710
  simp only [CollatzResearch.WordTrace]
  refine ⟨5068424350309001224648573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27031596534981339864792389 5068424350309001224648573)
  ·
    refine ⟨1900659131365875459243215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5068424350309001224648573 1900659131365875459243215)
    ·
      refine ⟨2850988697048813188864823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1900659131365875459243215 2850988697048813188864823)
      ·
        refine ⟨4276483045573219783297235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2850988697048813188864823 4276483045573219783297235)
        ·
          refine ⟨6414724568359829674945853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4276483045573219783297235 6414724568359829674945853)
          ·
            refine ⟨2405521713134936128104695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6414724568359829674945853 2405521713134936128104695)
            ·
              refine ⟨3608282569702404192157043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2405521713134936128104695 3608282569702404192157043)
              ·
                refine ⟨5412423854553606288235565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3608282569702404192157043 5412423854553606288235565)
                ·
                  refine ⟨2029658945457602358088337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5412423854553606288235565 2029658945457602358088337)
                  ·
                    refine ⟨1522244209093201768566253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2029658945457602358088337 1522244209093201768566253)
                    ·
                      refine ⟨570841578409950663212345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1522244209093201768566253 570841578409950663212345)
                      ·
                        rfl

theorem cell23_1111710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 1, 1, 3, 2, 3].length) (baseStart_1111710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1111710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1111710 prefixEnd_1111710 := by exact prefixLift 1111710
  have htrace : WordTrace (prefixWord ++ tailWord_1111710) baseStart_1111710 baseEnd_1111710 := by
    simpa [prefixWord, tailWord_1111710, baseEnd_1111710] using wordTrace_append hprefix tailTrace_1111710
  have hstable : (prefixWord ++ tailWord_1111710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1111710).length < 2 ^ (prefixWord ++ tailWord_1111710).sum := by decide
  have hdescent : baseEnd_1111710 < baseStart_1111710 := by decide
  rcases family_descends (prefixWord ++ tailWord_1111710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1111739 : List Nat := [1, 1, 1, 1, 1, 2, 3, 2, 3, 8]
def baseStart_1111739 : Nat := 118140960795 + 1111739 * 2 ^ 59
def prefixEnd_1111739 : Nat := 4983230072969 + 3 ^ 40 * 1111739 * 2
def baseEnd_1111739 : Nat := 190285489782977016583237

theorem tailTrace_1111739 : CollatzResearch.WordTrace tailWord_1111739 prefixEnd_1111739 190285489782977016583237 := by
  unfold tailWord_1111739
  simp only [CollatzResearch.WordTrace]
  refine ⟨40548452519366947749994271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27032301679577965166662847 40548452519366947749994271)
  ·
    refine ⟨60822678779050421624991407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40548452519366947749994271 60822678779050421624991407)
    ·
      refine ⟨91234018168575632437487111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60822678779050421624991407 91234018168575632437487111)
      ·
        refine ⟨136851027252863448656230667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91234018168575632437487111 136851027252863448656230667)
        ·
          refine ⟨205276540879295172984346001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 136851027252863448656230667 205276540879295172984346001)
          ·
            refine ⟨153957405659471379738259501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 205276540879295172984346001 153957405659471379738259501)
            ·
              refine ⟨57734027122301767401847313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 153957405659471379738259501 57734027122301767401847313)
              ·
                refine ⟨43300520341726325551385485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 57734027122301767401847313 43300520341726325551385485)
                ·
                  refine ⟨16237695128147372081769557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 43300520341726325551385485 16237695128147372081769557)
                  ·
                    refine ⟨190285489782977016583237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 16237695128147372081769557 190285489782977016583237)
                    ·
                      rfl

theorem cell23_1111739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 2, 3, 8].length) (baseStart_1111739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1111739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1111739 prefixEnd_1111739 := by exact prefixLift 1111739
  have htrace : WordTrace (prefixWord ++ tailWord_1111739) baseStart_1111739 baseEnd_1111739 := by
    simpa [prefixWord, tailWord_1111739, baseEnd_1111739] using wordTrace_append hprefix tailTrace_1111739
  have hstable : (prefixWord ++ tailWord_1111739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1111739).length < 2 ^ (prefixWord ++ tailWord_1111739).sum := by decide
  have hdescent : baseEnd_1111739 < baseStart_1111739 := by decide
  rcases family_descends (prefixWord ++ tailWord_1111739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1111740 : List Nat := [2, 2, 2, 3, 1, 2, 1, 4, 2, 1, 3]
def baseStart_1111740 : Nat := 118140960795 + 1111740 * 2 ^ 59
def prefixEnd_1111740 : Nat := 4983230072969 + 3 ^ 40 * 1111740 * 2
def baseEnd_1111740 : Nat := 570856982829585545837207

theorem tailTrace_1111740 : CollatzResearch.WordTrace tailWord_1111740 prefixEnd_1111740 570856982829585545837207 := by
  unfold tailWord_1111740
  simp only [CollatzResearch.WordTrace]
  refine ⟨20274244496181662460390337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27032325994908883280520449 20274244496181662460390337)
  ·
    refine ⟨15205683372136246845292753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20274244496181662460390337 15205683372136246845292753)
    ·
      refine ⟨11404262529102185133969565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15205683372136246845292753 11404262529102185133969565)
      ·
        refine ⟨4276598448413319425238587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11404262529102185133969565 4276598448413319425238587)
        ·
          refine ⟨6414897672619979137857881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4276598448413319425238587 6414897672619979137857881)
          ·
            refine ⟨4811173254464984353393411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6414897672619979137857881 4811173254464984353393411)
            ·
              refine ⟨7216759881697476530090117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4811173254464984353393411 7216759881697476530090117)
              ·
                refine ⟨1353142477818276849391897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7216759881697476530090117 1353142477818276849391897)
                ·
                  refine ⟨1014856858363707637043923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1353142477818276849391897 1014856858363707637043923)
                  ·
                    refine ⟨1522285287545561455565885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1014856858363707637043923 1522285287545561455565885)
                    ·
                      refine ⟨570856982829585545837207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1522285287545561455565885 570856982829585545837207)
                      ·
                        rfl

theorem cell23_1111740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 4, 2, 1, 3].length) (baseStart_1111740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1111740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1111740 prefixEnd_1111740 := by exact prefixLift 1111740
  have htrace : WordTrace (prefixWord ++ tailWord_1111740) baseStart_1111740 baseEnd_1111740 := by
    simpa [prefixWord, tailWord_1111740, baseEnd_1111740] using wordTrace_append hprefix tailTrace_1111740
  have hstable : (prefixWord ++ tailWord_1111740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1111740).length < 2 ^ (prefixWord ++ tailWord_1111740).sum := by decide
  have hdescent : baseEnd_1111740 < baseStart_1111740 := by decide
  rcases family_descends (prefixWord ++ tailWord_1111740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1111757 : List Nat := [1, 6, 2, 1, 1, 2, 2, 1, 1, 3, 3]
def baseStart_1111757 : Nat := 118140960795 + 1111757 * 2 ^ 59
def prefixEnd_1111757 : Nat := 4983230072969 + 3 ^ 40 * 1111757 * 2
def baseEnd_1111757 : Nat := 570865712000711979324629

theorem tailTrace_1111757 : CollatzResearch.WordTrace tailWord_1111757 prefixEnd_1111757 570865712000711979324629 := by
  unfold tailWord_1111757
  simp only [CollatzResearch.WordTrace]
  refine ⟨40549109033301736824149525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27032739355534491216099683 40549109033301736824149525)
  ·
    refine ⟨1900739485936018913632009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 40549109033301736824149525 1900739485936018913632009)
    ·
      refine ⟨1425554614452014185224007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1900739485936018913632009 1425554614452014185224007)
      ·
        refine ⟨2138331921678021277836011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1425554614452014185224007 2138331921678021277836011)
        ·
          refine ⟨3207497882517031916754017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2138331921678021277836011 3207497882517031916754017)
          ·
            refine ⟨2405623411887773937565513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3207497882517031916754017 2405623411887773937565513)
            ·
              refine ⟨1804217558915830453174135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2405623411887773937565513 1804217558915830453174135)
              ·
                refine ⟨2706326338373745679761203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1804217558915830453174135 2706326338373745679761203)
                ·
                  refine ⟨4059489507560618519641805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2706326338373745679761203 4059489507560618519641805)
                  ·
                    refine ⟨1522308565335231944865677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4059489507560618519641805 1522308565335231944865677)
                    ·
                      refine ⟨570865712000711979324629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1522308565335231944865677 570865712000711979324629)
                      ·
                        rfl

theorem cell23_1111757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 2, 1, 1, 3, 3].length) (baseStart_1111757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1111757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1111757 prefixEnd_1111757 := by exact prefixLift 1111757
  have htrace : WordTrace (prefixWord ++ tailWord_1111757) baseStart_1111757 baseEnd_1111757 := by
    simpa [prefixWord, tailWord_1111757, baseEnd_1111757] using wordTrace_append hprefix tailTrace_1111757
  have hstable : (prefixWord ++ tailWord_1111757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1111757).length < 2 ^ (prefixWord ++ tailWord_1111757).sum := by decide
  have hdescent : baseEnd_1111757 < baseStart_1111757 := by decide
  rcases family_descends (prefixWord ++ tailWord_1111757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1111780 : List Nat := [2, 3, 1, 1, 1, 3, 2, 2, 4, 2, 2]
def baseStart_1111780 : Nat := 118140960795 + 1111780 * 2 ^ 59
def prefixEnd_1111780 : Nat := 4983230072969 + 3 ^ 40 * 1111780 * 2
def baseEnd_1111780 : Nat := 570877522055765389337023

theorem tailTrace_1111780 : CollatzResearch.WordTrace tailWord_1111780 prefixEnd_1111780 570877522055765389337023 := by
  unfold tailWord_1111780
  simp only [CollatzResearch.WordTrace]
  refine ⟨20274973956109205876118397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27033298608145607834824529 20274973956109205876118397)
  ·
    refine ⟨7603115233540952203544399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20274973956109205876118397 7603115233540952203544399)
    ·
      refine ⟨11404672850311428305316599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7603115233540952203544399 11404672850311428305316599)
      ·
        refine ⟨17107009275467142457974899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11404672850311428305316599 17107009275467142457974899)
        ·
          refine ⟨25660513913200713686962349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17107009275467142457974899 25660513913200713686962349)
          ·
            refine ⟨9622692717450267632610881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25660513913200713686962349 9622692717450267632610881)
            ·
              refine ⟨7217019538087700724458161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9622692717450267632610881 7217019538087700724458161)
              ·
                refine ⟨5412764653565775543343621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7217019538087700724458161 5412764653565775543343621)
                ·
                  refine ⟨1014893372543582914376929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5412764653565775543343621 1014893372543582914376929)
                  ·
                    refine ⟨761170029407687185782697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1014893372543582914376929 761170029407687185782697)
                    ·
                      refine ⟨570877522055765389337023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 761170029407687185782697 570877522055765389337023)
                      ·
                        rfl

theorem cell23_1111780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 2, 4, 2, 2].length) (baseStart_1111780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1111780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1111780 prefixEnd_1111780 := by exact prefixLift 1111780
  have htrace : WordTrace (prefixWord ++ tailWord_1111780) baseStart_1111780 baseEnd_1111780 := by
    simpa [prefixWord, tailWord_1111780, baseEnd_1111780] using wordTrace_append hprefix tailTrace_1111780
  have hstable : (prefixWord ++ tailWord_1111780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1111780).length < 2 ^ (prefixWord ++ tailWord_1111780).sum := by decide
  have hdescent : baseEnd_1111780 < baseStart_1111780 := by decide
  rcases family_descends (prefixWord ++ tailWord_1111780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1111784 : List Nat := [2, 1, 4, 1, 3, 3, 2, 1, 1, 3, 2]
def baseStart_1111784 : Nat := 118140960795 + 1111784 * 2 ^ 59
def prefixEnd_1111784 : Nat := 4983230072969 + 3 ^ 40 * 1111784 * 2
def baseEnd_1111784 : Nat := 570879575978383373687005

theorem tailTrace_1111784 : CollatzResearch.WordTrace tailWord_1111784 prefixEnd_1111784 570879575978383373687005 := by
  unfold tailWord_1111784
  simp only [CollatzResearch.WordTrace]
  refine ⟨20275046902101960217691203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27033395869469280290254937 20275046902101960217691203)
  ·
    refine ⟨30412570353152940326536805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20275046902101960217691203 30412570353152940326536805)
    ·
      refine ⟨5702356941216176311225651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30412570353152940326536805 5702356941216176311225651)
      ·
        refine ⟨8553535411824264466838477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5702356941216176311225651 8553535411824264466838477)
        ·
          refine ⟨3207575779434099175064429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8553535411824264466838477 3207575779434099175064429)
          ·
            refine ⟨1202840917287787190649161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3207575779434099175064429 1202840917287787190649161)
            ·
              refine ⟨902130687965840392986871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1202840917287787190649161 902130687965840392986871)
              ·
                refine ⟨1353196031948760589480307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 902130687965840392986871 1353196031948760589480307)
                ·
                  refine ⟨2029794047923140884220461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1353196031948760589480307 2029794047923140884220461)
                  ·
                    refine ⟨761172767971177831582673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2029794047923140884220461 761172767971177831582673)
                    ·
                      refine ⟨570879575978383373687005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 761172767971177831582673 570879575978383373687005)
                      ·
                        rfl

theorem cell23_1111784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 3, 2, 1, 1, 3, 2].length) (baseStart_1111784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1111784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1111784 prefixEnd_1111784 := by exact prefixLift 1111784
  have htrace : WordTrace (prefixWord ++ tailWord_1111784) baseStart_1111784 baseEnd_1111784 := by
    simpa [prefixWord, tailWord_1111784, baseEnd_1111784] using wordTrace_append hprefix tailTrace_1111784
  have hstable : (prefixWord ++ tailWord_1111784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1111784).length < 2 ^ (prefixWord ++ tailWord_1111784).sum := by decide
  have hdescent : baseEnd_1111784 < baseStart_1111784 := by decide
  rcases family_descends (prefixWord ++ tailWord_1111784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1111816 : List Nat := [2, 1, 3, 2, 2, 1, 1, 1, 3, 7]
def baseStart_1111816 : Nat := 118140960795 + 1111816 * 2 ^ 59
def prefixEnd_1111816 : Nat := 4983230072969 + 3 ^ 40 * 1111816 * 2
def baseEnd_1111816 : Nat := 190298669119775749495619

theorem tailTrace_1111816 : CollatzResearch.WordTrace tailWord_1111816 prefixEnd_1111816 190298669119775749495619 := by
  unfold tailWord_1111816
  simp only [CollatzResearch.WordTrace]
  refine ⟨20275630470043994950273651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27034173960058659933698201 20275630470043994950273651)
  ·
    refine ⟨30413445705065992425410477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20275630470043994950273651 30413445705065992425410477)
    ·
      refine ⟨11405042139399747159528929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30413445705065992425410477 11405042139399747159528929)
      ·
        refine ⟨8553781604549810369646697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11405042139399747159528929 8553781604549810369646697)
        ·
          refine ⟨6415336203412357777235023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8553781604549810369646697 6415336203412357777235023)
          ·
            refine ⟨9623004305118536665852535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6415336203412357777235023 9623004305118536665852535)
            ·
              refine ⟨14434506457677804998778803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9623004305118536665852535 14434506457677804998778803)
              ·
                refine ⟨21651759686516707498168205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14434506457677804998778803 21651759686516707498168205)
                ·
                  refine ⟨8119409882443765311813077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21651759686516707498168205 8119409882443765311813077)
                  ·
                    refine ⟨190298669119775749495619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 8119409882443765311813077 190298669119775749495619)
                    ·
                      rfl

theorem cell23_1111816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 1, 3, 7].length) (baseStart_1111816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1111816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1111816 prefixEnd_1111816 := by exact prefixLift 1111816
  have htrace : WordTrace (prefixWord ++ tailWord_1111816) baseStart_1111816 baseEnd_1111816 := by
    simpa [prefixWord, tailWord_1111816, baseEnd_1111816] using wordTrace_append hprefix tailTrace_1111816
  have hstable : (prefixWord ++ tailWord_1111816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1111816).length < 2 ^ (prefixWord ++ tailWord_1111816).sum := by decide
  have hdescent : baseEnd_1111816 < baseStart_1111816 := by decide
  rcases family_descends (prefixWord ++ tailWord_1111816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1111854 : List Nat := [4, 1, 3, 2, 2, 1, 3, 2, 5]
def baseStart_1111854 : Nat := 118140960795 + 1111854 * 2 ^ 59
def prefixEnd_1111854 : Nat := 4983230072969 + 3 ^ 40 * 1111854 * 2
def baseEnd_1111854 : Nat := 63435057736022011090187

theorem tailTrace_1111854 : CollatzResearch.WordTrace tailWord_1111854 prefixEnd_1111854 63435057736022011090187 := by
  unfold tailWord_1111854
  simp only [CollatzResearch.WordTrace]
  refine ⟨5069080864243790298803827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27035097942633548260287077 5069080864243790298803827)
  ·
    refine ⟨7603621296365685448205741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5069080864243790298803827 7603621296365685448205741)
    ·
      refine ⟨2851357986137132043077153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7603621296365685448205741 2851357986137132043077153)
      ·
        refine ⟨2138518489602849032307865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2851357986137132043077153 2138518489602849032307865)
        ·
          refine ⟨1603888867202136774230899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2138518489602849032307865 1603888867202136774230899)
          ·
            refine ⟨2405833300803205161346349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1603888867202136774230899 2405833300803205161346349)
            ·
              refine ⟨902187487801201935504881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2405833300803205161346349 902187487801201935504881)
              ·
                refine ⟨676640615850901451628661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 902187487801201935504881 676640615850901451628661)
                ·
                  refine ⟨63435057736022011090187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 676640615850901451628661 63435057736022011090187)
                  ·
                    rfl

theorem cell23_1111854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 3, 2, 5].length) (baseStart_1111854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1111854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1111854 prefixEnd_1111854 := by exact prefixLift 1111854
  have htrace : WordTrace (prefixWord ++ tailWord_1111854) baseStart_1111854 baseEnd_1111854 := by
    simpa [prefixWord, tailWord_1111854, baseEnd_1111854] using wordTrace_append hprefix tailTrace_1111854
  have hstable : (prefixWord ++ tailWord_1111854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1111854).length < 2 ^ (prefixWord ++ tailWord_1111854).sum := by decide
  have hdescent : baseEnd_1111854 < baseStart_1111854 := by decide
  rcases family_descends (prefixWord ++ tailWord_1111854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1111860 : List Nat := [2, 5, 1, 1, 2, 2, 1, 1, 1, 2, 5]
def baseStart_1111860 : Nat := 118140960795 + 1111860 * 2 ^ 59
def prefixEnd_1111860 : Nat := 4983230072969 + 3 ^ 40 * 1111860 * 2
def baseEnd_1111860 : Nat := 570918600508125076336655

theorem tailTrace_1111860 : CollatzResearch.WordTrace tailWord_1111860 prefixEnd_1111860 570918600508125076336655 := by
  unfold tailWord_1111860
  simp only [CollatzResearch.WordTrace]
  refine ⟨20276432875964292707574517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27035243834619056943432689 20276432875964292707574517)
  ·
    refine ⟨1900915582121652441335111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 20276432875964292707574517 1900915582121652441335111)
    ·
      refine ⟨2851373373182478662002667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1900915582121652441335111 2851373373182478662002667)
      ·
        refine ⟨4277060059773717993004001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2851373373182478662002667 4277060059773717993004001)
        ·
          refine ⟨3207795044830288494753001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4277060059773717993004001 3207795044830288494753001)
          ·
            refine ⟨2405846283622716371064751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3207795044830288494753001 2405846283622716371064751)
            ·
              refine ⟨3608769425434074556597127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2405846283622716371064751 3608769425434074556597127)
              ·
                refine ⟨5413154138151111834895691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3608769425434074556597127 5413154138151111834895691)
                ·
                  refine ⟨8119731207226667752343537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5413154138151111834895691 8119731207226667752343537)
                  ·
                    refine ⟨6089798405420000814257653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8119731207226667752343537 6089798405420000814257653)
                    ·
                      refine ⟨570918600508125076336655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6089798405420000814257653 570918600508125076336655)
                      ·
                        rfl

theorem cell23_1111860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 1, 1, 1, 2, 5].length) (baseStart_1111860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1111860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1111860 prefixEnd_1111860 := by exact prefixLift 1111860
  have htrace : WordTrace (prefixWord ++ tailWord_1111860) baseStart_1111860 baseEnd_1111860 := by
    simpa [prefixWord, tailWord_1111860, baseEnd_1111860] using wordTrace_append hprefix tailTrace_1111860
  have hstable : (prefixWord ++ tailWord_1111860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1111860).length < 2 ^ (prefixWord ++ tailWord_1111860).sum := by decide
  have hdescent : baseEnd_1111860 < baseStart_1111860 := by decide
  rcases family_descends (prefixWord ++ tailWord_1111860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1111863 : List Nat := [1, 1, 3, 1, 2, 1, 2, 5, 3, 4]
def baseStart_1111863 : Nat := 118140960795 + 1111863 * 2 ^ 59
def prefixEnd_1111863 : Nat := 4983230072969 + 3 ^ 40 * 1111863 * 2
def baseEnd_1111863 : Nat := 190306713650029521533047

theorem tailTrace_1111863 : CollatzResearch.WordTrace tailWord_1111863 prefixEnd_1111863 190306713650029521533047 := by
  unfold tailWord_1111863
  simp only [CollatzResearch.WordTrace]
  refine ⟨40552975170917716927508243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27035316780611811285005495 40552975170917716927508243)
  ·
    refine ⟨60829462756376575391262365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40552975170917716927508243 60829462756376575391262365)
    ·
      refine ⟨22811048533641215771723387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60829462756376575391262365 22811048533641215771723387)
      ·
        refine ⟨34216572800461823657585081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22811048533641215771723387 34216572800461823657585081)
        ·
          refine ⟨25662429600346367743188811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34216572800461823657585081 25662429600346367743188811)
          ·
            refine ⟨38493644400519551614783217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25662429600346367743188811 38493644400519551614783217)
            ·
              refine ⟨28870233300389663711087413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38493644400519551614783217 28870233300389663711087413)
              ·
                refine ⟨2706584371911530972914445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 28870233300389663711087413 2706584371911530972914445)
                ·
                  refine ⟨1014969139466824114842917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2706584371911530972914445 1014969139466824114842917)
                  ·
                    refine ⟨190306713650029521533047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1014969139466824114842917 190306713650029521533047)
                    ·
                      rfl

theorem cell23_1111863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 5, 3, 4].length) (baseStart_1111863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1111863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1111863 prefixEnd_1111863 := by exact prefixLift 1111863
  have htrace : WordTrace (prefixWord ++ tailWord_1111863) baseStart_1111863 baseEnd_1111863 := by
    simpa [prefixWord, tailWord_1111863, baseEnd_1111863] using wordTrace_append hprefix tailTrace_1111863
  have hstable : (prefixWord ++ tailWord_1111863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1111863).length < 2 ^ (prefixWord ++ tailWord_1111863).sum := by decide
  have hdescent : baseEnd_1111863 < baseStart_1111863 := by decide
  rcases family_descends (prefixWord ++ tailWord_1111863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1111890 : List Nat := [3, 2, 2, 1, 1, 3, 1, 3, 2, 2, 3]
def baseStart_1111890 : Nat := 118140960795 + 1111890 * 2 ^ 59
def prefixEnd_1111890 : Nat := 4983230072969 + 3 ^ 40 * 1111890 * 2
def baseEnd_1111890 : Nat := 570934004927759958961517

theorem tailTrace_1111890 : CollatzResearch.WordTrace tailWord_1111890 prefixEnd_1111890 570934004927759958961517 := by
  unfold tailWord_1111890
  simp only [CollatzResearch.WordTrace]
  refine ⟨10138489985454975134685281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27035973294546600359160749 10138489985454975134685281)
  ·
    refine ⟨7603867489091231351013961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10138489985454975134685281 7603867489091231351013961)
    ·
      refine ⟨5702900616818423513260471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7603867489091231351013961 5702900616818423513260471)
      ·
        refine ⟨8554350925227635269890707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5702900616818423513260471 8554350925227635269890707)
        ·
          refine ⟨12831526387841452904836061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8554350925227635269890707 12831526387841452904836061)
          ·
            refine ⟨4811822395440544839313523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12831526387841452904836061 4811822395440544839313523)
            ·
              refine ⟨7217733593160817258970285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4811822395440544839313523 7217733593160817258970285)
              ·
                refine ⟨2706650097435306472113857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7217733593160817258970285 2706650097435306472113857)
                ·
                  refine ⟨2029987573076479854085393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2706650097435306472113857 2029987573076479854085393)
                  ·
                    refine ⟨1522490679807359890564045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2029987573076479854085393 1522490679807359890564045)
                    ·
                      refine ⟨570934004927759958961517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1522490679807359890564045 570934004927759958961517)
                      ·
                        rfl

theorem cell23_1111890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 3, 2, 2, 3].length) (baseStart_1111890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1111890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1111890 prefixEnd_1111890 := by exact prefixLift 1111890
  have htrace : WordTrace (prefixWord ++ tailWord_1111890) baseStart_1111890 baseEnd_1111890 := by
    simpa [prefixWord, tailWord_1111890, baseEnd_1111890] using wordTrace_append hprefix tailTrace_1111890
  have hstable : (prefixWord ++ tailWord_1111890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1111890).length < 2 ^ (prefixWord ++ tailWord_1111890).sum := by decide
  have hdescent : baseEnd_1111890 < baseStart_1111890 := by decide
  rcases family_descends (prefixWord ++ tailWord_1111890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1111896 : List Nat := [2, 1, 2, 2, 1, 1, 1, 1, 3, 1, 8]
def baseStart_1111896 : Nat := 118140960795 + 1111896 * 2 ^ 59
def prefixEnd_1111896 : Nat := 4983230072969 + 3 ^ 40 * 1111896 * 2
def baseEnd_1111896 : Nat := 570937085811686935486489

theorem tailTrace_1111896 : CollatzResearch.WordTrace tailWord_1111896 prefixEnd_1111896 570937085811686935486489 := by
  unfold tailWord_1111896
  simp only [CollatzResearch.WordTrace]
  refine ⟨20277089389899081781729771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27036119186532109042306361 20277089389899081781729771)
  ·
    refine ⟨30415634084848622672594657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20277089389899081781729771 30415634084848622672594657)
    ·
      refine ⟨22811725563636467004445993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30415634084848622672594657 22811725563636467004445993)
      ·
        refine ⟨17108794172727350253334495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22811725563636467004445993 17108794172727350253334495)
        ·
          refine ⟨25663191259091025380001743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17108794172727350253334495 25663191259091025380001743)
          ·
            refine ⟨38494786888636538070002615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25663191259091025380001743 38494786888636538070002615)
            ·
              refine ⟨57742180332954807105003923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38494786888636538070002615 57742180332954807105003923)
              ·
                refine ⟨86613270499432210657505885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57742180332954807105003923 86613270499432210657505885)
                ·
                  refine ⟨32479976437287078996564707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 86613270499432210657505885 32479976437287078996564707)
                  ·
                    refine ⟨48719964655930618494847061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 32479976437287078996564707 48719964655930618494847061)
                    ·
                      refine ⟨570937085811686935486489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 48719964655930618494847061 570937085811686935486489)
                      ·
                        rfl

theorem cell23_1111896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 3, 1, 8].length) (baseStart_1111896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1111896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1111896 prefixEnd_1111896 := by exact prefixLift 1111896
  have htrace : WordTrace (prefixWord ++ tailWord_1111896) baseStart_1111896 baseEnd_1111896 := by
    simpa [prefixWord, tailWord_1111896, baseEnd_1111896] using wordTrace_append hprefix tailTrace_1111896
  have hstable : (prefixWord ++ tailWord_1111896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1111896).length < 2 ^ (prefixWord ++ tailWord_1111896).sum := by decide
  have hdescent : baseEnd_1111896 < baseStart_1111896 := by decide
  rcases family_descends (prefixWord ++ tailWord_1111896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1111920 : List Nat := [2, 1, 1, 1, 4, 1, 1, 5, 3, 1, 3]
def baseStart_1111920 : Nat := 118140960795 + 1111920 * 2 ^ 59
def prefixEnd_1111920 : Nat := 4983230072969 + 3 ^ 40 * 1111920 * 2
def baseEnd_1111920 : Nat := 570949409347394841586379

theorem tailTrace_1111920 : CollatzResearch.WordTrace tailWord_1111920 prefixEnd_1111920 570949409347394841586379 := by
  unfold tailWord_1111920
  simp only [CollatzResearch.WordTrace]
  refine ⟨20277527065855607831166607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27036702754474143774888809 20277527065855607831166607)
  ·
    refine ⟨30416290598783411746749911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20277527065855607831166607 30416290598783411746749911)
    ·
      refine ⟨45624435898175117620124867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30416290598783411746749911 45624435898175117620124867)
      ·
        refine ⟨68436653847262676430187301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45624435898175117620124867 68436653847262676430187301)
        ·
          refine ⟨12831872596361751830660119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 68436653847262676430187301 12831872596361751830660119)
          ·
            refine ⟨19247808894542627745990179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12831872596361751830660119 19247808894542627745990179)
            ·
              refine ⟨28871713341813941618985269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19247808894542627745990179 28871713341813941618985269)
              ·
                refine ⟨2706723125795057026779869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 28871713341813941618985269 2706723125795057026779869)
                ·
                  refine ⟨1015021172173146385042451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2706723125795057026779869 1015021172173146385042451)
                  ·
                    refine ⟨1522531758259719577563677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1015021172173146385042451 1522531758259719577563677)
                    ·
                      refine ⟨570949409347394841586379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1522531758259719577563677 570949409347394841586379)
                      ·
                        rfl

theorem cell23_1111920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 5, 3, 1, 3].length) (baseStart_1111920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1111920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1111920 prefixEnd_1111920 := by exact prefixLift 1111920
  have htrace : WordTrace (prefixWord ++ tailWord_1111920) baseStart_1111920 baseEnd_1111920 := by
    simpa [prefixWord, tailWord_1111920, baseEnd_1111920] using wordTrace_append hprefix tailTrace_1111920
  have hstable : (prefixWord ++ tailWord_1111920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1111920).length < 2 ^ (prefixWord ++ tailWord_1111920).sum := by decide
  have hdescent : baseEnd_1111920 < baseStart_1111920 := by decide
  rcases family_descends (prefixWord ++ tailWord_1111920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1111930 : List Nat := [3, 1, 1, 1, 1, 1, 4, 2, 4, 3, 2]
def baseStart_1111930 : Nat := 118140960795 + 1111930 * 2 ^ 59
def prefixEnd_1111930 : Nat := 4983230072969 + 3 ^ 40 * 1111930 * 2
def baseEnd_1111930 : Nat := 570954544153939802461333

theorem tailTrace_1111930 : CollatzResearch.WordTrace tailWord_1111930 prefixEnd_1111930 570954544153939802461333 := by
  unfold tailWord_1111930
  simp only [CollatzResearch.WordTrace]
  refine ⟨10138854715418746842549311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27036945907783324913464829 10138854715418746842549311)
  ·
    refine ⟨15208282073128120263823967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10138854715418746842549311 15208282073128120263823967)
    ·
      refine ⟨22812423109692180395735951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15208282073128120263823967 22812423109692180395735951)
      ·
        refine ⟨34218634664538270593603927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22812423109692180395735951 34218634664538270593603927)
        ·
          refine ⟨51327951996807405890405891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34218634664538270593603927 51327951996807405890405891)
          ·
            refine ⟨76991927995211108835608837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51327951996807405890405891 76991927995211108835608837)
            ·
              refine ⟨14435986499102082906676657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 76991927995211108835608837 14435986499102082906676657)
              ·
                refine ⟨10826989874326562180007493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14435986499102082906676657 10826989874326562180007493)
                ·
                  refine ⟨2030060601436230408751405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10826989874326562180007493 2030060601436230408751405)
                  ·
                    refine ⟨761272725538586403281777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2030060601436230408751405 761272725538586403281777)
                    ·
                      refine ⟨570954544153939802461333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 761272725538586403281777 570954544153939802461333)
                      ·
                        rfl

theorem cell23_1111930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 2, 4, 3, 2].length) (baseStart_1111930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1111930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1111930 prefixEnd_1111930 := by exact prefixLift 1111930
  have htrace : WordTrace (prefixWord ++ tailWord_1111930) baseStart_1111930 baseEnd_1111930 := by
    simpa [prefixWord, tailWord_1111930, baseEnd_1111930] using wordTrace_append hprefix tailTrace_1111930
  have hstable : (prefixWord ++ tailWord_1111930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1111930).length < 2 ^ (prefixWord ++ tailWord_1111930).sum := by decide
  have hdescent : baseEnd_1111930 < baseStart_1111930 := by decide
  rcases family_descends (prefixWord ++ tailWord_1111930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1111953 : List Nat := [1, 2, 2, 1, 1, 1, 6, 2, 1, 6]
def baseStart_1111953 : Nat := 118140960795 + 1111953 * 2 ^ 59
def prefixEnd_1111953 : Nat := 4983230072969 + 3 ^ 40 * 1111953 * 2
def baseEnd_1111953 : Nat := 190322118069664404157909

theorem tailTrace_1111953 : CollatzResearch.WordTrace tailWord_1111953 prefixEnd_1111953 190322118069664404157909 := by
  unfold tailWord_1111953
  simp only [CollatzResearch.WordTrace]
  refine ⟨40556257740591662298284513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27037505160394441532189675 40556257740591662298284513)
  ·
    refine ⟨30417193305443746723713385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40556257740591662298284513 30417193305443746723713385)
    ·
      refine ⟨22812894979082810042785039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30417193305443746723713385 22812894979082810042785039)
      ·
        refine ⟨34219342468624215064177559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22812894979082810042785039 34219342468624215064177559)
        ·
          refine ⟨51329013702936322596266339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34219342468624215064177559 51329013702936322596266339)
          ·
            refine ⟨76993520554404483894399509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51329013702936322596266339 76993520554404483894399509)
            ·
              refine ⟨3609071275987710182549977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 76993520554404483894399509 3609071275987710182549977)
              ·
                refine ⟨2706803456990782636912483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3609071275987710182549977 2706803456990782636912483)
                ·
                  refine ⟨4060205185486173955368725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2706803456990782636912483 4060205185486173955368725)
                  ·
                    refine ⟨190322118069664404157909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4060205185486173955368725 190322118069664404157909)
                    ·
                      rfl

theorem cell23_1111953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 6].length) (baseStart_1111953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1111953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1111953 prefixEnd_1111953 := by exact prefixLift 1111953
  have htrace : WordTrace (prefixWord ++ tailWord_1111953) baseStart_1111953 baseEnd_1111953 := by
    simpa [prefixWord, tailWord_1111953, baseEnd_1111953] using wordTrace_append hprefix tailTrace_1111953
  have hstable : (prefixWord ++ tailWord_1111953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1111953).length < 2 ^ (prefixWord ++ tailWord_1111953).sum := by decide
  have hdescent : baseEnd_1111953 < baseStart_1111953 := by decide
  rcases family_descends (prefixWord ++ tailWord_1111953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1111973 : List Nat := [1, 3, 1, 2, 1, 1, 1, 4, 3, 2, 4]
def baseStart_1111973 : Nat := 118140960795 + 1111973 * 2 ^ 59
def prefixEnd_1111973 : Nat := 4983230072969 + 3 ^ 40 * 1111973 * 2
def baseEnd_1111973 : Nat := 570976623822083134223635

theorem tailTrace_1111973 : CollatzResearch.WordTrace tailWord_1111973 prefixEnd_1111973 570976623822083134223635 := by
  unfold tailWord_1111973
  simp only [CollatzResearch.WordTrace]
  refine ⟨40556987200519205714012573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27037991467012803809341715 40556987200519205714012573)
  ·
    refine ⟨15208870200194702142754715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40556987200519205714012573 15208870200194702142754715)
    ·
      refine ⟨22813305300292053214132073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15208870200194702142754715 22813305300292053214132073)
      ·
        refine ⟨17109978975219039910599055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22813305300292053214132073 17109978975219039910599055)
        ·
          refine ⟨25664968462828559865898583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17109978975219039910599055 25664968462828559865898583)
          ·
            refine ⟨38497452694242839798847875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25664968462828559865898583 38497452694242839798847875)
            ·
              refine ⟨57746179041364259698271813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38497452694242839798847875 57746179041364259698271813)
              ·
                refine ⟨10827408570255798693425965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 57746179041364259698271813 10827408570255798693425965)
                ·
                  refine ⟨4060278213845924510034737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10827408570255798693425965 4060278213845924510034737)
                  ·
                    refine ⟨3045208660384443382526053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4060278213845924510034737 3045208660384443382526053)
                    ·
                      refine ⟨570976623822083134223635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3045208660384443382526053 570976623822083134223635)
                      ·
                        rfl

theorem cell23_1111973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 4, 3, 2, 4].length) (baseStart_1111973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1111973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1111973 prefixEnd_1111973 := by exact prefixLift 1111973
  have htrace : WordTrace (prefixWord ++ tailWord_1111973) baseStart_1111973 baseEnd_1111973 := by
    simpa [prefixWord, tailWord_1111973, baseEnd_1111973] using wordTrace_append hprefix tailTrace_1111973
  have hstable : (prefixWord ++ tailWord_1111973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1111973).length < 2 ^ (prefixWord ++ tailWord_1111973).sum := by decide
  have hdescent : baseEnd_1111973 < baseStart_1111973 := by decide
  rcases family_descends (prefixWord ++ tailWord_1111973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1111987 : List Nat := [1, 1, 1, 2, 3, 1, 7, 1, 2, 4]
def baseStart_1111987 : Nat := 118140960795 + 1111987 * 2 ^ 59
def prefixEnd_1111987 : Nat := 4983230072969 + 3 ^ 40 * 1111987 * 2
def baseEnd_1111987 : Nat := 190327937517082026482857

theorem tailTrace_1111987 : CollatzResearch.WordTrace tailWord_1111987 prefixEnd_1111987 190327937517082026482857 := by
  unfold tailWord_1111987
  simp only [CollatzResearch.WordTrace]
  refine ⟨40557497822468486105022215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27038331881645657403348143 40557497822468486105022215)
  ·
    refine ⟨60836246733702729157533323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40557497822468486105022215 60836246733702729157533323)
    ·
      refine ⟨91254370100554093736299985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60836246733702729157533323 91254370100554093736299985)
      ·
        refine ⟨68440777575415570302224989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91254370100554093736299985 68440777575415570302224989)
        ·
          refine ⟨25665291590780838863334371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 68440777575415570302224989 25665291590780838863334371)
          ·
            refine ⟨38497937386171258295001557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25665291590780838863334371 38497937386171258295001557)
            ·
              refine ⟨902295407488388866289099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 38497937386171258295001557 902295407488388866289099)
              ·
                refine ⟨1353443111232583299433649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 902295407488388866289099 1353443111232583299433649)
                ·
                  refine ⟨1015082333424437474575237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1353443111232583299433649 1015082333424437474575237)
                  ·
                    refine ⟨190327937517082026482857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1015082333424437474575237 190327937517082026482857)
                    ·
                      rfl

theorem cell23_1111987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 7, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 7, 1, 2, 4].length) (baseStart_1111987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1111987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1111987 prefixEnd_1111987 := by exact prefixLift 1111987
  have htrace : WordTrace (prefixWord ++ tailWord_1111987) baseStart_1111987 baseEnd_1111987 := by
    simpa [prefixWord, tailWord_1111987, baseEnd_1111987] using wordTrace_append hprefix tailTrace_1111987
  have hstable : (prefixWord ++ tailWord_1111987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1111987).length < 2 ^ (prefixWord ++ tailWord_1111987).sum := by decide
  have hdescent : baseEnd_1111987 < baseStart_1111987 := by decide
  rcases family_descends (prefixWord ++ tailWord_1111987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1111997 : List Nat := [1, 4, 1, 2, 3, 1, 1, 4, 1, 2, 3]
def baseStart_1111997 : Nat := 118140960795 + 1111997 * 2 ^ 59
def prefixEnd_1111997 : Nat := 4983230072969 + 3 ^ 40 * 1111997 * 2
def baseEnd_1111997 : Nat := 570988947357791040323525

theorem tailTrace_1111997 : CollatzResearch.WordTrace tailWord_1111997 prefixEnd_1111997 570988947357791040323525 := by
  unfold tailWord_1111997
  simp only [CollatzResearch.WordTrace]
  refine ⟨40557862552432257812886245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27038575034954838541924163 40557862552432257812886245)
  ·
    refine ⟨7604599228581048339916171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 40557862552432257812886245 7604599228581048339916171)
    ·
      refine ⟨11406898842871572509874257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7604599228581048339916171 11406898842871572509874257)
      ·
        refine ⟨8555174132153679382405693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11406898842871572509874257 8555174132153679382405693)
        ·
          refine ⟨3208190299557629768402135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8555174132153679382405693 3208190299557629768402135)
          ·
            refine ⟨4812285449336444652603203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3208190299557629768402135 4812285449336444652603203)
            ·
              refine ⟨7218428174004666978904805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4812285449336444652603203 7218428174004666978904805)
              ·
                refine ⟨1353455282625875058544651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7218428174004666978904805 1353455282625875058544651)
                ·
                  refine ⟨2030182923938812587816977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1353455282625875058544651 2030182923938812587816977)
                  ·
                    refine ⟨1522637192954109440862733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2030182923938812587816977 1522637192954109440862733)
                    ·
                      refine ⟨570988947357791040323525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1522637192954109440862733 570988947357791040323525)
                      ·
                        rfl

theorem cell23_1111997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 4, 1, 2, 3].length) (baseStart_1111997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1111997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1111997 prefixEnd_1111997 := by exact prefixLift 1111997
  have htrace : WordTrace (prefixWord ++ tailWord_1111997) baseStart_1111997 baseEnd_1111997 := by
    simpa [prefixWord, tailWord_1111997, baseEnd_1111997] using wordTrace_append hprefix tailTrace_1111997
  have hstable : (prefixWord ++ tailWord_1111997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1111997).length < 2 ^ (prefixWord ++ tailWord_1111997).sum := by decide
  have hdescent : baseEnd_1111997 < baseStart_1111997 := by decide
  rcases family_descends (prefixWord ++ tailWord_1111997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1112010 : List Nat := [3, 1, 2, 1, 2, 1, 2, 4, 1, 3, 3]
def baseStart_1112010 : Nat := 118140960795 + 1112010 * 2 ^ 59
def prefixEnd_1112010 : Nat := 4983230072969 + 3 ^ 40 * 1112010 * 2
def baseEnd_1112010 : Nat := 570995622606299489460965

theorem tailTrace_1112010 : CollatzResearch.WordTrace tailWord_1112010 prefixEnd_1112010 570995622606299489460965 := by
  unfold tailWord_1112010
  simp only [CollatzResearch.WordTrace]
  refine ⟨10139584175346290258277371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27038891134256774022072989 10139584175346290258277371)
  ·
    refine ⟨15209376263019435387416057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10139584175346290258277371 15209376263019435387416057)
    ·
      refine ⟨11407032197264576540562043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15209376263019435387416057 11407032197264576540562043)
      ·
        refine ⟨17110548295896864810843065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11407032197264576540562043 17110548295896864810843065)
        ·
          refine ⟨12832911221922648608132299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17110548295896864810843065 12832911221922648608132299)
          ·
            refine ⟨19249366832883972912198449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12832911221922648608132299 19249366832883972912198449)
            ·
              refine ⟨14437025124662979684148837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19249366832883972912198449 14437025124662979684148837)
              ·
                refine ⟨2706942210874308690777907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14437025124662979684148837 2706942210874308690777907)
                ·
                  refine ⟨4060413316311463036166861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2706942210874308690777907 4060413316311463036166861)
                  ·
                    refine ⟨1522654993616798638562573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4060413316311463036166861 1522654993616798638562573)
                    ·
                      refine ⟨570995622606299489460965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1522654993616798638562573 570995622606299489460965)
                      ·
                        rfl

theorem cell23_1112010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 4, 1, 3, 3].length) (baseStart_1112010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1112010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1112010 prefixEnd_1112010 := by exact prefixLift 1112010
  have htrace : WordTrace (prefixWord ++ tailWord_1112010) baseStart_1112010 baseEnd_1112010 := by
    simpa [prefixWord, tailWord_1112010, baseEnd_1112010] using wordTrace_append hprefix tailTrace_1112010
  have hstable : (prefixWord ++ tailWord_1112010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1112010).length < 2 ^ (prefixWord ++ tailWord_1112010).sum := by decide
  have hdescent : baseEnd_1112010 < baseStart_1112010 := by decide
  rcases family_descends (prefixWord ++ tailWord_1112010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1112023 : List Nat := [1, 1, 3, 2, 1, 1, 3, 2, 2, 2, 5]
def baseStart_1112023 : Nat := 118140960795 + 1112023 * 2 ^ 59
def prefixEnd_1112023 : Nat := 4983230072969 + 3 ^ 40 * 1112023 * 2
def baseEnd_1112023 : Nat := 571002297854807938598405

theorem tailTrace_1112023 : CollatzResearch.WordTrace tailWord_1112023 prefixEnd_1112023 571002297854807938598405 := by
  unfold tailWord_1112023
  simp only [CollatzResearch.WordTrace]
  refine ⟨40558810850338064253332723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27039207233558709502221815 40558810850338064253332723)
  ·
    refine ⟨60838216275507096379999085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40558810850338064253332723 60838216275507096379999085)
    ·
      refine ⟨22814331103315161142499657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60838216275507096379999085 22814331103315161142499657)
      ·
        refine ⟨17110748327486370856874743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22814331103315161142499657 17110748327486370856874743)
        ·
          refine ⟨25666122491229556285312115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17110748327486370856874743 25666122491229556285312115)
          ·
            refine ⟨38499183736844334427968173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25666122491229556285312115 38499183736844334427968173)
            ·
              refine ⟨14437193901316625410488065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38499183736844334427968173 14437193901316625410488065)
              ·
                refine ⟨10827895425987469057866049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14437193901316625410488065 10827895425987469057866049)
                ·
                  refine ⟨8120921569490601793399537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10827895425987469057866049 8120921569490601793399537)
                  ·
                    refine ⟨6090691177117951345049653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8120921569490601793399537 6090691177117951345049653)
                    ·
                      refine ⟨571002297854807938598405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6090691177117951345049653 571002297854807938598405)
                      ·
                        rfl

theorem cell23_1112023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 2, 2, 2, 5].length) (baseStart_1112023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1112023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1112023 prefixEnd_1112023 := by exact prefixLift 1112023
  have htrace : WordTrace (prefixWord ++ tailWord_1112023) baseStart_1112023 baseEnd_1112023 := by
    simpa [prefixWord, tailWord_1112023, baseEnd_1112023] using wordTrace_append hprefix tailTrace_1112023
  have hstable : (prefixWord ++ tailWord_1112023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1112023).length < 2 ^ (prefixWord ++ tailWord_1112023).sum := by decide
  have hdescent : baseEnd_1112023 < baseStart_1112023 := by decide
  rcases family_descends (prefixWord ++ tailWord_1112023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1112043 : List Nat := [1, 1, 1, 1, 2, 3, 1, 5, 2, 6]
def baseStart_1112043 : Nat := 118140960795 + 1112043 * 2 ^ 59
def prefixEnd_1112043 : Nat := 4983230072969 + 3 ^ 40 * 1112043 * 2
def baseEnd_1112043 : Nat := 190337522489299286782771

theorem tailTrace_1112043 : CollatzResearch.WordTrace tailWord_1112043 prefixEnd_1112043 190337522489299286782771 := by
  unfold tailWord_1112043
  simp only [CollatzResearch.WordTrace]
  refine ⟨40559540310265607669060783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27039693540177071779373855 40559540310265607669060783)
  ·
    refine ⟨60839310465398411503591175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40559540310265607669060783 60839310465398411503591175)
    ·
      refine ⟨91258965698097617255386763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60839310465398411503591175 91258965698097617255386763)
      ·
        refine ⟨136888448547146425883080145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91258965698097617255386763 136888448547146425883080145)
        ·
          refine ⟨102666336410359819412310109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 136888448547146425883080145 102666336410359819412310109)
          ·
            refine ⟨38499876153884932279616291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 102666336410359819412310109 38499876153884932279616291)
            ·
              refine ⟨57749814230827398419424437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38499876153884932279616291 57749814230827398419424437)
              ·
                refine ⟨5414045084140068601821041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 57749814230827398419424437 5414045084140068601821041)
                ·
                  refine ⟨4060533813105051451365781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5414045084140068601821041 4060533813105051451365781)
                  ·
                    refine ⟨190337522489299286782771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4060533813105051451365781 190337522489299286782771)
                    ·
                      rfl

theorem cell23_1112043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 5, 2, 6].length) (baseStart_1112043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1112043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1112043 prefixEnd_1112043 := by exact prefixLift 1112043
  have htrace : WordTrace (prefixWord ++ tailWord_1112043) baseStart_1112043 baseEnd_1112043 := by
    simpa [prefixWord, tailWord_1112043, baseEnd_1112043] using wordTrace_append hprefix tailTrace_1112043
  have hstable : (prefixWord ++ tailWord_1112043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1112043).length < 2 ^ (prefixWord ++ tailWord_1112043).sum := by decide
  have hdescent : baseEnd_1112043 < baseStart_1112043 := by decide
  rcases family_descends (prefixWord ++ tailWord_1112043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1112067 : List Nat := [1, 1, 1, 3, 2, 1, 1, 3, 6, 2, 2]
def baseStart_1112067 : Nat := 118140960795 + 1112067 * 2 ^ 59
def prefixEnd_1112067 : Nat := 4983230072969 + 3 ^ 40 * 1112067 * 2
def baseEnd_1112067 : Nat := 571024891003605766448203

theorem tailTrace_1112067 : CollatzResearch.WordTrace tailWord_1112067 prefixEnd_1112067 571024891003605766448203 := by
  unfold tailWord_1112067
  simp only [CollatzResearch.WordTrace]
  refine ⟨40560415662178659767934455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27040277108119106511956303 40560415662178659767934455)
  ·
    refine ⟨60840623493267989651901683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40560415662178659767934455 60840623493267989651901683)
    ·
      refine ⟨91260935239901984477852525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60840623493267989651901683 91260935239901984477852525)
      ·
        refine ⟨34222850714963244179194697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 91260935239901984477852525 34222850714963244179194697)
        ·
          refine ⟨25667138036222433134396023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34222850714963244179194697 25667138036222433134396023)
          ·
            refine ⟨38500707054333649701594035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25667138036222433134396023 38500707054333649701594035)
            ·
              refine ⟨57751060581500474552391053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38500707054333649701594035 57751060581500474552391053)
              ·
                refine ⟨21656647718062677957146645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 57751060581500474552391053 21656647718062677957146645)
                ·
                  refine ⟨1015155361784188029241249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 21656647718062677957146645 1015155361784188029241249)
                  ·
                    refine ⟨761366521338141021930937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1015155361784188029241249 761366521338141021930937)
                    ·
                      refine ⟨571024891003605766448203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 761366521338141021930937 571024891003605766448203)
                      ·
                        rfl

theorem cell23_1112067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 3, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 3, 6, 2, 2].length) (baseStart_1112067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1112067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1112067 prefixEnd_1112067 := by exact prefixLift 1112067
  have htrace : WordTrace (prefixWord ++ tailWord_1112067) baseStart_1112067 baseEnd_1112067 := by
    simpa [prefixWord, tailWord_1112067, baseEnd_1112067] using wordTrace_append hprefix tailTrace_1112067
  have hstable : (prefixWord ++ tailWord_1112067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1112067).length < 2 ^ (prefixWord ++ tailWord_1112067).sum := by decide
  have hdescent : baseEnd_1112067 < baseStart_1112067 := by decide
  rcases family_descends (prefixWord ++ tailWord_1112067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1112071 : List Nat := [1, 1, 4, 3, 1, 3, 3, 1, 1, 3, 2]
def baseStart_1112071 : Nat := 118140960795 + 1112071 * 2 ^ 59
def prefixEnd_1112071 : Nat := 4983230072969 + 3 ^ 40 * 1112071 * 2
def baseEnd_1112071 : Nat := 571026944926223750798185

theorem tailTrace_1112071 : CollatzResearch.WordTrace tailWord_1112071 prefixEnd_1112071 571026944926223750798185 := by
  unfold tailWord_1112071
  simp only [CollatzResearch.WordTrace]
  refine ⟨40560561554164168451080067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27040374369442778967386711 40560561554164168451080067)
  ·
    refine ⟨60840842331246252676620101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40560561554164168451080067 60840842331246252676620101)
    ·
      refine ⟨11407657937108672376866269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 60840842331246252676620101 11407657937108672376866269)
      ·
        refine ⟨4277871726415752141324851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11407657937108672376866269 4277871726415752141324851)
        ·
          refine ⟨6416807589623628211987277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4277871726415752141324851 6416807589623628211987277)
          ·
            refine ⟨2406302846108860579495229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6416807589623628211987277 2406302846108860579495229)
            ·
              refine ⟨902363567290822717310711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2406302846108860579495229 902363567290822717310711)
              ·
                refine ⟨1353545350936234075966067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 902363567290822717310711 1353545350936234075966067)
                ·
                  refine ⟨2030318026404351113949101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1353545350936234075966067 2030318026404351113949101)
                  ·
                    refine ⟨761369259901631667730913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2030318026404351113949101 761369259901631667730913)
                    ·
                      refine ⟨571026944926223750798185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 761369259901631667730913 571026944926223750798185)
                      ·
                        rfl

theorem cell23_1112071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 3, 1, 1, 3, 2].length) (baseStart_1112071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1112071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1112071 prefixEnd_1112071 := by exact prefixLift 1112071
  have htrace : WordTrace (prefixWord ++ tailWord_1112071) baseStart_1112071 baseEnd_1112071 := by
    simpa [prefixWord, tailWord_1112071, baseEnd_1112071] using wordTrace_append hprefix tailTrace_1112071
  have hstable : (prefixWord ++ tailWord_1112071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1112071).length < 2 ^ (prefixWord ++ tailWord_1112071).sum := by decide
  have hdescent : baseEnd_1112071 < baseStart_1112071 := by decide
  rcases family_descends (prefixWord ++ tailWord_1112071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1112083 : List Nat := [1, 1, 1, 2, 1, 4, 2, 1, 1, 2, 7]
def baseStart_1112083 : Nat := 118140960795 + 1112083 * 2 ^ 59
def prefixEnd_1112083 : Nat := 4983230072969 + 3 ^ 40 * 1112083 * 2
def baseEnd_1112083 : Nat := 571033106694077703848129

theorem tailTrace_1112083 : CollatzResearch.WordTrace tailWord_1112083 prefixEnd_1112083 571033106694077703848129 := by
  unfold tailWord_1112083
  simp only [CollatzResearch.WordTrace]
  refine ⟨40560999230120694500516903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27040666153413796333677935 40560999230120694500516903)
  ·
    refine ⟨60841498845181041750775355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40560999230120694500516903 60841498845181041750775355)
    ·
      refine ⟨91262248267771562626163033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60841498845181041750775355 91262248267771562626163033)
      ·
        refine ⟨68446686200828671969622275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91262248267771562626163033 68446686200828671969622275)
        ·
          refine ⟨102670029301243007954433413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68446686200828671969622275 102670029301243007954433413)
          ·
            refine ⟨19250630493983063991456265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 102670029301243007954433413 19250630493983063991456265)
            ·
              refine ⟨14437972870487297993592199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19250630493983063991456265 14437972870487297993592199)
              ·
                refine ⟨21656959305730946990388299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14437972870487297993592199 21656959305730946990388299)
                ·
                  refine ⟨32485438958596420485582449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21656959305730946990388299 32485438958596420485582449)
                  ·
                    refine ⟨24364079218947315364186837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 32485438958596420485582449 24364079218947315364186837)
                    ·
                      refine ⟨571033106694077703848129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 24364079218947315364186837 571033106694077703848129)
                      ·
                        rfl

theorem cell23_1112083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 1, 1, 2, 7].length) (baseStart_1112083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1112083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1112083 prefixEnd_1112083 := by exact prefixLift 1112083
  have htrace : WordTrace (prefixWord ++ tailWord_1112083) baseStart_1112083 baseEnd_1112083 := by
    simpa [prefixWord, tailWord_1112083, baseEnd_1112083] using wordTrace_append hprefix tailTrace_1112083
  have hstable : (prefixWord ++ tailWord_1112083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1112083).length < 2 ^ (prefixWord ++ tailWord_1112083).sum := by decide
  have hdescent : baseEnd_1112083 < baseStart_1112083 := by decide
  rcases family_descends (prefixWord ++ tailWord_1112083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1112097 : List Nat := [1, 2, 3, 2, 4, 1, 1, 1, 2, 2, 4]
def baseStart_1112097 : Nat := 118140960795 + 1112097 * 2 ^ 59
def prefixEnd_1112097 : Nat := 4983230072969 + 3 ^ 40 * 1112097 * 2
def baseEnd_1112097 : Nat := 571040295423240649073065

theorem tailTrace_1112097 : CollatzResearch.WordTrace tailWord_1112097 prefixEnd_1112097 571040295423240649073065 := by
  unfold tailWord_1112097
  simp only [CollatzResearch.WordTrace]
  refine ⟨40561509852069974891526545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27041006568046649927684363 40561509852069974891526545)
  ·
    refine ⟨30421132389052481168644909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40561509852069974891526545 30421132389052481168644909)
    ·
      refine ⟨11407924645894680438241841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30421132389052481168644909 11407924645894680438241841)
      ·
        refine ⟨8555943484421010328681381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11407924645894680438241841 8555943484421010328681381)
        ·
          refine ⟨1604239403328939436627759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8555943484421010328681381 1604239403328939436627759)
          ·
            refine ⟨2406359104993409154941639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1604239403328939436627759 2406359104993409154941639)
            ·
              refine ⟨3609538657490113732412459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2406359104993409154941639 3609538657490113732412459)
              ·
                refine ⟨5414307986235170598618689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3609538657490113732412459 5414307986235170598618689)
                ·
                  refine ⟨4060730989676377948964017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5414307986235170598618689 4060730989676377948964017)
                  ·
                    refine ⟨3045548242257283461723013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4060730989676377948964017 3045548242257283461723013)
                    ·
                      refine ⟨571040295423240649073065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3045548242257283461723013 571040295423240649073065)
                      ·
                        rfl

theorem cell23_1112097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 1, 1, 2, 2, 4].length) (baseStart_1112097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1112097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1112097 prefixEnd_1112097 := by exact prefixLift 1112097
  have htrace : WordTrace (prefixWord ++ tailWord_1112097) baseStart_1112097 baseEnd_1112097 := by
    simpa [prefixWord, tailWord_1112097, baseEnd_1112097] using wordTrace_append hprefix tailTrace_1112097
  have hstable : (prefixWord ++ tailWord_1112097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1112097).length < 2 ^ (prefixWord ++ tailWord_1112097).sum := by decide
  have hdescent : baseEnd_1112097 < baseStart_1112097 := by decide
  rcases family_descends (prefixWord ++ tailWord_1112097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1112134 : List Nat := [6, 1, 1, 1, 1, 1, 1, 1, 4, 3, 3]
def baseStart_1112134 : Nat := 118140960795 + 1112134 * 2 ^ 59
def prefixEnd_1112134 : Nat := 4983230072969 + 3 ^ 40 * 1112134 * 2
def baseEnd_1112134 : Nat := 571059294207457004310395

theorem tailTrace_1112134 : CollatzResearch.WordTrace tailWord_1112134 prefixEnd_1112134 571059294207457004310395 := by
  unfold tailWord_1112134
  simp only [CollatzResearch.WordTrace]
  refine ⟨1267589354779247819081983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 27041906235290620140415637 1267589354779247819081983)
  ·
    refine ⟨1901384032168871728622975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1267589354779247819081983 1901384032168871728622975)
    ·
      refine ⟨2852076048253307592934463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1901384032168871728622975 2852076048253307592934463)
      ·
        refine ⟨4278114072379961389401695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2852076048253307592934463 4278114072379961389401695)
        ·
          refine ⟨6417171108569942084102543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4278114072379961389401695 6417171108569942084102543)
          ·
            refine ⟨9625756662854913126153815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6417171108569942084102543 9625756662854913126153815)
            ·
              refine ⟨14438634994282369689230723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9625756662854913126153815 14438634994282369689230723)
              ·
                refine ⟨21657952491423554533846085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14438634994282369689230723 21657952491423554533846085)
                ·
                  refine ⟨4060866092141916475096141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21657952491423554533846085 4060866092141916475096141)
                  ·
                    refine ⟨1522824784553218678161053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4060866092141916475096141 1522824784553218678161053)
                    ·
                      refine ⟨571059294207457004310395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1522824784553218678161053 571059294207457004310395)
                      ·
                        rfl

theorem cell23_1112134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 1, 4, 3, 3].length) (baseStart_1112134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1112134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1112134 prefixEnd_1112134 := by exact prefixLift 1112134
  have htrace : WordTrace (prefixWord ++ tailWord_1112134) baseStart_1112134 baseEnd_1112134 := by
    simpa [prefixWord, tailWord_1112134, baseEnd_1112134] using wordTrace_append hprefix tailTrace_1112134
  have hstable : (prefixWord ++ tailWord_1112134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1112134).length < 2 ^ (prefixWord ++ tailWord_1112134).sum := by decide
  have hdescent : baseEnd_1112134 < baseStart_1112134 := by decide
  rcases family_descends (prefixWord ++ tailWord_1112134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1112167 : List Nat := [1, 1, 5, 1, 1, 2, 1, 4, 3, 4]
def baseStart_1112167 : Nat := 118140960795 + 1112167 * 2 ^ 59
def prefixEnd_1112167 : Nat := 4983230072969 + 3 ^ 40 * 1112167 * 2
def baseEnd_1112167 : Nat := 190358746356351791732581

theorem tailTrace_1112167 : CollatzResearch.WordTrace tailWord_1112167 prefixEnd_1112167 190358746356351791732581 := by
  unfold tailWord_1112167
  simp only [CollatzResearch.WordTrace]
  refine ⟨40564062961816376846574755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27042708641210917897716503 40564062961816376846574755)
  ·
    refine ⟨60846094442724565269862133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40564062961816376846574755 60846094442724565269862133)
    ·
      refine ⟨5704321354005427994049575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 60846094442724565269862133 5704321354005427994049575)
      ·
        refine ⟨8556482031008141991074363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5704321354005427994049575 8556482031008141991074363)
        ·
          refine ⟨12834723046512212986611545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8556482031008141991074363 12834723046512212986611545)
          ·
            refine ⟨9626042284884159739958659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12834723046512212986611545 9626042284884159739958659)
            ·
              refine ⟨14439063427326239609937989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9626042284884159739958659 14439063427326239609937989)
              ·
                refine ⟨2707324392623669926863373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14439063427326239609937989 2707324392623669926863373)
                ·
                  refine ⟨1015246647233876222573765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2707324392623669926863373 1015246647233876222573765)
                  ·
                    refine ⟨190358746356351791732581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1015246647233876222573765 190358746356351791732581)
                    ·
                      rfl

theorem cell23_1112167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 4, 3, 4].length) (baseStart_1112167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1112167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1112167 prefixEnd_1112167 := by exact prefixLift 1112167
  have htrace : WordTrace (prefixWord ++ tailWord_1112167) baseStart_1112167 baseEnd_1112167 := by
    simpa [prefixWord, tailWord_1112167, baseEnd_1112167] using wordTrace_append hprefix tailTrace_1112167
  have hstable : (prefixWord ++ tailWord_1112167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1112167).length < 2 ^ (prefixWord ++ tailWord_1112167).sum := by decide
  have hdescent : baseEnd_1112167 < baseStart_1112167 := by decide
  rcases family_descends (prefixWord ++ tailWord_1112167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1112177 : List Nat := [1, 2, 2, 2, 1, 1, 4, 3, 2, 2, 3]
def baseStart_1112177 : Nat := 118140960795 + 1112177 * 2 ^ 59
def prefixEnd_1112177 : Nat := 4983230072969 + 3 ^ 40 * 1112177 * 2
def baseEnd_1112177 : Nat := 571081373875600336072697

theorem tailTrace_1112177 : CollatzResearch.WordTrace tailWord_1112177 prefixEnd_1112177 571081373875600336072697 := by
  unfold tailWord_1112177
  simp only [CollatzResearch.WordTrace]
  refine ⟨40564427691780148554438785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27042951794520099036292523 40564427691780148554438785)
  ·
    refine ⟨30423320768835111415829089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40564427691780148554438785 30423320768835111415829089)
    ·
      refine ⟨22817490576626333561871817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30423320768835111415829089 22817490576626333561871817)
      ·
        refine ⟨17113117932469750171403863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22817490576626333561871817 17113117932469750171403863)
        ·
          refine ⟨25669676898704625257105795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17113117932469750171403863 25669676898704625257105795)
          ·
            refine ⟨38504515348056937885658693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25669676898704625257105795 38504515348056937885658693)
            ·
              refine ⟨7219596627760675853561005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38504515348056937885658693 7219596627760675853561005)
              ·
                refine ⟨2707348735410253445085377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7219596627760675853561005 2707348735410253445085377)
                ·
                  refine ⟨2030511551557690083814033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2707348735410253445085377 2030511551557690083814033)
                  ·
                    refine ⟨1522883663668267562860525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2030511551557690083814033 1522883663668267562860525)
                    ·
                      refine ⟨571081373875600336072697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1522883663668267562860525 571081373875600336072697)
                      ·
                        rfl

theorem cell23_1112177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 3, 2, 2, 3].length) (baseStart_1112177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1112177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1112177 prefixEnd_1112177 := by exact prefixLift 1112177
  have htrace : WordTrace (prefixWord ++ tailWord_1112177) baseStart_1112177 baseEnd_1112177 := by
    simpa [prefixWord, tailWord_1112177, baseEnd_1112177] using wordTrace_append hprefix tailTrace_1112177
  have hstable : (prefixWord ++ tailWord_1112177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1112177).length < 2 ^ (prefixWord ++ tailWord_1112177).sum := by decide
  have hdescent : baseEnd_1112177 < baseStart_1112177 := by decide
  rcases family_descends (prefixWord ++ tailWord_1112177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1112201 : List Nat := [1, 2, 1, 1, 4, 2, 5, 2, 1, 4]
def baseStart_1112201 : Nat := 118140960795 + 1112201 * 2 ^ 59
def prefixEnd_1112201 : Nat := 4983230072969 + 3 ^ 40 * 1112201 * 2
def baseEnd_1112201 : Nat := 190364565803769414057529

theorem tailTrace_1112201 : CollatzResearch.WordTrace tailWord_1112201 prefixEnd_1112201 190364565803769414057529 := by
  unfold tailWord_1112201
  simp only [CollatzResearch.WordTrace]
  refine ⟨40565303043693200653312457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27043535362462133768874971 40565303043693200653312457)
  ·
    refine ⟨30423977282769900489984343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40565303043693200653312457 30423977282769900489984343)
    ·
      refine ⟨45635965924154850734976515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30423977282769900489984343 45635965924154850734976515)
      ·
        refine ⟨68453948886232276102464773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45635965924154850734976515 68453948886232276102464773)
        ·
          refine ⟨12835115416168551769212145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 68453948886232276102464773 12835115416168551769212145)
          ·
            refine ⟨9626336562126413826909109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12835115416168551769212145 9626336562126413826909109)
            ·
              refine ⟨902469052699351296272729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9626336562126413826909109 902469052699351296272729)
              ·
                refine ⟨676851789524513472204547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 902469052699351296272729 676851789524513472204547)
                ·
                  refine ⟨1015277684286770208306821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 676851789524513472204547 1015277684286770208306821)
                  ·
                    refine ⟨190364565803769414057529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1015277684286770208306821 190364565803769414057529)
                    ·
                      rfl

theorem cell23_1112201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 5, 2, 1, 4].length) (baseStart_1112201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1112201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1112201 prefixEnd_1112201 := by exact prefixLift 1112201
  have htrace : WordTrace (prefixWord ++ tailWord_1112201) baseStart_1112201 baseEnd_1112201 := by
    simpa [prefixWord, tailWord_1112201, baseEnd_1112201] using wordTrace_append hprefix tailTrace_1112201
  have hstable : (prefixWord ++ tailWord_1112201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1112201).length < 2 ^ (prefixWord ++ tailWord_1112201).sum := by decide
  have hdescent : baseEnd_1112201 < baseStart_1112201 := by decide
  rcases family_descends (prefixWord ++ tailWord_1112201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1112217 : List Nat := [1, 2, 1, 2, 1, 2, 1, 3, 3, 5, 2]
def baseStart_1112217 : Nat := 118140960795 + 1112217 * 2 ^ 59
def prefixEnd_1112217 : Nat := 4983230072969 + 3 ^ 40 * 1112217 * 2
def baseEnd_1112217 : Nat := 571101913101780179572513

theorem tailTrace_1112217 : CollatzResearch.WordTrace tailWord_1112217 prefixEnd_1112217 571101913101780179572513 := by
  unfold tailWord_1112217
  simp only [CollatzResearch.WordTrace]
  refine ⟨40565886611635235385894905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27043924407756823590596603 40565886611635235385894905)
  ·
    refine ⟨30424414958726426539421179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40565886611635235385894905 30424414958726426539421179)
    ·
      refine ⟨45636622438089639809131769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30424414958726426539421179 45636622438089639809131769)
      ·
        refine ⟨34227466828567229856848827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45636622438089639809131769 34227466828567229856848827)
        ·
          refine ⟨51341200242850844785273241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34227466828567229856848827 51341200242850844785273241)
          ·
            refine ⟨38505900182138133588954931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51341200242850844785273241 38505900182138133588954931)
            ·
              refine ⟨57758850273207200383432397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38505900182138133588954931 57758850273207200383432397)
              ·
                refine ⟨21659568852452700143787149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 57758850273207200383432397 21659568852452700143787149)
                ·
                  refine ⟨8122338319669762553920181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21659568852452700143787149 8122338319669762553920181)
                  ·
                    refine ⟨761469217469040239430017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8122338319669762553920181 761469217469040239430017)
                    ·
                      refine ⟨571101913101780179572513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 761469217469040239430017 571101913101780179572513)
                      ·
                        rfl

theorem cell23_1112217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 3, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 3, 3, 5, 2].length) (baseStart_1112217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1112217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1112217 prefixEnd_1112217 := by exact prefixLift 1112217
  have htrace : WordTrace (prefixWord ++ tailWord_1112217) baseStart_1112217 baseEnd_1112217 := by
    simpa [prefixWord, tailWord_1112217, baseEnd_1112217] using wordTrace_append hprefix tailTrace_1112217
  have hstable : (prefixWord ++ tailWord_1112217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1112217).length < 2 ^ (prefixWord ++ tailWord_1112217).sum := by decide
  have hdescent : baseEnd_1112217 < baseStart_1112217 := by decide
  rcases family_descends (prefixWord ++ tailWord_1112217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1112267 : List Nat := [1, 1, 1, 1, 3, 2, 3, 1, 5, 2, 3]
def baseStart_1112267 : Nat := 118140960795 + 1112267 * 2 ^ 59
def prefixEnd_1112267 : Nat := 4983230072969 + 3 ^ 40 * 1112267 * 2
def baseEnd_1112267 : Nat := 571127587134504983947283

theorem tailTrace_1112267 : CollatzResearch.WordTrace tailWord_1112267 prefixEnd_1112267 571127587134504983947283 := by
  unfold tailWord_1112267
  simp only [CollatzResearch.WordTrace]
  refine ⟨40567710261454093925215055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27045140174302729283476703 40567710261454093925215055)
  ·
    refine ⟨60851565392181140887822583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40567710261454093925215055 60851565392181140887822583)
    ·
      refine ⟨91277348088271711331733875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60851565392181140887822583 91277348088271711331733875)
      ·
        refine ⟨136916022132407566997600813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91277348088271711331733875 136916022132407566997600813)
        ·
          refine ⟨51343508299652837624100305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 136916022132407566997600813 51343508299652837624100305)
          ·
            refine ⟨38507631224739628218075229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51343508299652837624100305 38507631224739628218075229)
            ·
              refine ⟨14440361709277360581778211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38507631224739628218075229 14440361709277360581778211)
              ·
                refine ⟨21660542563916040872667317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14440361709277360581778211 21660542563916040872667317)
                ·
                  refine ⟨2030675865367128831812561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 21660542563916040872667317 2030675865367128831812561)
                  ·
                    refine ⟨1523006899025346623859421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2030675865367128831812561 1523006899025346623859421)
                    ·
                      refine ⟨571127587134504983947283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1523006899025346623859421 571127587134504983947283)
                      ·
                        rfl

theorem cell23_1112267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 1, 5, 2, 3].length) (baseStart_1112267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1112267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1112267 prefixEnd_1112267 := by exact prefixLift 1112267
  have htrace : WordTrace (prefixWord ++ tailWord_1112267) baseStart_1112267 baseEnd_1112267 := by
    simpa [prefixWord, tailWord_1112267, baseEnd_1112267] using wordTrace_append hprefix tailTrace_1112267
  have hstable : (prefixWord ++ tailWord_1112267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1112267).length < 2 ^ (prefixWord ++ tailWord_1112267).sum := by decide
  have hdescent : baseEnd_1112267 < baseStart_1112267 := by decide
  rcases family_descends (prefixWord ++ tailWord_1112267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1112274 : List Nat := [3, 2, 2, 2, 1, 3, 2, 1, 1, 6]
def baseStart_1112274 : Nat := 118140960795 + 1112274 * 2 ^ 59
def prefixEnd_1112274 : Nat := 4983230072969 + 3 ^ 40 * 1112274 * 2
def baseEnd_1112274 : Nat := 190377060499695485519917

theorem tailTrace_1112274 : CollatzResearch.WordTrace tailWord_1112274 prefixEnd_1112274 190377060499695485519917 := by
  unfold tailWord_1112274
  simp only [CollatzResearch.WordTrace]
  refine ⟨10141991393107183530179969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27045310381619156080479917 10141991393107183530179969)
  ·
    refine ⟨7606493544830387647634977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10141991393107183530179969 7606493544830387647634977)
    ·
      refine ⟨5704870158622790735726233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7606493544830387647634977 5704870158622790735726233)
      ·
        refine ⟨4278652618967093051794675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5704870158622790735726233 4278652618967093051794675)
        ·
          refine ⟨6417978928450639577692013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4278652618967093051794675 6417978928450639577692013)
          ·
            refine ⟨2406742098168989841634505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6417978928450639577692013 2406742098168989841634505)
            ·
              refine ⟨1805056573626742381225879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2406742098168989841634505 1805056573626742381225879)
              ·
                refine ⟨2707584860440113571838819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1805056573626742381225879 2707584860440113571838819)
                ·
                  refine ⟨4061377290660170357758229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2707584860440113571838819 4061377290660170357758229)
                  ·
                    refine ⟨190377060499695485519917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4061377290660170357758229 190377060499695485519917)
                    ·
                      rfl

theorem cell23_1112274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 2, 1, 1, 6].length) (baseStart_1112274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1112274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1112274 prefixEnd_1112274 := by exact prefixLift 1112274
  have htrace : WordTrace (prefixWord ++ tailWord_1112274) baseStart_1112274 baseEnd_1112274 := by
    simpa [prefixWord, tailWord_1112274, baseEnd_1112274] using wordTrace_append hprefix tailTrace_1112274
  have hstable : (prefixWord ++ tailWord_1112274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1112274).length < 2 ^ (prefixWord ++ tailWord_1112274).sum := by decide
  have hdescent : baseEnd_1112274 < baseStart_1112274 := by decide
  rcases family_descends (prefixWord ++ tailWord_1112274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1112341 : List Nat := [1, 3, 2, 1, 2, 1, 3, 4, 1, 3, 2]
def baseStart_1112341 : Nat := 118140960795 + 1112341 * 2 ^ 59
def prefixEnd_1112341 : Nat := 4983230072969 + 3 ^ 40 * 1112341 * 2
def baseEnd_1112341 : Nat := 571165584702937694421943

theorem tailTrace_1112341 : CollatzResearch.WordTrace tailWord_1112341 prefixEnd_1112341 571165584702937694421943 := by
  unfold tailWord_1112341
  simp only [CollatzResearch.WordTrace]
  refine ⟨40570409263186004563408877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27046939508790669708939251 40570409263186004563408877)
  ·
    refine ⟨15213903473694751711278329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40570409263186004563408877 15213903473694751711278329)
    ·
      refine ⟨11410427605271063783458747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15213903473694751711278329 11410427605271063783458747)
      ·
        refine ⟨17115641407906595675188121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11410427605271063783458747 17115641407906595675188121)
        ·
          refine ⟨12836731055929946756391091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17115641407906595675188121 12836731055929946756391091)
          ·
            refine ⟨19255096583894920134586637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12836731055929946756391091 19255096583894920134586637)
            ·
              refine ⟨7220661218960595050469989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19255096583894920134586637 7220661218960595050469989)
              ·
                refine ⟨1353873978555111571963123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7220661218960595050469989 1353873978555111571963123)
                ·
                  refine ⟨2030810967832667357944685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1353873978555111571963123 2030810967832667357944685)
                  ·
                    refine ⟨761554112937250259229257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2030810967832667357944685 761554112937250259229257)
                    ·
                      refine ⟨571165584702937694421943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 761554112937250259229257 571165584702937694421943)
                      ·
                        rfl

theorem cell23_1112341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 4, 1, 3, 2].length) (baseStart_1112341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1112341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1112341 prefixEnd_1112341 := by exact prefixLift 1112341
  have htrace : WordTrace (prefixWord ++ tailWord_1112341) baseStart_1112341 baseEnd_1112341 := by
    simpa [prefixWord, tailWord_1112341, baseEnd_1112341] using wordTrace_append hprefix tailTrace_1112341
  have hstable : (prefixWord ++ tailWord_1112341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1112341).length < 2 ^ (prefixWord ++ tailWord_1112341).sum := by decide
  have hdescent : baseEnd_1112341 < baseStart_1112341 := by decide
  rcases family_descends (prefixWord ++ tailWord_1112341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1112349 : List Nat := [1, 4, 2, 3, 3, 1, 1, 3, 1, 2, 2]
def baseStart_1112349 : Nat := 118140960795 + 1112349 * 2 ^ 59
def prefixEnd_1112349 : Nat := 4983230072969 + 3 ^ 40 * 1112349 * 2
def baseEnd_1112349 : Nat := 571169692548173663121907

theorem tailTrace_1112349 : CollatzResearch.WordTrace tailWord_1112349 prefixEnd_1112349 571169692548173663121907 := by
  unfold tailWord_1112349
  simp only [CollatzResearch.WordTrace]
  refine ⟨40570701047157021929700101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27047134031438014619800067 40570701047157021929700101)
  ·
    refine ⟨7607006446341941611818769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 40570701047157021929700101 7607006446341941611818769)
    ·
      refine ⟨5705254834756456208864077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7607006446341941611818769 5705254834756456208864077)
      ·
        refine ⟨2139470563033671078324029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5705254834756456208864077 2139470563033671078324029)
        ·
          refine ⟨802301461137626654371511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2139470563033671078324029 802301461137626654371511)
          ·
            refine ⟨1203452191706439981557267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 802301461137626654371511 1203452191706439981557267)
            ·
              refine ⟨1805178287559659972335901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1203452191706439981557267 1805178287559659972335901)
              ·
                refine ⟨676941857834872489625963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1805178287559659972335901 676941857834872489625963)
                ·
                  refine ⟨1015412786752308734438945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 676941857834872489625963 1015412786752308734438945)
                  ·
                    refine ⟨761559590064231550829209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1015412786752308734438945 761559590064231550829209)
                    ·
                      refine ⟨571169692548173663121907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 761559590064231550829209 571169692548173663121907)
                      ·
                        rfl

theorem cell23_1112349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 3, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 3, 1, 1, 3, 1, 2, 2].length) (baseStart_1112349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1112349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1112349 prefixEnd_1112349 := by exact prefixLift 1112349
  have htrace : WordTrace (prefixWord ++ tailWord_1112349) baseStart_1112349 baseEnd_1112349 := by
    simpa [prefixWord, tailWord_1112349, baseEnd_1112349] using wordTrace_append hprefix tailTrace_1112349
  have hstable : (prefixWord ++ tailWord_1112349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1112349).length < 2 ^ (prefixWord ++ tailWord_1112349).sum := by decide
  have hdescent : baseEnd_1112349 < baseStart_1112349 := by decide
  rcases family_descends (prefixWord ++ tailWord_1112349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1112367 : List Nat := [1, 1, 2, 1, 2, 1, 4, 1, 4, 2, 4]
def baseStart_1112367 : Nat := 118140960795 + 1112367 * 2 ^ 59
def prefixEnd_1112367 : Nat := 4983230072969 + 3 ^ 40 * 1112367 * 2
def baseEnd_1112367 : Nat := 571178935199954592696823

theorem tailTrace_1112367 : CollatzResearch.WordTrace tailWord_1112367 prefixEnd_1112367 571178935199954592696823 := by
  unfold tailWord_1112367
  simp only [CollatzResearch.WordTrace]
  refine ⟨40571357561091811003855355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27047571707394540669236903 40571357561091811003855355)
  ·
    refine ⟨60857036341637716505783033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40571357561091811003855355 60857036341637716505783033)
    ·
      refine ⟨45642777256228287379337275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60857036341637716505783033 45642777256228287379337275)
      ·
        refine ⟨68464165884342431069005913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45642777256228287379337275 68464165884342431069005913)
        ·
          refine ⟨51348124413256823301754435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68464165884342431069005913 51348124413256823301754435)
          ·
            refine ⟨77022186619885234952631653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51348124413256823301754435 77022186619885234952631653)
            ·
              refine ⟨14441659991228481553618435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 77022186619885234952631653 14441659991228481553618435)
              ·
                refine ⟨21662489986842722330427653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14441659991228481553618435 21662489986842722330427653)
                ·
                  refine ⟨4061716872533010436955185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21662489986842722330427653 4061716872533010436955185)
                  ·
                    refine ⟨3046287654399757827716389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4061716872533010436955185 3046287654399757827716389)
                    ·
                      refine ⟨571178935199954592696823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3046287654399757827716389 571178935199954592696823)
                      ·
                        rfl

theorem cell23_1112367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 1, 4, 2, 4].length) (baseStart_1112367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1112367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1112367 prefixEnd_1112367 := by exact prefixLift 1112367
  have htrace : WordTrace (prefixWord ++ tailWord_1112367) baseStart_1112367 baseEnd_1112367 := by
    simpa [prefixWord, tailWord_1112367, baseEnd_1112367] using wordTrace_append hprefix tailTrace_1112367
  have hstable : (prefixWord ++ tailWord_1112367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1112367).length < 2 ^ (prefixWord ++ tailWord_1112367).sum := by decide
  have hdescent : baseEnd_1112367 < baseStart_1112367 := by decide
  rcases family_descends (prefixWord ++ tailWord_1112367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1112371 : List Nat := [1, 1, 1, 2, 5, 1, 1, 3, 4, 2, 2]
def baseStart_1112371 : Nat := 118140960795 + 1112371 * 2 ^ 59
def prefixEnd_1112371 : Nat := 4983230072969 + 3 ^ 40 * 1112371 * 2
def baseEnd_1112371 : Nat := 571180989122572577046805

theorem tailTrace_1112371 : CollatzResearch.WordTrace tailWord_1112371 prefixEnd_1112371 571180989122572577046805 := by
  unfold tailWord_1112371
  simp only [CollatzResearch.WordTrace]
  refine ⟨40571503453077319687000967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27047668968718213124667311 40571503453077319687000967)
  ·
    refine ⟨60857255179615979530501451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40571503453077319687000967 60857255179615979530501451)
    ·
      refine ⟨91285882769423969295752177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60857255179615979530501451 91285882769423969295752177)
      ·
        refine ⟨68464412077067976971814133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91285882769423969295752177 68464412077067976971814133)
        ·
          refine ⟨6418538632225122841107575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 68464412077067976971814133 6418538632225122841107575)
          ·
            refine ⟨9627807948337684261661363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6418538632225122841107575 9627807948337684261661363)
            ·
              refine ⟨14441711922506526392492045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9627807948337684261661363 14441711922506526392492045)
              ·
                refine ⟨5415641970939947397184517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14441711922506526392492045 5415641970939947397184517)
                ·
                  refine ⟨1015432869551240136972097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5415641970939947397184517 1015432869551240136972097)
                  ·
                    refine ⟨761574652163430102729073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1015432869551240136972097 761574652163430102729073)
                    ·
                      refine ⟨571180989122572577046805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 761574652163430102729073 571180989122572577046805)
                      ·
                        rfl

theorem cell23_1112371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 3, 4, 2, 2].length) (baseStart_1112371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1112371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1112371 prefixEnd_1112371 := by exact prefixLift 1112371
  have htrace : WordTrace (prefixWord ++ tailWord_1112371) baseStart_1112371 baseEnd_1112371 := by
    simpa [prefixWord, tailWord_1112371, baseEnd_1112371] using wordTrace_append hprefix tailTrace_1112371
  have hstable : (prefixWord ++ tailWord_1112371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1112371).length < 2 ^ (prefixWord ++ tailWord_1112371).sum := by decide
  have hdescent : baseEnd_1112371 < baseStart_1112371 := by decide
  rcases family_descends (prefixWord ++ tailWord_1112371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1112434 : List Nat := [3, 2, 1, 2, 1, 3, 2, 1, 1, 2, 5]
def baseStart_1112434 : Nat := 118140960795 + 1112434 * 2 ^ 59
def prefixEnd_1112434 : Nat := 4983230072969 + 3 ^ 40 * 1112434 * 2
def baseEnd_1112434 : Nat := 571213338403805830559015

theorem tailTrace_1112434 : CollatzResearch.WordTrace tailWord_1112434 prefixEnd_1112434 571213338403805830559015 := by
  unfold tailWord_1112434
  simp only [CollatzResearch.WordTrace]
  refine ⟨10143450312962270361636089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27049200834566054297696237 10143450312962270361636089)
  ·
    refine ⟨7607587734721702771227067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10143450312962270361636089 7607587734721702771227067)
    ·
      refine ⟨11411381602082554156840601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7607587734721702771227067 11411381602082554156840601)
      ·
        refine ⟨8558536201561915617630451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11411381602082554156840601 8558536201561915617630451)
        ·
          refine ⟨12837804302342873426445677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8558536201561915617630451 12837804302342873426445677)
          ·
            refine ⟨4814176613378577534917129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12837804302342873426445677 4814176613378577534917129)
            ·
              refine ⟨3610632460033933151187847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4814176613378577534917129 3610632460033933151187847)
              ·
                refine ⟨5415948690050899726781771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3610632460033933151187847 5415948690050899726781771)
                ·
                  refine ⟨8123923035076349590172657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5415948690050899726781771 8123923035076349590172657)
                  ·
                    refine ⟨6092942276307262192629493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8123923035076349590172657 6092942276307262192629493)
                    ·
                      refine ⟨571213338403805830559015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6092942276307262192629493 571213338403805830559015)
                      ·
                        rfl

theorem cell23_1112434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 2, 1, 1, 2, 5].length) (baseStart_1112434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1112434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1112434 prefixEnd_1112434 := by exact prefixLift 1112434
  have htrace : WordTrace (prefixWord ++ tailWord_1112434) baseStart_1112434 baseEnd_1112434 := by
    simpa [prefixWord, tailWord_1112434, baseEnd_1112434] using wordTrace_append hprefix tailTrace_1112434
  have hstable : (prefixWord ++ tailWord_1112434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1112434).length < 2 ^ (prefixWord ++ tailWord_1112434).sum := by decide
  have hdescent : baseEnd_1112434 < baseStart_1112434 := by decide
  rcases family_descends (prefixWord ++ tailWord_1112434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1112447 : List Nat := [1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 5]
def baseStart_1112447 : Nat := 118140960795 + 1112447 * 2 ^ 59
def prefixEnd_1112447 : Nat := 4983230072969 + 3 ^ 40 * 1112447 * 2
def baseEnd_1112447 : Nat := 571220013652314279696455

theorem tailTrace_1112447 : CollatzResearch.WordTrace tailWord_1112447 prefixEnd_1112447 571220013652314279696455 := by
  unfold tailWord_1112447
  simp only [CollatzResearch.WordTrace]
  refine ⟨40574275400801984666767595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27049516933867989777845063 40574275400801984666767595)
  ·
    refine ⟨60861413101202977000151393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40574275400801984666767595 60861413101202977000151393)
    ·
      refine ⟨45646059825902232750113545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60861413101202977000151393 45646059825902232750113545)
      ·
        refine ⟨34234544869426674562585159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45646059825902232750113545 34234544869426674562585159)
        ·
          refine ⟨51351817304140011843877739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34234544869426674562585159 51351817304140011843877739)
          ·
            refine ⟨77027725956210017765816609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51351817304140011843877739 77027725956210017765816609)
            ·
              refine ⟨57770794467157513324362457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 77027725956210017765816609 57770794467157513324362457)
              ·
                refine ⟨43328095850368134993271843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 57770794467157513324362457 43328095850368134993271843)
                ·
                  refine ⟨64992143775552202489907765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43328095850368134993271843 64992143775552202489907765)
                  ·
                    refine ⟨6093013478958018983428853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 64992143775552202489907765 6093013478958018983428853)
                    ·
                      refine ⟨571220013652314279696455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6093013478958018983428853 571220013652314279696455)
                      ·
                        rfl

theorem cell23_1112447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 5].length) (baseStart_1112447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1112447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1112447 prefixEnd_1112447 := by exact prefixLift 1112447
  have htrace : WordTrace (prefixWord ++ tailWord_1112447) baseStart_1112447 baseEnd_1112447 := by
    simpa [prefixWord, tailWord_1112447, baseEnd_1112447] using wordTrace_append hprefix tailTrace_1112447
  have hstable : (prefixWord ++ tailWord_1112447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1112447).length < 2 ^ (prefixWord ++ tailWord_1112447).sum := by decide
  have hdescent : baseEnd_1112447 < baseStart_1112447 := by decide
  rcases family_descends (prefixWord ++ tailWord_1112447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1112464 : List Nat := [2, 1, 1, 1, 1, 1, 2, 1, 8, 2, 3]
def baseStart_1112464 : Nat := 118140960795 + 1112464 * 2 ^ 59
def prefixEnd_1112464 : Nat := 4983230072969 + 3 ^ 40 * 1112464 * 2
def baseEnd_1112464 : Nat := 571228742823440713183877

theorem tailTrace_1112464 : CollatzResearch.WordTrace tailWord_1112464 prefixEnd_1112464 571228742823440713183877 := by
  unfold tailWord_1112464
  simp only [CollatzResearch.WordTrace]
  refine ⟨20287447720870198285068223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27049930294493597713424297 20287447720870198285068223)
  ·
    refine ⟨30431171581305297427602335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20287447720870198285068223 30431171581305297427602335)
    ·
      refine ⟨45646757371957946141403503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30431171581305297427602335 45646757371957946141403503)
      ·
        refine ⟨68470136057936919212105255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45646757371957946141403503 68470136057936919212105255)
        ·
          refine ⟨102705204086905378818157883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68470136057936919212105255 102705204086905378818157883)
          ·
            refine ⟨154057806130358068227236825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 102705204086905378818157883 154057806130358068227236825)
            ·
              refine ⟨115543354597768551170427619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 154057806130358068227236825 115543354597768551170427619)
              ·
                refine ⟨173315031896652826755641429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 115543354597768551170427619 173315031896652826755641429)
                ·
                  refine ⟨2031035530038900313542673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 173315031896652826755641429 2031035530038900313542673)
                  ·
                    refine ⟨1523276647529175235157005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2031035530038900313542673 1523276647529175235157005)
                    ·
                      refine ⟨571228742823440713183877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1523276647529175235157005 571228742823440713183877)
                      ·
                        rfl

theorem cell23_1112464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 8, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 8, 2, 3].length) (baseStart_1112464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1112464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1112464 prefixEnd_1112464 := by exact prefixLift 1112464
  have htrace : WordTrace (prefixWord ++ tailWord_1112464) baseStart_1112464 baseEnd_1112464 := by
    simpa [prefixWord, tailWord_1112464, baseEnd_1112464] using wordTrace_append hprefix tailTrace_1112464
  have hstable : (prefixWord ++ tailWord_1112464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1112464).length < 2 ^ (prefixWord ++ tailWord_1112464).sum := by decide
  have hdescent : baseEnd_1112464 < baseStart_1112464 := by decide
  rcases family_descends (prefixWord ++ tailWord_1112464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1112474 : List Nat := [3, 1, 1, 4, 1, 2, 1, 1, 2, 1, 6]
def baseStart_1112474 : Nat := 118140960795 + 1112474 * 2 ^ 59
def prefixEnd_1112474 : Nat := 4983230072969 + 3 ^ 40 * 1112474 * 2
def baseEnd_1112474 : Nat := 571233877629985674058831

theorem tailTrace_1112474 : CollatzResearch.WordTrace tailWord_1112474 prefixEnd_1112474 571233877629985674058831 := by
  unfold tailWord_1112474
  simp only [CollatzResearch.WordTrace]
  refine ⟨10143815042926042069500119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27050173447802778852000317 10143815042926042069500119)
  ·
    refine ⟨15215722564389063104250179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10143815042926042069500119 15215722564389063104250179)
    ·
      refine ⟨22823583846583594656375269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15215722564389063104250179 22823583846583594656375269)
      ·
        refine ⟨4279421971234423998070363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22823583846583594656375269 4279421971234423998070363)
        ·
          refine ⟨6419132956851635997105545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4279421971234423998070363 6419132956851635997105545)
          ·
            refine ⟨4814349717638726997829159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6419132956851635997105545 4814349717638726997829159)
            ·
              refine ⟨7221524576458090496743739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4814349717638726997829159 7221524576458090496743739)
              ·
                refine ⟨10832286864687135745115609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7221524576458090496743739 10832286864687135745115609)
                ·
                  refine ⟨8124215148515351808836707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10832286864687135745115609 8124215148515351808836707)
                  ·
                    refine ⟨12186322722773027713255061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8124215148515351808836707 12186322722773027713255061)
                    ·
                      refine ⟨571233877629985674058831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 12186322722773027713255061 571233877629985674058831)
                      ·
                        rfl

theorem cell23_1112474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 1, 2, 1, 6].length) (baseStart_1112474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1112474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1112474 prefixEnd_1112474 := by exact prefixLift 1112474
  have htrace : WordTrace (prefixWord ++ tailWord_1112474) baseStart_1112474 baseEnd_1112474 := by
    simpa [prefixWord, tailWord_1112474, baseEnd_1112474] using wordTrace_append hprefix tailTrace_1112474
  have hstable : (prefixWord ++ tailWord_1112474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1112474).length < 2 ^ (prefixWord ++ tailWord_1112474).sum := by decide
  have hdescent : baseEnd_1112474 < baseStart_1112474 := by decide
  rcases family_descends (prefixWord ++ tailWord_1112474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1112488 : List Nat := [2, 1, 6, 1, 1, 1, 1, 3, 3, 4]
def baseStart_1112488 : Nat := 118140960795 + 1112488 * 2 ^ 59
def prefixEnd_1112488 : Nat := 4983230072969 + 3 ^ 40 * 1112488 * 2
def baseEnd_1112488 : Nat := 190413688786382873094589

theorem tailTrace_1112488 : CollatzResearch.WordTrace tailWord_1112488 prefixEnd_1112488 190413688786382873094589 := by
  unfold tailWord_1112488
  simp only [CollatzResearch.WordTrace]
  refine ⟨20287885396826724334505059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27050513862435632446006745 20287885396826724334505059)
  ·
    refine ⟨30431828095240086501757589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20287885396826724334505059 30431828095240086501757589)
    ·
      refine ⟨1426491941964379054769887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 30431828095240086501757589 1426491941964379054769887)
      ·
        refine ⟨2139737912946568582154831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1426491941964379054769887 2139737912946568582154831)
        ·
          refine ⟨3209606869419852873232247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2139737912946568582154831 3209606869419852873232247)
          ·
            refine ⟨4814410304129779309848371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3209606869419852873232247 4814410304129779309848371)
            ·
              refine ⟨7221615456194668964772557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4814410304129779309848371 7221615456194668964772557)
              ·
                refine ⟨2708105796073000861789709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7221615456194668964772557 2708105796073000861789709)
                ·
                  refine ⟨1015539673527375323171141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2708105796073000861789709 1015539673527375323171141)
                  ·
                    refine ⟨190413688786382873094589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1015539673527375323171141 190413688786382873094589)
                    ·
                      rfl

theorem cell23_1112488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 3, 3, 4].length) (baseStart_1112488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1112488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1112488 prefixEnd_1112488 := by exact prefixLift 1112488
  have htrace : WordTrace (prefixWord ++ tailWord_1112488) baseStart_1112488 baseEnd_1112488 := by
    simpa [prefixWord, tailWord_1112488, baseEnd_1112488] using wordTrace_append hprefix tailTrace_1112488
  have hstable : (prefixWord ++ tailWord_1112488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1112488).length < 2 ^ (prefixWord ++ tailWord_1112488).sum := by decide
  have hdescent : baseEnd_1112488 < baseStart_1112488 := by decide
  rcases family_descends (prefixWord ++ tailWord_1112488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1112521 : List Nat := [1, 2, 1, 1, 2, 1, 6, 1, 1, 5, 2]
def baseStart_1112521 : Nat := 118140960795 + 1112521 * 2 ^ 59
def prefixEnd_1112521 : Nat := 4983230072969 + 3 ^ 40 * 1112521 * 2
def baseEnd_1112521 : Nat := 571258011220746990171115

theorem tailTrace_1112521 : CollatzResearch.WordTrace tailWord_1112521 prefixEnd_1112521 571258011220746990171115 := by
  unfold tailWord_1112521
  simp only [CollatzResearch.WordTrace]
  refine ⟨40576974402533895304961417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27051316268355930203307611 40576974402533895304961417)
  ·
    refine ⟨30432730801900421478721063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40576974402533895304961417 30432730801900421478721063)
    ·
      refine ⟨45649096202850632218081595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30432730801900421478721063 45649096202850632218081595)
      ·
        refine ⟨68473644304275948327122393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45649096202850632218081595 68473644304275948327122393)
        ·
          refine ⟨51355233228206961245341795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68473644304275948327122393 51355233228206961245341795)
          ·
            refine ⟨77032849842310441868012693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51355233228206961245341795 77032849842310441868012693)
            ·
              refine ⟨3610914836358301962563095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 77032849842310441868012693 3610914836358301962563095)
              ·
                refine ⟨5416372254537452943844643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3610914836358301962563095 5416372254537452943844643)
                ·
                  refine ⟨8124558381806179415766965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5416372254537452943844643 8124558381806179415766965)
                  ·
                    refine ⟨761677348294329320228153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8124558381806179415766965 761677348294329320228153)
                    ·
                      refine ⟨571258011220746990171115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 761677348294329320228153 571258011220746990171115)
                      ·
                        rfl

theorem cell23_1112521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 6, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 6, 1, 1, 5, 2].length) (baseStart_1112521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1112521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1112521 prefixEnd_1112521 := by exact prefixLift 1112521
  have htrace : WordTrace (prefixWord ++ tailWord_1112521) baseStart_1112521 baseEnd_1112521 := by
    simpa [prefixWord, tailWord_1112521, baseEnd_1112521] using wordTrace_append hprefix tailTrace_1112521
  have hstable : (prefixWord ++ tailWord_1112521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1112521).length < 2 ^ (prefixWord ++ tailWord_1112521).sum := by decide
  have hdescent : baseEnd_1112521 < baseStart_1112521 := by decide
  rcases family_descends (prefixWord ++ tailWord_1112521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1112538 : List Nat := [3, 1, 1, 2, 3, 1, 3, 2, 2, 3, 2]
def baseStart_1112538 : Nat := 118140960795 + 1112538 * 2 ^ 59
def prefixEnd_1112538 : Nat := 4983230072969 + 3 ^ 40 * 1112538 * 2
def baseEnd_1112538 : Nat := 571266740391873423658537

theorem tailTrace_1112538 : CollatzResearch.WordTrace tailWord_1112538 prefixEnd_1112538 571266740391873423658537 := by
  unfold tailWord_1112538
  simp only [CollatzResearch.WordTrace]
  refine ⟨10144398610868076802082567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27051729628981538138886845 10144398610868076802082567)
  ·
    refine ⟨15216597916302115203123851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10144398610868076802082567 15216597916302115203123851)
    ·
      refine ⟨22824896874453172804685777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15216597916302115203123851 22824896874453172804685777)
      ·
        refine ⟨17118672655839879603514333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22824896874453172804685777 17118672655839879603514333)
        ·
          refine ⟨6419502245939954851317875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17118672655839879603514333 6419502245939954851317875)
          ·
            refine ⟨9629253368909932276976813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6419502245939954851317875 9629253368909932276976813)
            ·
              refine ⟨3610970013341224603866305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9629253368909932276976813 3610970013341224603866305)
              ·
                refine ⟨2708227510005918452899729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3610970013341224603866305 2708227510005918452899729)
                ·
                  refine ⟨2031170632504438839674797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2708227510005918452899729 2031170632504438839674797)
                  ·
                    refine ⟨761688987189164564878049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2031170632504438839674797 761688987189164564878049)
                    ·
                      refine ⟨571266740391873423658537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 761688987189164564878049 571266740391873423658537)
                      ·
                        rfl

theorem cell23_1112538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 3, 2, 2, 3, 2].length) (baseStart_1112538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1112538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1112538 prefixEnd_1112538 := by exact prefixLift 1112538
  have htrace : WordTrace (prefixWord ++ tailWord_1112538) baseStart_1112538 baseEnd_1112538 := by
    simpa [prefixWord, tailWord_1112538, baseEnd_1112538] using wordTrace_append hprefix tailTrace_1112538
  have hstable : (prefixWord ++ tailWord_1112538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1112538).length < 2 ^ (prefixWord ++ tailWord_1112538).sum := by decide
  have hdescent : baseEnd_1112538 < baseStart_1112538 := by decide
  rcases family_descends (prefixWord ++ tailWord_1112538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1112551 : List Nat := [1, 1, 5, 2, 1, 1, 2, 2, 3, 1, 4]
def baseStart_1112551 : Nat := 118140960795 + 1112551 * 2 ^ 59
def prefixEnd_1112551 : Nat := 4983230072969 + 3 ^ 40 * 1112551 * 2
def baseEnd_1112551 : Nat := 571273415640381872795977

theorem tailTrace_1112551 : CollatzResearch.WordTrace tailWord_1112551 prefixEnd_1112551 571273415640381872795977 := by
  unfold tailWord_1112551
  simp only [CollatzResearch.WordTrace]
  refine ⟨40578068592425210428553507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27052045728283473619035671 40578068592425210428553507)
  ·
    refine ⟨60867102888637815642830261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40578068592425210428553507 60867102888637815642830261)
    ·
      refine ⟨5706290895809795216515337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 60867102888637815642830261 5706290895809795216515337)
      ·
        refine ⟨4279718171857346412386503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5706290895809795216515337 4279718171857346412386503)
        ·
          refine ⟨6419577257786019618579755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4279718171857346412386503 6419577257786019618579755)
          ·
            refine ⟨9629365886679029427869633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6419577257786019618579755 9629365886679029427869633)
            ·
              refine ⟨7222024415009272070902225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9629365886679029427869633 7222024415009272070902225)
              ·
                refine ⟨5416518311256954053176669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7222024415009272070902225 5416518311256954053176669)
                ·
                  refine ⟨2031194366721357769941251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5416518311256954053176669 2031194366721357769941251)
                  ·
                    refine ⟨3046791550082036654911877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2031194366721357769941251 3046791550082036654911877)
                    ·
                      refine ⟨571273415640381872795977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3046791550082036654911877 571273415640381872795977)
                      ·
                        rfl

theorem cell23_1112551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 2, 3, 1, 4].length) (baseStart_1112551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1112551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1112551 prefixEnd_1112551 := by exact prefixLift 1112551
  have htrace : WordTrace (prefixWord ++ tailWord_1112551) baseStart_1112551 baseEnd_1112551 := by
    simpa [prefixWord, tailWord_1112551, baseEnd_1112551] using wordTrace_append hprefix tailTrace_1112551
  have hstable : (prefixWord ++ tailWord_1112551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1112551).length < 2 ^ (prefixWord ++ tailWord_1112551).sum := by decide
  have hdescent : baseEnd_1112551 < baseStart_1112551 := by decide
  rcases family_descends (prefixWord ++ tailWord_1112551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1112568 : List Nat := [2, 1, 2, 1, 1, 4, 2, 1, 5, 2, 2]
def baseStart_1112568 : Nat := 118140960795 + 1112568 * 2 ^ 59
def prefixEnd_1112568 : Nat := 4983230072969 + 3 ^ 40 * 1112568 * 2
def baseEnd_1112568 : Nat := 571282144811508306283399

theorem tailTrace_1112568 : CollatzResearch.WordTrace tailWord_1112568 prefixEnd_1112568 571282144811508306283399 := by
  unfold tailWord_1112568
  simp only [CollatzResearch.WordTrace]
  refine ⟨20289344316681811165961179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27052459088909081554614905 20289344316681811165961179)
  ·
    refine ⟨30434016475022716748941769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20289344316681811165961179 30434016475022716748941769)
    ·
      refine ⟨22825512356267037561706327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30434016475022716748941769 22825512356267037561706327)
      ·
        refine ⟨34238268534400556342559491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22825512356267037561706327 34238268534400556342559491)
        ·
          refine ⟨51357402801600834513839237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34238268534400556342559491 51357402801600834513839237)
          ·
            refine ⟨9629513025300156471344857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 51357402801600834513839237 9629513025300156471344857)
            ·
              refine ⟨7222134768975117353508643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9629513025300156471344857 7222134768975117353508643)
              ·
                refine ⟨10833202153462676030262965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7222134768975117353508643 10833202153462676030262965)
                ·
                  refine ⟨1015612701887125877837153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 10833202153462676030262965 1015612701887125877837153)
                  ·
                    refine ⟨761709526415344408377865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1015612701887125877837153 761709526415344408377865)
                    ·
                      refine ⟨571282144811508306283399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 761709526415344408377865 571282144811508306283399)
                      ·
                        rfl

theorem cell23_1112568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 1, 5, 2, 2].length) (baseStart_1112568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1112568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1112568 prefixEnd_1112568 := by exact prefixLift 1112568
  have htrace : WordTrace (prefixWord ++ tailWord_1112568) baseStart_1112568 baseEnd_1112568 := by
    simpa [prefixWord, tailWord_1112568, baseEnd_1112568] using wordTrace_append hprefix tailTrace_1112568
  have hstable : (prefixWord ++ tailWord_1112568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1112568).length < 2 ^ (prefixWord ++ tailWord_1112568).sum := by decide
  have hdescent : baseEnd_1112568 < baseStart_1112568 := by decide
  rcases family_descends (prefixWord ++ tailWord_1112568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1112588 : List Nat := [2, 2, 1, 2, 4, 3, 1, 1, 1, 1, 5]
def baseStart_1112588 : Nat := 118140960795 + 1112588 * 2 ^ 59
def prefixEnd_1112588 : Nat := 4983230072969 + 3 ^ 40 * 1112588 * 2
def baseEnd_1112588 : Nat := 571292414424598228033307

theorem tailTrace_1112588 : CollatzResearch.WordTrace tailWord_1112588 prefixEnd_1112588 571292414424598228033307 := by
  unfold tailWord_1112588
  simp only [CollatzResearch.WordTrace]
  refine ⟨20289709046645582873825209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27052945395527443831766945 20289709046645582873825209)
  ·
    refine ⟨15217281784984187155368907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20289709046645582873825209 15217281784984187155368907)
    ·
      refine ⟨22825922677476280733053361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15217281784984187155368907 22825922677476280733053361)
      ·
        refine ⟨17119442008107210549790021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22825922677476280733053361 17119442008107210549790021)
        ·
          refine ⟨3209895376520101978085629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17119442008107210549790021 3209895376520101978085629)
          ·
            refine ⟨1203710766195038241782111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3209895376520101978085629 1203710766195038241782111)
            ·
              refine ⟨1805566149292557362673167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1203710766195038241782111 1805566149292557362673167)
              ·
                refine ⟨2708349223938836044009751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1805566149292557362673167 2708349223938836044009751)
                ·
                  refine ⟨4062523835908254066014627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2708349223938836044009751 4062523835908254066014627)
                  ·
                    refine ⟨6093785753862381099021941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4062523835908254066014627 6093785753862381099021941)
                    ·
                      refine ⟨571292414424598228033307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6093785753862381099021941 571292414424598228033307)
                      ·
                        rfl

theorem cell23_1112588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 3, 1, 1, 1, 1, 5].length) (baseStart_1112588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1112588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1112588 prefixEnd_1112588 := by exact prefixLift 1112588
  have htrace : WordTrace (prefixWord ++ tailWord_1112588) baseStart_1112588 baseEnd_1112588 := by
    simpa [prefixWord, tailWord_1112588, baseEnd_1112588] using wordTrace_append hprefix tailTrace_1112588
  have hstable : (prefixWord ++ tailWord_1112588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1112588).length < 2 ^ (prefixWord ++ tailWord_1112588).sum := by decide
  have hdescent : baseEnd_1112588 < baseStart_1112588 := by decide
  rcases family_descends (prefixWord ++ tailWord_1112588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1112596 : List Nat := [2, 4, 3, 1, 1, 3, 2, 2, 1, 1, 3]
def baseStart_1112596 : Nat := 118140960795 + 1112596 * 2 ^ 59
def prefixEnd_1112596 : Nat := 4983230072969 + 3 ^ 40 * 1112596 * 2
def baseEnd_1112596 : Nat := 571296522269834196733271

theorem tailTrace_1112596 : CollatzResearch.WordTrace tailWord_1112596 prefixEnd_1112596 571296522269834196733271 := by
  unfold tailWord_1112596
  simp only [CollatzResearch.WordTrace]
  refine ⟨20289854938631091556970821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27053139918174788742627761 20289854938631091556970821)
  ·
    refine ⟨3804347800993329666932029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20289854938631091556970821 3804347800993329666932029)
    ·
      refine ⟨1426630425372498625099511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3804347800993329666932029 1426630425372498625099511)
      ·
        refine ⟨2139945638058747937649267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1426630425372498625099511 2139945638058747937649267)
        ·
          refine ⟨3209918457088121906473901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2139945638058747937649267 3209918457088121906473901)
          ·
            refine ⟨1203719421408045714927713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3209918457088121906473901 1203719421408045714927713)
            ·
              refine ⟨902789566056034286195785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1203719421408045714927713 902789566056034286195785)
              ·
                refine ⟨677092174542025714646839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 902789566056034286195785 677092174542025714646839)
                ·
                  refine ⟨1015638261813038571970259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 677092174542025714646839 1015638261813038571970259)
                  ·
                    refine ⟨1523457392719557857955389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1015638261813038571970259 1523457392719557857955389)
                    ·
                      refine ⟨571296522269834196733271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1523457392719557857955389 571296522269834196733271)
                      ·
                        rfl

theorem cell23_1112596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 3, 2, 2, 1, 1, 3].length) (baseStart_1112596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1112596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1112596 prefixEnd_1112596 := by exact prefixLift 1112596
  have htrace : WordTrace (prefixWord ++ tailWord_1112596) baseStart_1112596 baseEnd_1112596 := by
    simpa [prefixWord, tailWord_1112596, baseEnd_1112596] using wordTrace_append hprefix tailTrace_1112596
  have hstable : (prefixWord ++ tailWord_1112596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1112596).length < 2 ^ (prefixWord ++ tailWord_1112596).sum := by decide
  have hdescent : baseEnd_1112596 < baseStart_1112596 := by decide
  rcases family_descends (prefixWord ++ tailWord_1112596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1112608 : List Nat := [2, 1, 1, 6, 2, 2, 1, 8]
def baseStart_1112608 : Nat := 118140960795 + 1112608 * 2 ^ 59
def prefixEnd_1112608 : Nat := 4983230072969 + 3 ^ 40 * 1112608 * 2
def baseEnd_1112608 : Nat := 21159358668062524066045

theorem tailTrace_1112608 : CollatzResearch.WordTrace tailWord_1112608 prefixEnd_1112608 21159358668062524066045 := by
  unfold tailWord_1112608
  simp only [CollatzResearch.WordTrace]
  refine ⟨20290073776609354581689239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27053431702145806108918985 20290073776609354581689239)
  ·
    refine ⟨30435110664914031872533859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20290073776609354581689239 30435110664914031872533859)
    ·
      refine ⟨45652665997371047808800789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30435110664914031872533859 45652665997371047808800789)
      ·
        refine ⟨2139968718626767866037537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 45652665997371047808800789 2139968718626767866037537)
        ·
          refine ⟨1604976538970075899528153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2139968718626767866037537 1604976538970075899528153)
          ·
            refine ⟨1203732404227556924646115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1604976538970075899528153 1203732404227556924646115)
            ·
              refine ⟨1805598606341335386969173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1203732404227556924646115 1805598606341335386969173)
              ·
                refine ⟨21159358668062524066045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1805598606341335386969173 21159358668062524066045)
                ·
                  rfl

theorem cell23_1112608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 2, 1, 8].length) (baseStart_1112608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1112608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1112608 prefixEnd_1112608 := by exact prefixLift 1112608
  have htrace : WordTrace (prefixWord ++ tailWord_1112608) baseStart_1112608 baseEnd_1112608 := by
    simpa [prefixWord, tailWord_1112608, baseEnd_1112608] using wordTrace_append hprefix tailTrace_1112608
  have hstable : (prefixWord ++ tailWord_1112608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1112608).length < 2 ^ (prefixWord ++ tailWord_1112608).sum := by decide
  have hdescent : baseEnd_1112608 < baseStart_1112608 := by decide
  rcases family_descends (prefixWord ++ tailWord_1112608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1112618 : List Nat := [3, 1, 4, 1, 1, 2, 1, 3, 1, 3, 3]
def baseStart_1112618 : Nat := 118140960795 + 1112618 * 2 ^ 59
def prefixEnd_1112618 : Nat := 4983230072969 + 3 ^ 40 * 1112618 * 2
def baseEnd_1112618 : Nat := 571307818844233110658169

theorem tailTrace_1112618 : CollatzResearch.WordTrace tailWord_1112618 prefixEnd_1112618 571307818844233110658169 := by
  unfold tailWord_1112618
  simp only [CollatzResearch.WordTrace]
  refine ⟨10145128070795620217810627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27053674855454987247495005 10145128070795620217810627)
  ·
    refine ⟨15217692106193430326715941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10145128070795620217810627 15217692106193430326715941)
    ·
      refine ⟨2853317269911268186259239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15217692106193430326715941 2853317269911268186259239)
      ·
        refine ⟨4279975904866902279388859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2853317269911268186259239 4279975904866902279388859)
        ·
          refine ⟨6419963857300353419083289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4279975904866902279388859 6419963857300353419083289)
          ·
            refine ⟨4814972892975265064312467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6419963857300353419083289 4814972892975265064312467)
            ·
              refine ⟨7222459339462897596468701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4814972892975265064312467 7222459339462897596468701)
              ·
                refine ⟨2708422252298586598675763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7222459339462897596468701 2708422252298586598675763)
                ·
                  refine ⟨4062633378447879898013645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2708422252298586598675763 4062633378447879898013645)
                  ·
                    refine ⟨1523487516917954961755117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4062633378447879898013645 1523487516917954961755117)
                    ·
                      refine ⟨571307818844233110658169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1523487516917954961755117 571307818844233110658169)
                      ·
                        rfl

theorem cell23_1112618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 3, 1, 3, 3].length) (baseStart_1112618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1112618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1112618 prefixEnd_1112618 := by exact prefixLift 1112618
  have htrace : WordTrace (prefixWord ++ tailWord_1112618) baseStart_1112618 baseEnd_1112618 := by
    simpa [prefixWord, tailWord_1112618, baseEnd_1112618] using wordTrace_append hprefix tailTrace_1112618
  have hstable : (prefixWord ++ tailWord_1112618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1112618).length < 2 ^ (prefixWord ++ tailWord_1112618).sum := by decide
  have hdescent : baseEnd_1112618 < baseStart_1112618 := by decide
  rcases family_descends (prefixWord ++ tailWord_1112618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1112645 : List Nat := [1, 3, 1, 1, 1, 6, 1, 3, 1, 3, 2]
def baseStart_1112645 : Nat := 118140960795 + 1112645 * 2 ^ 59
def prefixEnd_1112645 : Nat := 4983230072969 + 3 ^ 40 * 1112645 * 2
def baseEnd_1112645 : Nat := 571321682821904505020545

theorem tailTrace_1112645 : CollatzResearch.WordTrace tailWord_1112645 prefixEnd_1112645 571321682821904505020545 := by
  unfold tailWord_1112645
  simp only [CollatzResearch.WordTrace]
  refine ⟨40581497054084664482475389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27054331369389776321650259 40581497054084664482475389)
  ·
    refine ⟨15218061395281749180928271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40581497054084664482475389 15218061395281749180928271)
    ·
      refine ⟨22827092092922623771392407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15218061395281749180928271 22827092092922623771392407)
      ·
        refine ⟨34240638139383935657088611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22827092092922623771392407 34240638139383935657088611)
        ·
          refine ⟨51360957209075903485632917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34240638139383935657088611 51360957209075903485632917)
          ·
            refine ⟨2407544869175432975889043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 51360957209075903485632917 2407544869175432975889043)
            ·
              refine ⟨3611317303763149463833565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2407544869175432975889043 3611317303763149463833565)
              ·
                refine ⟨1354243988911181048937587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3611317303763149463833565 1354243988911181048937587)
                ·
                  refine ⟨2031365983366771573406381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1354243988911181048937587 2031365983366771573406381)
                  ·
                    refine ⟨761762243762539340027393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2031365983366771573406381 761762243762539340027393)
                    ·
                      refine ⟨571321682821904505020545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 761762243762539340027393 571321682821904505020545)
                      ·
                        rfl

theorem cell23_1112645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 1, 3, 1, 3, 2].length) (baseStart_1112645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1112645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1112645 prefixEnd_1112645 := by exact prefixLift 1112645
  have htrace : WordTrace (prefixWord ++ tailWord_1112645) baseStart_1112645 baseEnd_1112645 := by
    simpa [prefixWord, tailWord_1112645, baseEnd_1112645] using wordTrace_append hprefix tailTrace_1112645
  have hstable : (prefixWord ++ tailWord_1112645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1112645).length < 2 ^ (prefixWord ++ tailWord_1112645).sum := by decide
  have hdescent : baseEnd_1112645 < baseStart_1112645 := by decide
  rcases family_descends (prefixWord ++ tailWord_1112645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1112661 : List Nat := [1, 3, 2, 2, 1, 1, 2, 1, 1, 6, 3]
def baseStart_1112661 : Nat := 118140960795 + 1112661 * 2 ^ 59
def prefixEnd_1112661 : Nat := 4983230072969 + 3 ^ 40 * 1112661 * 2
def baseEnd_1112661 : Nat := 571329898512376442420471

theorem tailTrace_1112661 : CollatzResearch.WordTrace tailWord_1112661 prefixEnd_1112661 571329898512376442420471 := by
  unfold tailWord_1112661
  simp only [CollatzResearch.WordTrace]
  refine ⟨40582080622026699215057837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27054720414684466143371891 40582080622026699215057837)
  ·
    refine ⟨15218280233260012205646689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40582080622026699215057837 15218280233260012205646689)
    ·
      refine ⟨11413710174945009154235017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15218280233260012205646689 11413710174945009154235017)
      ·
        refine ⟨8560282631208756865676263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11413710174945009154235017 8560282631208756865676263)
        ·
          refine ⟨12840423946813135298514395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8560282631208756865676263 12840423946813135298514395)
          ·
            refine ⟨19260635920219702947771593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12840423946813135298514395 19260635920219702947771593)
            ·
              refine ⟨14445476940164777210828695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19260635920219702947771593 14445476940164777210828695)
              ·
                refine ⟨21668215410247165816243043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14445476940164777210828695 21668215410247165816243043)
                ·
                  refine ⟨32502323115370748724364565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21668215410247165816243043 32502323115370748724364565)
                  ·
                    refine ⟨1523546396033003846454589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 32502323115370748724364565 1523546396033003846454589)
                    ·
                      refine ⟨571329898512376442420471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1523546396033003846454589 571329898512376442420471)
                      ·
                        rfl

theorem cell23_1112661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 1, 1, 6, 3].length) (baseStart_1112661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1112661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1112661 prefixEnd_1112661 := by exact prefixLift 1112661
  have htrace : WordTrace (prefixWord ++ tailWord_1112661) baseStart_1112661 baseEnd_1112661 := by
    simpa [prefixWord, tailWord_1112661, baseEnd_1112661] using wordTrace_append hprefix tailTrace_1112661
  have hstable : (prefixWord ++ tailWord_1112661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1112661).length < 2 ^ (prefixWord ++ tailWord_1112661).sum := by decide
  have hdescent : baseEnd_1112661 < baseStart_1112661 := by decide
  rcases family_descends (prefixWord ++ tailWord_1112661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
