import V185TrunkScan23Chunk0275

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_1632771 : List Nat := [1, 1, 1, 3, 2, 1, 6, 2, 2, 1, 3]
def baseStart_1632771 : Nat := 118140960795 + 1632771 * 2 ^ 59
def prefixEnd_1632771 : Nat := 4983230072969 + 3 ^ 40 * 1632771 * 2
def baseEnd_1632771 : Nat := 838396321722336509653529

theorem tailTrace_1632771 : CollatzResearch.WordTrace tailWord_1632771 prefixEnd_1632771 838396321722336509653529 := by
  unfold tailWord_1632771
  simp only [CollatzResearch.WordTrace]
  refine ⟨59552050767756996931122167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39701367178504664620748111 59552050767756996931122167)
  ·
    refine ⟨89328076151635495396683251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59552050767756996931122167 89328076151635495396683251)
    ·
      refine ⟨133992114227453243095024877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89328076151635495396683251 133992114227453243095024877)
      ·
        refine ⟨50247042835294966160634329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 133992114227453243095024877 50247042835294966160634329)
        ·
          refine ⟨37685282126471224620475747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50247042835294966160634329 37685282126471224620475747)
          ·
            refine ⟨56527923189706836930713621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37685282126471224620475747 56527923189706836930713621)
            ·
              refine ⟨2649746399517507981127201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 56527923189706836930713621 2649746399517507981127201)
              ·
                refine ⟨1987309799638130985845401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2649746399517507981127201 1987309799638130985845401)
                ·
                  refine ⟨1490482349728598239384051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1987309799638130985845401 1490482349728598239384051)
                  ·
                    refine ⟨2235723524592897359076077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1490482349728598239384051 2235723524592897359076077)
                    ·
                      refine ⟨838396321722336509653529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2235723524592897359076077 838396321722336509653529)
                      ·
                        rfl

theorem cell23_1632771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 6, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 6, 2, 2, 1, 3].length) (baseStart_1632771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1632771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1632771 prefixEnd_1632771 := by exact prefixLift 1632771
  have htrace : WordTrace (prefixWord ++ tailWord_1632771) baseStart_1632771 baseEnd_1632771 := by
    simpa [prefixWord, tailWord_1632771, baseEnd_1632771] using wordTrace_append hprefix tailTrace_1632771
  have hstable : (prefixWord ++ tailWord_1632771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1632771).length < 2 ^ (prefixWord ++ tailWord_1632771).sum := by decide
  have hdescent : baseEnd_1632771 < baseStart_1632771 := by decide
  rcases family_descends (prefixWord ++ tailWord_1632771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1632772 : List Nat := [2, 3, 2, 3, 1, 1, 4, 2, 1, 2, 2]
def baseStart_1632772 : Nat := 118140960795 + 1632772 * 2 ^ 59
def prefixEnd_1632772 : Nat := 4983230072969 + 3 ^ 40 * 1632772 * 2
def baseEnd_1632772 : Nat := 838396835202991005741025

theorem tailTrace_1632772 : CollatzResearch.WordTrace tailWord_1632772 prefixEnd_1632772 838396835202991005741025 := by
  unfold tailWord_1632772
  simp only [CollatzResearch.WordTrace]
  refine ⟨29776043620376687050954285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39701391493835582734605713 29776043620376687050954285)
  ·
    refine ⟨11166016357641257644107857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29776043620376687050954285 11166016357641257644107857)
    ·
      refine ⟨8374512268230943233080893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11166016357641257644107857 8374512268230943233080893)
      ·
        refine ⟨3140442100586603712405335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8374512268230943233080893 3140442100586603712405335)
        ·
          refine ⟨4710663150879905568608003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3140442100586603712405335 4710663150879905568608003)
          ·
            refine ⟨7065994726319858352912005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4710663150879905568608003 7065994726319858352912005)
            ·
              refine ⟨1324874011184973441171001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7065994726319858352912005 1324874011184973441171001)
              ·
                refine ⟨993655508388730080878251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1324874011184973441171001 993655508388730080878251)
                ·
                  refine ⟨1490483262583095121317377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 993655508388730080878251 1490483262583095121317377)
                  ·
                    refine ⟨1117862446937321340988033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1490483262583095121317377 1117862446937321340988033)
                    ·
                      refine ⟨838396835202991005741025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1117862446937321340988033 838396835202991005741025)
                      ·
                        rfl

theorem cell23_1632772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 4, 2, 1, 2, 2].length) (baseStart_1632772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1632772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1632772 prefixEnd_1632772 := by exact prefixLift 1632772
  have htrace : WordTrace (prefixWord ++ tailWord_1632772) baseStart_1632772 baseEnd_1632772 := by
    simpa [prefixWord, tailWord_1632772, baseEnd_1632772] using wordTrace_append hprefix tailTrace_1632772
  have hstable : (prefixWord ++ tailWord_1632772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1632772).length < 2 ^ (prefixWord ++ tailWord_1632772).sum := by decide
  have hdescent : baseEnd_1632772 < baseStart_1632772 := by decide
  rcases family_descends (prefixWord ++ tailWord_1632772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1632787 : List Nat := [1, 1, 1, 2, 1, 5, 3, 1, 2, 6]
def baseStart_1632787 : Nat := 118140960795 + 1632787 * 2 ^ 59
def prefixEnd_1632787 : Nat := 4983230072969 + 3 ^ 40 * 1632787 * 2
def baseEnd_1632787 : Nat := 279468179137602815684485

theorem tailTrace_1632787 : CollatzResearch.WordTrace tailWord_1632787 prefixEnd_1632787 279468179137602815684485 := by
  unfold tailWord_1632787
  simp only [CollatzResearch.WordTrace]
  refine ⟨59552634335699031663704615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39701756223799354442469743 59552634335699031663704615)
  ·
    refine ⟨89328951503548547495556923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59552634335699031663704615 89328951503548547495556923)
    ·
      refine ⟨133993427255322821243335385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89328951503548547495556923 133993427255322821243335385)
      ·
        refine ⟨100495070441492115932501539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133993427255322821243335385 100495070441492115932501539)
        ·
          refine ⟨150742605662238173898752309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100495070441492115932501539 150742605662238173898752309)
          ·
            refine ⟨14132119280834828803008029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 150742605662238173898752309 14132119280834828803008029)
            ·
              refine ⟨5299544730313060801128011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14132119280834828803008029 5299544730313060801128011)
              ·
                refine ⟨7949317095469591201692017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5299544730313060801128011 7949317095469591201692017)
                ·
                  refine ⟨5961987821602193401269013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7949317095469591201692017 5961987821602193401269013)
                  ·
                    refine ⟨279468179137602815684485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5961987821602193401269013 279468179137602815684485)
                    ·
                      rfl

theorem cell23_1632787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 3, 1, 2, 6].length) (baseStart_1632787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1632787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1632787 prefixEnd_1632787 := by exact prefixLift 1632787
  have htrace : WordTrace (prefixWord ++ tailWord_1632787) baseStart_1632787 baseEnd_1632787 := by
    simpa [prefixWord, tailWord_1632787, baseEnd_1632787] using wordTrace_append hprefix tailTrace_1632787
  have hstable : (prefixWord ++ tailWord_1632787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1632787).length < 2 ^ (prefixWord ++ tailWord_1632787).sum := by decide
  have hdescent : baseEnd_1632787 < baseStart_1632787 := by decide
  rcases family_descends (prefixWord ++ tailWord_1632787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1632788 : List Nat := [2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3]
def baseStart_1632788 : Nat := 118140960795 + 1632788 * 2 ^ 59
def prefixEnd_1632788 : Nat := 4983230072969 + 3 ^ 40 * 1632788 * 2
def baseEnd_1632788 : Nat := 838405050893462943140951

theorem tailTrace_1632788 : CollatzResearch.WordTrace tailWord_1632788 prefixEnd_1632788 838405050893462943140951 := by
  unfold tailWord_1632788
  simp only [CollatzResearch.WordTrace]
  refine ⟨29776335404347704417245509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39701780539130272556327345 29776335404347704417245509)
  ·
    refine ⟨5583062888315194578233533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29776335404347704417245509 5583062888315194578233533)
    ·
      refine ⟨2093648583118197966837575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5583062888315194578233533 2093648583118197966837575)
      ·
        refine ⟨3140472874677296950256363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2093648583118197966837575 3140472874677296950256363)
        ·
          refine ⟨4710709312015945425384545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3140472874677296950256363 4710709312015945425384545)
          ·
            refine ⟨3533031984011959069038409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4710709312015945425384545 3533031984011959069038409)
            ·
              refine ⟨2649773988008969301778807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3533031984011959069038409 2649773988008969301778807)
              ·
                refine ⟨3974660982013453952668211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2649773988008969301778807 3974660982013453952668211)
                ·
                  refine ⟨5961991473020180929002317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3974660982013453952668211 5961991473020180929002317)
                  ·
                    refine ⟨2235746802382567848375869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5961991473020180929002317 2235746802382567848375869)
                    ·
                      refine ⟨838405050893462943140951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2235746802382567848375869 838405050893462943140951)
                      ·
                        rfl

theorem cell23_1632788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3].length) (baseStart_1632788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1632788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1632788 prefixEnd_1632788 := by exact prefixLift 1632788
  have htrace : WordTrace (prefixWord ++ tailWord_1632788) baseStart_1632788 baseEnd_1632788 := by
    simpa [prefixWord, tailWord_1632788, baseEnd_1632788] using wordTrace_append hprefix tailTrace_1632788
  have hstable : (prefixWord ++ tailWord_1632788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1632788).length < 2 ^ (prefixWord ++ tailWord_1632788).sum := by decide
  have hdescent : baseEnd_1632788 < baseStart_1632788 := by decide
  rcases family_descends (prefixWord ++ tailWord_1632788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1632828 : List Nat := [2, 2, 2, 2, 3, 2, 1, 1, 4, 2, 2]
def baseStart_1632828 : Nat := 118140960795 + 1632828 * 2 ^ 59
def prefixEnd_1632828 : Nat := 4983230072969 + 3 ^ 40 * 1632828 * 2
def baseEnd_1632828 : Nat := 838425590119642786640767

theorem tailTrace_1632828 : CollatzResearch.WordTrace tailWord_1632828 prefixEnd_1632828 838425590119642786640767 := by
  unfold tailWord_1632828
  simp only [CollatzResearch.WordTrace]
  refine ⟨29777064864275247832973569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39702753152366997110631425 29777064864275247832973569)
  ·
    refine ⟨22332798648206435874730177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29777064864275247832973569 22332798648206435874730177)
    ·
      refine ⟨16749598986154826906047633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22332798648206435874730177 16749598986154826906047633)
      ·
        refine ⟨12562199239616120179535725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16749598986154826906047633 12562199239616120179535725)
        ·
          refine ⟨4710824714856045067325897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12562199239616120179535725 4710824714856045067325897)
          ·
            refine ⟨3533118536142033800494423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4710824714856045067325897 3533118536142033800494423)
            ·
              refine ⟨5299677804213050700741635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3533118536142033800494423 5299677804213050700741635)
              ·
                refine ⟨7949516706319576051112453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5299677804213050700741635 7949516706319576051112453)
                ·
                  refine ⟨1490534382434920509583585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7949516706319576051112453 1490534382434920509583585)
                  ·
                    refine ⟨1117900786826190382187689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1490534382434920509583585 1117900786826190382187689)
                    ·
                      refine ⟨838425590119642786640767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1117900786826190382187689 838425590119642786640767)
                      ·
                        rfl

theorem cell23_1632828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 1, 1, 4, 2, 2].length) (baseStart_1632828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1632828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1632828 prefixEnd_1632828 := by exact prefixLift 1632828
  have htrace : WordTrace (prefixWord ++ tailWord_1632828) baseStart_1632828 baseEnd_1632828 := by
    simpa [prefixWord, tailWord_1632828, baseEnd_1632828] using wordTrace_append hprefix tailTrace_1632828
  have hstable : (prefixWord ++ tailWord_1632828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1632828).length < 2 ^ (prefixWord ++ tailWord_1632828).sum := by decide
  have hdescent : baseEnd_1632828 < baseStart_1632828 := by decide
  rcases family_descends (prefixWord ++ tailWord_1632828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1632844 : List Nat := [2, 2, 1, 3, 1, 2, 1, 3, 2, 3, 3]
def baseStart_1632844 : Nat := 118140960795 + 1632844 * 2 ^ 59
def prefixEnd_1632844 : Nat := 4983230072969 + 3 ^ 40 * 1632844 * 2
def baseEnd_1632844 : Nat := 838433805810114724040693

theorem tailTrace_1632844 : CollatzResearch.WordTrace tailWord_1632844 prefixEnd_1632844 838433805810114724040693 := by
  unfold tailWord_1632844
  simp only [CollatzResearch.WordTrace]
  refine ⟨29777356648246265199264793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39703142197661686932353057 29777356648246265199264793)
  ·
    refine ⟨22333017486184698899448595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29777356648246265199264793 22333017486184698899448595)
    ·
      refine ⟨33499526229277048349172893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22333017486184698899448595 33499526229277048349172893)
      ·
        refine ⟨12562322335978893130939835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33499526229277048349172893 12562322335978893130939835)
        ·
          refine ⟨18843483503968339696409753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12562322335978893130939835 18843483503968339696409753)
          ·
            refine ⟨14132612627976254772307315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18843483503968339696409753 14132612627976254772307315)
            ·
              refine ⟨21198918941964382158460973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14132612627976254772307315 21198918941964382158460973)
              ·
                refine ⟨7949594603236643309422865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21198918941964382158460973 7949594603236643309422865)
                ·
                  refine ⟨5962195952427482482067149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7949594603236643309422865 5962195952427482482067149)
                  ·
                    refine ⟨2235823482160305930775181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5962195952427482482067149 2235823482160305930775181)
                    ·
                      refine ⟨838433805810114724040693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2235823482160305930775181 838433805810114724040693)
                      ·
                        rfl

theorem cell23_1632844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 3, 2, 3, 3].length) (baseStart_1632844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1632844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1632844 prefixEnd_1632844 := by exact prefixLift 1632844
  have htrace : WordTrace (prefixWord ++ tailWord_1632844) baseStart_1632844 baseEnd_1632844 := by
    simpa [prefixWord, tailWord_1632844, baseEnd_1632844] using wordTrace_append hprefix tailTrace_1632844
  have hstable : (prefixWord ++ tailWord_1632844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1632844).length < 2 ^ (prefixWord ++ tailWord_1632844).sum := by decide
  have hdescent : baseEnd_1632844 < baseStart_1632844 := by decide
  rcases family_descends (prefixWord ++ tailWord_1632844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1632845 : List Nat := [1, 6, 1, 1, 2, 3, 1, 1, 1, 4, 2]
def baseStart_1632845 : Nat := 118140960795 + 1632845 * 2 ^ 59
def prefixEnd_1632845 : Nat := 4983230072969 + 3 ^ 40 * 1632845 * 2
def baseEnd_1632845 : Nat := 838434319290769220128189

theorem tailTrace_1632845 : CollatzResearch.WordTrace tailWord_1632845 prefixEnd_1632845 838434319290769220128189 := by
  unfold tailWord_1632845
  simp only [CollatzResearch.WordTrace]
  refine ⟨59554749769488907569315989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39703166512992605046210659 59554749769488907569315989)
  ·
    refine ⟨2791628895444792542311687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 59554749769488907569315989 2791628895444792542311687)
    ·
      refine ⟨4187443343167188813467531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2791628895444792542311687 4187443343167188813467531)
      ·
        refine ⟨6281165014750783220201297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4187443343167188813467531 6281165014750783220201297)
        ·
          refine ⟨4710873761063087415150973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6281165014750783220201297 4710873761063087415150973)
          ·
            refine ⟨1766577660398657780681615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4710873761063087415150973 1766577660398657780681615)
            ·
              refine ⟨2649866490597986671022423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1766577660398657780681615 2649866490597986671022423)
              ·
                refine ⟨3974799735896980006533635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2649866490597986671022423 3974799735896980006533635)
                ·
                  refine ⟨5962199603845470009800453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3974799735896980006533635 5962199603845470009800453)
                  ·
                    refine ⟨1117912425721025626837585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5962199603845470009800453 1117912425721025626837585)
                    ·
                      refine ⟨838434319290769220128189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1117912425721025626837585 838434319290769220128189)
                      ·
                        rfl

theorem cell23_1632845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 3, 1, 1, 1, 4, 2].length) (baseStart_1632845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1632845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1632845 prefixEnd_1632845 := by exact prefixLift 1632845
  have htrace : WordTrace (prefixWord ++ tailWord_1632845) baseStart_1632845 baseEnd_1632845 := by
    simpa [prefixWord, tailWord_1632845, baseEnd_1632845] using wordTrace_append hprefix tailTrace_1632845
  have hstable : (prefixWord ++ tailWord_1632845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1632845).length < 2 ^ (prefixWord ++ tailWord_1632845).sum := by decide
  have hdescent : baseEnd_1632845 < baseStart_1632845 := by decide
  rcases family_descends (prefixWord ++ tailWord_1632845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1632847 : List Nat := [1, 1, 2, 1, 1, 2, 5, 2, 1, 7]
def baseStart_1632847 : Nat := 118140960795 + 1632847 * 2 ^ 59
def prefixEnd_1632847 : Nat := 4983230072969 + 3 ^ 40 * 1632847 * 2
def baseEnd_1632847 : Nat := 279478448750692737434393

theorem tailTrace_1632847 : CollatzResearch.WordTrace tailWord_1632847 prefixEnd_1632847 279478448750692737434393 := by
  unfold tailWord_1632847
  simp only [CollatzResearch.WordTrace]
  refine ⟨59554822715481661910888795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39703215143654441273925863 59554822715481661910888795)
  ·
    refine ⟨89332234073222492866333193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59554822715481661910888795 89332234073222492866333193)
    ·
      refine ⟨66999175554916869649749895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89332234073222492866333193 66999175554916869649749895)
      ·
        refine ⟨100498763332375304474624843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66999175554916869649749895 100498763332375304474624843)
        ·
          refine ⟨150748144998562956711937265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100498763332375304474624843 150748144998562956711937265)
          ·
            refine ⟨113061108748922217533952949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 150748144998562956711937265 113061108748922217533952949)
            ·
              refine ⟨10599478945211457893808089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 113061108748922217533952949 10599478945211457893808089)
              ·
                refine ⟨7949609208908593420356067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10599478945211457893808089 7949609208908593420356067)
                ·
                  refine ⟨11924413813362890130534101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7949609208908593420356067 11924413813362890130534101)
                  ·
                    refine ⟨279478448750692737434393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 11924413813362890130534101 279478448750692737434393)
                    ·
                      rfl

theorem cell23_1632847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 2, 1, 7].length) (baseStart_1632847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1632847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1632847 prefixEnd_1632847 := by exact prefixLift 1632847
  have htrace : WordTrace (prefixWord ++ tailWord_1632847) baseStart_1632847 baseEnd_1632847 := by
    simpa [prefixWord, tailWord_1632847, baseEnd_1632847] using wordTrace_append hprefix tailTrace_1632847
  have hstable : (prefixWord ++ tailWord_1632847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1632847).length < 2 ^ (prefixWord ++ tailWord_1632847).sum := by decide
  have hdescent : baseEnd_1632847 < baseStart_1632847 := by decide
  rcases family_descends (prefixWord ++ tailWord_1632847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1632857 : List Nat := [1, 2, 1, 2, 2, 1, 1, 1, 5, 2, 5]
def baseStart_1632857 : Nat := 118140960795 + 1632857 * 2 ^ 59
def prefixEnd_1632857 : Nat := 4983230072969 + 3 ^ 40 * 1632857 * 2
def baseEnd_1632857 : Nat := 838440481058623173178133

theorem tailTrace_1632857 : CollatzResearch.WordTrace tailWord_1632857 prefixEnd_1632857 838440481058623173178133 := by
  unfold tailWord_1632857
  simp only [CollatzResearch.WordTrace]
  refine ⟨59555187445445433618752825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39703458296963622412501883 59555187445445433618752825)
  ·
    refine ⟨44666390584084075214064619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59555187445445433618752825 44666390584084075214064619)
    ·
      refine ⟨66999585876126112821096929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44666390584084075214064619 66999585876126112821096929)
      ·
        refine ⟨50249689407094584615822697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66999585876126112821096929 50249689407094584615822697)
        ·
          refine ⟨37687267055320938461867023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50249689407094584615822697 37687267055320938461867023)
          ·
            refine ⟨56530900582981407692800535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37687267055320938461867023 56530900582981407692800535)
            ·
              refine ⟨84796350874472111539200803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56530900582981407692800535 84796350874472111539200803)
              ·
                refine ⟨127194526311708167308801205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84796350874472111539200803 127194526311708167308801205)
                ·
                  refine ⟨11924486841722640685200113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 127194526311708167308801205 11924486841722640685200113)
                  ·
                    refine ⟨8943365131291980513900085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11924486841722640685200113 8943365131291980513900085)
                    ·
                      refine ⟨838440481058623173178133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8943365131291980513900085 838440481058623173178133)
                      ·
                        rfl

theorem cell23_1632857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 1, 5, 2, 5].length) (baseStart_1632857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1632857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1632857 prefixEnd_1632857 := by exact prefixLift 1632857
  have htrace : WordTrace (prefixWord ++ tailWord_1632857) baseStart_1632857 baseEnd_1632857 := by
    simpa [prefixWord, tailWord_1632857, baseEnd_1632857] using wordTrace_append hprefix tailTrace_1632857
  have hstable : (prefixWord ++ tailWord_1632857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1632857).length < 2 ^ (prefixWord ++ tailWord_1632857).sum := by decide
  have hdescent : baseEnd_1632857 < baseStart_1632857 := by decide
  rcases family_descends (prefixWord ++ tailWord_1632857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1632874 : List Nat := [3, 1, 3, 2, 1, 1, 2, 2, 1, 2, 5]
def baseStart_1632874 : Nat := 118140960795 + 1632874 * 2 ^ 59
def prefixEnd_1632874 : Nat := 4983230072969 + 3 ^ 40 * 1632874 * 2
def baseEnd_1632874 : Nat := 838449210229749606665555

theorem tailTrace_1632874 : CollatzResearch.WordTrace tailWord_1632874 prefixEnd_1632874 838449210229749606665555 := by
  unfold tailWord_1632874
  simp only [CollatzResearch.WordTrace]
  refine ⟨14888951871595961380530419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39703871657589230348081117 14888951871595961380530419)
  ·
    refine ⟨22333427807393942070795629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14888951871595961380530419 22333427807393942070795629)
    ·
      refine ⟨8375035427772728276548361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22333427807393942070795629 8375035427772728276548361)
      ·
        refine ⟨6281276570829546207411271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8375035427772728276548361 6281276570829546207411271)
        ·
          refine ⟨9421914856244319311116907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6281276570829546207411271 9421914856244319311116907)
          ·
            refine ⟨14132872284366478966675361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9421914856244319311116907 14132872284366478966675361)
            ·
              refine ⟨10599654213274859225006521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14132872284366478966675361 10599654213274859225006521)
              ·
                refine ⟨7949740659956144418754891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10599654213274859225006521 7949740659956144418754891)
                ·
                  refine ⟨11924610989934216628132337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7949740659956144418754891 11924610989934216628132337)
                  ·
                    refine ⟨8943458242450662471099253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11924610989934216628132337 8943458242450662471099253)
                    ·
                      refine ⟨838449210229749606665555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8943458242450662471099253 838449210229749606665555)
                      ·
                        rfl

theorem cell23_1632874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 2, 1, 2, 5].length) (baseStart_1632874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1632874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1632874 prefixEnd_1632874 := by exact prefixLift 1632874
  have htrace : WordTrace (prefixWord ++ tailWord_1632874) baseStart_1632874 baseEnd_1632874 := by
    simpa [prefixWord, tailWord_1632874, baseEnd_1632874] using wordTrace_append hprefix tailTrace_1632874
  have hstable : (prefixWord ++ tailWord_1632874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1632874).length < 2 ^ (prefixWord ++ tailWord_1632874).sum := by decide
  have hdescent : baseEnd_1632874 < baseStart_1632874 := by decide
  rcases family_descends (prefixWord ++ tailWord_1632874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1632885 : List Nat := [1, 3, 4, 2, 2, 1, 3, 2, 5]
def baseStart_1632885 : Nat := 118140960795 + 1632885 * 2 ^ 59
def prefixEnd_1632885 : Nat := 4983230072969 + 3 ^ 40 * 1632885 * 2
def baseEnd_1632885 : Nat := 93161650946327673736445

theorem tailTrace_1632885 : CollatzResearch.WordTrace tailWord_1632885 prefixEnd_1632885 93161650946327673736445 := by
  unfold tailWord_1632885
  simp only [CollatzResearch.WordTrace]
  refine ⟨59556208689343994400772109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39704139126229329600514739 59556208689343994400772109)
  ·
    refine ⟨22333578258503997900289541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59556208689343994400772109 22333578258503997900289541)
    ·
      refine ⟨4187545923469499606304289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22333578258503997900289541 4187545923469499606304289)
      ·
        refine ⟨3140659442602124704728217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4187545923469499606304289 3140659442602124704728217)
        ·
          refine ⟨2355494581951593528546163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3140659442602124704728217 2355494581951593528546163)
          ·
            refine ⟨3533241872927390292819245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2355494581951593528546163 3533241872927390292819245)
            ·
              refine ⟨1324965702347771359807217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3533241872927390292819245 1324965702347771359807217)
              ·
                refine ⟨993724276760828519855413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1324965702347771359807217 993724276760828519855413)
                ·
                  refine ⟨93161650946327673736445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 993724276760828519855413 93161650946327673736445)
                  ·
                    rfl

theorem cell23_1632885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 3, 2, 5].length) (baseStart_1632885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1632885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1632885 prefixEnd_1632885 := by exact prefixLift 1632885
  have htrace : WordTrace (prefixWord ++ tailWord_1632885) baseStart_1632885 baseEnd_1632885 := by
    simpa [prefixWord, tailWord_1632885, baseEnd_1632885] using wordTrace_append hprefix tailTrace_1632885
  have hstable : (prefixWord ++ tailWord_1632885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1632885).length < 2 ^ (prefixWord ++ tailWord_1632885).sum := by decide
  have hdescent : baseEnd_1632885 < baseStart_1632885 := by decide
  rcases family_descends (prefixWord ++ tailWord_1632885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1632907 : List Nat := [1, 1, 1, 1, 4, 1, 2, 2, 10]
def baseStart_1632907 : Nat := 118140960795 + 1632907 * 2 ^ 59
def prefixEnd_1632907 : Nat := 4983230072969 + 3 ^ 40 * 1632907 * 2
def baseEnd_1632907 : Nat := 93162906121260886394767

theorem tailTrace_1632907 : CollatzResearch.WordTrace tailWord_1632907 prefixEnd_1632907 93162906121260886394767 := by
  unfold tailWord_1632907
  simp only [CollatzResearch.WordTrace]
  refine ⟨59557011095264292158072975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39704674063509528105381983 59557011095264292158072975)
  ·
    refine ⟨89335516642896438237109463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59557011095264292158072975 89335516642896438237109463)
    ·
      refine ⟨134003274964344657355664195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89335516642896438237109463 134003274964344657355664195)
      ·
        refine ⟨201004912446516986033496293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134003274964344657355664195 201004912446516986033496293)
        ·
          refine ⟨37688421083721934881280555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 201004912446516986033496293 37688421083721934881280555)
          ·
            refine ⟨56532631625582902321920833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37688421083721934881280555 56532631625582902321920833)
            ·
              refine ⟨42399473719187176741440625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56532631625582902321920833 42399473719187176741440625)
              ·
                refine ⟨31799605289390382556080469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42399473719187176741440625 31799605289390382556080469)
                ·
                  refine ⟨93162906121260886394767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 31799605289390382556080469 93162906121260886394767)
                  ·
                    rfl

theorem cell23_1632907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 2, 10].length) (baseStart_1632907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1632907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1632907 prefixEnd_1632907 := by exact prefixLift 1632907
  have htrace : WordTrace (prefixWord ++ tailWord_1632907) baseStart_1632907 baseEnd_1632907 := by
    simpa [prefixWord, tailWord_1632907, baseEnd_1632907] using wordTrace_append hprefix tailTrace_1632907
  have hstable : (prefixWord ++ tailWord_1632907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1632907).length < 2 ^ (prefixWord ++ tailWord_1632907).sum := by decide
  have hdescent : baseEnd_1632907 < baseStart_1632907 := by decide
  rcases family_descends (prefixWord ++ tailWord_1632907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1632921 : List Nat := [1, 2, 1, 2, 1, 2, 6, 1, 2, 2, 3]
def baseStart_1632921 : Nat := 118140960795 + 1632921 * 2 ^ 59
def prefixEnd_1632921 : Nat := 4983230072969 + 3 ^ 40 * 1632921 * 2
def baseEnd_1632921 : Nat := 838473343820510922777839

theorem tailTrace_1632921 : CollatzResearch.WordTrace tailWord_1632921 prefixEnd_1632921 838473343820510922777839 := by
  unfold tailWord_1632921
  simp only [CollatzResearch.WordTrace]
  refine ⟨59557521717213572549082617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39705014478142381699388411 59557521717213572549082617)
  ·
    refine ⟨44668141287910179411811963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59557521717213572549082617 44668141287910179411811963)
    ·
      refine ⟨67002211931865269117717945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44668141287910179411811963 67002211931865269117717945)
      ·
        refine ⟨50251658948898951838288459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67002211931865269117717945 50251658948898951838288459)
        ·
          refine ⟨75377488423348427757432689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50251658948898951838288459 75377488423348427757432689)
          ·
            refine ⟨56533116317511320818074517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75377488423348427757432689 56533116317511320818074517)
            ·
              refine ⟨2649989827383343163347243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 56533116317511320818074517 2649989827383343163347243)
              ·
                refine ⟨3974984741075014745020865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2649989827383343163347243 3974984741075014745020865)
                ·
                  refine ⟨2981238555806261058765649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3974984741075014745020865 2981238555806261058765649)
                  ·
                    refine ⟨2235928916854695794074237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2981238555806261058765649 2235928916854695794074237)
                    ·
                      refine ⟨838473343820510922777839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2235928916854695794074237 838473343820510922777839)
                      ·
                        rfl

theorem cell23_1632921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 6, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 6, 1, 2, 2, 3].length) (baseStart_1632921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1632921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1632921 prefixEnd_1632921 := by exact prefixLift 1632921
  have htrace : WordTrace (prefixWord ++ tailWord_1632921) baseStart_1632921 baseEnd_1632921 := by
    simpa [prefixWord, tailWord_1632921, baseEnd_1632921] using wordTrace_append hprefix tailTrace_1632921
  have hstable : (prefixWord ++ tailWord_1632921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1632921).length < 2 ^ (prefixWord ++ tailWord_1632921).sum := by decide
  have hdescent : baseEnd_1632921 < baseStart_1632921 := by decide
  rcases family_descends (prefixWord ++ tailWord_1632921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1632941 : List Nat := [1, 5, 2, 1, 1, 2, 1, 4, 6]
def baseStart_1632941 : Nat := 118140960795 + 1632941 * 2 ^ 59
def prefixEnd_1632941 : Nat := 4983230072969 + 3 ^ 40 * 1632941 * 2
def baseEnd_1632941 : Nat := 93164845937066760503083

theorem tailTrace_1632941 : CollatzResearch.WordTrace tailWord_1632941 prefixEnd_1632941 93164845937066760503083 := by
  unfold tailWord_1632941
  simp only [CollatzResearch.WordTrace]
  refine ⟨59558251177141115964810677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39705500784760743976540451 59558251177141115964810677)
  ·
    refine ⟨5583586047856979621701001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 59558251177141115964810677 5583586047856979621701001)
    ·
      refine ⟨4187689535892734716275751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5583586047856979621701001 4187689535892734716275751)
      ·
        refine ⟨6281534303839102074413627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4187689535892734716275751 6281534303839102074413627)
        ·
          refine ⟨9422301455758653111620441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6281534303839102074413627 9422301455758653111620441)
          ·
            refine ⟨7066726091818989833715331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9422301455758653111620441 7066726091818989833715331)
            ·
              refine ⟨10600089137728484750572997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7066726091818989833715331 10600089137728484750572997)
              ·
                refine ⟨1987516713324090890732437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10600089137728484750572997 1987516713324090890732437)
                ·
                  refine ⟨93164845937066760503083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1987516713324090890732437 93164845937066760503083)
                  ·
                    rfl

theorem cell23_1632941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 4, 6].length) (baseStart_1632941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1632941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1632941 prefixEnd_1632941 := by exact prefixLift 1632941
  have htrace : WordTrace (prefixWord ++ tailWord_1632941) baseStart_1632941 baseEnd_1632941 := by
    simpa [prefixWord, tailWord_1632941, baseEnd_1632941] using wordTrace_append hprefix tailTrace_1632941
  have hstable : (prefixWord ++ tailWord_1632941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1632941).length < 2 ^ (prefixWord ++ tailWord_1632941).sum := by decide
  have hdescent : baseEnd_1632941 < baseStart_1632941 := by decide
  rcases family_descends (prefixWord ++ tailWord_1632941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1632954 : List Nat := [3, 1, 1, 1, 2, 3, 1, 1, 5, 5]
def baseStart_1632954 : Nat := 118140960795 + 1632954 * 2 ^ 59
def prefixEnd_1632954 : Nat := 4983230072969 + 3 ^ 40 * 1632954 * 2
def baseEnd_1632954 : Nat := 279496762894036431221729

theorem tailTrace_1632954 : CollatzResearch.WordTrace tailWord_1632954 prefixEnd_1632954 279496762894036431221729 := by
  unfold tailWord_1632954
  simp only [CollatzResearch.WordTrace]
  refine ⟨14889681331523504796258479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39705816884062679456689277 14889681331523504796258479)
  ·
    refine ⟨22334521997285257194387719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14889681331523504796258479 22334521997285257194387719)
    ·
      refine ⟨33501782995927885791581579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22334521997285257194387719 33501782995927885791581579)
      ·
        refine ⟨50252674493891828687372369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33501782995927885791581579 50252674493891828687372369)
        ·
          refine ⟨37689505870418871515529277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50252674493891828687372369 37689505870418871515529277)
          ·
            refine ⟨14133564701407076818323479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37689505870418871515529277 14133564701407076818323479)
            ·
              refine ⟨21200347052110615227485219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14133564701407076818323479 21200347052110615227485219)
              ·
                refine ⟨31800520578165922841227829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21200347052110615227485219 31800520578165922841227829)
                ·
                  refine ⟨2981298804203055266365109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 31800520578165922841227829 2981298804203055266365109)
                  ·
                    refine ⟨279496762894036431221729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2981298804203055266365109 279496762894036431221729)
                    ·
                      rfl

theorem cell23_1632954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 1, 5, 5].length) (baseStart_1632954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1632954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1632954 prefixEnd_1632954 := by exact prefixLift 1632954
  have htrace : WordTrace (prefixWord ++ tailWord_1632954) baseStart_1632954 baseEnd_1632954 := by
    simpa [prefixWord, tailWord_1632954, baseEnd_1632954] using wordTrace_append hprefix tailTrace_1632954
  have hstable : (prefixWord ++ tailWord_1632954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1632954).length < 2 ^ (prefixWord ++ tailWord_1632954).sum := by decide
  have hdescent : baseEnd_1632954 < baseStart_1632954 := by decide
  rcases family_descends (prefixWord ++ tailWord_1632954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1632968 : List Nat := [2, 1, 3, 1, 2, 4, 1, 2, 3, 1, 3]
def baseStart_1632968 : Nat := 118140960795 + 1632968 * 2 ^ 59
def prefixEnd_1632968 : Nat := 4983230072969 + 3 ^ 40 * 1632968 * 2
def baseEnd_1632968 : Nat := 838497477411272238890123

theorem tailTrace_1632968 : CollatzResearch.WordTrace tailWord_1632968 prefixEnd_1632968 838497477411272238890123 := by
  unfold tailWord_1632968
  simp only [CollatzResearch.WordTrace]
  refine ⟨29779617974021649788021779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39706157298695533050695705 29779617974021649788021779)
  ·
    refine ⟨44669426961032474682032669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29779617974021649788021779 44669426961032474682032669)
    ·
      refine ⟨16751035110387178005762251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44669426961032474682032669 16751035110387178005762251)
      ·
        refine ⟨25126552665580767008643377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16751035110387178005762251 25126552665580767008643377)
        ·
          refine ⟨18844914499185575256482533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25126552665580767008643377 18844914499185575256482533)
          ·
            refine ⟨3533421468597295360590475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18844914499185575256482533 3533421468597295360590475)
            ·
              refine ⟨5300132202895943040885713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3533421468597295360590475 5300132202895943040885713)
              ·
                refine ⟨3975099152171957280664285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5300132202895943040885713 3975099152171957280664285)
                ·
                  refine ⟨1490662182064483980249107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3975099152171957280664285 1490662182064483980249107)
                  ·
                    refine ⟨2235993273096725970373661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1490662182064483980249107 2235993273096725970373661)
                    ·
                      refine ⟨838497477411272238890123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2235993273096725970373661 838497477411272238890123)
                      ·
                        rfl

theorem cell23_1632968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 1, 2, 3, 1, 3].length) (baseStart_1632968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1632968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1632968 prefixEnd_1632968 := by exact prefixLift 1632968
  have htrace : WordTrace (prefixWord ++ tailWord_1632968) baseStart_1632968 baseEnd_1632968 := by
    simpa [prefixWord, tailWord_1632968, baseEnd_1632968] using wordTrace_append hprefix tailTrace_1632968
  have hstable : (prefixWord ++ tailWord_1632968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1632968).length < 2 ^ (prefixWord ++ tailWord_1632968).sum := by decide
  have hdescent : baseEnd_1632968 < baseStart_1632968 := by decide
  rcases family_descends (prefixWord ++ tailWord_1632968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1632985 : List Nat := [1, 2, 1, 2, 3, 2, 4, 3, 1, 1, 3]
def baseStart_1632985 : Nat := 118140960795 + 1632985 * 2 ^ 59
def prefixEnd_1632985 : Nat := 4983230072969 + 3 ^ 40 * 1632985 * 2
def baseEnd_1632985 : Nat := 838506206582398672377545

theorem tailTrace_1632985 : CollatzResearch.WordTrace tailWord_1632985 prefixEnd_1632985 838506206582398672377545 := by
  unfold tailWord_1632985
  simp only [CollatzResearch.WordTrace]
  refine ⟨59559855988981711479412409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39706570659321140986274939 59559855988981711479412409)
  ·
    refine ⟨44669891991736283609559307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59559855988981711479412409 44669891991736283609559307)
    ·
      refine ⟨67004837987604425414338961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44669891991736283609559307 67004837987604425414338961)
      ·
        refine ⟨50253628490703319060754221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67004837987604425414338961 50253628490703319060754221)
        ·
          refine ⟨18845110684013744647782833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50253628490703319060754221 18845110684013744647782833)
          ·
            refine ⟨14133833013010308485837125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18845110684013744647782833 14133833013010308485837125)
            ·
              refine ⟨2650093689939432841094461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14133833013010308485837125 2650093689939432841094461)
              ·
                refine ⟨993785133727287315410423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2650093689939432841094461 993785133727287315410423)
                ·
                  refine ⟨1490677700590930973115635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 993785133727287315410423 1490677700590930973115635)
                  ·
                    refine ⟨2236016550886396459673453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1490677700590930973115635 2236016550886396459673453)
                    ·
                      refine ⟨838506206582398672377545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2236016550886396459673453 838506206582398672377545)
                      ·
                        rfl

theorem cell23_1632985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 4, 3, 1, 1, 3].length) (baseStart_1632985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1632985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1632985 prefixEnd_1632985 := by exact prefixLift 1632985
  have htrace : WordTrace (prefixWord ++ tailWord_1632985) baseStart_1632985 baseEnd_1632985 := by
    simpa [prefixWord, tailWord_1632985, baseEnd_1632985] using wordTrace_append hprefix tailTrace_1632985
  have hstable : (prefixWord ++ tailWord_1632985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1632985).length < 2 ^ (prefixWord ++ tailWord_1632985).sum := by decide
  have hdescent : baseEnd_1632985 < baseStart_1632985 := by decide
  rcases family_descends (prefixWord ++ tailWord_1632985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1633004 : List Nat := [2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 6]
def baseStart_1633004 : Nat := 118140960795 + 1633004 * 2 ^ 59
def prefixEnd_1633004 : Nat := 4983230072969 + 3 ^ 40 * 1633004 * 2
def baseEnd_1633004 : Nat := 838515962714834098039957

theorem tailTrace_1633004 : CollatzResearch.WordTrace tailWord_1633004 prefixEnd_1633004 838515962714834098039957 := by
  unfold tailWord_1633004
  simp only [CollatzResearch.WordTrace]
  refine ⟨29780274487956438862177033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39707032650608585149569377 29780274487956438862177033)
  ·
    refine ⟨22335205865967329146632775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29780274487956438862177033 22335205865967329146632775)
    ·
      refine ⟨33502808798950993719949163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22335205865967329146632775 33502808798950993719949163)
      ·
        refine ⟨50254213198426490579923745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33502808798950993719949163 50254213198426490579923745)
        ·
          refine ⟨37690659898819867934942809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50254213198426490579923745 37690659898819867934942809)
          ·
            refine ⟨28267994924114900951207107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37690659898819867934942809 28267994924114900951207107)
            ·
              refine ⟨42401992386172351426810661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28267994924114900951207107 42401992386172351426810661)
              ·
                refine ⟨7950373572407315892526999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42401992386172351426810661 7950373572407315892526999)
                ·
                  refine ⟨11925560358610973838790499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7950373572407315892526999 11925560358610973838790499)
                  ·
                    refine ⟨17888340537916460758185749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11925560358610973838790499 17888340537916460758185749)
                    ·
                      refine ⟨838515962714834098039957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 17888340537916460758185749 838515962714834098039957)
                      ·
                        rfl

theorem cell23_1633004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 6].length) (baseStart_1633004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1633004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1633004 prefixEnd_1633004 := by exact prefixLift 1633004
  have htrace : WordTrace (prefixWord ++ tailWord_1633004) baseStart_1633004 baseEnd_1633004 := by
    simpa [prefixWord, tailWord_1633004, baseEnd_1633004] using wordTrace_append hprefix tailTrace_1633004
  have hstable : (prefixWord ++ tailWord_1633004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1633004).length < 2 ^ (prefixWord ++ tailWord_1633004).sum := by decide
  have hdescent : baseEnd_1633004 < baseStart_1633004 := by decide
  rcases family_descends (prefixWord ++ tailWord_1633004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1633031 : List Nat := [1, 1, 4, 4, 1, 2, 1, 9]
def baseStart_1633031 : Nat := 118140960795 + 1633031 * 2 ^ 59
def prefixEnd_1633031 : Nat := 4983230072969 + 3 ^ 40 * 1633031 * 2
def baseEnd_1633031 : Nat := 31056660247870573792679

theorem tailTrace_1633031 : CollatzResearch.WordTrace tailWord_1633031 prefixEnd_1633031 31056660247870573792679 := by
  unfold tailWord_1633031
  simp only [CollatzResearch.WordTrace]
  refine ⟨59561533746815061335586947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39707689164543374223724631 59561533746815061335586947)
  ·
    refine ⟨89342300620222592003380421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59561533746815061335586947 89342300620222592003380421)
    ·
      refine ⟨16751681366291736000633829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 89342300620222592003380421 16751681366291736000633829)
      ·
        refine ⟨3140940256179700500118843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16751681366291736000633829 3140940256179700500118843)
        ·
          refine ⟨4711410384269550750178265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3140940256179700500118843 4711410384269550750178265)
          ·
            refine ⟨3533557788202163062633699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4711410384269550750178265 3533557788202163062633699)
            ·
              refine ⟨5300336682303244593950549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3533557788202163062633699 5300336682303244593950549)
              ·
                refine ⟨31056660247870573792679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 5300336682303244593950549 31056660247870573792679)
                ·
                  rfl

theorem cell23_1633031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 1, 9].length) (baseStart_1633031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1633031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1633031 prefixEnd_1633031 := by exact prefixLift 1633031
  have htrace : WordTrace (prefixWord ++ tailWord_1633031) baseStart_1633031 baseEnd_1633031 := by
    simpa [prefixWord, tailWord_1633031, baseEnd_1633031] using wordTrace_append hprefix tailTrace_1633031
  have hstable : (prefixWord ++ tailWord_1633031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1633031).length < 2 ^ (prefixWord ++ tailWord_1633031).sum := by decide
  have hdescent : baseEnd_1633031 < baseStart_1633031 := by decide
  rcases family_descends (prefixWord ++ tailWord_1633031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1633041 : List Nat := [1, 2, 2, 1, 1, 3, 2, 4, 1, 3, 3]
def baseStart_1633041 : Nat := 118140960795 + 1633041 * 2 ^ 59
def prefixEnd_1633041 : Nat := 4983230072969 + 3 ^ 40 * 1633041 * 2
def baseEnd_1633041 : Nat := 838534961499050453277287

theorem tailTrace_1633041 : CollatzResearch.WordTrace tailWord_1633041 prefixEnd_1633041 838534961499050453277287 := by
  unfold tailWord_1633041
  simp only [CollatzResearch.WordTrace]
  refine ⟨59561898476778833043450977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39707932317852555362300651 59561898476778833043450977)
  ·
    refine ⟨44671423857584124782588233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59561898476778833043450977 44671423857584124782588233)
    ·
      refine ⟨33503567893188093586941175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44671423857584124782588233 33503567893188093586941175)
      ·
        refine ⟨50255351839782140380411763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33503567893188093586941175 50255351839782140380411763)
        ·
          refine ⟨75383027759673210570617645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50255351839782140380411763 75383027759673210570617645)
          ·
            refine ⟨28268635409877453963981617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75383027759673210570617645 28268635409877453963981617)
            ·
              refine ⟨21201476557408090472986213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28268635409877453963981617 21201476557408090472986213)
              ·
                refine ⟨3975276854514016963684915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21201476557408090472986213 3975276854514016963684915)
                ·
                  refine ⟨5962915281771025445527373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3975276854514016963684915 5962915281771025445527373)
                  ·
                    refine ⟨2236093230664134542072765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5962915281771025445527373 2236093230664134542072765)
                    ·
                      refine ⟨838534961499050453277287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2236093230664134542072765 838534961499050453277287)
                      ·
                        rfl

theorem cell23_1633041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 3, 3].length) (baseStart_1633041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1633041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1633041 prefixEnd_1633041 := by exact prefixLift 1633041
  have htrace : WordTrace (prefixWord ++ tailWord_1633041) baseStart_1633041 baseEnd_1633041 := by
    simpa [prefixWord, tailWord_1633041, baseEnd_1633041] using wordTrace_append hprefix tailTrace_1633041
  have hstable : (prefixWord ++ tailWord_1633041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1633041).length < 2 ^ (prefixWord ++ tailWord_1633041).sum := by decide
  have hdescent : baseEnd_1633041 < baseStart_1633041 := by decide
  rcases family_descends (prefixWord ++ tailWord_1633041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1633068 : List Nat := [2, 2, 1, 1, 1, 4, 2, 2, 3, 3, 2]
def baseStart_1633068 : Nat := 118140960795 + 1633068 * 2 ^ 59
def prefixEnd_1633068 : Nat := 4983230072969 + 3 ^ 40 * 1633068 * 2
def baseEnd_1633068 : Nat := 838548825476721847639663

theorem tailTrace_1633068 : CollatzResearch.WordTrace tailWord_1633068 prefixEnd_1633068 838548825476721847639663 := by
  unfold tailWord_1633068
  simp only [CollatzResearch.WordTrace]
  refine ⟨29781441623840508327341929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39708588831787344436455905 29781441623840508327341929)
  ·
    refine ⟨22336081217880381245506447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29781441623840508327341929 22336081217880381245506447)
    ·
      refine ⟨33504121826820571868259671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22336081217880381245506447 33504121826820571868259671)
      ·
        refine ⟨50256182740230857802389507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33504121826820571868259671 50256182740230857802389507)
        ·
          refine ⟨75384274110346286703584261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50256182740230857802389507 75384274110346286703584261)
          ·
            refine ⟨14134551395689928756922049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 75384274110346286703584261 14134551395689928756922049)
            ·
              refine ⟨10600913546767446567691537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14134551395689928756922049 10600913546767446567691537)
              ·
                refine ⟨7950685160075584925768653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10600913546767446567691537 7950685160075584925768653)
                ·
                  refine ⟨2981506935028344347163245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7950685160075584925768653 2981506935028344347163245)
                  ·
                    refine ⟨1118065100635629130186217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2981506935028344347163245 1118065100635629130186217)
                    ·
                      refine ⟨838548825476721847639663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1118065100635629130186217 838548825476721847639663)
                      ·
                        rfl

theorem cell23_1633068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 3, 2].length) (baseStart_1633068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1633068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1633068 prefixEnd_1633068 := by exact prefixLift 1633068
  have htrace : WordTrace (prefixWord ++ tailWord_1633068) baseStart_1633068 baseEnd_1633068 := by
    simpa [prefixWord, tailWord_1633068, baseEnd_1633068] using wordTrace_append hprefix tailTrace_1633068
  have hstable : (prefixWord ++ tailWord_1633068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1633068).length < 2 ^ (prefixWord ++ tailWord_1633068).sum := by decide
  have hdescent : baseEnd_1633068 < baseStart_1633068 := by decide
  rcases family_descends (prefixWord ++ tailWord_1633068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1633075 : List Nat := [1, 1, 1, 2, 6, 2, 1, 3, 2, 1, 3]
def baseStart_1633075 : Nat := 118140960795 + 1633075 * 2 ^ 59
def prefixEnd_1633075 : Nat := 4983230072969 + 3 ^ 40 * 1633075 * 2
def baseEnd_1633075 : Nat := 838552419841303320252131

theorem tailTrace_1633075 : CollatzResearch.WordTrace tailWord_1633075 prefixEnd_1633075 838552419841303320252131 := by
  unfold tailWord_1633075
  simp only [CollatzResearch.WordTrace]
  refine ⟨59563138558655656850188679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39708759039103771233459119 59563138558655656850188679)
  ·
    refine ⟨89344707837983485275283019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59563138558655656850188679 89344707837983485275283019)
    ·
      refine ⟨134017061756975227912924529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89344707837983485275283019 134017061756975227912924529)
      ·
        refine ⟨100512796317731420934693397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134017061756975227912924529 100512796317731420934693397)
        ·
          refine ⟨4711537327393660356313753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 100512796317731420934693397 4711537327393660356313753)
          ·
            refine ⟨3533652995545245267235315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4711537327393660356313753 3533652995545245267235315)
            ·
              refine ⟨5300479493317867900852973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3533652995545245267235315 5300479493317867900852973)
              ·
                refine ⟨1987679809994200462819865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5300479493317867900852973 1987679809994200462819865)
                ·
                  refine ⟨1490759857495650347114899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1987679809994200462819865 1490759857495650347114899)
                  ·
                    refine ⟨2236139786243475520672349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1490759857495650347114899 2236139786243475520672349)
                    ·
                      refine ⟨838552419841303320252131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2236139786243475520672349 838552419841303320252131)
                      ·
                        rfl

theorem cell23_1633075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 1, 3, 2, 1, 3].length) (baseStart_1633075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1633075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1633075 prefixEnd_1633075 := by exact prefixLift 1633075
  have htrace : WordTrace (prefixWord ++ tailWord_1633075) baseStart_1633075 baseEnd_1633075 := by
    simpa [prefixWord, tailWord_1633075, baseEnd_1633075] using wordTrace_append hprefix tailTrace_1633075
  have hstable : (prefixWord ++ tailWord_1633075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1633075).length < 2 ^ (prefixWord ++ tailWord_1633075).sum := by decide
  have hdescent : baseEnd_1633075 < baseStart_1633075 := by decide
  rcases family_descends (prefixWord ++ tailWord_1633075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1633092 : List Nat := [2, 3, 4, 2, 1, 1, 1, 2, 1, 3, 3]
def baseStart_1633092 : Nat := 118140960795 + 1633092 * 2 ^ 59
def prefixEnd_1633092 : Nat := 4983230072969 + 3 ^ 40 * 1633092 * 2
def baseEnd_1633092 : Nat := 838561149012429753739553

theorem tailTrace_1633092 : CollatzResearch.WordTrace tailWord_1633092 prefixEnd_1633092 838561149012429753739553 := by
  unfold tailWord_1633092
  simp only [CollatzResearch.WordTrace]
  refine ⟨29781879299797034376778765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39709172399729379169038353 29781879299797034376778765)
  ·
    refine ⟨11168204737423887891292037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29781879299797034376778765 11168204737423887891292037)
    ·
      refine ⟨2094038388266978979617257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11168204737423887891292037 2094038388266978979617257)
      ·
        refine ⟨1570528791200234234712943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2094038388266978979617257 1570528791200234234712943)
        ·
          refine ⟨2355793186800351352069415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1570528791200234234712943 2355793186800351352069415)
          ·
            refine ⟨3533689780200527028104123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2355793186800351352069415 3533689780200527028104123)
            ·
              refine ⟨5300534670300790542156185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3533689780200527028104123 5300534670300790542156185)
              ·
                refine ⟨3975401002725592906617139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5300534670300790542156185 3975401002725592906617139)
                ·
                  refine ⟨5963101504088389359925709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3975401002725592906617139 5963101504088389359925709)
                  ·
                    refine ⟨2236163064033146009972141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5963101504088389359925709 2236163064033146009972141)
                    ·
                      refine ⟨838561149012429753739553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2236163064033146009972141 838561149012429753739553)
                      ·
                        rfl

theorem cell23_1633092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 1, 2, 1, 3, 3].length) (baseStart_1633092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1633092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1633092 prefixEnd_1633092 := by exact prefixLift 1633092
  have htrace : WordTrace (prefixWord ++ tailWord_1633092) baseStart_1633092 baseEnd_1633092 := by
    simpa [prefixWord, tailWord_1633092, baseEnd_1633092] using wordTrace_append hprefix tailTrace_1633092
  have hstable : (prefixWord ++ tailWord_1633092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1633092).length < 2 ^ (prefixWord ++ tailWord_1633092).sum := by decide
  have hdescent : baseEnd_1633092 < baseStart_1633092 := by decide
  rcases family_descends (prefixWord ++ tailWord_1633092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1633128 : List Nat := [2, 1, 4, 2, 1, 3, 1, 1, 2, 2, 4]
def baseStart_1633128 : Nat := 118140960795 + 1633128 * 2 ^ 59
def prefixEnd_1633128 : Nat := 4983230072969 + 3 ^ 40 * 1633128 * 2
def baseEnd_1633128 : Nat := 838579634315991612889387

theorem tailTrace_1633128 : CollatzResearch.WordTrace tailWord_1633128 prefixEnd_1633128 838579634315991612889387 := by
  unfold tailWord_1633128
  simp only [CollatzResearch.WordTrace]
  refine ⟨29782535813731823450934019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39710047751642431267912025 29782535813731823450934019)
  ·
    refine ⟨44673803720597735176401029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29782535813731823450934019 44673803720597735176401029)
    ·
      refine ⟨8376338197612075345575193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44673803720597735176401029 8376338197612075345575193)
      ·
        refine ⟨6282253648209056509181395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8376338197612075345575193 6282253648209056509181395)
        ·
          refine ⟨9423380472313584763772093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6282253648209056509181395 9423380472313584763772093)
          ·
            refine ⟨3533767677117594286414535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9423380472313584763772093 3533767677117594286414535)
            ·
              refine ⟨5300651515676391429621803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3533767677117594286414535 5300651515676391429621803)
              ·
                refine ⟨7950977273514587144432705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5300651515676391429621803 7950977273514587144432705)
                ·
                  refine ⟨5963232955135940358324529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7950977273514587144432705 5963232955135940358324529)
                  ·
                    refine ⟨4472424716351955268743397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5963232955135940358324529 4472424716351955268743397)
                    ·
                      refine ⟨838579634315991612889387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4472424716351955268743397 838579634315991612889387)
                      ·
                        rfl

theorem cell23_1633128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 1, 1, 2, 2, 4].length) (baseStart_1633128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1633128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1633128 prefixEnd_1633128 := by exact prefixLift 1633128
  have htrace : WordTrace (prefixWord ++ tailWord_1633128) baseStart_1633128 baseEnd_1633128 := by
    simpa [prefixWord, tailWord_1633128, baseEnd_1633128] using wordTrace_append hprefix tailTrace_1633128
  have hstable : (prefixWord ++ tailWord_1633128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1633128).length < 2 ^ (prefixWord ++ tailWord_1633128).sum := by decide
  have hdescent : baseEnd_1633128 < baseStart_1633128 := by decide
  rcases family_descends (prefixWord ++ tailWord_1633128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1633131 : List Nat := [1, 1, 1, 1, 2, 2, 5, 1, 1, 5, 3]
def baseStart_1633131 : Nat := 118140960795 + 1633131 * 2 ^ 59
def prefixEnd_1633131 : Nat := 4983230072969 + 3 ^ 40 * 1633131 * 2
def baseEnd_1633131 : Nat := 838581174757955101151873

theorem tailTrace_1633131 : CollatzResearch.WordTrace tailWord_1633131 prefixEnd_1633131 838581174757955101151873 := by
  unfold tailWord_1633131
  simp only [CollatzResearch.WordTrace]
  refine ⟨59565181046452778414227247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39710120697635185609484831 59565181046452778414227247)
  ·
    refine ⟨89347771569679167621340871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59565181046452778414227247 89347771569679167621340871)
    ·
      refine ⟨134021657354518751432011307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89347771569679167621340871 134021657354518751432011307)
      ·
        refine ⟨201032486031778127148016961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134021657354518751432011307 201032486031778127148016961)
        ·
          refine ⟨150774364523833595361012721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 201032486031778127148016961 150774364523833595361012721)
          ·
            refine ⟨113080773392875196520759541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 150774364523833595361012721 113080773392875196520759541)
            ·
              refine ⟨10601322505582049673821207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 113080773392875196520759541 10601322505582049673821207)
              ·
                refine ⟨15901983758373074510731811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10601322505582049673821207 15901983758373074510731811)
                ·
                  refine ⟨23852975637559611766097717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15901983758373074510731811 23852975637559611766097717)
                  ·
                    refine ⟨2236216466021213603071661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 23852975637559611766097717 2236216466021213603071661)
                    ·
                      refine ⟨838581174757955101151873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2236216466021213603071661 838581174757955101151873)
                      ·
                        rfl

theorem cell23_1633131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 1, 1, 5, 3].length) (baseStart_1633131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1633131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1633131 prefixEnd_1633131 := by exact prefixLift 1633131
  have htrace : WordTrace (prefixWord ++ tailWord_1633131) baseStart_1633131 baseEnd_1633131 := by
    simpa [prefixWord, tailWord_1633131, baseEnd_1633131] using wordTrace_append hprefix tailTrace_1633131
  have hstable : (prefixWord ++ tailWord_1633131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1633131).length < 2 ^ (prefixWord ++ tailWord_1633131).sum := by decide
  have hdescent : baseEnd_1633131 < baseStart_1633131 := by decide
  rcases family_descends (prefixWord ++ tailWord_1633131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1633208 : List Nat := [2, 1, 2, 1, 2, 4, 2, 1, 1, 4, 3]
def baseStart_1633208 : Nat := 118140960795 + 1633208 * 2 ^ 59
def prefixEnd_1633208 : Nat := 4983230072969 + 3 ^ 40 * 1633208 * 2
def baseEnd_1633208 : Nat := 838620712768351299889019

theorem tailTrace_1633208 : CollatzResearch.WordTrace tailWord_1633208 prefixEnd_1633208 838620712768351299889019 := by
  unfold tailWord_1633208
  simp only [CollatzResearch.WordTrace]
  refine ⟨29783994733586910282390139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39711992978115880376520185 29783994733586910282390139)
  ·
    refine ⟨44675992100380365423585209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29783994733586910282390139 44675992100380365423585209)
    ·
      refine ⟨33506994075285274067688907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44675992100380365423585209 33506994075285274067688907)
      ·
        refine ⟨50260491112927911101533361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33506994075285274067688907 50260491112927911101533361)
        ·
          refine ⟨37695368334695933326150021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50260491112927911101533361 37695368334695933326150021)
          ·
            refine ⟨7067881562755487498653129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37695368334695933326150021 7067881562755487498653129)
            ·
              refine ⟨5300911172066615623989847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7067881562755487498653129 5300911172066615623989847)
              ·
                refine ⟨7951366758099923435984771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5300911172066615623989847 7951366758099923435984771)
                ·
                  refine ⟨11927050137149885153977157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7951366758099923435984771 11927050137149885153977157)
                  ·
                    refine ⟨2236321900715603466370717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11927050137149885153977157 2236321900715603466370717)
                    ·
                      refine ⟨838620712768351299889019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2236321900715603466370717 838620712768351299889019)
                      ·
                        rfl

theorem cell23_1633208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 2, 1, 1, 4, 3].length) (baseStart_1633208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1633208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1633208 prefixEnd_1633208 := by exact prefixLift 1633208
  have htrace : WordTrace (prefixWord ++ tailWord_1633208) baseStart_1633208 baseEnd_1633208 := by
    simpa [prefixWord, tailWord_1633208, baseEnd_1633208] using wordTrace_append hprefix tailTrace_1633208
  have hstable : (prefixWord ++ tailWord_1633208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1633208).length < 2 ^ (prefixWord ++ tailWord_1633208).sum := by decide
  have hdescent : baseEnd_1633208 < baseStart_1633208 := by decide
  rcases family_descends (prefixWord ++ tailWord_1633208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1633215 : List Nat := [1, 1, 2, 2, 2, 1, 2, 7, 1, 4]
def baseStart_1633215 : Nat := 118140960795 + 1633215 * 2 ^ 59
def prefixEnd_1633215 : Nat := 4983230072969 + 3 ^ 40 * 1633215 * 2
def baseEnd_1633215 : Nat := 279541435710977590833829

theorem tailTrace_1633215 : CollatzResearch.WordTrace tailWord_1633215 prefixEnd_1633215 279541435710977590833829 := by
  unfold tailWord_1633215
  simp only [CollatzResearch.WordTrace]
  refine ⟨59568244778148460760285099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39712163185432307173523399 59568244778148460760285099)
  ·
    refine ⟨89352367167222691140427649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59568244778148460760285099 89352367167222691140427649)
    ·
      refine ⟨67014275375417018355320737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89352367167222691140427649 67014275375417018355320737)
      ·
        refine ⟨50260706531562763766490553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67014275375417018355320737 50260706531562763766490553)
        ·
          refine ⟨37695529898672072824867915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50260706531562763766490553 37695529898672072824867915)
          ·
            refine ⟨56543294848008109237301873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37695529898672072824867915 56543294848008109237301873)
            ·
              refine ⟨42407471136006081927976405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56543294848008109237301873 42407471136006081927976405)
              ·
                refine ⟨993925104750142545186947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 42407471136006081927976405 993925104750142545186947)
                ·
                  refine ⟨1490887657125213817780421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 993925104750142545186947 1490887657125213817780421)
                  ·
                    refine ⟨279541435710977590833829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1490887657125213817780421 279541435710977590833829)
                    ·
                      rfl

theorem cell23_1633215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 7, 1, 4].length) (baseStart_1633215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1633215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1633215 prefixEnd_1633215 := by exact prefixLift 1633215
  have htrace : WordTrace (prefixWord ++ tailWord_1633215) baseStart_1633215 baseEnd_1633215 := by
    simpa [prefixWord, tailWord_1633215, baseEnd_1633215] using wordTrace_append hprefix tailTrace_1633215
  have hstable : (prefixWord ++ tailWord_1633215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1633215).length < 2 ^ (prefixWord ++ tailWord_1633215).sum := by decide
  have hdescent : baseEnd_1633215 < baseStart_1633215 := by decide
  rcases family_descends (prefixWord ++ tailWord_1633215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1633228 : List Nat := [2, 2, 1, 4, 1, 1, 2, 4, 6]
def baseStart_1633228 : Nat := 118140960795 + 1633228 * 2 ^ 59
def prefixEnd_1633228 : Nat := 4983230072969 + 3 ^ 40 * 1633228 * 2
def baseEnd_1633228 : Nat := 93181220264604580182103

theorem tailTrace_1633228 : CollatzResearch.WordTrace tailWord_1633228 prefixEnd_1633228 93181220264604580182103 := by
  unfold tailWord_1633228
  simp only [CollatzResearch.WordTrace]
  refine ⟨29784359463550681990254169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39712479284734242653672225 29784359463550681990254169)
  ·
    refine ⟨22338269597663011492690627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29784359463550681990254169 22338269597663011492690627)
    ·
      refine ⟨33507404396494517239035941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22338269597663011492690627 33507404396494517239035941)
      ·
        refine ⟨6282638324342721982319239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33507404396494517239035941 6282638324342721982319239)
        ·
          refine ⟨9423957486514082973478859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6282638324342721982319239 9423957486514082973478859)
          ·
            refine ⟨14135936229771124460218289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9423957486514082973478859 14135936229771124460218289)
            ·
              refine ⟨10601952172328343345163717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14135936229771124460218289 10601952172328343345163717)
              ·
                refine ⟨1987866032311564377218197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10601952172328343345163717 1987866032311564377218197)
                ·
                  refine ⟨93181220264604580182103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1987866032311564377218197 93181220264604580182103)
                  ·
                    rfl

theorem cell23_1633228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 4, 6].length) (baseStart_1633228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1633228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1633228 prefixEnd_1633228 := by exact prefixLift 1633228
  have htrace : WordTrace (prefixWord ++ tailWord_1633228) baseStart_1633228 baseEnd_1633228 := by
    simpa [prefixWord, tailWord_1633228, baseEnd_1633228] using wordTrace_append hprefix tailTrace_1633228
  have hstable : (prefixWord ++ tailWord_1633228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1633228).length < 2 ^ (prefixWord ++ tailWord_1633228).sum := by decide
  have hdescent : baseEnd_1633228 < baseStart_1633228 := by decide
  rcases family_descends (prefixWord ++ tailWord_1633228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1633229 : List Nat := [1, 6, 3, 1, 1, 1, 1, 1, 1, 2, 5]
def baseStart_1633229 : Nat := 118140960795 + 1633229 * 2 ^ 59
def prefixEnd_1633229 : Nat := 4983230072969 + 3 ^ 40 * 1633229 * 2
def baseEnd_1633229 : Nat := 838631495862095717726423

theorem tailTrace_1633229 : CollatzResearch.WordTrace tailWord_1633229 prefixEnd_1633229 838631495862095717726423 := by
  unfold tailWord_1633229
  simp only [CollatzResearch.WordTrace]
  refine ⟨59568755400097741151294741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39712503600065160767529827 59568755400097741151294741)
  ·
    refine ⟨2792285409379581616466941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 59568755400097741151294741 2792285409379581616466941)
    ·
      refine ⟨1047107028517343106175103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2792285409379581616466941 1047107028517343106175103)
      ·
        refine ⟨1570660542776014659262655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1047107028517343106175103 1570660542776014659262655)
        ·
          refine ⟨2355990814164021988893983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1570660542776014659262655 2355990814164021988893983)
          ·
            refine ⟨3533986221246032983340975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2355990814164021988893983 3533986221246032983340975)
            ·
              refine ⟨5300979331869049475011463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3533986221246032983340975 5300979331869049475011463)
              ·
                refine ⟨7951468997803574212517195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5300979331869049475011463 7951468997803574212517195)
                ·
                  refine ⟨11927203496705361318775793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7951468997803574212517195 11927203496705361318775793)
                  ·
                    refine ⟨8945402622529020989081845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11927203496705361318775793 8945402622529020989081845)
                    ·
                      refine ⟨838631495862095717726423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8945402622529020989081845 838631495862095717726423)
                      ·
                        rfl

theorem cell23_1633229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 1, 1, 1, 2, 5].length) (baseStart_1633229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1633229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1633229 prefixEnd_1633229 := by exact prefixLift 1633229
  have htrace : WordTrace (prefixWord ++ tailWord_1633229) baseStart_1633229 baseEnd_1633229 := by
    simpa [prefixWord, tailWord_1633229, baseEnd_1633229] using wordTrace_append hprefix tailTrace_1633229
  have hstable : (prefixWord ++ tailWord_1633229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1633229).length < 2 ^ (prefixWord ++ tailWord_1633229).sum := by decide
  have hdescent : baseEnd_1633229 < baseStart_1633229 := by decide
  rcases family_descends (prefixWord ++ tailWord_1633229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1633245 : List Nat := [1, 4, 3, 1, 2, 2, 1, 3, 6]
def baseStart_1633245 : Nat := 118140960795 + 1633245 * 2 ^ 59
def prefixEnd_1633245 : Nat := 4983230072969 + 3 ^ 40 * 1633245 * 2
def baseEnd_1633245 : Nat := 93182190172507517236261

theorem tailTrace_1633245 : CollatzResearch.WordTrace tailWord_1633245 prefixEnd_1633245 93182190172507517236261 := by
  unfold tailWord_1633245
  simp only [CollatzResearch.WordTrace]
  refine ⟨59569338968039775883877189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39712892645359850589251459 59569338968039775883877189)
  ·
    refine ⟨11169251056507457978226973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 59569338968039775883877189 11169251056507457978226973)
    ·
      refine ⟨4188469146190296741835115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11169251056507457978226973 4188469146190296741835115)
      ·
        refine ⟨6282703719285445112752673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4188469146190296741835115 6282703719285445112752673)
        ·
          refine ⟨4712027789464083834564505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6282703719285445112752673 4712027789464083834564505)
          ·
            refine ⟨3534020842098062875923379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4712027789464083834564505 3534020842098062875923379)
            ·
              refine ⟨5301031263147094313885069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3534020842098062875923379 5301031263147094313885069)
              ·
                refine ⟨1987886723680160367706901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5301031263147094313885069 1987886723680160367706901)
                ·
                  refine ⟨93182190172507517236261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1987886723680160367706901 93182190172507517236261)
                  ·
                    rfl

theorem cell23_1633245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 1, 3, 6].length) (baseStart_1633245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1633245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1633245 prefixEnd_1633245 := by exact prefixLift 1633245
  have htrace : WordTrace (prefixWord ++ tailWord_1633245) baseStart_1633245 baseEnd_1633245 := by
    simpa [prefixWord, tailWord_1633245, baseEnd_1633245] using wordTrace_append hprefix tailTrace_1633245
  have hstable : (prefixWord ++ tailWord_1633245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1633245).length < 2 ^ (prefixWord ++ tailWord_1633245).sum := by decide
  have hdescent : baseEnd_1633245 < baseStart_1633245 := by decide
  rcases family_descends (prefixWord ++ tailWord_1633245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1633272 : List Nat := [2, 1, 2, 1, 1, 3, 1, 7, 1, 1, 3]
def baseStart_1633272 : Nat := 118140960795 + 1633272 * 2 ^ 59
def prefixEnd_1633272 : Nat := 4983230072969 + 3 ^ 40 * 1633272 * 2
def baseEnd_1633272 : Nat := 838653575530239049488725

theorem tailTrace_1633272 : CollatzResearch.WordTrace tailWord_1633272 prefixEnd_1633272 838653575530239049488725 := by
  unfold tailWord_1633272
  simp only [CollatzResearch.WordTrace]
  refine ⟨29785161869470979747555035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39713549159294639663406713 29785161869470979747555035)
  ·
    refine ⟨44677742804206469621332553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29785161869470979747555035 44677742804206469621332553)
    ·
      refine ⟨33508307103154852215999415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44677742804206469621332553 33508307103154852215999415)
      ·
        refine ⟨50262460654732278323999123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33508307103154852215999415 50262460654732278323999123)
        ·
          refine ⟨75393690982098417485998685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50262460654732278323999123 75393690982098417485998685)
          ·
            refine ⟨28272634118286906557249507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75393690982098417485998685 28272634118286906557249507)
            ·
              refine ⟨42408951177430359835874261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28272634118286906557249507 42408951177430359835874261)
              ·
                refine ⟨993959793221024058653303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 42408951177430359835874261 993959793221024058653303)
                ·
                  refine ⟨1490939689831536087979955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 993959793221024058653303 1490939689831536087979955)
                  ·
                    refine ⟨2236409534747304131969933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1490939689831536087979955 2236409534747304131969933)
                    ·
                      refine ⟨838653575530239049488725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2236409534747304131969933 838653575530239049488725)
                      ·
                        rfl

theorem cell23_1633272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 7, 1, 1, 3].length) (baseStart_1633272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1633272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1633272 prefixEnd_1633272 := by exact prefixLift 1633272
  have htrace : WordTrace (prefixWord ++ tailWord_1633272) baseStart_1633272 baseEnd_1633272 := by
    simpa [prefixWord, tailWord_1633272, baseEnd_1633272] using wordTrace_append hprefix tailTrace_1633272
  have hstable : (prefixWord ++ tailWord_1633272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1633272).length < 2 ^ (prefixWord ++ tailWord_1633272).sum := by decide
  have hdescent : baseEnd_1633272 < baseStart_1633272 := by decide
  rcases family_descends (prefixWord ++ tailWord_1633272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1633305 : List Nat := [1, 2, 1, 2, 1, 1, 6, 3, 2, 4]
def baseStart_1633305 : Nat := 118140960795 + 1633305 * 2 ^ 59
def prefixEnd_1633305 : Nat := 4983230072969 + 3 ^ 40 * 1633305 * 2
def baseEnd_1633305 : Nat := 279556840130612473458691

theorem tailTrace_1633305 : CollatzResearch.WordTrace tailWord_1633305 prefixEnd_1633305 279556840130612473458691 := by
  unfold tailWord_1633305
  simp only [CollatzResearch.WordTrace]
  refine ⟨59571527347822406131061369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39714351565214937420707579 59571527347822406131061369)
  ·
    refine ⟨44678645510866804598296027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59571527347822406131061369 44678645510866804598296027)
    ·
      refine ⟨67017968266300206897444041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44678645510866804598296027 67017968266300206897444041)
      ·
        refine ⟨50263476199725155173083031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67017968266300206897444041 50263476199725155173083031)
        ·
          refine ⟨75395214299587732759624547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50263476199725155173083031 75395214299587732759624547)
          ·
            refine ⟨113092821449381599139436821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75395214299587732759624547 113092821449381599139436821)
            ·
              refine ⟨5301226005439762459661101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 113092821449381599139436821 5301226005439762459661101)
              ·
                refine ⟨1987959752039910922372913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5301226005439762459661101 1987959752039910922372913)
                ·
                  refine ⟨1490969814029933191779685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1987959752039910922372913 1490969814029933191779685)
                  ·
                    refine ⟨279556840130612473458691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1490969814029933191779685 279556840130612473458691)
                    ·
                      rfl

theorem cell23_1633305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 6, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 6, 3, 2, 4].length) (baseStart_1633305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1633305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1633305 prefixEnd_1633305 := by exact prefixLift 1633305
  have htrace : WordTrace (prefixWord ++ tailWord_1633305) baseStart_1633305 baseEnd_1633305 := by
    simpa [prefixWord, tailWord_1633305, baseEnd_1633305] using wordTrace_append hprefix tailTrace_1633305
  have hstable : (prefixWord ++ tailWord_1633305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1633305).length < 2 ^ (prefixWord ++ tailWord_1633305).sum := by decide
  have hdescent : baseEnd_1633305 < baseStart_1633305 := by decide
  rcases family_descends (prefixWord ++ tailWord_1633305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1633315 : List Nat := [1, 1, 1, 4, 3, 2, 2, 1, 3, 2, 3]
def baseStart_1633315 : Nat := 118140960795 + 1633315 * 2 ^ 59
def prefixEnd_1633315 : Nat := 4983230072969 + 3 ^ 40 * 1633315 * 2
def baseEnd_1633315 : Nat := 838675655198382381251027

theorem tailTrace_1633315 : CollatzResearch.WordTrace tailWord_1633315 prefixEnd_1633315 838675655198382381251027 := by
  unfold tailWord_1633315
  simp only [CollatzResearch.WordTrace]
  refine ⟨59571892077786177838925399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39714594718524118559283599 59571892077786177838925399)
  ·
    refine ⟨89357838116679266758388099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59571892077786177838925399 89357838116679266758388099)
    ·
      refine ⟨134036757175018900137582149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89357838116679266758388099 134036757175018900137582149)
      ·
        refine ⟨25131891970316043775796653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 134036757175018900137582149 25131891970316043775796653)
        ·
          refine ⟨9424459488868516415923745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25131891970316043775796653 9424459488868516415923745)
          ·
            refine ⟨7068344616651387311942809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9424459488868516415923745 7068344616651387311942809)
            ·
              refine ⟨5301258462488540483957107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7068344616651387311942809 5301258462488540483957107)
              ·
                refine ⟨7951887693732810725935661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5301258462488540483957107 7951887693732810725935661)
                ·
                  refine ⟨2981957885149804022225873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7951887693732810725935661 2981957885149804022225873)
                  ·
                    refine ⟨2236468413862353016669405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2981957885149804022225873 2236468413862353016669405)
                    ·
                      refine ⟨838675655198382381251027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2236468413862353016669405 838675655198382381251027)
                      ·
                        rfl

theorem cell23_1633315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 2, 1, 3, 2, 3].length) (baseStart_1633315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1633315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1633315 prefixEnd_1633315 := by exact prefixLift 1633315
  have htrace : WordTrace (prefixWord ++ tailWord_1633315) baseStart_1633315 baseEnd_1633315 := by
    simpa [prefixWord, tailWord_1633315, baseEnd_1633315] using wordTrace_append hprefix tailTrace_1633315
  have hstable : (prefixWord ++ tailWord_1633315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1633315).length < 2 ^ (prefixWord ++ tailWord_1633315).sum := by decide
  have hdescent : baseEnd_1633315 < baseStart_1633315 := by decide
  rcases family_descends (prefixWord ++ tailWord_1633315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1633362 : List Nat := [3, 2, 2, 1, 3, 1, 3, 1, 1, 3, 3]
def baseStart_1633362 : Nat := 118140960795 + 1633362 * 2 ^ 59
def prefixEnd_1633362 : Nat := 4983230072969 + 3 ^ 40 * 1633362 * 2
def baseEnd_1633362 : Nat := 838699788789143697363311

theorem tailTrace_1633362 : CollatzResearch.WordTrace tailWord_1633362 prefixEnd_1633362 838699788789143697363311 := by
  unfold tailWord_1633362
  simp only [CollatzResearch.WordTrace]
  refine ⟨14893401577153976216471585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39715737539077269910590893 14893401577153976216471585)
  ·
    refine ⟨11170051182865482162353689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14893401577153976216471585 11170051182865482162353689)
    ·
      refine ⟨8377538387149111621765267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11170051182865482162353689 8377538387149111621765267)
      ·
        refine ⟨12566307580723667432647901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8377538387149111621765267 12566307580723667432647901)
        ·
          refine ⟨4712365342771375287242963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12566307580723667432647901 4712365342771375287242963)
          ·
            refine ⟨7068548014157062930864445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4712365342771375287242963 7068548014157062930864445)
            ·
              refine ⟨2650705505308898599074167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7068548014157062930864445 2650705505308898599074167)
              ·
                refine ⟨3976058257963347898611251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2650705505308898599074167 3976058257963347898611251)
                ·
                  refine ⟨5964087386945021847916877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3976058257963347898611251 5964087386945021847916877)
                  ·
                    refine ⟨2236532770104383192968829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5964087386945021847916877 2236532770104383192968829)
                    ·
                      refine ⟨838699788789143697363311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2236532770104383192968829 838699788789143697363311)
                      ·
                        rfl

theorem cell23_1633362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 3, 1, 1, 3, 3].length) (baseStart_1633362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1633362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1633362 prefixEnd_1633362 := by exact prefixLift 1633362
  have htrace : WordTrace (prefixWord ++ tailWord_1633362) baseStart_1633362 baseEnd_1633362 := by
    simpa [prefixWord, tailWord_1633362, baseEnd_1633362] using wordTrace_append hprefix tailTrace_1633362
  have hstable : (prefixWord ++ tailWord_1633362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1633362).length < 2 ^ (prefixWord ++ tailWord_1633362).sum := by decide
  have hdescent : baseEnd_1633362 < baseStart_1633362 := by decide
  rcases family_descends (prefixWord ++ tailWord_1633362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1633389 : List Nat := [1, 5, 1, 1, 2, 2, 2, 3, 1, 3, 2]
def baseStart_1633389 : Nat := 118140960795 + 1633389 * 2 ^ 59
def prefixEnd_1633389 : Nat := 4983230072969 + 3 ^ 40 * 1633389 * 2
def baseEnd_1633389 : Nat := 838713652766815091725687

theorem tailTrace_1633389 : CollatzResearch.WordTrace tailWord_1633389 prefixEnd_1633389 838713652766815091725687 := by
  unfold tailWord_1633389
  simp only [CollatzResearch.WordTrace]
  refine ⟨59574591079518088477119221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39716394053012058984746147 59574591079518088477119221)
  ·
    refine ⟨5585117913704820794729927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 59574591079518088477119221 5585117913704820794729927)
    ·
      refine ⟨8377676870557231192094891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5585117913704820794729927 8377676870557231192094891)
      ·
        refine ⟨12566515305835846788142337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8377676870557231192094891 12566515305835846788142337)
        ·
          refine ⟨9424886479376885091106753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12566515305835846788142337 9424886479376885091106753)
          ·
            refine ⟨7068664859532663818330065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9424886479376885091106753 7068664859532663818330065)
            ·
              refine ⟨5301498644649497863747549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7068664859532663818330065 5301498644649497863747549)
              ·
                refine ⟨1988061991743561698905331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5301498644649497863747549 1988061991743561698905331)
                ·
                  refine ⟨2982092987615342548357997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1988061991743561698905331 2982092987615342548357997)
                  ·
                    refine ⟨1118284870355753455634249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2982092987615342548357997 1118284870355753455634249)
                    ·
                      refine ⟨838713652766815091725687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1118284870355753455634249 838713652766815091725687)
                      ·
                        rfl

theorem cell23_1633389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 2, 3, 1, 3, 2].length) (baseStart_1633389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1633389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1633389 prefixEnd_1633389 := by exact prefixLift 1633389
  have htrace : WordTrace (prefixWord ++ tailWord_1633389) baseStart_1633389 baseEnd_1633389 := by
    simpa [prefixWord, tailWord_1633389, baseEnd_1633389] using wordTrace_append hprefix tailTrace_1633389
  have hstable : (prefixWord ++ tailWord_1633389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1633389).length < 2 ^ (prefixWord ++ tailWord_1633389).sum := by decide
  have hdescent : baseEnd_1633389 < baseStart_1633389 := by decide
  rcases family_descends (prefixWord ++ tailWord_1633389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1633405 : List Nat := [1, 4, 1, 1, 3, 1, 2, 1, 2, 4, 3]
def baseStart_1633405 : Nat := 118140960795 + 1633405 * 2 ^ 59
def prefixEnd_1633405 : Nat := 4983230072969 + 3 ^ 40 * 1633405 * 2
def baseEnd_1633405 : Nat := 838721868457287029125613

theorem tailTrace_1633405 : CollatzResearch.WordTrace tailWord_1633405 prefixEnd_1633405 838721868457287029125613 := by
  unfold tailWord_1633405
  simp only [CollatzResearch.WordTrace]
  refine ⟨59575174647460123209701669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39716783098306748806467779 59575174647460123209701669)
  ·
    refine ⟨11170345246398773101819063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 59575174647460123209701669 11170345246398773101819063)
    ·
      refine ⟨16755517869598159652728595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11170345246398773101819063 16755517869598159652728595)
      ·
        refine ⟨25133276804397239479092893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16755517869598159652728595 25133276804397239479092893)
        ·
          refine ⟨9424978801648964804659835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25133276804397239479092893 9424978801648964804659835)
          ·
            refine ⟨14137468202473447206989753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9424978801648964804659835 14137468202473447206989753)
            ·
              refine ⟨10603101151855085405242315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14137468202473447206989753 10603101151855085405242315)
              ·
                refine ⟨15904651727782628107863473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10603101151855085405242315 15904651727782628107863473)
                ·
                  refine ⟨11928488795836971080897605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15904651727782628107863473 11928488795836971080897605)
                  ·
                    refine ⟨2236591649219432077668301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11928488795836971080897605 2236591649219432077668301)
                    ·
                      refine ⟨838721868457287029125613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2236591649219432077668301 838721868457287029125613)
                      ·
                        rfl

theorem cell23_1633405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 1, 2, 4, 3].length) (baseStart_1633405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1633405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1633405 prefixEnd_1633405 := by exact prefixLift 1633405
  have htrace : WordTrace (prefixWord ++ tailWord_1633405) baseStart_1633405 baseEnd_1633405 := by
    simpa [prefixWord, tailWord_1633405, baseEnd_1633405] using wordTrace_append hprefix tailTrace_1633405
  have hstable : (prefixWord ++ tailWord_1633405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1633405).length < 2 ^ (prefixWord ++ tailWord_1633405).sum := by decide
  have hdescent : baseEnd_1633405 < baseStart_1633405 := by decide
  rcases family_descends (prefixWord ++ tailWord_1633405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1633413 : List Nat := [1, 3, 1, 1, 7, 1, 2, 1, 2, 1, 3]
def baseStart_1633413 : Nat := 118140960795 + 1633413 * 2 ^ 59
def prefixEnd_1633413 : Nat := 4983230072969 + 3 ^ 40 * 1633413 * 2
def baseEnd_1633413 : Nat := 838725976302522997825577

theorem tailTrace_1633413 : CollatzResearch.WordTrace tailWord_1633413 prefixEnd_1633413 838725976302522997825577 := by
  unfold tailWord_1633413
  simp only [CollatzResearch.WordTrace]
  refine ⟨59575466431431140575992893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39716977620954093717328595 59575466431431140575992893)
  ·
    refine ⟨22340799911786677715997335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59575466431431140575992893 22340799911786677715997335)
    ·
      refine ⟨33511199867680016573996003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22340799911786677715997335 33511199867680016573996003)
      ·
        refine ⟨50266799801520024860994005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33511199867680016573996003 50266799801520024860994005)
        ·
          refine ⟨1178128120348125582679547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 50266799801520024860994005 1178128120348125582679547)
          ·
            refine ⟨1767192180522188374019321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1178128120348125582679547 1767192180522188374019321)
            ·
              refine ⟨1325394135391641280514491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1767192180522188374019321 1325394135391641280514491)
              ·
                refine ⟨1988091203087461920771737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1325394135391641280514491 1988091203087461920771737)
                ·
                  refine ⟨1491068402315596440578803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1988091203087461920771737 1491068402315596440578803)
                  ·
                    refine ⟨2236602603473394660868205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1491068402315596440578803 2236602603473394660868205)
                    ·
                      refine ⟨838725976302522997825577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2236602603473394660868205 838725976302522997825577)
                      ·
                        rfl

theorem cell23_1633413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 7, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 7, 1, 2, 1, 2, 1, 3].length) (baseStart_1633413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1633413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1633413 prefixEnd_1633413 := by exact prefixLift 1633413
  have htrace : WordTrace (prefixWord ++ tailWord_1633413) baseStart_1633413 baseEnd_1633413 := by
    simpa [prefixWord, tailWord_1633413, baseEnd_1633413] using wordTrace_append hprefix tailTrace_1633413
  have hstable : (prefixWord ++ tailWord_1633413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1633413).length < 2 ^ (prefixWord ++ tailWord_1633413).sum := by decide
  have hdescent : baseEnd_1633413 < baseStart_1633413 := by decide
  rcases family_descends (prefixWord ++ tailWord_1633413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1633453 : List Nat := [1, 5, 2, 1, 3, 1, 2, 2, 2, 2, 2]
def baseStart_1633453 : Nat := 118140960795 + 1633453 * 2 ^ 59
def prefixEnd_1633453 : Nat := 4983230072969 + 3 ^ 40 * 1633453 * 2
def baseEnd_1633453 : Nat := 838746515528702841325393

theorem tailTrace_1633453 : CollatzResearch.WordTrace tailWord_1633453 prefixEnd_1633453 838746515528702841325393 := by
  unfold tailWord_1633453
  simp only [CollatzResearch.WordTrace]
  refine ⟨59576925351286227407449013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39717950234190818271632675 59576925351286227407449013)
  ·
    refine ⟨5585336751683083819448345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 59576925351286227407449013 5585336751683083819448345)
    ·
      refine ⟨4189002563762312864586259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5585336751683083819448345 4189002563762312864586259)
      ·
        refine ⟨6283503845643469296879389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4189002563762312864586259 6283503845643469296879389)
        ·
          refine ⟨2356313942116300986329771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6283503845643469296879389 2356313942116300986329771)
          ·
            refine ⟨3534470913174451479494657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2356313942116300986329771 3534470913174451479494657)
            ·
              refine ⟨2650853184880838609620993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3534470913174451479494657 2650853184880838609620993)
              ·
                refine ⟨1988139888660628957215745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2650853184880838609620993 1988139888660628957215745)
                ·
                  refine ⟨1491104916495471717911809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1988139888660628957215745 1491104916495471717911809)
                  ·
                    refine ⟨1118328687371603788433857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1491104916495471717911809 1118328687371603788433857)
                    ·
                      refine ⟨838746515528702841325393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1118328687371603788433857 838746515528702841325393)
                      ·
                        rfl

theorem cell23_1633453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 2, 2, 2, 2, 2].length) (baseStart_1633453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1633453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1633453 prefixEnd_1633453 := by exact prefixLift 1633453
  have htrace : WordTrace (prefixWord ++ tailWord_1633453) baseStart_1633453 baseEnd_1633453 := by
    simpa [prefixWord, tailWord_1633453, baseEnd_1633453] using wordTrace_append hprefix tailTrace_1633453
  have hstable : (prefixWord ++ tailWord_1633453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1633453).length < 2 ^ (prefixWord ++ tailWord_1633453).sum := by decide
  have hdescent : baseEnd_1633453 < baseStart_1633453 := by decide
  rcases family_descends (prefixWord ++ tailWord_1633453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1633455 : List Nat := [1, 1, 2, 1, 2, 3, 4, 2, 2, 5]
def baseStart_1633455 : Nat := 118140960795 + 1633455 * 2 ^ 59
def prefixEnd_1633455 : Nat := 4983230072969 + 3 ^ 40 * 1633455 * 2
def baseEnd_1633455 : Nat := 279582514163337277833461

theorem tailTrace_1633455 : CollatzResearch.WordTrace tailWord_1633455 prefixEnd_1633455 279582514163337277833461 := by
  unfold tailWord_1633455
  simp only [CollatzResearch.WordTrace]
  refine ⟨59576998297278981749021819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39717998864852654499347879 59576998297278981749021819)
  ·
    refine ⟨89365497445918472623532729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59576998297278981749021819 89365497445918472623532729)
    ·
      refine ⟨67024123084438854467649547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89365497445918472623532729 67024123084438854467649547)
      ·
        refine ⟨100536184626658281701474321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67024123084438854467649547 100536184626658281701474321)
        ·
          refine ⟨75402138469993711276105741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100536184626658281701474321 75402138469993711276105741)
          ·
            refine ⟨28275801926247641728539653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75402138469993711276105741 28275801926247641728539653)
            ·
              refine ⟨5301712861171432824101185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28275801926247641728539653 5301712861171432824101185)
              ·
                refine ⟨3976284645878574618075889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5301712861171432824101185 3976284645878574618075889)
                ·
                  refine ⟨2982213484408930963556917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3976284645878574618075889 2982213484408930963556917)
                  ·
                    refine ⟨279582514163337277833461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2982213484408930963556917 279582514163337277833461)
                    ·
                      rfl

theorem cell23_1633455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 4, 2, 2, 5].length) (baseStart_1633455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1633455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1633455 prefixEnd_1633455 := by exact prefixLift 1633455
  have htrace : WordTrace (prefixWord ++ tailWord_1633455) baseStart_1633455 baseEnd_1633455 := by
    simpa [prefixWord, tailWord_1633455, baseEnd_1633455] using wordTrace_append hprefix tailTrace_1633455
  have hstable : (prefixWord ++ tailWord_1633455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1633455).length < 2 ^ (prefixWord ++ tailWord_1633455).sum := by decide
  have hdescent : baseEnd_1633455 < baseStart_1633455 := by decide
  rcases family_descends (prefixWord ++ tailWord_1633455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1633465 : List Nat := [1, 2, 1, 4, 1, 3, 2, 1, 1, 2, 5]
def baseStart_1633465 : Nat := 118140960795 + 1633465 * 2 ^ 59
def prefixEnd_1633465 : Nat := 4983230072969 + 3 ^ 40 * 1633465 * 2
def baseEnd_1633465 : Nat := 838752677296556794375337

theorem tailTrace_1633465 : CollatzResearch.WordTrace tailWord_1633465 prefixEnd_1633465 838752677296556794375337 := by
  unfold tailWord_1633465
  simp only [CollatzResearch.WordTrace]
  refine ⟨59577363027242753456885849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39718242018161835637923899 59577363027242753456885849)
  ·
    refine ⟨44683022270432065092664387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59577363027242753456885849 44683022270432065092664387)
    ·
      refine ⟨67024533405648097638996581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44683022270432065092664387 67024533405648097638996581)
      ·
        refine ⟨12567100013559018307311859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 67024533405648097638996581 12567100013559018307311859)
        ·
          refine ⟨18850650020338527460967789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12567100013559018307311859 18850650020338527460967789)
          ·
            refine ⟨7068993757626947797862921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18850650020338527460967789 7068993757626947797862921)
            ·
              refine ⟨5301745318220210848397191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7068993757626947797862921 5301745318220210848397191)
              ·
                refine ⟨7952617977330316272595787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5301745318220210848397191 7952617977330316272595787)
                ·
                  refine ⟨11928926965995474408893681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7952617977330316272595787 11928926965995474408893681)
                  ·
                    refine ⟨8946695224496605806670261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11928926965995474408893681 8946695224496605806670261)
                    ·
                      refine ⟨838752677296556794375337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8946695224496605806670261 838752677296556794375337)
                      ·
                        rfl

theorem cell23_1633465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 2, 1, 1, 2, 5].length) (baseStart_1633465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1633465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1633465 prefixEnd_1633465 := by exact prefixLift 1633465
  have htrace : WordTrace (prefixWord ++ tailWord_1633465) baseStart_1633465 baseEnd_1633465 := by
    simpa [prefixWord, tailWord_1633465, baseEnd_1633465] using wordTrace_append hprefix tailTrace_1633465
  have hstable : (prefixWord ++ tailWord_1633465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1633465).length < 2 ^ (prefixWord ++ tailWord_1633465).sum := by decide
  have hdescent : baseEnd_1633465 < baseStart_1633465 := by decide
  rcases family_descends (prefixWord ++ tailWord_1633465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1633505 : List Nat := [1, 2, 3, 1, 3, 2, 1, 1, 2, 1, 6]
def baseStart_1633505 : Nat := 118140960795 + 1633505 * 2 ^ 59
def prefixEnd_1633505 : Nat := 4983230072969 + 3 ^ 40 * 1633505 * 2
def baseEnd_1633505 : Nat := 838773216522736637875153

theorem tailTrace_1633505 : CollatzResearch.WordTrace tailWord_1633505 prefixEnd_1633505 838773216522736637875153 := by
  unfold tailWord_1633505
  simp only [CollatzResearch.WordTrace]
  refine ⟨59578821947097840288341969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39719214631398560192227979 59578821947097840288341969)
  ·
    refine ⟨44684116460323380216256477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59578821947097840288341969 44684116460323380216256477)
    ·
      refine ⟨16756543672621267581096179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44684116460323380216256477 16756543672621267581096179)
      ·
        refine ⟨25134815508931901371644269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16756543672621267581096179 25134815508931901371644269)
        ·
          refine ⟨9425555815849463014366601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25134815508931901371644269 9425555815849463014366601)
          ·
            refine ⟨7069166861887097260774951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9425555815849463014366601 7069166861887097260774951)
            ·
              refine ⟨10603750292830645891162427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7069166861887097260774951 10603750292830645891162427)
              ·
                refine ⟨15905625439245968836743641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10603750292830645891162427 15905625439245968836743641)
                ·
                  refine ⟨11929219079434476627557731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15905625439245968836743641 11929219079434476627557731)
                  ·
                    refine ⟨17893828619151714941336597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11929219079434476627557731 17893828619151714941336597)
                    ·
                      refine ⟨838773216522736637875153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 17893828619151714941336597 838773216522736637875153)
                      ·
                        rfl

theorem cell23_1633505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 1, 2, 1, 6].length) (baseStart_1633505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1633505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1633505 prefixEnd_1633505 := by exact prefixLift 1633505
  have htrace : WordTrace (prefixWord ++ tailWord_1633505) baseStart_1633505 baseEnd_1633505 := by
    simpa [prefixWord, tailWord_1633505, baseEnd_1633505] using wordTrace_append hprefix tailTrace_1633505
  have hstable : (prefixWord ++ tailWord_1633505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1633505).length < 2 ^ (prefixWord ++ tailWord_1633505).sum := by decide
  have hdescent : baseEnd_1633505 < baseStart_1633505 := by decide
  rcases family_descends (prefixWord ++ tailWord_1633505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1633512 : List Nat := [2, 1, 4, 1, 2, 1, 2, 1, 4, 2, 3]
def baseStart_1633512 : Nat := 118140960795 + 1633512 * 2 ^ 59
def prefixEnd_1633512 : Nat := 4983230072969 + 3 ^ 40 * 1633512 * 2
def baseEnd_1633512 : Nat := 838776810887318110487621

theorem tailTrace_1633512 : CollatzResearch.WordTrace tailWord_1633512 prefixEnd_1633512 838776810887318110487621 := by
  unfold tailWord_1633512
  simp only [CollatzResearch.WordTrace]
  refine ⟨29789538629036240241923395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39719384838714986989231193 29789538629036240241923395)
  ·
    refine ⟨44684307943554360362885093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29789538629036240241923395 44684307943554360362885093)
    ·
      refine ⟨8378307739416442568040955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44684307943554360362885093 8378307739416442568040955)
      ·
        refine ⟨12567461609124663852061433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8378307739416442568040955 12567461609124663852061433)
        ·
          refine ⟨9425596206843497889046075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12567461609124663852061433 9425596206843497889046075)
          ·
            refine ⟨14138394310265246833569113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9425596206843497889046075 14138394310265246833569113)
            ·
              refine ⟨10603795732698935125176835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14138394310265246833569113 10603795732698935125176835)
              ·
                refine ⟨15905693599048402687765253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10603795732698935125176835 15905693599048402687765253)
                ·
                  refine ⟨2982317549821575503955985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15905693599048402687765253 2982317549821575503955985)
                  ·
                    refine ⟨2236738162366181627966989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2982317549821575503955985 2236738162366181627966989)
                    ·
                      refine ⟨838776810887318110487621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2236738162366181627966989 838776810887318110487621)
                      ·
                        rfl

theorem cell23_1633512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 1, 4, 2, 3].length) (baseStart_1633512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1633512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1633512 prefixEnd_1633512 := by exact prefixLift 1633512
  have htrace : WordTrace (prefixWord ++ tailWord_1633512) baseStart_1633512 baseEnd_1633512 := by
    simpa [prefixWord, tailWord_1633512, baseEnd_1633512] using wordTrace_append hprefix tailTrace_1633512
  have hstable : (prefixWord ++ tailWord_1633512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1633512).length < 2 ^ (prefixWord ++ tailWord_1633512).sum := by decide
  have hdescent : baseEnd_1633512 < baseStart_1633512 := by decide
  rcases family_descends (prefixWord ++ tailWord_1633512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1633515 : List Nat := [1, 1, 1, 1, 2, 7, 1, 1, 8]
def baseStart_1633515 : Nat := 118140960795 + 1633515 * 2 ^ 59
def prefixEnd_1633515 : Nat := 4983230072969 + 3 ^ 40 * 1633515 * 2
def baseEnd_1633515 : Nat := 93197594592142399861123

theorem tailTrace_1633515 : CollatzResearch.WordTrace tailWord_1633515 prefixEnd_1633515 93197594592142399861123 := by
  unfold tailWord_1633515
  simp only [CollatzResearch.WordTrace]
  refine ⟨59579186677061611996205999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39719457784707741330803999 59579186677061611996205999)
  ·
    refine ⟨89368780015592417994308999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59579186677061611996205999 89368780015592417994308999)
    ·
      refine ⟨134053170023388626991463499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89368780015592417994308999 134053170023388626991463499)
      ·
        refine ⟨201079755035082940487195249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134053170023388626991463499 201079755035082940487195249)
        ·
          refine ⟨150809816276312205365396437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 201079755035082940487195249 150809816276312205365396437)
          ·
            refine ⟨3534605068976067313251479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 150809816276312205365396437 3534605068976067313251479)
            ·
              refine ⟨5301907603464100969877219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3534605068976067313251479 5301907603464100969877219)
              ·
                refine ⟨7952861405196151454815829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5301907603464100969877219 7952861405196151454815829)
                ·
                  refine ⟨93197594592142399861123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 7952861405196151454815829 93197594592142399861123)
                  ·
                    rfl

theorem cell23_1633515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 1, 1, 8].length) (baseStart_1633515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1633515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1633515 prefixEnd_1633515 := by exact prefixLift 1633515
  have htrace : WordTrace (prefixWord ++ tailWord_1633515) baseStart_1633515 baseEnd_1633515 := by
    simpa [prefixWord, tailWord_1633515, baseEnd_1633515] using wordTrace_append hprefix tailTrace_1633515
  have hstable : (prefixWord ++ tailWord_1633515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1633515).length < 2 ^ (prefixWord ++ tailWord_1633515).sum := by decide
  have hdescent : baseEnd_1633515 < baseStart_1633515 := by decide
  rcases family_descends (prefixWord ++ tailWord_1633515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1633519 : List Nat := [1, 1, 2, 1, 7, 1, 2, 1, 3, 4]
def baseStart_1633519 : Nat := 118140960795 + 1633519 * 2 ^ 59
def prefixEnd_1633519 : Nat := 4983230072969 + 3 ^ 40 * 1633519 * 2
def baseEnd_1633519 : Nat := 279593468417299861033363

theorem tailTrace_1633519 : CollatzResearch.WordTrace tailWord_1633519 prefixEnd_1633519 279593468417299861033363 := by
  unfold tailWord_1633519
  simp only [CollatzResearch.WordTrace]
  refine ⟨59579332569047120679351611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39719555046031413786234407 59579332569047120679351611)
  ·
    refine ⟨89368998853570681019027417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59579332569047120679351611 89368998853570681019027417)
    ·
      refine ⟨67026749140178010764270563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89368998853570681019027417 67026749140178010764270563)
      ·
        refine ⟨100540123710267016146405845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67026749140178010764270563 100540123710267016146405845)
        ·
          refine ⟨2356409149459383190931387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 100540123710267016146405845 2356409149459383190931387)
          ·
            refine ⟨3534613724189074786397081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2356409149459383190931387 3534613724189074786397081)
            ·
              refine ⟨2650960293141806089797811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3534613724189074786397081 2650960293141806089797811)
              ·
                refine ⟨3976440439712709134696717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2650960293141806089797811 3976440439712709134696717)
                ·
                  refine ⟨1491165164892265925511269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3976440439712709134696717 1491165164892265925511269)
                  ·
                    refine ⟨279593468417299861033363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1491165164892265925511269 279593468417299861033363)
                    ·
                      rfl

theorem cell23_1633519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 2, 1, 3, 4].length) (baseStart_1633519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1633519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1633519 prefixEnd_1633519 := by exact prefixLift 1633519
  have htrace : WordTrace (prefixWord ++ tailWord_1633519) baseStart_1633519 baseEnd_1633519 := by
    simpa [prefixWord, tailWord_1633519, baseEnd_1633519] using wordTrace_append hprefix tailTrace_1633519
  have hstable : (prefixWord ++ tailWord_1633519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1633519).length < 2 ^ (prefixWord ++ tailWord_1633519).sum := by decide
  have hdescent : baseEnd_1633519 < baseStart_1633519 := by decide
  rcases family_descends (prefixWord ++ tailWord_1633519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1633576 : List Nat := [2, 1, 5, 1, 2, 1, 3, 1, 3, 1, 3]
def baseStart_1633576 : Nat := 118140960795 + 1633576 * 2 ^ 59
def prefixEnd_1633576 : Nat := 4983230072969 + 3 ^ 40 * 1633576 * 2
def baseEnd_1633576 : Nat := 838809673649205860087327

theorem tailTrace_1633576 : CollatzResearch.WordTrace tailWord_1633576 prefixEnd_1633576 838809673649205860087327 := by
  unfold tailWord_1633576
  simp only [CollatzResearch.WordTrace]
  refine ⟨29790705764920309707088291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39720941019893746276117721 29790705764920309707088291)
  ·
    refine ⟨44686058647380464560632437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29790705764920309707088291 44686058647380464560632437)
    ·
      refine ⟨4189317998191918552559291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 44686058647380464560632437 4189317998191918552559291)
      ·
        refine ⟨6283976997287877828838937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4189317998191918552559291 6283976997287877828838937)
        ·
          refine ⟨4712982747965908371629203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6283976997287877828838937 4712982747965908371629203)
          ·
            refine ⟨7069474121948862557443805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4712982747965908371629203 7069474121948862557443805)
            ·
              refine ⟨2651052795730823459041427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7069474121948862557443805 2651052795730823459041427)
              ·
                refine ⟨3976579193596235188562141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2651052795730823459041427 3976579193596235188562141)
                ·
                  refine ⟨1491217197598588195710803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3976579193596235188562141 1491217197598588195710803)
                  ·
                    refine ⟨2236825796397882293566205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1491217197598588195710803 2236825796397882293566205)
                    ·
                      refine ⟨838809673649205860087327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2236825796397882293566205 838809673649205860087327)
                      ·
                        rfl

theorem cell23_1633576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 3, 1, 3, 1, 3].length) (baseStart_1633576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1633576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1633576 prefixEnd_1633576 := by exact prefixLift 1633576
  have htrace : WordTrace (prefixWord ++ tailWord_1633576) baseStart_1633576 baseEnd_1633576 := by
    simpa [prefixWord, tailWord_1633576, baseEnd_1633576] using wordTrace_append hprefix tailTrace_1633576
  have hstable : (prefixWord ++ tailWord_1633576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1633576).length < 2 ^ (prefixWord ++ tailWord_1633576).sum := by decide
  have hdescent : baseEnd_1633576 < baseStart_1633576 := by decide
  rcases family_descends (prefixWord ++ tailWord_1633576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1633599 : List Nat := [1, 1, 2, 2, 4, 2, 3, 2, 1, 1, 4]
def baseStart_1633599 : Nat := 118140960795 + 1633599 * 2 ^ 59
def prefixEnd_1633599 : Nat := 4983230072969 + 3 ^ 40 * 1633599 * 2
def baseEnd_1633599 : Nat := 838821483704259270099721

theorem tailTrace_1633599 : CollatzResearch.WordTrace tailWord_1633599 prefixEnd_1633599 838821483704259270099721 := by
  unfold tailWord_1633599
  simp only [CollatzResearch.WordTrace]
  refine ⟨59582250408757294342263851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39721500272504862894842567 59582250408757294342263851)
  ·
    refine ⟨89373375613135941513395777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59582250408757294342263851 89373375613135941513395777)
    ·
      refine ⟨67030031709851956135046833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89373375613135941513395777 67030031709851956135046833)
      ·
        refine ⟨50272523782388967101285125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67030031709851956135046833 50272523782388967101285125)
        ·
          refine ⟨9426098209197931331490961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50272523782388967101285125 9426098209197931331490961)
          ·
            refine ⟨7069573656898448498618221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9426098209197931331490961 7069573656898448498618221)
            ·
              refine ⟨2651090121336918186981833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7069573656898448498618221 2651090121336918186981833)
              ·
                refine ⟨1988317591002688640236375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2651090121336918186981833 1988317591002688640236375)
                ·
                  refine ⟨2982476386504032960354563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1988317591002688640236375 2982476386504032960354563)
                  ·
                    refine ⟨4473714579756049440531845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2982476386504032960354563 4473714579756049440531845)
                    ·
                      refine ⟨838821483704259270099721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4473714579756049440531845 838821483704259270099721)
                      ·
                        rfl

theorem cell23_1633599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 3, 2, 1, 1, 4].length) (baseStart_1633599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1633599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1633599 prefixEnd_1633599 := by exact prefixLift 1633599
  have htrace : WordTrace (prefixWord ++ tailWord_1633599) baseStart_1633599 baseEnd_1633599 := by
    simpa [prefixWord, tailWord_1633599, baseEnd_1633599] using wordTrace_append hprefix tailTrace_1633599
  have hstable : (prefixWord ++ tailWord_1633599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1633599).length < 2 ^ (prefixWord ++ tailWord_1633599).sum := by decide
  have hdescent : baseEnd_1633599 < baseStart_1633599 := by decide
  rcases family_descends (prefixWord ++ tailWord_1633599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1633612 : List Nat := [2, 2, 1, 3, 2, 2, 1, 1, 3, 2, 4]
def baseStart_1633612 : Nat := 118140960795 + 1633612 * 2 ^ 59
def prefixEnd_1633612 : Nat := 4983230072969 + 3 ^ 40 * 1633612 * 2
def baseEnd_1633612 : Nat := 838828158952767719237161

theorem tailTrace_1633612 : CollatzResearch.WordTrace tailWord_1633612 prefixEnd_1633612 838828158952767719237161 := by
  unfold tailWord_1633612
  simp only [CollatzResearch.WordTrace]
  refine ⟨29791362278855098781243545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39721816371806798374991393 29791362278855098781243545)
  ·
    refine ⟨22343521709141324085932659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29791362278855098781243545 22343521709141324085932659)
    ·
      refine ⟨33515282563711986128898989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22343521709141324085932659 33515282563711986128898989)
      ·
        refine ⟨12568230961391994798337121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33515282563711986128898989 12568230961391994798337121)
        ·
          refine ⟨9426173221043996098752841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12568230961391994798337121 9426173221043996098752841)
          ·
            refine ⟨7069629915782997074064631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9426173221043996098752841 7069629915782997074064631)
            ·
              refine ⟨10604444873674495611096947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7069629915782997074064631 10604444873674495611096947)
              ·
                refine ⟨15906667310511743416645421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10604444873674495611096947 15906667310511743416645421)
                ·
                  refine ⟨5965000241441903781242033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15906667310511743416645421 5965000241441903781242033)
                  ·
                    refine ⟨4473750181081427835931525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5965000241441903781242033 4473750181081427835931525)
                    ·
                      refine ⟨838828158952767719237161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4473750181081427835931525 838828158952767719237161)
                      ·
                        rfl

theorem cell23_1633612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 1, 3, 2, 4].length) (baseStart_1633612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1633612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1633612 prefixEnd_1633612 := by exact prefixLift 1633612
  have htrace : WordTrace (prefixWord ++ tailWord_1633612) baseStart_1633612 baseEnd_1633612 := by
    simpa [prefixWord, tailWord_1633612, baseEnd_1633612] using wordTrace_append hprefix tailTrace_1633612
  have hstable : (prefixWord ++ tailWord_1633612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1633612).length < 2 ^ (prefixWord ++ tailWord_1633612).sum := by decide
  have hdescent : baseEnd_1633612 < baseStart_1633612 := by decide
  rcases family_descends (prefixWord ++ tailWord_1633612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1633639 : List Nat := [1, 1, 5, 1, 4, 2, 1, 8]
def baseStart_1633639 : Nat := 118140960795 + 1633639 * 2 ^ 59
def prefixEnd_1633639 : Nat := 4983230072969 + 3 ^ 40 * 1633639 * 2
def baseEnd_1633639 : Nat := 31068223071497744948131

theorem tailTrace_1633639 : CollatzResearch.WordTrace tailWord_1633639 prefixEnd_1633639 31068223071497744948131 := by
  unfold tailWord_1633639
  simp only [CollatzResearch.WordTrace]
  refine ⟨59583709328612381173719971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39722472885741587449146647 59583709328612381173719971)
  ·
    refine ⟨89375563992918571760579957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59583709328612381173719971 89375563992918571760579957)
    ·
      refine ⟨8378959124336116102554371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 89375563992918571760579957 8378959124336116102554371)
      ·
        refine ⟨12568438686504174153831557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8378959124336116102554371 12568438686504174153831557)
        ·
          refine ⟨2356582253719532653843417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12568438686504174153831557 2356582253719532653843417)
          ·
            refine ⟨1767436690289649490382563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2356582253719532653843417 1767436690289649490382563)
            ·
              refine ⟨2651155035434474235573845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1767436690289649490382563 2651155035434474235573845)
              ·
                refine ⟨31068223071497744948131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2651155035434474235573845 31068223071497744948131)
                ·
                  rfl

theorem cell23_1633639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 2, 1, 8].length) (baseStart_1633639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1633639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1633639 prefixEnd_1633639 := by exact prefixLift 1633639
  have htrace : WordTrace (prefixWord ++ tailWord_1633639) baseStart_1633639 baseEnd_1633639 := by
    simpa [prefixWord, tailWord_1633639, baseEnd_1633639] using wordTrace_append hprefix tailTrace_1633639
  have hstable : (prefixWord ++ tailWord_1633639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1633639).length < 2 ^ (prefixWord ++ tailWord_1633639).sum := by decide
  have hdescent : baseEnd_1633639 < baseStart_1633639 := by decide
  rcases family_descends (prefixWord ++ tailWord_1633639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1633659 : List Nat := [1, 1, 1, 1, 1, 6, 1, 3, 3, 3, 2]
def baseStart_1633659 : Nat := 118140960795 + 1633659 * 2 ^ 59
def prefixEnd_1633659 : Nat := 4983230072969 + 3 ^ 40 * 1633659 * 2
def baseEnd_1633659 : Nat := 838852292543529035349445

theorem tailTrace_1633659 : CollatzResearch.WordTrace tailWord_1633659 prefixEnd_1633659 838852292543529035349445 := by
  unfold tailWord_1633659
  simp only [CollatzResearch.WordTrace]
  refine ⟨59584438788539924589448031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39722959192359949726298687 59584438788539924589448031)
  ·
    refine ⟨89376658182809886884172047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59584438788539924589448031 89376658182809886884172047)
    ·
      refine ⟨134064987274214830326258071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89376658182809886884172047 134064987274214830326258071)
      ·
        refine ⟨201097480911322245489387107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134064987274214830326258071 201097480911322245489387107)
        ·
          refine ⟨301646221366983368234080661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 201097480911322245489387107 301646221366983368234080661)
          ·
            refine ⟨14139666626577345385972531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 301646221366983368234080661 14139666626577345385972531)
            ·
              refine ⟨21209499939866018078958797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14139666626577345385972531 21209499939866018078958797)
              ·
                refine ⟨7953562477449756779609549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21209499939866018078958797 7953562477449756779609549)
                ·
                  refine ⟨2982585929043658792353581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7953562477449756779609549 2982585929043658792353581)
                  ·
                    refine ⟨1118469723391372047132593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2982585929043658792353581 1118469723391372047132593)
                    ·
                      refine ⟨838852292543529035349445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1118469723391372047132593 838852292543529035349445)
                      ·
                        rfl

theorem cell23_1633659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 3, 3, 3, 2].length) (baseStart_1633659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1633659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1633659 prefixEnd_1633659 := by exact prefixLift 1633659
  have htrace : WordTrace (prefixWord ++ tailWord_1633659) baseStart_1633659 baseEnd_1633659 := by
    simpa [prefixWord, tailWord_1633659, baseEnd_1633659] using wordTrace_append hprefix tailTrace_1633659
  have hstable : (prefixWord ++ tailWord_1633659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1633659).length < 2 ^ (prefixWord ++ tailWord_1633659).sum := by decide
  have hdescent : baseEnd_1633659 < baseStart_1633659 := by decide
  rcases family_descends (prefixWord ++ tailWord_1633659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1633676 : List Nat := [2, 2, 1, 2, 1, 3, 3, 3, 1, 3, 2]
def baseStart_1633676 : Nat := 118140960795 + 1633676 * 2 ^ 59
def prefixEnd_1633676 : Nat := 4983230072969 + 3 ^ 40 * 1633676 * 2
def baseEnd_1633676 : Nat := 838861021714655468836867

theorem tailTrace_1633676 : CollatzResearch.WordTrace tailWord_1633676 prefixEnd_1633676 838861021714655468836867 := by
  unfold tailWord_1633676
  simp only [CollatzResearch.WordTrace]
  refine ⟨29792529414739168246408441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39723372552985557661877921 29792529414739168246408441)
  ·
    refine ⟨22344397061054376184806331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29792529414739168246408441 22344397061054376184806331)
    ·
      refine ⟨33516595591581564277209497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22344397061054376184806331 33516595591581564277209497)
      ·
        refine ⟨25137446693686173207907123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33516595591581564277209497 25137446693686173207907123)
        ·
          refine ⟨37706170040529259811860685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25137446693686173207907123 37706170040529259811860685)
          ·
            refine ⟨14139813765198472429447757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37706170040529259811860685 14139813765198472429447757)
            ·
              refine ⟨5302430161949427161042909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14139813765198472429447757 5302430161949427161042909)
              ·
                refine ⟨1988411310731035185391091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5302430161949427161042909 1988411310731035185391091)
                ·
                  refine ⟨2982616966096552778086637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1988411310731035185391091 2982616966096552778086637)
                  ·
                    refine ⟨1118481362286207291782489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2982616966096552778086637 1118481362286207291782489)
                    ·
                      refine ⟨838861021714655468836867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1118481362286207291782489 838861021714655468836867)
                      ·
                        rfl

theorem cell23_1633676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 3, 3, 1, 3, 2].length) (baseStart_1633676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1633676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1633676 prefixEnd_1633676 := by exact prefixLift 1633676
  have htrace : WordTrace (prefixWord ++ tailWord_1633676) baseStart_1633676 baseEnd_1633676 := by
    simpa [prefixWord, tailWord_1633676, baseEnd_1633676] using wordTrace_append hprefix tailTrace_1633676
  have hstable : (prefixWord ++ tailWord_1633676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1633676).length < 2 ^ (prefixWord ++ tailWord_1633676).sum := by decide
  have hdescent : baseEnd_1633676 < baseStart_1633676 := by decide
  rcases family_descends (prefixWord ++ tailWord_1633676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1633752 : List Nat := [2, 1, 2, 2, 2, 1, 3, 1, 1, 1, 7]
def baseStart_1633752 : Nat := 118140960795 + 1633752 * 2 ^ 59
def prefixEnd_1633752 : Nat := 4983230072969 + 3 ^ 40 * 1633752 * 2
def baseEnd_1633752 : Nat := 838900046244397171486517

theorem tailTrace_1633752 : CollatzResearch.WordTrace tailWord_1633752 prefixEnd_1633752 838900046244397171486517 := by
  unfold tailWord_1633752
  simp only [CollatzResearch.WordTrace]
  refine ⟨29793915388601500736291755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39725220518135334315055673 29793915388601500736291755)
  ·
    refine ⟨44690873082902251104437633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29793915388601500736291755 44690873082902251104437633)
    ·
      refine ⟨33518154812176688328328225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44690873082902251104437633 33518154812176688328328225)
      ·
        refine ⟨25138616109132516246246169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33518154812176688328328225 25138616109132516246246169)
        ·
          refine ⟨18853962081849387184684627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25138616109132516246246169 18853962081849387184684627)
          ·
            refine ⟨28280943122774080777026941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18853962081849387184684627 28280943122774080777026941)
            ·
              refine ⟨10605353671040280291385103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28280943122774080777026941 10605353671040280291385103)
              ·
                refine ⟨15908030506560420437077655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10605353671040280291385103 15908030506560420437077655)
                ·
                  refine ⟨23862045759840630655616483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15908030506560420437077655 23862045759840630655616483)
                  ·
                    refine ⟨35793068639760945983424725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23862045759840630655616483 35793068639760945983424725)
                    ·
                      refine ⟨838900046244397171486517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 35793068639760945983424725 838900046244397171486517)
                      ·
                        rfl

theorem cell23_1633752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 1, 1, 1, 7].length) (baseStart_1633752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1633752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1633752 prefixEnd_1633752 := by exact prefixLift 1633752
  have htrace : WordTrace (prefixWord ++ tailWord_1633752) baseStart_1633752 baseEnd_1633752 := by
    simpa [prefixWord, tailWord_1633752, baseEnd_1633752] using wordTrace_append hprefix tailTrace_1633752
  have hstable : (prefixWord ++ tailWord_1633752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1633752).length < 2 ^ (prefixWord ++ tailWord_1633752).sum := by decide
  have hdescent : baseEnd_1633752 < baseStart_1633752 := by decide
  rcases family_descends (prefixWord ++ tailWord_1633752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1633757 : List Nat := [1, 4, 3, 1, 1, 4, 2, 1, 2, 2, 2]
def baseStart_1633757 : Nat := 118140960795 + 1633757 * 2 ^ 59
def prefixEnd_1633757 : Nat := 4983230072969 + 3 ^ 40 * 1633757 * 2
def baseEnd_1633757 : Nat := 838902613647669651923995

theorem tailTrace_1633757 : CollatzResearch.WordTrace tailWord_1633757 prefixEnd_1633757 838902613647669651923995 := by
  unfold tailWord_1633757
  simp only [CollatzResearch.WordTrace]
  refine ⟨59588013142184887326515525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39725342094789924884343683 59588013142184887326515525)
  ·
    refine ⟨11172752464159666373721661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 59588013142184887326515525 11172752464159666373721661)
    ·
      refine ⟨4189782174059874890145623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11172752464159666373721661 4189782174059874890145623)
      ·
        refine ⟨6284673261089812335218435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4189782174059874890145623 6284673261089812335218435)
        ·
          refine ⟨9427009891634718502827653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6284673261089812335218435 9427009891634718502827653)
          ·
            refine ⟨1767564354681509719280185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9427009891634718502827653 1767564354681509719280185)
            ·
              refine ⟨1325673266011132289460139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1767564354681509719280185 1325673266011132289460139)
              ·
                refine ⟨1988509899016698434190209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1325673266011132289460139 1988509899016698434190209)
                ·
                  refine ⟨1491382424262523825642657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1988509899016698434190209 1491382424262523825642657)
                  ·
                    refine ⟨1118536818196892869231993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1491382424262523825642657 1118536818196892869231993)
                    ·
                      refine ⟨838902613647669651923995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1118536818196892869231993 838902613647669651923995)
                      ·
                        rfl

theorem cell23_1633757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 4, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 4, 2, 1, 2, 2, 2].length) (baseStart_1633757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1633757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1633757 prefixEnd_1633757 := by exact prefixLift 1633757
  have htrace : WordTrace (prefixWord ++ tailWord_1633757) baseStart_1633757 baseEnd_1633757 := by
    simpa [prefixWord, tailWord_1633757, baseEnd_1633757] using wordTrace_append hprefix tailTrace_1633757
  have hstable : (prefixWord ++ tailWord_1633757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1633757).length < 2 ^ (prefixWord ++ tailWord_1633757).sum := by decide
  have hdescent : baseEnd_1633757 < baseStart_1633757 := by decide
  rcases family_descends (prefixWord ++ tailWord_1633757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1633779 : List Nat := [1, 1, 1, 2, 2, 2, 2, 1, 3, 6, 2]
def baseStart_1633779 : Nat := 118140960795 + 1633779 * 2 ^ 59
def prefixEnd_1633779 : Nat := 4983230072969 + 3 ^ 40 * 1633779 * 2
def baseEnd_1633779 : Nat := 838913910222068565848893

theorem tailTrace_1633779 : CollatzResearch.WordTrace tailWord_1633779 prefixEnd_1633779 838913910222068565848893 := by
  unfold tailWord_1633779
  simp only [CollatzResearch.WordTrace]
  refine ⟨59588815548105185083816391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39725877032070123389210927 59588815548105185083816391)
  ·
    refine ⟨89383223322157777625724587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59588815548105185083816391 89383223322157777625724587)
    ·
      refine ⟨134074834983236666438586881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89383223322157777625724587 134074834983236666438586881)
      ·
        refine ⟨100556126237427499828940161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134074834983236666438586881 100556126237427499828940161)
        ·
          refine ⟨75417094678070624871705121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100556126237427499828940161 75417094678070624871705121)
          ·
            refine ⟨56562821008552968653778841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75417094678070624871705121 56562821008552968653778841)
            ·
              refine ⟨42422115756414726490334131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56562821008552968653778841 42422115756414726490334131)
              ·
                refine ⟨63633173634622089735501197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42422115756414726490334131 63633173634622089735501197)
                ·
                  refine ⟨23862440112983283650812949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 63633173634622089735501197 23862440112983283650812949)
                  ·
                    refine ⟨1118551880296091421131857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23862440112983283650812949 1118551880296091421131857)
                    ·
                      refine ⟨838913910222068565848893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1118551880296091421131857 838913910222068565848893)
                      ·
                        rfl

theorem cell23_1633779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 1, 3, 6, 2].length) (baseStart_1633779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1633779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1633779 prefixEnd_1633779 := by exact prefixLift 1633779
  have htrace : WordTrace (prefixWord ++ tailWord_1633779) baseStart_1633779 baseEnd_1633779 := by
    simpa [prefixWord, tailWord_1633779, baseEnd_1633779] using wordTrace_append hprefix tailTrace_1633779
  have hstable : (prefixWord ++ tailWord_1633779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1633779).length < 2 ^ (prefixWord ++ tailWord_1633779).sum := by decide
  have hdescent : baseEnd_1633779 < baseStart_1633779 := by decide
  rcases family_descends (prefixWord ++ tailWord_1633779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1633853 : List Nat := [1, 4, 1, 3, 3, 2, 1, 2, 6]
def baseStart_1633853 : Nat := 118140960795 + 1633853 * 2 ^ 59
def prefixEnd_1633853 : Nat := 4983230072969 + 3 ^ 40 * 1633853 * 2
def baseEnd_1633853 : Nat := 93216878643389030702617

theorem tailTrace_1633853 : CollatzResearch.WordTrace tailWord_1633853 prefixEnd_1633853 93216878643389030702617 := by
  unfold tailWord_1633853
  simp only [CollatzResearch.WordTrace]
  refine ⟨59591514549837095722010213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39727676366558063814673475 59591514549837095722010213)
  ·
    refine ⟨11173408978094455447876915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 59591514549837095722010213 11173408978094455447876915)
    ·
      refine ⟨16760113467141683171815373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11173408978094455447876915 16760113467141683171815373)
      ·
        refine ⟨6285042550178131189430765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16760113467141683171815373 6285042550178131189430765)
        ·
          refine ⟨2356890956316799196036537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6285042550178131189430765 2356890956316799196036537)
          ·
            refine ⟨1767668217237599397027403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2356890956316799196036537 1767668217237599397027403)
            ·
              refine ⟨2651502325856399095541105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1767668217237599397027403 2651502325856399095541105)
              ·
                refine ⟨1988626744392299321655829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2651502325856399095541105 1988626744392299321655829)
                ·
                  refine ⟨93216878643389030702617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1988626744392299321655829 93216878643389030702617)
                  ·
                    rfl

theorem cell23_1633853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 2, 1, 2, 6].length) (baseStart_1633853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1633853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1633853 prefixEnd_1633853 := by exact prefixLift 1633853
  have htrace : WordTrace (prefixWord ++ tailWord_1633853) baseStart_1633853 baseEnd_1633853 := by
    simpa [prefixWord, tailWord_1633853, baseEnd_1633853] using wordTrace_append hprefix tailTrace_1633853
  have hstable : (prefixWord ++ tailWord_1633853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1633853).length < 2 ^ (prefixWord ++ tailWord_1633853).sum := by decide
  have hdescent : baseEnd_1633853 < baseStart_1633853 := by decide
  rcases family_descends (prefixWord ++ tailWord_1633853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1633856 : List Nat := [2, 1, 1, 2, 2, 2, 1, 3, 4, 3, 2]
def baseStart_1633856 : Nat := 118140960795 + 1633856 * 2 ^ 59
def prefixEnd_1633856 : Nat := 4983230072969 + 3 ^ 40 * 1633856 * 2
def baseEnd_1633856 : Nat := 838953448232464764586039

theorem tailTrace_1633856 : CollatzResearch.WordTrace tailWord_1633856 prefixEnd_1633856 838953448232464764586039 := by
  unfold tailWord_1633856
  simp only [CollatzResearch.WordTrace]
  refine ⟨29795811984413113617184711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39727749312550818156246281 29795811984413113617184711)
  ·
    refine ⟨44693717976619670425777067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29795811984413113617184711 44693717976619670425777067)
    ·
      refine ⟨67040576964929505638665601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44693717976619670425777067 67040576964929505638665601)
      ·
        refine ⟨50280432723697129228999201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67040576964929505638665601 50280432723697129228999201)
        ·
          refine ⟨37710324542772846921749401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50280432723697129228999201 37710324542772846921749401)
          ·
            refine ⟨28282743407079635191312051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37710324542772846921749401 28282743407079635191312051)
            ·
              refine ⟨42424115110619452786968077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28282743407079635191312051 42424115110619452786968077)
              ·
                refine ⟨15909043166482294795113029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42424115110619452786968077 15909043166482294795113029)
                ·
                  refine ⟨2982945593715430274083693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15909043166482294795113029 2982945593715430274083693)
                  ·
                    refine ⟨1118604597643286352781385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2982945593715430274083693 1118604597643286352781385)
                    ·
                      refine ⟨838953448232464764586039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1118604597643286352781385 838953448232464764586039)
                      ·
                        rfl

theorem cell23_1633856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 3, 4, 3, 2].length) (baseStart_1633856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1633856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1633856 prefixEnd_1633856 := by exact prefixLift 1633856
  have htrace : WordTrace (prefixWord ++ tailWord_1633856) baseStart_1633856 baseEnd_1633856 := by
    simpa [prefixWord, tailWord_1633856, baseEnd_1633856] using wordTrace_append hprefix tailTrace_1633856
  have hstable : (prefixWord ++ tailWord_1633856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1633856).length < 2 ^ (prefixWord ++ tailWord_1633856).sum := by decide
  have hdescent : baseEnd_1633856 < baseStart_1633856 := by decide
  rcases family_descends (prefixWord ++ tailWord_1633856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1633889 : List Nat := [1, 2, 3, 1, 1, 3, 1, 2, 3, 1, 5]
def baseStart_1633889 : Nat := 118140960795 + 1633889 * 2 ^ 59
def prefixEnd_1633889 : Nat := 4983230072969 + 3 ^ 40 * 1633889 * 2
def baseEnd_1633889 : Nat := 838970393094063135473387

theorem tailTrace_1633889 : CollatzResearch.WordTrace tailWord_1633889 prefixEnd_1633889 838970393094063135473387 := by
  unfold tailWord_1633889
  simp only [CollatzResearch.WordTrace]
  refine ⟨59592827577706673870320721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39728551718471115913547147 59592827577706673870320721)
  ·
    refine ⟨44694620683280005402740541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59592827577706673870320721 44694620683280005402740541)
    ·
      refine ⟨16760482756230002026027703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44694620683280005402740541 16760482756230002026027703)
      ·
        refine ⟨25140724134345003039041555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16760482756230002026027703 25140724134345003039041555)
        ·
          refine ⟨37711086201517504558562333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25140724134345003039041555 37711086201517504558562333)
          ·
            refine ⟨14141657325569064209460875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37711086201517504558562333 14141657325569064209460875)
            ·
              refine ⟨21212485988353596314191313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14141657325569064209460875 21212485988353596314191313)
              ·
                refine ⟨15909364491265197235643485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21212485988353596314191313 15909364491265197235643485)
                ·
                  refine ⟨5966011684224448963366307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15909364491265197235643485 5966011684224448963366307)
                  ·
                    refine ⟨8949017526336673445049461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5966011684224448963366307 8949017526336673445049461)
                    ·
                      refine ⟨838970393094063135473387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8949017526336673445049461 838970393094063135473387)
                      ·
                        rfl

theorem cell23_1633889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 2, 3, 1, 5].length) (baseStart_1633889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1633889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1633889 prefixEnd_1633889 := by exact prefixLift 1633889
  have htrace : WordTrace (prefixWord ++ tailWord_1633889) baseStart_1633889 baseEnd_1633889 := by
    simpa [prefixWord, tailWord_1633889, baseEnd_1633889] using wordTrace_append hprefix tailTrace_1633889
  have hstable : (prefixWord ++ tailWord_1633889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1633889).length < 2 ^ (prefixWord ++ tailWord_1633889).sum := by decide
  have hdescent : baseEnd_1633889 < baseStart_1633889 := by decide
  rcases family_descends (prefixWord ++ tailWord_1633889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1633906 : List Nat := [3, 2, 1, 2, 3, 1, 1, 3, 1, 1, 5]
def baseStart_1633906 : Nat := 118140960795 + 1633906 * 2 ^ 59
def prefixEnd_1633906 : Nat := 4983230072969 + 3 ^ 40 * 1633906 * 2
def baseEnd_1633906 : Nat := 838979122265189568960809

theorem tailTrace_1633906 : CollatzResearch.WordTrace tailWord_1633906 prefixEnd_1633906 838979122265189568960809 := by
  unfold tailWord_1633906
  simp only [CollatzResearch.WordTrace]
  refine ⟨14898361904661271443422393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39728965079096723849126381 14898361904661271443422393)
  ·
    refine ⟨11173771428495953582566795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14898361904661271443422393 11173771428495953582566795)
    ·
      refine ⟨16760657142743930373850193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11173771428495953582566795 16760657142743930373850193)
      ·
        refine ⟨12570492857057947780387645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16760657142743930373850193 12570492857057947780387645)
        ·
          refine ⟨4713934821396730417645367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12570492857057947780387645 4713934821396730417645367)
          ·
            refine ⟨7070902232095095626468051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4713934821396730417645367 7070902232095095626468051)
            ·
              refine ⟨10606353348142643439702077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7070902232095095626468051 10606353348142643439702077)
              ·
                refine ⟨3977382505553491289888279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10606353348142643439702077 3977382505553491289888279)
                ·
                  refine ⟨5966073758330236934832419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3977382505553491289888279 5966073758330236934832419)
                  ·
                    refine ⟨8949110637495355402248629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5966073758330236934832419 8949110637495355402248629)
                    ·
                      refine ⟨838979122265189568960809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8949110637495355402248629 838979122265189568960809)
                      ·
                        rfl

theorem cell23_1633906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 3, 1, 1, 5].length) (baseStart_1633906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1633906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1633906 prefixEnd_1633906 := by exact prefixLift 1633906
  have htrace : WordTrace (prefixWord ++ tailWord_1633906) baseStart_1633906 baseEnd_1633906 := by
    simpa [prefixWord, tailWord_1633906, baseEnd_1633906] using wordTrace_append hprefix tailTrace_1633906
  have hstable : (prefixWord ++ tailWord_1633906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1633906).length < 2 ^ (prefixWord ++ tailWord_1633906).sum := by decide
  have hdescent : baseEnd_1633906 < baseStart_1633906 := by decide
  rcases family_descends (prefixWord ++ tailWord_1633906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1633930 : List Nat := [3, 1, 2, 3, 2, 1, 4, 1, 2, 4]
def baseStart_1633930 : Nat := 118140960795 + 1633930 * 2 ^ 59
def prefixEnd_1633930 : Nat := 4983230072969 + 3 ^ 40 * 1633930 * 2
def baseEnd_1633930 : Nat := 279663815266965825020233

theorem tailTrace_1633930 : CollatzResearch.WordTrace tailWord_1633930 prefixEnd_1633930 279663815266965825020233 := by
  unfold tailWord_1633930
  simp only [CollatzResearch.WordTrace]
  refine ⟨14898580742639534468140811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39729548647038758581708829 14898580742639534468140811)
  ·
    refine ⟨22347871113959301702211217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14898580742639534468140811 22347871113959301702211217)
    ·
      refine ⟨16760903335469476276658413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22347871113959301702211217 16760903335469476276658413)
      ·
        refine ⟨6285338750801053603746905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16760903335469476276658413 6285338750801053603746905)
        ·
          refine ⟨4714004063100790202810179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6285338750801053603746905 4714004063100790202810179)
          ·
            refine ⟨7071006094651185304215269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4714004063100790202810179 7071006094651185304215269)
            ·
              refine ⟨1325813642747097244540363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7071006094651185304215269 1325813642747097244540363)
              ·
                refine ⟨1988720464120645866810545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1325813642747097244540363 1988720464120645866810545)
                ·
                  refine ⟨1491540348090484400107909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1988720464120645866810545 1491540348090484400107909)
                  ·
                    refine ⟨279663815266965825020233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1491540348090484400107909 279663815266965825020233)
                    ·
                      rfl

theorem cell23_1633930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 4, 1, 2, 4].length) (baseStart_1633930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1633930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1633930 prefixEnd_1633930 := by exact prefixLift 1633930
  have htrace : WordTrace (prefixWord ++ tailWord_1633930) baseStart_1633930 baseEnd_1633930 := by
    simpa [prefixWord, tailWord_1633930, baseEnd_1633930] using wordTrace_append hprefix tailTrace_1633930
  have hstable : (prefixWord ++ tailWord_1633930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1633930).length < 2 ^ (prefixWord ++ tailWord_1633930).sum := by decide
  have hdescent : baseEnd_1633930 < baseStart_1633930 := by decide
  rcases family_descends (prefixWord ++ tailWord_1633930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1633940 : List Nat := [2, 4, 2, 2, 2, 1, 1, 1, 3, 2, 3]
def baseStart_1633940 : Nat := 118140960795 + 1633940 * 2 ^ 59
def prefixEnd_1633940 : Nat := 4983230072969 + 3 ^ 40 * 1633940 * 2
def baseEnd_1633940 : Nat := 838996580607442435935653

theorem tailTrace_1633940 : CollatzResearch.WordTrace tailWord_1633940 prefixEnd_1633940 838996580607442435935653 := by
  unfold tailWord_1633940
  simp only [CollatzResearch.WordTrace]
  refine ⟨29797343850260954790213637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39729791800347939720284849 29797343850260954790213637)
  ·
    refine ⟨5587001971923929023165057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29797343850260954790213637 5587001971923929023165057)
    ·
      refine ⟨4190251478942946767373793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5587001971923929023165057 4190251478942946767373793)
      ·
        refine ⟨3142688609207210075530345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4190251478942946767373793 3142688609207210075530345)
        ·
          refine ⟨2357016456905407556647759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3142688609207210075530345 2357016456905407556647759)
          ·
            refine ⟨3535524685358111334971639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2357016456905407556647759 3535524685358111334971639)
            ·
              refine ⟨5303287028037167002457459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3535524685358111334971639 5303287028037167002457459)
              ·
                refine ⟨7954930542055750503686189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5303287028037167002457459 7954930542055750503686189)
                ·
                  refine ⟨2983098953270906438882321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7954930542055750503686189 2983098953270906438882321)
                  ·
                    refine ⟨2237324214953179829161741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2983098953270906438882321 2237324214953179829161741)
                    ·
                      refine ⟨838996580607442435935653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2237324214953179829161741 838996580607442435935653)
                      ·
                        rfl

theorem cell23_1633940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 1, 1, 3, 2, 3].length) (baseStart_1633940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1633940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1633940 prefixEnd_1633940 := by exact prefixLift 1633940
  have htrace : WordTrace (prefixWord ++ tailWord_1633940) baseStart_1633940 baseEnd_1633940 := by
    simpa [prefixWord, tailWord_1633940, baseEnd_1633940] using wordTrace_append hprefix tailTrace_1633940
  have hstable : (prefixWord ++ tailWord_1633940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1633940).length < 2 ^ (prefixWord ++ tailWord_1633940).sum := by decide
  have hdescent : baseEnd_1633940 < baseStart_1633940 := by decide
  rcases family_descends (prefixWord ++ tailWord_1633940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1633953 : List Nat := [1, 2, 3, 3, 2, 2, 1, 2, 1, 3, 3]
def baseStart_1633953 : Nat := 118140960795 + 1633953 * 2 ^ 59
def prefixEnd_1633953 : Nat := 4983230072969 + 3 ^ 40 * 1633953 * 2
def baseEnd_1633953 : Nat := 839003255855950885073093

theorem tailTrace_1633953 : CollatzResearch.WordTrace tailWord_1633953 prefixEnd_1633953 839003255855950885073093 := by
  unfold tailWord_1633953
  simp only [CollatzResearch.WordTrace]
  refine ⟨59595161849474812800650513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39730107899649875200433675 59595161849474812800650513)
  ·
    refine ⟨44696371387106109600487885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59595161849474812800650513 44696371387106109600487885)
    ·
      refine ⟨16761139270164791100182957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44696371387106109600487885 16761139270164791100182957)
      ·
        refine ⟨6285427226311796662568609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16761139270164791100182957 6285427226311796662568609)
        ·
          refine ⟨4714070419733847496926457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6285427226311796662568609 4714070419733847496926457)
          ·
            refine ⟨3535552814800385622694843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4714070419733847496926457 3535552814800385622694843)
            ·
              refine ⟨5303329222200578434042265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3535552814800385622694843 5303329222200578434042265)
              ·
                refine ⟨3977496916650433825531699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5303329222200578434042265 3977496916650433825531699)
                ·
                  refine ⟨5966245374975650738297549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3977496916650433825531699 5966245374975650738297549)
                  ·
                    refine ⟨2237342015615869026861581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5966245374975650738297549 2237342015615869026861581)
                    ·
                      refine ⟨839003255855950885073093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2237342015615869026861581 839003255855950885073093)
                      ·
                        rfl

theorem cell23_1633953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 1, 2, 1, 3, 3].length) (baseStart_1633953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1633953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1633953 prefixEnd_1633953 := by exact prefixLift 1633953
  have htrace : WordTrace (prefixWord ++ tailWord_1633953) baseStart_1633953 baseEnd_1633953 := by
    simpa [prefixWord, tailWord_1633953, baseEnd_1633953] using wordTrace_append hprefix tailTrace_1633953
  have hstable : (prefixWord ++ tailWord_1633953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1633953).length < 2 ^ (prefixWord ++ tailWord_1633953).sum := by decide
  have hdescent : baseEnd_1633953 < baseStart_1633953 := by decide
  rcases family_descends (prefixWord ++ tailWord_1633953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1633960 : List Nat := [2, 1, 7, 1, 2, 10]
def baseStart_1633960 : Nat := 118140960795 + 1633960 * 2 ^ 59
def prefixEnd_1633960 : Nat := 4983230072969 + 3 ^ 40 * 1633960 * 2
def baseEnd_1633960 : Nat := 3452703087327293653027

theorem tailTrace_1633960 : CollatzResearch.WordTrace tailWord_1633960 prefixEnd_1633960 3452703087327293653027 := by
  unfold tailWord_1633960
  simp only [CollatzResearch.WordTrace]
  refine ⟨29797708580224726498077667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39730278106966301997436889 29797708580224726498077667)
  ·
    refine ⟨44696562870337089747116501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29797708580224726498077667 44696562870337089747116501)
    ·
      refine ⟨1047575692273525540948043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 44696562870337089747116501 1047575692273525540948043)
      ·
        refine ⟨1571363538410288311422065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1047575692273525540948043 1571363538410288311422065)
        ·
          refine ⟨1178522653807716233566549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1571363538410288311422065 1178522653807716233566549)
          ·
            refine ⟨3452703087327293653027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 1178522653807716233566549 3452703087327293653027)
            ·
              rfl

theorem cell23_1633960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 2, 10].length) (baseStart_1633960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1633960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1633960 prefixEnd_1633960 := by exact prefixLift 1633960
  have htrace : WordTrace (prefixWord ++ tailWord_1633960) baseStart_1633960 baseEnd_1633960 := by
    simpa [prefixWord, tailWord_1633960, baseEnd_1633960] using wordTrace_append hprefix tailTrace_1633960
  have hstable : (prefixWord ++ tailWord_1633960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1633960).length < 2 ^ (prefixWord ++ tailWord_1633960).sum := by decide
  have hdescent : baseEnd_1633960 < baseStart_1633960 := by decide
  rcases family_descends (prefixWord ++ tailWord_1633960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1633979 : List Nat := [1, 1, 1, 1, 1, 2, 3, 4, 1, 3, 5]
def baseStart_1633979 : Nat := 118140960795 + 1633979 * 2 ^ 59
def prefixEnd_1633979 : Nat := 4983230072969 + 3 ^ 40 * 1633979 * 2
def baseEnd_1633979 : Nat := 839016606352967783347973

theorem tailTrace_1633979 : CollatzResearch.WordTrace tailWord_1633979 prefixEnd_1633979 839016606352967783347973 := by
  unfold tailWord_1633979
  simp only [CollatzResearch.WordTrace]
  refine ⟨59596110147380619241096991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39730740098253746160731327 59596110147380619241096991)
  ·
    refine ⟨89394165221070928861645487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59596110147380619241096991 89394165221070928861645487)
    ·
      refine ⟨134091247831606393292468231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89394165221070928861645487 134091247831606393292468231)
      ·
        refine ⟨201136871747409589938702347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134091247831606393292468231 201136871747409589938702347)
        ·
          refine ⟨301705307621114384908053521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 201136871747409589938702347 301705307621114384908053521)
          ·
            refine ⟨226278980715835788681040141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 301705307621114384908053521 226278980715835788681040141)
            ·
              refine ⟨84854617768438420755390053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 226278980715835788681040141 84854617768438420755390053)
              ·
                refine ⟨15910240831582203891635635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 84854617768438420755390053 15910240831582203891635635)
                ·
                  refine ⟨23865361247373305837453453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15910240831582203891635635 23865361247373305837453453)
                  ·
                    refine ⟨8949510467764989689045045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23865361247373305837453453 8949510467764989689045045)
                    ·
                      refine ⟨839016606352967783347973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8949510467764989689045045 839016606352967783347973)
                      ·
                        rfl

theorem cell23_1633979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 4, 1, 3, 5].length) (baseStart_1633979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1633979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1633979 prefixEnd_1633979 := by exact prefixLift 1633979
  have htrace : WordTrace (prefixWord ++ tailWord_1633979) baseStart_1633979 baseEnd_1633979 := by
    simpa [prefixWord, tailWord_1633979, baseEnd_1633979] using wordTrace_append hprefix tailTrace_1633979
  have hstable : (prefixWord ++ tailWord_1633979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1633979).length < 2 ^ (prefixWord ++ tailWord_1633979).sum := by decide
  have hdescent : baseEnd_1633979 < baseStart_1633979 := by decide
  rcases family_descends (prefixWord ++ tailWord_1633979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1633989 : List Nat := [1, 3, 1, 1, 1, 1, 2, 2, 2, 3, 6]
def baseStart_1633989 : Nat := 118140960795 + 1633989 * 2 ^ 59
def prefixEnd_1633989 : Nat := 4983230072969 + 3 ^ 40 * 1633989 * 2
def baseEnd_1633989 : Nat := 839021741159512744222927

theorem tailTrace_1633989 : CollatzResearch.WordTrace tailWord_1633989 prefixEnd_1633989 839021741159512744222927 := by
  unfold tailWord_1633989
  simp only [CollatzResearch.WordTrace]
  refine ⟨59596474877344390948961021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39730983251562927299307347 59596474877344390948961021)
  ·
    refine ⟨22348678079004146605860383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59596474877344390948961021 22348678079004146605860383)
    ·
      refine ⟨33523017118506219908790575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22348678079004146605860383 33523017118506219908790575)
      ·
        refine ⟨50284525677759329863185863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33523017118506219908790575 50284525677759329863185863)
        ·
          refine ⟨75426788516638994794778795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50284525677759329863185863 75426788516638994794778795)
          ·
            refine ⟨113140182774958492192168193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75426788516638994794778795 113140182774958492192168193)
            ·
              refine ⟨84855137081218869144126145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 113140182774958492192168193 84855137081218869144126145)
              ·
                refine ⟨63641352810914151858094609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 84855137081218869144126145 63641352810914151858094609)
                ·
                  refine ⟨47731014608185613893570957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63641352810914151858094609 47731014608185613893570957)
                  ·
                    refine ⟨17899130478069605210089109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 47731014608185613893570957 17899130478069605210089109)
                    ·
                      refine ⟨839021741159512744222927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 17899130478069605210089109 839021741159512744222927)
                      ·
                        rfl

theorem cell23_1633989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 2, 2, 3, 6].length) (baseStart_1633989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1633989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1633989 prefixEnd_1633989 := by exact prefixLift 1633989
  have htrace : WordTrace (prefixWord ++ tailWord_1633989) baseStart_1633989 baseEnd_1633989 := by
    simpa [prefixWord, tailWord_1633989, baseEnd_1633989] using wordTrace_append hprefix tailTrace_1633989
  have hstable : (prefixWord ++ tailWord_1633989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1633989).length < 2 ^ (prefixWord ++ tailWord_1633989).sum := by decide
  have hdescent : baseEnd_1633989 < baseStart_1633989 := by decide
  rcases family_descends (prefixWord ++ tailWord_1633989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1633997 : List Nat := [1, 6, 2, 1, 1, 1, 2, 1, 3, 3, 2]
def baseStart_1633997 : Nat := 118140960795 + 1633997 * 2 ^ 59
def prefixEnd_1633997 : Nat := 4983230072969 + 3 ^ 40 * 1633997 * 2
def baseEnd_1633997 : Nat := 839025849004748712922891

theorem tailTrace_1633997 : CollatzResearch.WordTrace tailWord_1633997 prefixEnd_1633997 839025849004748712922891 := by
  unfold tailWord_1633997
  simp only [CollatzResearch.WordTrace]
  refine ⟨59596766661315408315252245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39731177774210272210168163 59596766661315408315252245)
  ·
    refine ⟨2793598437249159764777449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 59596766661315408315252245 2793598437249159764777449)
    ·
      refine ⟨2095198827936869823583087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2793598437249159764777449 2095198827936869823583087)
      ·
        refine ⟨3142798241905304735374631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2095198827936869823583087 3142798241905304735374631)
        ·
          refine ⟨4714197362857957103061947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3142798241905304735374631 4714197362857957103061947)
          ·
            refine ⟨7071296044286935654592921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4714197362857957103061947 7071296044286935654592921)
            ·
              refine ⟨5303472033215201740944691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7071296044286935654592921 5303472033215201740944691)
              ·
                refine ⟨7955208049822802611417037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5303472033215201740944691 7955208049822802611417037)
                ·
                  refine ⟨2983203018683550979281389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7955208049822802611417037 2983203018683550979281389)
                  ·
                    refine ⟨1118701132006331617230521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2983203018683550979281389 1118701132006331617230521)
                    ·
                      refine ⟨839025849004748712922891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1118701132006331617230521 839025849004748712922891)
                      ·
                        rfl

theorem cell23_1633997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 2, 1, 3, 3, 2].length) (baseStart_1633997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1633997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1633997 prefixEnd_1633997 := by exact prefixLift 1633997
  have htrace : WordTrace (prefixWord ++ tailWord_1633997) baseStart_1633997 baseEnd_1633997 := by
    simpa [prefixWord, tailWord_1633997, baseEnd_1633997] using wordTrace_append hprefix tailTrace_1633997
  have hstable : (prefixWord ++ tailWord_1633997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1633997).length < 2 ^ (prefixWord ++ tailWord_1633997).sum := by decide
  have hdescent : baseEnd_1633997 < baseStart_1633997 := by decide
  rcases family_descends (prefixWord ++ tailWord_1633997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1634033 : List Nat := [1, 2, 2, 2, 2, 3, 2, 4, 5]
def baseStart_1634033 : Nat := 118140960795 + 1634033 * 2 ^ 59
def prefixEnd_1634033 : Nat := 4983230072969 + 3 ^ 40 * 1634033 * 2
def baseEnd_1634033 : Nat := 93227148256478952452525

theorem tailTrace_1634033 : CollatzResearch.WordTrace tailWord_1634033 prefixEnd_1634033 93227148256478952452525 := by
  unfold tailWord_1634033
  simp only [CollatzResearch.WordTrace]
  refine ⟨59598079689184986463562753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39732053126123324309041835 59598079689184986463562753)
  ·
    refine ⟨44698559766888739847672065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59598079689184986463562753 44698559766888739847672065)
    ·
      refine ⟨33523919825166554885754049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44698559766888739847672065 33523919825166554885754049)
      ·
        refine ⟨25142939868874916164315537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33523919825166554885754049 25142939868874916164315537)
        ·
          refine ⟨18857204901656187123236653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25142939868874916164315537 18857204901656187123236653)
          ·
            refine ⟨7071451838121070171213745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18857204901656187123236653 7071451838121070171213745)
            ·
              refine ⟨5303588878590802628410309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7071451838121070171213745 5303588878590802628410309)
              ·
                refine ⟨994422914735775492826933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5303588878590802628410309 994422914735775492826933)
                ·
                  refine ⟨93227148256478952452525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 994422914735775492826933 93227148256478952452525)
                  ·
                    rfl

theorem cell23_1634033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 2, 4, 5].length) (baseStart_1634033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1634033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1634033 prefixEnd_1634033 := by exact prefixLift 1634033
  have htrace : WordTrace (prefixWord ++ tailWord_1634033) baseStart_1634033 baseEnd_1634033 := by
    simpa [prefixWord, tailWord_1634033, baseEnd_1634033] using wordTrace_append hprefix tailTrace_1634033
  have hstable : (prefixWord ++ tailWord_1634033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1634033).length < 2 ^ (prefixWord ++ tailWord_1634033).sum := by decide
  have hdescent : baseEnd_1634033 < baseStart_1634033 := by decide
  rcases family_descends (prefixWord ++ tailWord_1634033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1634083 : List Nat := [1, 1, 1, 4, 2, 1, 2, 1, 4, 4, 2]
def baseStart_1634083 : Nat := 118140960795 + 1634083 * 2 ^ 59
def prefixEnd_1634083 : Nat := 4983230072969 + 3 ^ 40 * 1634083 * 2
def baseEnd_1634083 : Nat := 839070008341035376447495

theorem tailTrace_1634083 : CollatzResearch.WordTrace tailWord_1634083 prefixEnd_1634083 839070008341035376447495 := by
  unfold tailWord_1634083
  simp only [CollatzResearch.WordTrace]
  refine ⟨59599903339003845002882903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39733268892669230001921935 59599903339003845002882903)
  ·
    refine ⟨89399855008505767504324355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59599903339003845002882903 89399855008505767504324355)
    ·
      refine ⟨134099782512758651256486533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89399855008505767504324355 134099782512758651256486533)
      ·
        refine ⟨25143709221142247110591225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 134099782512758651256486533 25143709221142247110591225)
        ·
          refine ⟨18857781915856685332943419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25143709221142247110591225 18857781915856685332943419)
          ·
            refine ⟨28286672873785027999415129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18857781915856685332943419 28286672873785027999415129)
            ·
              refine ⟨21215004655338770999561347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28286672873785027999415129 21215004655338770999561347)
              ·
                refine ⟨31822506983008156499342021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21215004655338770999561347 31822506983008156499342021)
                ·
                  refine ⟨5966720059314029343626629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31822506983008156499342021 5966720059314029343626629)
                  ·
                    refine ⟨1118760011121380501929993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5966720059314029343626629 1118760011121380501929993)
                    ·
                      refine ⟨839070008341035376447495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1118760011121380501929993 839070008341035376447495)
                      ·
                        rfl

theorem cell23_1634083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 1, 4, 4, 2].length) (baseStart_1634083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1634083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1634083 prefixEnd_1634083 := by exact prefixLift 1634083
  have htrace : WordTrace (prefixWord ++ tailWord_1634083) baseStart_1634083 baseEnd_1634083 := by
    simpa [prefixWord, tailWord_1634083, baseEnd_1634083] using wordTrace_append hprefix tailTrace_1634083
  have hstable : (prefixWord ++ tailWord_1634083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1634083).length < 2 ^ (prefixWord ++ tailWord_1634083).sum := by decide
  have hdescent : baseEnd_1634083 < baseStart_1634083 := by decide
  rcases family_descends (prefixWord ++ tailWord_1634083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1634120 : List Nat := [2, 1, 3, 1, 1, 5, 2, 1, 2, 2, 3]
def baseStart_1634120 : Nat := 118140960795 + 1634120 * 2 ^ 59
def prefixEnd_1634120 : Nat := 4983230072969 + 3 ^ 40 * 1634120 * 2
def baseEnd_1634120 : Nat := 839089007125251731684825

theorem tailTrace_1634120 : CollatzResearch.WordTrace tailWord_1634120 prefixEnd_1634120 839089007125251731684825 := by
  unfold tailWord_1634120
  simp only [CollatzResearch.WordTrace]
  refine ⟨29800626419934900160989907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39734168559913200214653209 29800626419934900160989907)
  ·
    refine ⟨44700939629902350241484861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29800626419934900160989907 44700939629902350241484861)
    ·
      refine ⟨16762852361213381340556823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44700939629902350241484861 16762852361213381340556823)
      ·
        refine ⟨25144278541820072010835235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16762852361213381340556823 25144278541820072010835235)
        ·
          refine ⟨37716417812730108016252853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25144278541820072010835235 37716417812730108016252853)
          ·
            refine ⟨3535914169943447626523705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 37716417812730108016252853 3535914169943447626523705)
            ·
              refine ⟨2651935627457585719892779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3535914169943447626523705 2651935627457585719892779)
              ·
                refine ⟨3977903441186378579839169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2651935627457585719892779 3977903441186378579839169)
                ·
                  refine ⟨2983427580889783934879377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3977903441186378579839169 2983427580889783934879377)
                  ·
                    refine ⟨2237570685667337951159533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2983427580889783934879377 2237570685667337951159533)
                    ·
                      refine ⟨839089007125251731684825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2237570685667337951159533 839089007125251731684825)
                      ·
                        rfl

theorem cell23_1634120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 2, 1, 2, 2, 3].length) (baseStart_1634120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1634120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1634120 prefixEnd_1634120 := by exact prefixLift 1634120
  have htrace : WordTrace (prefixWord ++ tailWord_1634120) baseStart_1634120 baseEnd_1634120 := by
    simpa [prefixWord, tailWord_1634120, baseEnd_1634120] using wordTrace_append hprefix tailTrace_1634120
  have hstable : (prefixWord ++ tailWord_1634120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1634120).length < 2 ^ (prefixWord ++ tailWord_1634120).sum := by decide
  have hdescent : baseEnd_1634120 < baseStart_1634120 := by decide
  rcases family_descends (prefixWord ++ tailWord_1634120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1634126 : List Nat := [4, 1, 1, 1, 1, 1, 1, 1, 3, 1, 8]
def baseStart_1634126 : Nat := 118140960795 + 1634126 * 2 ^ 59
def prefixEnd_1634126 : Nat := 4983230072969 + 3 ^ 40 * 1634126 * 2
def baseEnd_1634126 : Nat := 839092088009178708209797

theorem tailTrace_1634126 : CollatzResearch.WordTrace tailWord_1634126 prefixEnd_1634126 839092088009178708209797 := by
  unfold tailWord_1634126
  simp only [CollatzResearch.WordTrace]
  refine ⟨7450183959731007918337279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39734314451898708897798821 7450183959731007918337279)
  ·
    refine ⟨11175275939596511877505919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7450183959731007918337279 11175275939596511877505919)
    ·
      refine ⟨16762913909394767816258879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11175275939596511877505919 16762913909394767816258879)
      ·
        refine ⟨25144370864092151724388319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16762913909394767816258879 25144370864092151724388319)
        ·
          refine ⟨37716556296138227586582479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25144370864092151724388319 37716556296138227586582479)
          ·
            refine ⟨56574834444207341379873719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37716556296138227586582479 56574834444207341379873719)
            ·
              refine ⟨84862251666311012069810579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56574834444207341379873719 84862251666311012069810579)
              ·
                refine ⟨127293377499466518104715869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84862251666311012069810579 127293377499466518104715869)
                ·
                  refine ⟨47735016562299944289268451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 127293377499466518104715869 47735016562299944289268451)
                  ·
                    refine ⟨71602524843449916433902677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 47735016562299944289268451 71602524843449916433902677)
                    ·
                      refine ⟨839092088009178708209797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 71602524843449916433902677 839092088009178708209797)
                      ·
                        rfl

theorem cell23_1634126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 1, 3, 1, 8].length) (baseStart_1634126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1634126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1634126 prefixEnd_1634126 := by exact prefixLift 1634126
  have htrace : WordTrace (prefixWord ++ tailWord_1634126) baseStart_1634126 baseEnd_1634126 := by
    simpa [prefixWord, tailWord_1634126, baseEnd_1634126] using wordTrace_append hprefix tailTrace_1634126
  have hstable : (prefixWord ++ tailWord_1634126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1634126).length < 2 ^ (prefixWord ++ tailWord_1634126).sum := by decide
  have hdescent : baseEnd_1634126 < baseStart_1634126 := by decide
  rcases family_descends (prefixWord ++ tailWord_1634126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1634144 : List Nat := [2, 1, 1, 3, 3, 4, 2, 2, 1, 4]
def baseStart_1634144 : Nat := 118140960795 + 1634144 * 2 ^ 59
def prefixEnd_1634144 : Nat := 4983230072969 + 3 ^ 40 * 1634144 * 2
def baseEnd_1634144 : Nat := 279700443553653212594905

theorem tailTrace_1634144 : CollatzResearch.WordTrace tailWord_1634144 prefixEnd_1634144 279700443553653212594905 := by
  unfold tailWord_1634144
  simp only [CollatzResearch.WordTrace]
  refine ⟨29801064095891426210426743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39734752127855234947235657 29801064095891426210426743)
  ·
    refine ⟨44701596143837139315640115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29801064095891426210426743 44701596143837139315640115)
    ·
      refine ⟨67052394215755708973460173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44701596143837139315640115 67052394215755708973460173)
      ·
        refine ⟨25144647830908390865047565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67052394215755708973460173 25144647830908390865047565)
        ·
          refine ⟨9429242936590646574392837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25144647830908390865047565 9429242936590646574392837)
          ·
            refine ⟨1767983050610746232698657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9429242936590646574392837 1767983050610746232698657)
            ·
              refine ⟨1325987287958059674523993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1767983050610746232698657 1325987287958059674523993)
              ·
                refine ⟨994490465968544755892995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1325987287958059674523993 994490465968544755892995)
                ·
                  refine ⟨1491735698952817133839493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 994490465968544755892995 1491735698952817133839493)
                  ·
                    refine ⟨279700443553653212594905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1491735698952817133839493 279700443553653212594905)
                    ·
                      rfl

theorem cell23_1634144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 4, 2, 2, 1, 4].length) (baseStart_1634144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1634144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1634144 prefixEnd_1634144 := by exact prefixLift 1634144
  have htrace : WordTrace (prefixWord ++ tailWord_1634144) baseStart_1634144 baseEnd_1634144 := by
    simpa [prefixWord, tailWord_1634144, baseEnd_1634144] using wordTrace_append hprefix tailTrace_1634144
  have hstable : (prefixWord ++ tailWord_1634144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1634144).length < 2 ^ (prefixWord ++ tailWord_1634144).sum := by decide
  have hdescent : baseEnd_1634144 < baseStart_1634144 := by decide
  rcases family_descends (prefixWord ++ tailWord_1634144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1634240 : List Nat := [2, 1, 1, 2, 3, 2, 1, 1, 6, 1, 3]
def baseStart_1634240 : Nat := 118140960795 + 1634240 * 2 ^ 59
def prefixEnd_1634240 : Nat := 4983230072969 + 3 ^ 40 * 1634240 * 2
def baseEnd_1634240 : Nat := 839150624803791262184273

theorem tailTrace_1634240 : CollatzResearch.WordTrace tailWord_1634240 prefixEnd_1634240 839150624803791262184273 := by
  unfold tailWord_1634240
  simp only [CollatzResearch.WordTrace]
  refine ⟨29802814799717530408174087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39737086399623373877565449 29802814799717530408174087)
  ·
    refine ⟨44704222199576295612261131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29802814799717530408174087 44704222199576295612261131)
    ·
      refine ⟨67056333299364443418391697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44704222199576295612261131 67056333299364443418391697)
      ·
        refine ⟨50292249974523332563793773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67056333299364443418391697 50292249974523332563793773)
        ·
          refine ⟨18859593740446249711422665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50292249974523332563793773 18859593740446249711422665)
          ·
            refine ⟨14144695305334687283566999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18859593740446249711422665 14144695305334687283566999)
            ·
              refine ⟨21217042958002030925350499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14144695305334687283566999 21217042958002030925350499)
              ·
                refine ⟨31825564437003046388025749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21217042958002030925350499 31825564437003046388025749)
                ·
                  refine ⟨1491823332984517799438707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 31825564437003046388025749 1491823332984517799438707)
                  ·
                    refine ⟨2237734999476776699158061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1491823332984517799438707 2237734999476776699158061)
                    ·
                      refine ⟨839150624803791262184273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2237734999476776699158061 839150624803791262184273)
                      ·
                        rfl

theorem cell23_1634240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 1, 6, 1, 3].length) (baseStart_1634240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1634240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1634240 prefixEnd_1634240 := by exact prefixLift 1634240
  have htrace : WordTrace (prefixWord ++ tailWord_1634240) baseStart_1634240 baseEnd_1634240 := by
    simpa [prefixWord, tailWord_1634240, baseEnd_1634240] using wordTrace_append hprefix tailTrace_1634240
  have hstable : (prefixWord ++ tailWord_1634240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1634240).length < 2 ^ (prefixWord ++ tailWord_1634240).sum := by decide
  have hdescent : baseEnd_1634240 < baseStart_1634240 := by decide
  rcases family_descends (prefixWord ++ tailWord_1634240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1634258 : List Nat := [3, 2, 2, 3, 3, 1, 1, 1, 3, 2, 2]
def baseStart_1634258 : Nat := 118140960795 + 1634258 * 2 ^ 59
def prefixEnd_1634258 : Nat := 4983230072969 + 3 ^ 40 * 1634258 * 2
def baseEnd_1634258 : Nat := 839159867455572191759191

theorem tailTrace_1634258 : CollatzResearch.WordTrace tailWord_1634258 prefixEnd_1634258 839159867455572191759191 := by
  unfold tailWord_1634258
  simp only [CollatzResearch.WordTrace]
  refine ⟨14901571528342462472625857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39737524075579899927002285 14901571528342462472625857)
  ·
    refine ⟨11176178646256846854469393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14901571528342462472625857 11176178646256846854469393)
    ·
      refine ⟨8382133984692635140852045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11176178646256846854469393 8382133984692635140852045)
      ·
        refine ⟨3143300244259738177819517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8382133984692635140852045 3143300244259738177819517)
        ·
          refine ⟨1178737591597401816682319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3143300244259738177819517 1178737591597401816682319)
          ·
            refine ⟨1768106387396102725023479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1178737591597401816682319 1768106387396102725023479)
            ·
              refine ⟨2652159581094154087535219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1768106387396102725023479 2652159581094154087535219)
              ·
                refine ⟨3978239371641231131302829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2652159581094154087535219 3978239371641231131302829)
                ·
                  refine ⟨1491839764365461674238561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3978239371641231131302829 1491839764365461674238561)
                  ·
                    refine ⟨1118879823274096255678921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1491839764365461674238561 1118879823274096255678921)
                    ·
                      refine ⟨839159867455572191759191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1118879823274096255678921 839159867455572191759191)
                      ·
                        rfl

theorem cell23_1634258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 3, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 3, 1, 1, 1, 3, 2, 2].length) (baseStart_1634258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1634258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1634258 prefixEnd_1634258 := by exact prefixLift 1634258
  have htrace : WordTrace (prefixWord ++ tailWord_1634258) baseStart_1634258 baseEnd_1634258 := by
    simpa [prefixWord, tailWord_1634258, baseEnd_1634258] using wordTrace_append hprefix tailTrace_1634258
  have hstable : (prefixWord ++ tailWord_1634258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1634258).length < 2 ^ (prefixWord ++ tailWord_1634258).sum := by decide
  have hdescent : baseEnd_1634258 < baseStart_1634258 := by decide
  rcases family_descends (prefixWord ++ tailWord_1634258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1634263 : List Nat := [1, 1, 3, 2, 1, 1, 4, 1, 2, 3, 4]
def baseStart_1634263 : Nat := 118140960795 + 1634263 * 2 ^ 59
def prefixEnd_1634263 : Nat := 4983230072969 + 3 ^ 40 * 1634263 * 2
def baseEnd_1634263 : Nat := 839162434858844672196667

theorem tailTrace_1634263 : CollatzResearch.WordTrace tailWord_1634263 prefixEnd_1634263 839162434858844672196667 := by
  unfold tailWord_1634263
  simp only [CollatzResearch.WordTrace]
  refine ⟨59606468478351735744435443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39737645652234490496290295 59606468478351735744435443)
  ·
    refine ⟨89409702717527603616653165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59606468478351735744435443 89409702717527603616653165)
    ·
      refine ⟨33528638519072851356244937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89409702717527603616653165 33528638519072851356244937)
      ·
        refine ⟨25146478889304638517183703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33528638519072851356244937 25146478889304638517183703)
        ·
          refine ⟨37719718333956957775775555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25146478889304638517183703 37719718333956957775775555)
          ·
            refine ⟨56579577500935436663663333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37719718333956957775775555 56579577500935436663663333)
            ·
              refine ⟨10608670781425394374436875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 56579577500935436663663333 10608670781425394374436875)
              ·
                refine ⟨15913006172138091561655313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10608670781425394374436875 15913006172138091561655313)
                ·
                  refine ⟨11934754629103568671241485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15913006172138091561655313 11934754629103568671241485)
                  ·
                    refine ⟨4475532985913838251715557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11934754629103568671241485 4475532985913838251715557)
                    ·
                      refine ⟨839162434858844672196667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4475532985913838251715557 839162434858844672196667)
                      ·
                        rfl

theorem cell23_1634263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 1, 2, 3, 4].length) (baseStart_1634263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1634263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1634263 prefixEnd_1634263 := by exact prefixLift 1634263
  have htrace : WordTrace (prefixWord ++ tailWord_1634263) baseStart_1634263 baseEnd_1634263 := by
    simpa [prefixWord, tailWord_1634263, baseEnd_1634263] using wordTrace_append hprefix tailTrace_1634263
  have hstable : (prefixWord ++ tailWord_1634263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1634263).length < 2 ^ (prefixWord ++ tailWord_1634263).sum := by decide
  have hdescent : baseEnd_1634263 < baseStart_1634263 := by decide
  rcases family_descends (prefixWord ++ tailWord_1634263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1634273 : List Nat := [1, 2, 3, 1, 2, 1, 2, 3, 2, 6]
def baseStart_1634273 : Nat := 118140960795 + 1634273 * 2 ^ 59
def prefixEnd_1634273 : Nat := 4983230072969 + 3 ^ 40 * 1634273 * 2
def baseEnd_1634273 : Nat := 279722523221796544357207

theorem tailTrace_1634273 : CollatzResearch.WordTrace tailWord_1634273 prefixEnd_1634273 279722523221796544357207 := by
  unfold tailWord_1634273
  simp only [CollatzResearch.WordTrace]
  refine ⟨59606833208315507452299473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39737888805543671634866315 59606833208315507452299473)
  ·
    refine ⟨44705124906236630589224605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59606833208315507452299473 44705124906236630589224605)
    ·
      refine ⟨16764421839838736470959227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44705124906236630589224605 16764421839838736470959227)
      ·
        refine ⟨25146632759758104706438841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16764421839838736470959227 25146632759758104706438841)
        ·
          refine ⟨18859974569818578529829131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25146632759758104706438841 18859974569818578529829131)
          ·
            refine ⟨28289961854727867794743697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18859974569818578529829131 28289961854727867794743697)
            ·
              refine ⟨21217471391045900846057773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28289961854727867794743697 21217471391045900846057773)
              ·
                refine ⟨7956551771642212817271665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21217471391045900846057773 7956551771642212817271665)
                ·
                  refine ⟨5967413828731659612953749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7956551771642212817271665 5967413828731659612953749)
                  ·
                    refine ⟨279722523221796544357207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5967413828731659612953749 279722523221796544357207)
                    ·
                      rfl

theorem cell23_1634273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 3, 2, 6].length) (baseStart_1634273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1634273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1634273 prefixEnd_1634273 := by exact prefixLift 1634273
  have htrace : WordTrace (prefixWord ++ tailWord_1634273) baseStart_1634273 baseEnd_1634273 := by
    simpa [prefixWord, tailWord_1634273, baseEnd_1634273] using wordTrace_append hprefix tailTrace_1634273
  have hstable : (prefixWord ++ tailWord_1634273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1634273).length < 2 ^ (prefixWord ++ tailWord_1634273).sum := by decide
  have hdescent : baseEnd_1634273 < baseStart_1634273 := by decide
  rcases family_descends (prefixWord ++ tailWord_1634273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1634297 : List Nat := [1, 2, 1, 3, 1, 5, 1, 2, 1, 4, 2]
def baseStart_1634297 : Nat := 118140960795 + 1634297 * 2 ^ 59
def prefixEnd_1634297 : Nat := 4983230072969 + 3 ^ 40 * 1634297 * 2
def baseEnd_1634297 : Nat := 839179893201097539171511

theorem tailTrace_1634297 : CollatzResearch.WordTrace tailWord_1634297 prefixEnd_1634297 839179893201097539171511 := by
  unfold tailWord_1634297
  simp only [CollatzResearch.WordTrace]
  refine ⟨59607708560228559551173145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39738472373485706367448763 59607708560228559551173145)
  ·
    refine ⟨44705781420171419663379859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59607708560228559551173145 44705781420171419663379859)
    ·
      refine ⟨67058672130257129495069789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44705781420171419663379859 67058672130257129495069789)
      ·
        refine ⟨25147002048846423560651171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67058672130257129495069789 25147002048846423560651171)
        ·
          refine ⟨37720503073269635340976757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25147002048846423560651171 37720503073269635340976757)
          ·
            refine ⟨3536297163119028313216571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 37720503073269635340976757 3536297163119028313216571)
            ·
              refine ⟨5304445744678542469824857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3536297163119028313216571 5304445744678542469824857)
              ·
                refine ⟨3978334308508906852368643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5304445744678542469824857 3978334308508906852368643)
                ·
                  refine ⟨5967501462763360278552965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3978334308508906852368643 5967501462763360278552965)
                  ·
                    refine ⟨1118906524268130052228681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5967501462763360278552965 1118906524268130052228681)
                    ·
                      refine ⟨839179893201097539171511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1118906524268130052228681 839179893201097539171511)
                      ·
                        rfl

theorem cell23_1634297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 1, 2, 1, 4, 2].length) (baseStart_1634297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1634297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1634297 prefixEnd_1634297 := by exact prefixLift 1634297
  have htrace : WordTrace (prefixWord ++ tailWord_1634297) baseStart_1634297 baseEnd_1634297 := by
    simpa [prefixWord, tailWord_1634297, baseEnd_1634297] using wordTrace_append hprefix tailTrace_1634297
  have hstable : (prefixWord ++ tailWord_1634297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1634297).length < 2 ^ (prefixWord ++ tailWord_1634297).sum := by decide
  have hdescent : baseEnd_1634297 < baseStart_1634297 := by decide
  rcases family_descends (prefixWord ++ tailWord_1634297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1634320 : List Nat := [2, 1, 1, 1, 1, 1, 1, 10, 5]
def baseStart_1634320 : Nat := 118140960795 + 1634320 * 2 ^ 59
def prefixEnd_1634320 : Nat := 4983230072969 + 3 ^ 40 * 1634320 * 2
def baseEnd_1634320 : Nat := 93243522584016772131545

theorem tailTrace_1634320 : CollatzResearch.WordTrace tailWord_1634320 prefixEnd_1634320 93243522584016772131545 := by
  unfold tailWord_1634320
  simp only [CollatzResearch.WordTrace]
  refine ⟨29804273719572617239630207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39739031626096822986173609 29804273719572617239630207)
  ·
    refine ⟨44706410579358925859445311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29804273719572617239630207 44706410579358925859445311)
    ·
      refine ⟨67059615869038388789167967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44706410579358925859445311 67059615869038388789167967)
      ·
        refine ⟨100589423803557583183751951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67059615869038388789167967 100589423803557583183751951)
        ·
          refine ⟨150884135705336374775627927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100589423803557583183751951 150884135705336374775627927)
          ·
            refine ⟨226326203558004562163441891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150884135705336374775627927 226326203558004562163441891)
            ·
              refine ⟨339489305337006843245162837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 226326203558004562163441891 339489305337006843245162837)
              ·
                refine ⟨994597574229512236069813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 339489305337006843245162837 994597574229512236069813)
                ·
                  refine ⟨93243522584016772131545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 994597574229512236069813 93243522584016772131545)
                  ·
                    rfl

theorem cell23_1634320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 10, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 10, 5].length) (baseStart_1634320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1634320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1634320 prefixEnd_1634320 := by exact prefixLift 1634320
  have htrace : WordTrace (prefixWord ++ tailWord_1634320) baseStart_1634320 baseEnd_1634320 := by
    simpa [prefixWord, tailWord_1634320, baseEnd_1634320] using wordTrace_append hprefix tailTrace_1634320
  have hstable : (prefixWord ++ tailWord_1634320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1634320).length < 2 ^ (prefixWord ++ tailWord_1634320).sum := by decide
  have hdescent : baseEnd_1634320 < baseStart_1634320 := by decide
  rcases family_descends (prefixWord ++ tailWord_1634320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1634324 : List Nat := [2, 4, 3, 2, 1, 1, 1, 1, 2, 6]
def baseStart_1634324 : Nat := 118140960795 + 1634324 * 2 ^ 59
def prefixEnd_1634324 : Nat := 4983230072969 + 3 ^ 40 * 1634324 * 2
def baseEnd_1634324 : Nat := 279731252392922977844629

theorem tailTrace_1634324 : CollatzResearch.WordTrace tailWord_1634324 prefixEnd_1634324 279731252392922977844629 := by
  unfold tailWord_1634324
  simp only [CollatzResearch.WordTrace]
  refine ⟨29804346665565371581203013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39739128887420495441604017 29804346665565371581203013)
  ·
    refine ⟨5588314999793507171475565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29804346665565371581203013 5588314999793507171475565)
    ·
      refine ⟨2095618124922565189303337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5588314999793507171475565 2095618124922565189303337)
      ·
        refine ⟨1571713593691923891977503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2095618124922565189303337 1571713593691923891977503)
        ·
          refine ⟨2357570390537885837966255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1571713593691923891977503 2357570390537885837966255)
          ·
            refine ⟨3536355585806828756949383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2357570390537885837966255 3536355585806828756949383)
            ·
              refine ⟨5304533378710243135424075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3536355585806828756949383 5304533378710243135424075)
              ·
                refine ⟨7956800068065364703136113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5304533378710243135424075 7956800068065364703136113)
                ·
                  refine ⟨5967600051049023527352085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7956800068065364703136113 5967600051049023527352085)
                  ·
                    refine ⟨279731252392922977844629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5967600051049023527352085 279731252392922977844629)
                    ·
                      rfl

theorem cell23_1634324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 1, 1, 2, 6].length) (baseStart_1634324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1634324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1634324 prefixEnd_1634324 := by exact prefixLift 1634324
  have htrace : WordTrace (prefixWord ++ tailWord_1634324) baseStart_1634324 baseEnd_1634324 := by
    simpa [prefixWord, tailWord_1634324, baseEnd_1634324] using wordTrace_append hprefix tailTrace_1634324
  have hstable : (prefixWord ++ tailWord_1634324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1634324).length < 2 ^ (prefixWord ++ tailWord_1634324).sum := by decide
  have hdescent : baseEnd_1634324 < baseStart_1634324 := by decide
  rcases family_descends (prefixWord ++ tailWord_1634324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1634327 : List Nat := [1, 1, 3, 5, 2, 1, 1, 1, 2, 2, 4]
def baseStart_1634327 : Nat := 118140960795 + 1634327 * 2 ^ 59
def prefixEnd_1634327 : Nat := 4983230072969 + 3 ^ 40 * 1634327 * 2
def baseEnd_1634327 : Nat := 839195297620732421796373

theorem tailTrace_1634327 : CollatzResearch.WordTrace tailWord_1634327 prefixEnd_1634327 839195297620732421796373 := by
  unfold tailWord_1634327
  simp only [CollatzResearch.WordTrace]
  refine ⟨59608802750119874674765235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39739201833413249783176823 59608802750119874674765235)
  ·
    refine ⟨89413204125179812012147853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59608802750119874674765235 89413204125179812012147853)
    ·
      refine ⟨33529951546942429504555445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89413204125179812012147853 33529951546942429504555445)
      ·
        refine ⟨3143432957525852766052073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 33529951546942429504555445 3143432957525852766052073)
        ·
          refine ⟨2357574718144389574539055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3143432957525852766052073 2357574718144389574539055)
          ·
            refine ⟨3536362077216584361808583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2357574718144389574539055 3536362077216584361808583)
            ·
              refine ⟨5304543115824876542712875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3536362077216584361808583 5304543115824876542712875)
              ·
                refine ⟨7956814673737314814069313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5304543115824876542712875 7956814673737314814069313)
                ·
                  refine ⟨5967611005302986110551985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7956814673737314814069313 5967611005302986110551985)
                  ·
                    refine ⟨4475708253977239582913989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5967611005302986110551985 4475708253977239582913989)
                    ·
                      refine ⟨839195297620732421796373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4475708253977239582913989 839195297620732421796373)
                      ·
                        rfl

theorem cell23_1634327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 1, 1, 2, 2, 4].length) (baseStart_1634327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1634327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1634327 prefixEnd_1634327 := by exact prefixLift 1634327
  have htrace : WordTrace (prefixWord ++ tailWord_1634327) baseStart_1634327 baseEnd_1634327 := by
    simpa [prefixWord, tailWord_1634327, baseEnd_1634327] using wordTrace_append hprefix tailTrace_1634327
  have hstable : (prefixWord ++ tailWord_1634327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1634327).length < 2 ^ (prefixWord ++ tailWord_1634327).sum := by decide
  have hdescent : baseEnd_1634327 < baseStart_1634327 := by decide
  rcases family_descends (prefixWord ++ tailWord_1634327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1634330 : List Nat := [3, 1, 1, 3, 1, 3, 1, 1, 1, 5, 3]
def baseStart_1634330 : Nat := 118140960795 + 1634330 * 2 ^ 59
def prefixEnd_1634330 : Nat := 4983230072969 + 3 ^ 40 * 1634330 * 2
def baseEnd_1634330 : Nat := 839196838062695910058859

theorem tailTrace_1634330 : CollatzResearch.WordTrace tailWord_1634330 prefixEnd_1634330 839196838062695910058859 := by
  unfold tailWord_1634330
  simp only [CollatzResearch.WordTrace]
  refine ⟨14902228042277251546781111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39739274779406004124749629 14902228042277251546781111)
  ·
    refine ⟨22353342063415877320171667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14902228042277251546781111 22353342063415877320171667)
    ·
      refine ⟨33530013095123815980257501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22353342063415877320171667 33530013095123815980257501)
      ·
        refine ⟨12573754910671430992596563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33530013095123815980257501 12573754910671430992596563)
        ·
          refine ⟨18860632366007146488894845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12573754910671430992596563 18860632366007146488894845)
          ·
            refine ⟨7072737137252679933335567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18860632366007146488894845 7072737137252679933335567)
            ·
              refine ⟨10609105705879019900003351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7072737137252679933335567 10609105705879019900003351)
              ·
                refine ⟨15913658558818529850005027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10609105705879019900003351 15913658558818529850005027)
                ·
                  refine ⟨23870487838227794775007541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15913658558818529850005027 23870487838227794775007541)
                  ·
                    refine ⟨2237858234833855760156957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 23870487838227794775007541 2237858234833855760156957)
                    ·
                      refine ⟨839196838062695910058859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2237858234833855760156957 839196838062695910058859)
                      ·
                        rfl

theorem cell23_1634330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 1, 1, 5, 3].length) (baseStart_1634330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1634330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1634330 prefixEnd_1634330 := by exact prefixLift 1634330
  have htrace : WordTrace (prefixWord ++ tailWord_1634330) baseStart_1634330 baseEnd_1634330 := by
    simpa [prefixWord, tailWord_1634330, baseEnd_1634330] using wordTrace_append hprefix tailTrace_1634330
  have hstable : (prefixWord ++ tailWord_1634330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1634330).length < 2 ^ (prefixWord ++ tailWord_1634330).sum := by decide
  have hdescent : baseEnd_1634330 < baseStart_1634330 := by decide
  rcases family_descends (prefixWord ++ tailWord_1634330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1634407 : List Nat := [1, 1, 5, 1, 1, 2, 2, 3, 2, 2, 3]
def baseStart_1634407 : Nat := 118140960795 + 1634407 * 2 ^ 59
def prefixEnd_1634407 : Nat := 4983230072969 + 3 ^ 40 * 1634407 * 2
def baseEnd_1634407 : Nat := 839236376073092108796005

theorem tailTrace_1634407 : CollatzResearch.WordTrace tailWord_1634407 prefixEnd_1634407 839236376073092108796005 := by
  unfold tailWord_1634407
  simp only [CollatzResearch.WordTrace]
  refine ⟨59611720589830048337677475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39741147059886698891784983 59611720589830048337677475)
  ·
    refine ⟨89417580884745072506516213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59611720589830048337677475 89417580884745072506516213)
    ·
      refine ⟨8382898207944850547485895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 89417580884745072506516213 8382898207944850547485895)
      ·
        refine ⟨12574347311917275821228843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8382898207944850547485895 12574347311917275821228843)
        ·
          refine ⟨18861520967875913731843265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12574347311917275821228843 18861520967875913731843265)
          ·
            refine ⟨14146140725906935298882449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18861520967875913731843265 14146140725906935298882449)
            ·
              refine ⟨10609605544430201474161837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14146140725906935298882449 10609605544430201474161837)
              ·
                refine ⟨3978602079161325552810689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10609605544430201474161837 3978602079161325552810689)
                ·
                  refine ⟨2983951559370994164608017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3978602079161325552810689 2983951559370994164608017)
                  ·
                    refine ⟨2237963669528245623456013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2983951559370994164608017 2237963669528245623456013)
                    ·
                      refine ⟨839236376073092108796005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2237963669528245623456013 839236376073092108796005)
                      ·
                        rfl

theorem cell23_1634407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 3, 2, 2, 3].length) (baseStart_1634407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1634407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1634407 prefixEnd_1634407 := by exact prefixLift 1634407
  have htrace : WordTrace (prefixWord ++ tailWord_1634407) baseStart_1634407 baseEnd_1634407 := by
    simpa [prefixWord, tailWord_1634407, baseEnd_1634407] using wordTrace_append hprefix tailTrace_1634407
  have hstable : (prefixWord ++ tailWord_1634407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1634407).length < 2 ^ (prefixWord ++ tailWord_1634407).sum := by decide
  have hdescent : baseEnd_1634407 < baseStart_1634407 := by decide
  rcases family_descends (prefixWord ++ tailWord_1634407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1634464 : List Nat := [2, 1, 1, 4, 2, 2, 1, 3, 2, 3, 2]
def baseStart_1634464 : Nat := 118140960795 + 1634464 * 2 ^ 59
def prefixEnd_1634464 : Nat := 4983230072969 + 3 ^ 40 * 1634464 * 2
def baseEnd_1634464 : Nat := 839265644470398385783243

theorem tailTrace_1634464 : CollatzResearch.WordTrace tailWord_1634464 prefixEnd_1634464 839265644470398385783243 := by
  unfold tailWord_1634464
  simp only [CollatzResearch.WordTrace]
  refine ⟨29806899775311773536251223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39742533033749031381668297 29806899775311773536251223)
  ·
    refine ⟨44710349662967660304376835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29806899775311773536251223 44710349662967660304376835)
    ·
      refine ⟨67065524494451490456565253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44710349662967660304376835 67065524494451490456565253)
      ·
        refine ⟨12574785842709654460605985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 67065524494451490456565253 12574785842709654460605985)
        ·
          refine ⟨9431089382032240845454489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12574785842709654460605985 9431089382032240845454489)
          ·
            refine ⟨7073317036524180634090867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9431089382032240845454489 7073317036524180634090867)
            ·
              refine ⟨10609975554786270951136301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7073317036524180634090867 10609975554786270951136301)
              ·
                refine ⟨3978740833044851606676113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10609975554786270951136301 3978740833044851606676113)
                ·
                  refine ⟨2984055624783638705007085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3978740833044851606676113 2984055624783638705007085)
                  ·
                    refine ⟨1119020859293864514377657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2984055624783638705007085 1119020859293864514377657)
                    ·
                      refine ⟨839265644470398385783243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1119020859293864514377657 839265644470398385783243)
                      ·
                        rfl

theorem cell23_1634464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 3, 2, 3, 2].length) (baseStart_1634464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1634464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1634464 prefixEnd_1634464 := by exact prefixLift 1634464
  have htrace : WordTrace (prefixWord ++ tailWord_1634464) baseStart_1634464 baseEnd_1634464 := by
    simpa [prefixWord, tailWord_1634464, baseEnd_1634464] using wordTrace_append hprefix tailTrace_1634464
  have hstable : (prefixWord ++ tailWord_1634464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1634464).length < 2 ^ (prefixWord ++ tailWord_1634464).sum := by decide
  have hdescent : baseEnd_1634464 < baseStart_1634464 := by decide
  rcases family_descends (prefixWord ++ tailWord_1634464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1634490 : List Nat := [3, 1, 1, 1, 2, 2, 2, 1, 3, 1, 6]
def baseStart_1634490 : Nat := 118140960795 + 1634490 * 2 ^ 59
def prefixEnd_1634490 : Nat := 4983230072969 + 3 ^ 40 * 1634490 * 2
def baseEnd_1634490 : Nat := 839278994967415284058123

theorem tailTrace_1634490 : CollatzResearch.WordTrace tailWord_1634490 prefixEnd_1634490 839278994967415284058123 := by
  unfold tailWord_1634490
  simp only [CollatzResearch.WordTrace]
  refine ⟨14903686962132338378237231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39743165232352902341965949 14903686962132338378237231)
  ·
    refine ⟨22355530443198507567355847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14903686962132338378237231 22355530443198507567355847)
    ·
      refine ⟨33533295664797761351033771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22355530443198507567355847 33533295664797761351033771)
      ·
        refine ⟨50299943497196642026550657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33533295664797761351033771 50299943497196642026550657)
        ·
          refine ⟨37724957622897481519912993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50299943497196642026550657 37724957622897481519912993)
          ·
            refine ⟨28293718217173111139934745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37724957622897481519912993 28293718217173111139934745)
            ·
              refine ⟨21220288662879833354951059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28293718217173111139934745 21220288662879833354951059)
              ·
                refine ⟨31830432994319750032426589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21220288662879833354951059 31830432994319750032426589)
                ·
                  refine ⟨11936412372869906262159971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31830432994319750032426589 11936412372869906262159971)
                  ·
                    refine ⟨17904618559304859393239957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11936412372869906262159971 17904618559304859393239957)
                    ·
                      refine ⟨839278994967415284058123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 17904618559304859393239957 839278994967415284058123)
                      ·
                        rfl

theorem cell23_1634490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 1, 3, 1, 6].length) (baseStart_1634490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1634490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1634490 prefixEnd_1634490 := by exact prefixLift 1634490
  have htrace : WordTrace (prefixWord ++ tailWord_1634490) baseStart_1634490 baseEnd_1634490 := by
    simpa [prefixWord, tailWord_1634490, baseEnd_1634490] using wordTrace_append hprefix tailTrace_1634490
  have hstable : (prefixWord ++ tailWord_1634490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1634490).length < 2 ^ (prefixWord ++ tailWord_1634490).sum := by decide
  have hdescent : baseEnd_1634490 < baseStart_1634490 := by decide
  rcases family_descends (prefixWord ++ tailWord_1634490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1634507 : List Nat := [1, 1, 1, 1, 3, 2, 6, 1, 1, 2, 4]
def baseStart_1634507 : Nat := 118140960795 + 1634507 * 2 ^ 59
def prefixEnd_1634507 : Nat := 4983230072969 + 3 ^ 40 * 1634507 * 2
def baseEnd_1634507 : Nat := 839287724138541717545545

theorem tailTrace_1634507 : CollatzResearch.WordTrace tailWord_1634507 prefixEnd_1634507 839287724138541717545545 := by
  unfold tailWord_1634507
  simp only [CollatzResearch.WordTrace]
  refine ⟨59615367889467765416317775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39743578592978510277545183 59615367889467765416317775)
  ·
    refine ⟨89423051834201648124476663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59615367889467765416317775 89423051834201648124476663)
    ·
      refine ⟨134134577751302472186714995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89423051834201648124476663 134134577751302472186714995)
      ·
        refine ⟨201201866626953708280072493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134134577751302472186714995 201201866626953708280072493)
        ·
          refine ⟨75450699985107640605027185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 201201866626953708280072493 75450699985107640605027185)
          ·
            refine ⟨56588024988830730453770389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75450699985107640605027185 56588024988830730453770389)
            ·
              refine ⟨2652563671351440490020487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 56588024988830730453770389 2652563671351440490020487)
              ·
                refine ⟨3978845507027160735030731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2652563671351440490020487 3978845507027160735030731)
                ·
                  refine ⟨5968268260540741102546097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3978845507027160735030731 5968268260540741102546097)
                  ·
                    refine ⟨4476201195405555826909573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5968268260540741102546097 4476201195405555826909573)
                    ·
                      refine ⟨839287724138541717545545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4476201195405555826909573 839287724138541717545545)
                      ·
                        rfl

theorem cell23_1634507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 6, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 6, 1, 1, 2, 4].length) (baseStart_1634507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1634507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1634507 prefixEnd_1634507 := by exact prefixLift 1634507
  have htrace : WordTrace (prefixWord ++ tailWord_1634507) baseStart_1634507 baseEnd_1634507 := by
    simpa [prefixWord, tailWord_1634507, baseEnd_1634507] using wordTrace_append hprefix tailTrace_1634507
  have hstable : (prefixWord ++ tailWord_1634507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1634507).length < 2 ^ (prefixWord ++ tailWord_1634507).sum := by decide
  have hdescent : baseEnd_1634507 < baseStart_1634507 := by decide
  rcases family_descends (prefixWord ++ tailWord_1634507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1634514 : List Nat := [3, 2, 2, 2, 1, 2, 2, 1, 3, 2, 3]
def baseStart_1634514 : Nat := 118140960795 + 1634514 * 2 ^ 59
def prefixEnd_1634514 : Nat := 4983230072969 + 3 ^ 40 * 1634514 * 2
def baseEnd_1634514 : Nat := 839291318503123190158013

theorem tailTrace_1634514 : CollatzResearch.WordTrace tailWord_1634514 prefixEnd_1634514 839291318503123190158013 := by
  unfold tailWord_1634514
  simp only [CollatzResearch.WordTrace]
  refine ⟨14903905800110601402955649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39743748800294937074548397 14903905800110601402955649)
  ·
    refine ⟨11177929350082951052216737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14903905800110601402955649 11177929350082951052216737)
    ·
      refine ⟨8383447012562213289162553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11177929350082951052216737 8383447012562213289162553)
      ·
        refine ⟨6287585259421659966871915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8383447012562213289162553 6287585259421659966871915)
        ·
          refine ⟨9431377889132489950307873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6287585259421659966871915 9431377889132489950307873)
          ·
            refine ⟨7073533416849367462730905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9431377889132489950307873 7073533416849367462730905)
            ·
              refine ⟨5305150062637025597048179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7073533416849367462730905 5305150062637025597048179)
              ·
                refine ⟨7957725093955538395572269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5305150062637025597048179 7957725093955538395572269)
                ·
                  refine ⟨2984146910233326898339601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7957725093955538395572269 2984146910233326898339601)
                  ·
                    refine ⟨2238110182674995173754701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2984146910233326898339601 2238110182674995173754701)
                    ·
                      refine ⟨839291318503123190158013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2238110182674995173754701 839291318503123190158013)
                      ·
                        rfl

theorem cell23_1634514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 2, 1, 3, 2, 3].length) (baseStart_1634514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1634514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1634514 prefixEnd_1634514 := by exact prefixLift 1634514
  have htrace : WordTrace (prefixWord ++ tailWord_1634514) baseStart_1634514 baseEnd_1634514 := by
    simpa [prefixWord, tailWord_1634514, baseEnd_1634514] using wordTrace_append hprefix tailTrace_1634514
  have hstable : (prefixWord ++ tailWord_1634514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1634514).length < 2 ^ (prefixWord ++ tailWord_1634514).sum := by decide
  have hdescent : baseEnd_1634514 < baseStart_1634514 := by decide
  rcases family_descends (prefixWord ++ tailWord_1634514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1634528 : List Nat := [2, 1, 1, 3, 1, 3, 4, 3, 1, 2, 2]
def baseStart_1634528 : Nat := 118140960795 + 1634528 * 2 ^ 59
def prefixEnd_1634528 : Nat := 4983230072969 + 3 ^ 40 * 1634528 * 2
def baseEnd_1634528 : Nat := 839298507232286135382949

theorem tailTrace_1634528 : CollatzResearch.WordTrace tailWord_1634528 prefixEnd_1634528 839298507232286135382949 := by
  unfold tailWord_1634528
  simp only [CollatzResearch.WordTrace]
  refine ⟨29808066911195843001416119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39744089214927790668554825 29808066911195843001416119)
  ·
    refine ⟨44712100366793764502124179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29808066911195843001416119 44712100366793764502124179)
    ·
      refine ⟨67068150550190646753186269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44712100366793764502124179 67068150550190646753186269)
      ·
        refine ⟨25150556456321492532444851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67068150550190646753186269 25150556456321492532444851)
        ·
          refine ⟨37725834684482238798667277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25150556456321492532444851 37725834684482238798667277)
          ·
            refine ⟨14147188006680839549500229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37725834684482238798667277 14147188006680839549500229)
            ·
              refine ⟨2652597751252657415531293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14147188006680839549500229 2652597751252657415531293)
              ·
                refine ⟨994724156719746530824235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2652597751252657415531293 994724156719746530824235)
                ·
                  refine ⟨1492086235079619796236353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 994724156719746530824235 1492086235079619796236353)
                  ·
                    refine ⟨1119064676309714847177265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1492086235079619796236353 1119064676309714847177265)
                    ·
                      refine ⟨839298507232286135382949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1119064676309714847177265 839298507232286135382949)
                      ·
                        rfl

theorem cell23_1634528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 4, 3, 1, 2, 2].length) (baseStart_1634528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1634528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1634528 prefixEnd_1634528 := by exact prefixLift 1634528
  have htrace : WordTrace (prefixWord ++ tailWord_1634528) baseStart_1634528 baseEnd_1634528 := by
    simpa [prefixWord, tailWord_1634528, baseEnd_1634528] using wordTrace_append hprefix tailTrace_1634528
  have hstable : (prefixWord ++ tailWord_1634528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1634528).length < 2 ^ (prefixWord ++ tailWord_1634528).sum := by decide
  have hdescent : baseEnd_1634528 < baseStart_1634528 := by decide
  rcases family_descends (prefixWord ++ tailWord_1634528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1634571 : List Nat := [1, 1, 1, 1, 5, 2, 4, 2, 1, 3, 2]
def baseStart_1634571 : Nat := 118140960795 + 1634571 * 2 ^ 59
def prefixEnd_1634571 : Nat := 4983230072969 + 3 ^ 40 * 1634571 * 2
def baseEnd_1634571 : Nat := 839320586900429467145251

theorem tailTrace_1634571 : CollatzResearch.WordTrace tailWord_1634571 prefixEnd_1634571 839320586900429467145251 := by
  unfold tailWord_1634571
  simp only [CollatzResearch.WordTrace]
  refine ⟨59617702161235904346647567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39745134774157269564431711 59617702161235904346647567)
  ·
    refine ⟨89426553241853856519971351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59617702161235904346647567 89426553241853856519971351)
    ·
      refine ⟨134139829862780784779957027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89426553241853856519971351 134139829862780784779957027)
      ·
        refine ⟨201209744794171177169935541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134139829862780784779957027 201209744794171177169935541)
        ·
          refine ⟨18863413574453547859681457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 201209744794171177169935541 18863413574453547859681457)
          ·
            refine ⟨14147560180840160894761093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18863413574453547859681457 14147560180840160894761093)
            ·
              refine ⟨2652667533907530167767705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14147560180840160894761093 2652667533907530167767705)
              ·
                refine ⟨1989500650430647625825779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2652667533907530167767705 1989500650430647625825779)
                ·
                  refine ⟨2984250975645971438738669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1989500650430647625825779 2984250975645971438738669)
                  ·
                    refine ⟨1119094115867239289527001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2984250975645971438738669 1119094115867239289527001)
                    ·
                      refine ⟨839320586900429467145251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1119094115867239289527001 839320586900429467145251)
                      ·
                        rfl

theorem cell23_1634571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 4, 2, 1, 3, 2].length) (baseStart_1634571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1634571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1634571 prefixEnd_1634571 := by exact prefixLift 1634571
  have htrace : WordTrace (prefixWord ++ tailWord_1634571) baseStart_1634571 baseEnd_1634571 := by
    simpa [prefixWord, tailWord_1634571, baseEnd_1634571] using wordTrace_append hprefix tailTrace_1634571
  have hstable : (prefixWord ++ tailWord_1634571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1634571).length < 2 ^ (prefixWord ++ tailWord_1634571).sum := by decide
  have hdescent : baseEnd_1634571 < baseStart_1634571 := by decide
  rcases family_descends (prefixWord ++ tailWord_1634571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1634584 : List Nat := [2, 1, 2, 3, 1, 2, 2, 1, 3, 4, 2]
def baseStart_1634584 : Nat := 118140960795 + 1634584 * 2 ^ 59
def prefixEnd_1634584 : Nat := 4983230072969 + 3 ^ 40 * 1634584 * 2
def baseEnd_1634584 : Nat := 839327262148937916282691

theorem tailTrace_1634584 : CollatzResearch.WordTrace tailWord_1634584 prefixEnd_1634584 839327262148937916282691 := by
  unfold tailWord_1634584
  simp only [CollatzResearch.WordTrace]
  refine ⟨29809088155094403783435403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39745450873459205044580537 29809088155094403783435403)
  ·
    refine ⟨44713632232641605675153105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29809088155094403783435403 44713632232641605675153105)
    ·
      refine ⟨33535224174481204256364829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44713632232641605675153105 33535224174481204256364829)
      ·
        refine ⟨12575709065430451596136811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33535224174481204256364829 12575709065430451596136811)
        ·
          refine ⟨18863563598145677394205217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12575709065430451596136811 18863563598145677394205217)
          ·
            refine ⟨14147672698609258045653913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18863563598145677394205217 14147672698609258045653913)
            ·
              refine ⟨10610754523956943534240435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14147672698609258045653913 10610754523956943534240435)
              ·
                refine ⟨15916131785935415301360653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10610754523956943534240435 15916131785935415301360653)
                ·
                  refine ⟨5968549419725780738010245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15916131785935415301360653 5968549419725780738010245)
                  ·
                    refine ⟨1119103016198583888376921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5968549419725780738010245 1119103016198583888376921)
                    ·
                      refine ⟨839327262148937916282691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1119103016198583888376921 839327262148937916282691)
                      ·
                        rfl

theorem cell23_1634584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 1, 3, 4, 2].length) (baseStart_1634584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1634584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1634584 prefixEnd_1634584 := by exact prefixLift 1634584
  have htrace : WordTrace (prefixWord ++ tailWord_1634584) baseStart_1634584 baseEnd_1634584 := by
    simpa [prefixWord, tailWord_1634584, baseEnd_1634584] using wordTrace_append hprefix tailTrace_1634584
  have hstable : (prefixWord ++ tailWord_1634584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1634584).length < 2 ^ (prefixWord ++ tailWord_1634584).sum := by decide
  have hdescent : baseEnd_1634584 < baseStart_1634584 := by decide
  rcases family_descends (prefixWord ++ tailWord_1634584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1634607 : List Nat := [1, 1, 2, 1, 2, 1, 7, 1, 7]
def baseStart_1634607 : Nat := 118140960795 + 1634607 * 2 ^ 59
def prefixEnd_1634607 : Nat := 4983230072969 + 3 ^ 40 * 1634607 * 2
def baseEnd_1634607 : Nat := 93259896911554591810565

theorem tailTrace_1634607 : CollatzResearch.WordTrace tailWord_1634607 prefixEnd_1634607 93259896911554591810565 := by
  unfold tailWord_1634607
  simp only [CollatzResearch.WordTrace]
  refine ⟨59619015189105482494958075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39746010126070321663305383 59619015189105482494958075)
  ·
    refine ⟨89428522783658223742437113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59619015189105482494958075 89428522783658223742437113)
    ·
      refine ⟨67071392087743667806827835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89428522783658223742437113 67071392087743667806827835)
      ·
        refine ⟨100607088131615501710241753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67071392087743667806827835 100607088131615501710241753)
        ·
          refine ⟨75455316098711626282681315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100607088131615501710241753 75455316098711626282681315)
          ·
            refine ⟨113182974148067439424021973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75455316098711626282681315 113182974148067439424021973)
            ·
              refine ⟨2652725956595330611500515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 113182974148067439424021973 2652725956595330611500515)
              ·
                refine ⟨3979088934892995917250773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2652725956595330611500515 3979088934892995917250773)
                ·
                  refine ⟨93259896911554591810565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3979088934892995917250773 93259896911554591810565)
                  ·
                    rfl

theorem cell23_1634607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 7, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 7, 1, 7].length) (baseStart_1634607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1634607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1634607 prefixEnd_1634607 := by exact prefixLift 1634607
  have htrace : WordTrace (prefixWord ++ tailWord_1634607) baseStart_1634607 baseEnd_1634607 := by
    simpa [prefixWord, tailWord_1634607, baseEnd_1634607] using wordTrace_append hprefix tailTrace_1634607
  have hstable : (prefixWord ++ tailWord_1634607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1634607).length < 2 ^ (prefixWord ++ tailWord_1634607).sum := by decide
  have hdescent : baseEnd_1634607 < baseStart_1634607 := by decide
  rcases family_descends (prefixWord ++ tailWord_1634607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1634618 : List Nat := [3, 1, 1, 1, 4, 3, 1, 3, 2, 2, 2]
def baseStart_1634618 : Nat := 118140960795 + 1634618 * 2 ^ 59
def prefixEnd_1634618 : Nat := 4983230072969 + 3 ^ 40 * 1634618 * 2
def baseEnd_1634618 : Nat := 839344720491190783257535

theorem tailTrace_1634618 : CollatzResearch.WordTrace tailWord_1634618 prefixEnd_1634618 839344720491190783257535 := by
  unfold tailWord_1634618
  simp only [CollatzResearch.WordTrace]
  refine ⟨14904854098016407843402127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39746277594710420915739005 14904854098016407843402127)
  ·
    refine ⟨22357281147024611765103191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14904854098016407843402127 22357281147024611765103191)
    ·
      refine ⟨33535921720536917647654787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22357281147024611765103191 33535921720536917647654787)
      ·
        refine ⟨50303882580805376471482181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33535921720536917647654787 50303882580805376471482181)
        ·
          refine ⟨9431977983901008088402909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50303882580805376471482181 9431977983901008088402909)
          ·
            refine ⟨3536991743962878033151091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9431977983901008088402909 3536991743962878033151091)
            ·
              refine ⟨5305487615944317049726637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3536991743962878033151091 5305487615944317049726637)
              ·
                refine ⟨1989557855979118893647489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5305487615944317049726637 1989557855979118893647489)
                ·
                  refine ⟨1492168391984339170235617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1989557855979118893647489 1492168391984339170235617)
                  ·
                    refine ⟨1119126293988254377676713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1492168391984339170235617 1119126293988254377676713)
                    ·
                      refine ⟨839344720491190783257535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1119126293988254377676713 839344720491190783257535)
                      ·
                        rfl

theorem cell23_1634618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 1, 3, 2, 2, 2].length) (baseStart_1634618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1634618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1634618 prefixEnd_1634618 := by exact prefixLift 1634618
  have htrace : WordTrace (prefixWord ++ tailWord_1634618) baseStart_1634618 baseEnd_1634618 := by
    simpa [prefixWord, tailWord_1634618, baseEnd_1634618] using wordTrace_append hprefix tailTrace_1634618
  have hstable : (prefixWord ++ tailWord_1634618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1634618).length < 2 ^ (prefixWord ++ tailWord_1634618).sum := by decide
  have hdescent : baseEnd_1634618 < baseStart_1634618 := by decide
  rcases family_descends (prefixWord ++ tailWord_1634618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1634647 : List Nat := [1, 1, 3, 2, 3, 1, 1, 1, 3, 2, 5]
def baseStart_1634647 : Nat := 118140960795 + 1634647 * 2 ^ 59
def prefixEnd_1634647 : Nat := 4983230072969 + 3 ^ 40 * 1634647 * 2
def baseEnd_1634647 : Nat := 839359611430171169794901

theorem tailTrace_1634647 : CollatzResearch.WordTrace tailWord_1634647 prefixEnd_1634647 839359611430171169794901 := by
  unfold tailWord_1634647
  simp only [CollatzResearch.WordTrace]
  refine ⟨59620474108960569326414195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39746982739307046217609463 59620474108960569326414195)
  ·
    refine ⟨89430711163440853989621293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59620474108960569326414195 89430711163440853989621293)
    ·
      refine ⟨33536516686290320246107985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89430711163440853989621293 33536516686290320246107985)
      ·
        refine ⟨25152387514717740184580989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33536516686290320246107985 25152387514717740184580989)
        ·
          refine ⟨9432145318019152569217871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25152387514717740184580989 9432145318019152569217871)
          ·
            refine ⟨14148217977028728853826807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9432145318019152569217871 14148217977028728853826807)
            ·
              refine ⟨21222326965543093280740211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14148217977028728853826807 21222326965543093280740211)
              ·
                refine ⟨31833490448314639921110317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21222326965543093280740211 31833490448314639921110317)
                ·
                  refine ⟨11937558918117989970416369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31833490448314639921110317 11937558918117989970416369)
                  ·
                    refine ⟨8953169188588492477812277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11937558918117989970416369 8953169188588492477812277)
                    ·
                      refine ⟨839359611430171169794901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8953169188588492477812277 839359611430171169794901)
                      ·
                        rfl

theorem cell23_1634647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 1, 3, 2, 5].length) (baseStart_1634647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1634647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1634647 prefixEnd_1634647 := by exact prefixLift 1634647
  have htrace : WordTrace (prefixWord ++ tailWord_1634647) baseStart_1634647 baseEnd_1634647 := by
    simpa [prefixWord, tailWord_1634647, baseEnd_1634647] using wordTrace_append hprefix tailTrace_1634647
  have hstable : (prefixWord ++ tailWord_1634647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1634647).length < 2 ^ (prefixWord ++ tailWord_1634647).sum := by decide
  have hdescent : baseEnd_1634647 < baseStart_1634647 := by decide
  rcases family_descends (prefixWord ++ tailWord_1634647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1634652 : List Nat := [2, 2, 4, 3, 1, 1, 2, 2, 2, 2, 2]
def baseStart_1634652 : Nat := 118140960795 + 1634652 * 2 ^ 59
def prefixEnd_1634652 : Nat := 4983230072969 + 3 ^ 40 * 1634652 * 2
def baseEnd_1634652 : Nat := 839362178833443650232379

theorem tailTrace_1634652 : CollatzResearch.WordTrace tailWord_1634652 prefixEnd_1634652 839362178833443650232379 := by
  unfold tailWord_1634652
  simp only [CollatzResearch.WordTrace]
  refine ⟨29810328236971227590173105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39747104315961636786897473 29810328236971227590173105)
  ·
    refine ⟨22357746177728420692629829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29810328236971227590173105 22357746177728420692629829)
    ·
      refine ⟨4192077408324078879868093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22357746177728420692629829 4192077408324078879868093)
      ·
        refine ⟨1572029028121529579950535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4192077408324078879868093 1572029028121529579950535)
        ·
          refine ⟨2358043542182294369925803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1572029028121529579950535 2358043542182294369925803)
          ·
            refine ⟨3537065313273441554888705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2358043542182294369925803 3537065313273441554888705)
            ·
              refine ⟨2652798984955081166166529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3537065313273441554888705 2652798984955081166166529)
              ·
                refine ⟨1989599238716310874624897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2652798984955081166166529 1989599238716310874624897)
                ·
                  refine ⟨1492199429037233155968673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1989599238716310874624897 1492199429037233155968673)
                  ·
                    refine ⟨1119149571777924866976505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1492199429037233155968673 1119149571777924866976505)
                    ·
                      refine ⟨839362178833443650232379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1119149571777924866976505 839362178833443650232379)
                      ·
                        rfl

theorem cell23_1634652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 2, 2, 2, 2, 2].length) (baseStart_1634652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1634652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1634652 prefixEnd_1634652 := by exact prefixLift 1634652
  have htrace : WordTrace (prefixWord ++ tailWord_1634652) baseStart_1634652 baseEnd_1634652 := by
    simpa [prefixWord, tailWord_1634652, baseEnd_1634652] using wordTrace_append hprefix tailTrace_1634652
  have hstable : (prefixWord ++ tailWord_1634652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1634652).length < 2 ^ (prefixWord ++ tailWord_1634652).sum := by decide
  have hdescent : baseEnd_1634652 < baseStart_1634652 := by decide
  rcases family_descends (prefixWord ++ tailWord_1634652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1634657 : List Nat := [1, 2, 3, 1, 1, 1, 1, 1, 5, 3, 4]
def baseStart_1634657 : Nat := 118140960795 + 1634657 * 2 ^ 59
def prefixEnd_1634657 : Nat := 4983230072969 + 3 ^ 40 * 1634657 * 2
def baseEnd_1634657 : Nat := 839364746236716130669855

theorem tailTrace_1634657 : CollatzResearch.WordTrace tailWord_1634657 prefixEnd_1634657 839364746236716130669855 := by
  unfold tailWord_1634657
  simp only [CollatzResearch.WordTrace]
  refine ⟨59620838838924341034278225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39747225892616227356185483 59620838838924341034278225)
  ·
    refine ⟨44715629129193255775708669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59620838838924341034278225 44715629129193255775708669)
    ·
      refine ⟨16768360923447470915890751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44715629129193255775708669 16768360923447470915890751)
      ·
        refine ⟨25152541385171206373836127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16768360923447470915890751 25152541385171206373836127)
        ·
          refine ⟨37728812077756809560754191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25152541385171206373836127 37728812077756809560754191)
          ·
            refine ⟨56593218116635214341131287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37728812077756809560754191 56593218116635214341131287)
            ·
              refine ⟨84889827174952821511696931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56593218116635214341131287 84889827174952821511696931)
              ·
                refine ⟨127334740762429232267545397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84889827174952821511696931 127334740762429232267545397)
                ·
                  refine ⟨11937631946477740525082381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 127334740762429232267545397 11937631946477740525082381)
                  ·
                    refine ⟨4476611979929152696905893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11937631946477740525082381 4476611979929152696905893)
                    ·
                      refine ⟨839364746236716130669855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4476611979929152696905893 839364746236716130669855)
                      ·
                        rfl

theorem cell23_1634657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 1, 5, 3, 4].length) (baseStart_1634657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1634657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1634657 prefixEnd_1634657 := by exact prefixLift 1634657
  have htrace : WordTrace (prefixWord ++ tailWord_1634657) baseStart_1634657 baseEnd_1634657 := by
    simpa [prefixWord, tailWord_1634657, baseEnd_1634657] using wordTrace_append hprefix tailTrace_1634657
  have hstable : (prefixWord ++ tailWord_1634657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1634657).length < 2 ^ (prefixWord ++ tailWord_1634657).sum := by decide
  have hdescent : baseEnd_1634657 < baseStart_1634657 := by decide
  rcases family_descends (prefixWord ++ tailWord_1634657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1634658 : List Nat := [3, 3, 2, 1, 1, 2, 4, 2, 5]
def baseStart_1634658 : Nat := 118140960795 + 1634658 * 2 ^ 59
def prefixEnd_1634658 : Nat := 4983230072969 + 3 ^ 40 * 1634658 * 2
def baseEnd_1634658 : Nat := 93262806635263402973039

theorem tailTrace_1634658 : CollatzResearch.WordTrace tailWord_1634658 prefixEnd_1634658 93262806635263402973039 := by
  unfold tailWord_1634658
  simp only [CollatzResearch.WordTrace]
  refine ⟨14905218827980179551266157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39747250207947145470043085 14905218827980179551266157)
  ·
    refine ⟨5589457060492567331724809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14905218827980179551266157 5589457060492567331724809)
    ·
      refine ⟨4192092795369425498793607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5589457060492567331724809 4192092795369425498793607)
      ·
        refine ⟨6288139193054138248190411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4192092795369425498793607 6288139193054138248190411)
        ·
          refine ⟨9432208789581207372285617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6288139193054138248190411 9432208789581207372285617)
          ·
            refine ⟨7074156592185905529214213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9432208789581207372285617 7074156592185905529214213)
            ·
              refine ⟨1326404361034857286727665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7074156592185905529214213 1326404361034857286727665)
              ·
                refine ⟨994803270776142965045749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1326404361034857286727665 994803270776142965045749)
                ·
                  refine ⟨93262806635263402973039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 994803270776142965045749 93262806635263402973039)
                  ·
                    rfl

theorem cell23_1634658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 4, 2, 5].length) (baseStart_1634658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1634658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1634658 prefixEnd_1634658 := by exact prefixLift 1634658
  have htrace : WordTrace (prefixWord ++ tailWord_1634658) baseStart_1634658 baseEnd_1634658 := by
    simpa [prefixWord, tailWord_1634658, baseEnd_1634658] using wordTrace_append hprefix tailTrace_1634658
  have hstable : (prefixWord ++ tailWord_1634658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1634658).length < 2 ^ (prefixWord ++ tailWord_1634658).sum := by decide
  have hdescent : baseEnd_1634658 < baseStart_1634658 := by decide
  rcases family_descends (prefixWord ++ tailWord_1634658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1634664 : List Nat := [2, 1, 4, 2, 2, 1, 2, 1, 1, 2, 5]
def baseStart_1634664 : Nat := 118140960795 + 1634664 * 2 ^ 59
def prefixEnd_1634664 : Nat := 4983230072969 + 3 ^ 40 * 1634664 * 2
def baseEnd_1634664 : Nat := 839368340601297603282323

theorem tailTrace_1634664 : CollatzResearch.WordTrace tailWord_1634664 prefixEnd_1634664 839368340601297603282323 := by
  unfold tailWord_1634664
  simp only [CollatzResearch.WordTrace]
  refine ⟨29810547074949490614891523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39747396099932654153188697 29810547074949490614891523)
  ·
    refine ⟨44715820612424235922337285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29810547074949490614891523 44715820612424235922337285)
    ·
      refine ⟨8384216364829544235438241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44715820612424235922337285 8384216364829544235438241)
      ·
        refine ⟨6288162273622158176578681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8384216364829544235438241 6288162273622158176578681)
        ·
          refine ⟨4716121705216618632434011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6288162273622158176578681 4716121705216618632434011)
          ·
            refine ⟨7074182557824927948651017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4716121705216618632434011 7074182557824927948651017)
            ·
              refine ⟨5305636918368695961488263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7074182557824927948651017 5305636918368695961488263)
              ·
                refine ⟨7958455377553043942232395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5305636918368695961488263 7958455377553043942232395)
                ·
                  refine ⟨11937683066329565913348593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7958455377553043942232395 11937683066329565913348593)
                  ·
                    refine ⟨8953262299747174435011445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11937683066329565913348593 8953262299747174435011445)
                    ·
                      refine ⟨839368340601297603282323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8953262299747174435011445 839368340601297603282323)
                      ·
                        rfl

theorem cell23_1634664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 2, 1, 1, 2, 5].length) (baseStart_1634664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1634664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1634664 prefixEnd_1634664 := by exact prefixLift 1634664
  have htrace : WordTrace (prefixWord ++ tailWord_1634664) baseStart_1634664 baseEnd_1634664 := by
    simpa [prefixWord, tailWord_1634664, baseEnd_1634664] using wordTrace_append hprefix tailTrace_1634664
  have hstable : (prefixWord ++ tailWord_1634664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1634664).length < 2 ^ (prefixWord ++ tailWord_1634664).sum := by decide
  have hdescent : baseEnd_1634664 < baseStart_1634664 := by decide
  rcases family_descends (prefixWord ++ tailWord_1634664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1634687 : List Nat := [1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 4]
def baseStart_1634687 : Nat := 118140960795 + 1634687 * 2 ^ 59
def prefixEnd_1634687 : Nat := 4983230072969 + 3 ^ 40 * 1634687 * 2
def baseEnd_1634687 : Nat := 839380150656351013294717

theorem tailTrace_1634687 : CollatzResearch.WordTrace tailWord_1634687 prefixEnd_1634687 839380150656351013294717 := by
  unfold tailWord_1634687
  simp only [CollatzResearch.WordTrace]
  refine ⟨59621933028815656157870315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39747955352543770771913543 59621933028815656157870315)
  ·
    refine ⟨89432899543223484236805473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59621933028815656157870315 89432899543223484236805473)
    ·
      refine ⟨67074674657417613177604105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89432899543223484236805473 67074674657417613177604105)
      ·
        refine ⟨50306005993063209883203079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67074674657417613177604105 50306005993063209883203079)
        ·
          refine ⟨75459008989594814824804619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50306005993063209883203079 75459008989594814824804619)
          ·
            refine ⟨113188513484392222237206929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75459008989594814824804619 113188513484392222237206929)
            ·
              refine ⟨84891385113294166677905197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 113188513484392222237206929 84891385113294166677905197)
              ·
                refine ⟨31834269417485312504214449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 84891385113294166677905197 31834269417485312504214449)
                ·
                  refine ⟨23875702063113984378160837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31834269417485312504214449 23875702063113984378160837)
                  ·
                    refine ⟨4476694136833872070905157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23875702063113984378160837 4476694136833872070905157)
                    ·
                      refine ⟨839380150656351013294717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4476694136833872070905157 839380150656351013294717)
                      ·
                        rfl

theorem cell23_1634687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 4].length) (baseStart_1634687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1634687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1634687 prefixEnd_1634687 := by exact prefixLift 1634687
  have htrace : WordTrace (prefixWord ++ tailWord_1634687) baseStart_1634687 baseEnd_1634687 := by
    simpa [prefixWord, tailWord_1634687, baseEnd_1634687] using wordTrace_append hprefix tailTrace_1634687
  have hstable : (prefixWord ++ tailWord_1634687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1634687).length < 2 ^ (prefixWord ++ tailWord_1634687).sum := by decide
  have hdescent : baseEnd_1634687 < baseStart_1634687 := by decide
  rcases family_descends (prefixWord ++ tailWord_1634687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1634714 : List Nat := [3, 1, 1, 4, 1, 3, 1, 1, 8]
def baseStart_1634714 : Nat := 118140960795 + 1634714 * 2 ^ 59
def prefixEnd_1634714 : Nat := 4983230072969 + 3 ^ 40 * 1634714 * 2
def baseEnd_1634714 : Nat := 93266001626002489739677

theorem tailTrace_1634714 : CollatzResearch.WordTrace tailWord_1634714 prefixEnd_1634714 93266001626002489739677 := by
  unfold tailWord_1634714
  simp only [CollatzResearch.WordTrace]
  refine ⟨14905729449929459942275799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39748611866478559846068797 14905729449929459942275799)
  ·
    refine ⟨22358594174894189913413699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14905729449929459942275799 22358594174894189913413699)
    ·
      refine ⟨33537891262341284870120549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22358594174894189913413699 33537891262341284870120549)
      ·
        refine ⟨6288354611688990913147603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33537891262341284870120549 6288354611688990913147603)
        ·
          refine ⟨9432531917533486369721405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6288354611688990913147603 9432531917533486369721405)
          ·
            refine ⟨3537199469075057388645527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9432531917533486369721405 3537199469075057388645527)
            ·
              refine ⟨5305799203612586082968291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3537199469075057388645527 5305799203612586082968291)
              ·
                refine ⟨7958698805418879124452437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5305799203612586082968291 7958698805418879124452437)
                ·
                  refine ⟨93266001626002489739677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 7958698805418879124452437 93266001626002489739677)
                  ·
                    rfl

theorem cell23_1634714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 1, 1, 8].length) (baseStart_1634714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1634714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1634714 prefixEnd_1634714 := by exact prefixLift 1634714
  have htrace : WordTrace (prefixWord ++ tailWord_1634714) baseStart_1634714 baseEnd_1634714 := by
    simpa [prefixWord, tailWord_1634714, baseEnd_1634714] using wordTrace_append hprefix tailTrace_1634714
  have hstable : (prefixWord ++ tailWord_1634714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1634714).length < 2 ^ (prefixWord ++ tailWord_1634714).sum := by decide
  have hdescent : baseEnd_1634714 < baseStart_1634714 := by decide
  rcases family_descends (prefixWord ++ tailWord_1634714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1634718 : List Nat := [4, 3, 1, 2, 1, 1, 1, 3, 3, 4]
def baseStart_1634718 : Nat := 118140960795 + 1634718 * 2 ^ 59
def prefixEnd_1634718 : Nat := 4983230072969 + 3 ^ 40 * 1634718 * 2
def baseEnd_1634718 : Nat := 279798689518880130669025

theorem tailTrace_1634718 : CollatzResearch.WordTrace tailWord_1634718 prefixEnd_1634718 279798689518880130669025 := by
  unfold tailWord_1634718
  simp only [CollatzResearch.WordTrace]
  refine ⟨7452882961462918556531101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39748709127802232301499205 7452882961462918556531101)
  ·
    refine ⟨2794831110548594458699163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7452882961462918556531101 2794831110548594458699163)
    ·
      refine ⟨4192246665822891688048745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2794831110548594458699163 4192246665822891688048745)
      ·
        refine ⟨3144184999367168766036559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4192246665822891688048745 3144184999367168766036559)
        ·
          refine ⟨4716277499050753149054839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3144184999367168766036559 4716277499050753149054839)
          ·
            refine ⟨7074416248576129723582259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4716277499050753149054839 7074416248576129723582259)
            ·
              refine ⟨10611624372864194585373389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7074416248576129723582259 10611624372864194585373389)
              ·
                refine ⟨3979359139824072969515021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10611624372864194585373389 3979359139824072969515021)
                ·
                  refine ⟨1492259677434027363568133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3979359139824072969515021 1492259677434027363568133)
                  ·
                    refine ⟨279798689518880130669025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1492259677434027363568133 279798689518880130669025)
                    ·
                      rfl

theorem cell23_1634718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 3, 3, 4].length) (baseStart_1634718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1634718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1634718 prefixEnd_1634718 := by exact prefixLift 1634718
  have htrace : WordTrace (prefixWord ++ tailWord_1634718) baseStart_1634718 baseEnd_1634718 := by
    simpa [prefixWord, tailWord_1634718, baseEnd_1634718] using wordTrace_append hprefix tailTrace_1634718
  have hstable : (prefixWord ++ tailWord_1634718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1634718).length < 2 ^ (prefixWord ++ tailWord_1634718).sum := by decide
  have hdescent : baseEnd_1634718 < baseStart_1634718 := by decide
  rcases family_descends (prefixWord ++ tailWord_1634718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1634781 : List Nat := [1, 4, 3, 1, 1, 1, 2, 2, 3, 1, 4]
def baseStart_1634781 : Nat := 118140960795 + 1634781 * 2 ^ 59
def prefixEnd_1634781 : Nat := 4983230072969 + 3 ^ 40 * 1634781 * 2
def baseEnd_1634781 : Nat := 839428417837873645519285

theorem tailTrace_1634781 : CollatzResearch.WordTrace tailWord_1634781 prefixEnd_1634781 839428417837873645519285 := by
  unfold tailWord_1634781
  simp only [CollatzResearch.WordTrace]
  refine ⟨59625361490475110211792197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39750240993650073474528131 59625361490475110211792197)
  ·
    refine ⟨11179755279464083164711037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 59625361490475110211792197 11179755279464083164711037)
    ·
      refine ⟨4192408229799031186766639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11179755279464083164711037 4192408229799031186766639)
      ·
        refine ⟨6288612344698546780149959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4192408229799031186766639 6288612344698546780149959)
        ·
          refine ⟨9432918517047820170224939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6288612344698546780149959 9432918517047820170224939)
          ·
            refine ⟨14149377775571730255337409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9432918517047820170224939 14149377775571730255337409)
            ·
              refine ⟨10612033331678797691503057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14149377775571730255337409 10612033331678797691503057)
              ·
                refine ⟨7959024998759098268627293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10612033331678797691503057 7959024998759098268627293)
                ·
                  refine ⟨2984634374534661850735235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7959024998759098268627293 2984634374534661850735235)
                  ·
                    refine ⟨4476951561801992776102853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2984634374534661850735235 4476951561801992776102853)
                    ·
                      refine ⟨839428417837873645519285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4476951561801992776102853 839428417837873645519285)
                      ·
                        rfl

theorem cell23_1634781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 2, 3, 1, 4].length) (baseStart_1634781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1634781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1634781 prefixEnd_1634781 := by exact prefixLift 1634781
  have htrace : WordTrace (prefixWord ++ tailWord_1634781) baseStart_1634781 baseEnd_1634781 := by
    simpa [prefixWord, tailWord_1634781, baseEnd_1634781] using wordTrace_append hprefix tailTrace_1634781
  have hstable : (prefixWord ++ tailWord_1634781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1634781).length < 2 ^ (prefixWord ++ tailWord_1634781).sum := by decide
  have hdescent : baseEnd_1634781 < baseStart_1634781 := by decide
  rcases family_descends (prefixWord ++ tailWord_1634781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1634784 : List Nat := [2, 1, 1, 3, 1, 1, 3, 4, 1, 1, 5]
def baseStart_1634784 : Nat := 118140960795 + 1634784 * 2 ^ 59
def prefixEnd_1634784 : Nat := 4983230072969 + 3 ^ 40 * 1634784 * 2
def baseEnd_1634784 : Nat := 839429958279837133781771

theorem tailTrace_1634784 : CollatzResearch.WordTrace tailWord_1634784 prefixEnd_1634784 839429958279837133781771 := by
  unfold tailWord_1634784
  simp only [CollatzResearch.WordTrace]
  refine ⟨29812735454732120862075703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39750313939642827816100937 29812735454732120862075703)
  ·
    refine ⟨44719103182098181293113555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29812735454732120862075703 44719103182098181293113555)
    ·
      refine ⟨67078654773147271939670333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44719103182098181293113555 67078654773147271939670333)
      ·
        refine ⟨25154495539930226977376375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67078654773147271939670333 25154495539930226977376375)
        ·
          refine ⟨37731743309895340466064563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25154495539930226977376375 37731743309895340466064563)
          ·
            refine ⟨56597614964843010699096845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37731743309895340466064563 56597614964843010699096845)
            ·
              refine ⟨21224105611816129012161317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56597614964843010699096845 21224105611816129012161317)
              ·
                refine ⟨3979519802215524189780247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21224105611816129012161317 3979519802215524189780247)
                ·
                  refine ⟨5969279703323286284670371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3979519802215524189780247 5969279703323286284670371)
                  ·
                    refine ⟨8953919554984929427005557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5969279703323286284670371 8953919554984929427005557)
                    ·
                      refine ⟨839429958279837133781771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8953919554984929427005557 839429958279837133781771)
                      ·
                        rfl

theorem cell23_1634784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 4, 1, 1, 5].length) (baseStart_1634784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1634784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1634784 prefixEnd_1634784 := by exact prefixLift 1634784
  have htrace : WordTrace (prefixWord ++ tailWord_1634784) baseStart_1634784 baseEnd_1634784 := by
    simpa [prefixWord, tailWord_1634784, baseEnd_1634784] using wordTrace_append hprefix tailTrace_1634784
  have hstable : (prefixWord ++ tailWord_1634784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1634784).length < 2 ^ (prefixWord ++ tailWord_1634784).sum := by decide
  have hdescent : baseEnd_1634784 < baseStart_1634784 := by decide
  rcases family_descends (prefixWord ++ tailWord_1634784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1634798 : List Nat := [4, 1, 2, 1, 2, 2, 3, 2, 1, 1, 4]
def baseStart_1634798 : Nat := 118140960795 + 1634798 * 2 ^ 59
def prefixEnd_1634798 : Nat := 4983230072969 + 3 ^ 40 * 1634798 * 2
def baseEnd_1634798 : Nat := 839437147009000079006707

theorem tailTrace_1634798 : CollatzResearch.WordTrace tailWord_1634798 prefixEnd_1634798 839437147009000079006707 := by
  unfold tailWord_1634798
  simp only [CollatzResearch.WordTrace]
  refine ⟨7453247691426690264395131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39750654354275681410107365 7453247691426690264395131)
  ·
    refine ⟨11179871537140035396592697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7453247691426690264395131 11179871537140035396592697)
    ·
      refine ⟨8384903652855026547444523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11179871537140035396592697 8384903652855026547444523)
      ·
        refine ⟨12577355479282539821166785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8384903652855026547444523 12577355479282539821166785)
        ·
          refine ⟨9433016609461904865875089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12577355479282539821166785 9433016609461904865875089)
          ·
            refine ⟨7074762457096428649406317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9433016609461904865875089 7074762457096428649406317)
            ·
              refine ⟨2653035921411160743527369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7074762457096428649406317 2653035921411160743527369)
              ·
                refine ⟨1989776941058370557645527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2653035921411160743527369 1989776941058370557645527)
                ·
                  refine ⟨2984665411587555836468291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1989776941058370557645527 2984665411587555836468291)
                  ·
                    refine ⟨4476998117381333754702437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2984665411587555836468291 4476998117381333754702437)
                    ·
                      refine ⟨839437147009000079006707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4476998117381333754702437 839437147009000079006707)
                      ·
                        rfl

theorem cell23_1634798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 3, 2, 1, 1, 4].length) (baseStart_1634798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1634798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1634798 prefixEnd_1634798 := by exact prefixLift 1634798
  have htrace : WordTrace (prefixWord ++ tailWord_1634798) baseStart_1634798 baseEnd_1634798 := by
    simpa [prefixWord, tailWord_1634798, baseEnd_1634798] using wordTrace_append hprefix tailTrace_1634798
  have hstable : (prefixWord ++ tailWord_1634798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1634798).length < 2 ^ (prefixWord ++ tailWord_1634798).sum := by decide
  have hdescent : baseEnd_1634798 < baseStart_1634798 := by decide
  rcases family_descends (prefixWord ++ tailWord_1634798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1634801 : List Nat := [1, 2, 2, 2, 3, 1, 3, 1, 3, 2, 3]
def baseStart_1634801 : Nat := 118140960795 + 1634801 * 2 ^ 59
def prefixEnd_1634801 : Nat := 4983230072969 + 3 ^ 40 * 1634801 * 2
def baseEnd_1634801 : Nat := 839438687450963567269193

theorem tailTrace_1634801 : CollatzResearch.WordTrace tailWord_1634801 prefixEnd_1634801 839438687450963567269193 := by
  unfold tailWord_1634801
  simp only [CollatzResearch.WordTrace]
  refine ⟨59626090950402653627520257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39750727300268435751680171 59626090950402653627520257)
  ·
    refine ⟨44719568212801990220640193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59626090950402653627520257 44719568212801990220640193)
    ·
      refine ⟨33539676159601492665480145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44719568212801990220640193 33539676159601492665480145)
      ·
        refine ⟨25154757119701119499110109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33539676159601492665480145 25154757119701119499110109)
        ·
          refine ⟨9433033919887919812166291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25154757119701119499110109 9433033919887919812166291)
          ·
            refine ⟨14149550879831879718249437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9433033919887919812166291 14149550879831879718249437)
            ·
              refine ⟨5306081579936954894343539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14149550879831879718249437 5306081579936954894343539)
              ·
                refine ⟨7959122369905432341515309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5306081579936954894343539 7959122369905432341515309)
                ·
                  refine ⟨2984670888714537128068241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7959122369905432341515309 2984670888714537128068241)
                  ·
                    refine ⟨2238503166535902846051181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2984670888714537128068241 2238503166535902846051181)
                    ·
                      refine ⟨839438687450963567269193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2238503166535902846051181 839438687450963567269193)
                      ·
                        rfl

theorem cell23_1634801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 3, 1, 3, 2, 3].length) (baseStart_1634801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1634801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1634801 prefixEnd_1634801 := by exact prefixLift 1634801
  have htrace : WordTrace (prefixWord ++ tailWord_1634801) baseStart_1634801 baseEnd_1634801 := by
    simpa [prefixWord, tailWord_1634801, baseEnd_1634801] using wordTrace_append hprefix tailTrace_1634801
  have hstable : (prefixWord ++ tailWord_1634801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1634801).length < 2 ^ (prefixWord ++ tailWord_1634801).sum := by decide
  have hdescent : baseEnd_1634801 < baseStart_1634801 := by decide
  rcases family_descends (prefixWord ++ tailWord_1634801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1634815 : List Nat := [1, 1, 2, 2, 1, 2, 4, 5, 1, 2, 2]
def baseStart_1634815 : Nat := 118140960795 + 1634815 * 2 ^ 59
def prefixEnd_1634815 : Nat := 4983230072969 + 3 ^ 40 * 1634815 * 2
def baseEnd_1634815 : Nat := 839445876180126512494129

theorem tailTrace_1634815 : CollatzResearch.WordTrace tailWord_1634815 prefixEnd_1634815 839445876180126512494129 := by
  unfold tailWord_1634815
  simp only [CollatzResearch.WordTrace]
  refine ⟨59626601572351934018529899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39751067714901289345686599 59626601572351934018529899)
  ·
    refine ⟨89439902358527901027794849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59626601572351934018529899 89439902358527901027794849)
    ·
      refine ⟨67079926768895925770846137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89439902358527901027794849 67079926768895925770846137)
      ·
        refine ⟨50309945076671944328134603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67079926768895925770846137 50309945076671944328134603)
        ·
          refine ⟨75464917615007916492201905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50309945076671944328134603 75464917615007916492201905)
          ·
            refine ⟨56598688211255937369151429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75464917615007916492201905 56598688211255937369151429)
            ·
              refine ⟨10612254039610488256715893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 56598688211255937369151429 10612254039610488256715893)
              ·
                refine ⟨994898816213483274067115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10612254039610488256715893 994898816213483274067115)
                ·
                  refine ⟨1492348224320224911100673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 994898816213483274067115 1492348224320224911100673)
                  ·
                    refine ⟨1119261168240168683325505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1492348224320224911100673 1119261168240168683325505)
                    ·
                      refine ⟨839445876180126512494129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1119261168240168683325505 839445876180126512494129)
                      ·
                        rfl

theorem cell23_1634815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 5, 1, 2, 2].length) (baseStart_1634815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1634815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1634815 prefixEnd_1634815 := by exact prefixLift 1634815
  have htrace : WordTrace (prefixWord ++ tailWord_1634815) baseStart_1634815 baseEnd_1634815 := by
    simpa [prefixWord, tailWord_1634815, baseEnd_1634815] using wordTrace_append hprefix tailTrace_1634815
  have hstable : (prefixWord ++ tailWord_1634815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1634815).length < 2 ^ (prefixWord ++ tailWord_1634815).sum := by decide
  have hdescent : baseEnd_1634815 < baseStart_1634815 := by decide
  rcases family_descends (prefixWord ++ tailWord_1634815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1634855 : List Nat := [1, 1, 7, 2, 1, 1, 3, 7]
def baseStart_1634855 : Nat := 118140960795 + 1634855 * 2 ^ 59
def prefixEnd_1634855 : Nat := 4983230072969 + 3 ^ 40 * 1634855 * 2
def baseEnd_1634855 : Nat := 31091348718752087259035

theorem tailTrace_1634855 : CollatzResearch.WordTrace tailWord_1634855 prefixEnd_1634855 31091348718752087259035 := by
  unfold tailWord_1634855
  simp only [CollatzResearch.WordTrace]
  refine ⟨59628060492207020849986019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39752040328138013899990679 59628060492207020849986019)
  ·
    refine ⟨89442090738310531274979029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59628060492207020849986019 89442090738310531274979029)
    ·
      refine ⟨2096299001679153076757321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 89442090738310531274979029 2096299001679153076757321)
      ·
        refine ⟨1572224251259364807567991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2096299001679153076757321 1572224251259364807567991)
        ·
          refine ⟨2358336376889047211351987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1572224251259364807567991 2358336376889047211351987)
          ·
            refine ⟨3537504565333570817027981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2358336376889047211351987 3537504565333570817027981)
            ·
              refine ⟨1326564212000089056385493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3537504565333570817027981 1326564212000089056385493)
              ·
                refine ⟨31091348718752087259035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1326564212000089056385493 31091348718752087259035)
                ·
                  rfl

theorem cell23_1634855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 3, 7].length) (baseStart_1634855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1634855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1634855 prefixEnd_1634855 := by exact prefixLift 1634855
  have htrace : WordTrace (prefixWord ++ tailWord_1634855) baseStart_1634855 baseEnd_1634855 := by
    simpa [prefixWord, tailWord_1634855, baseEnd_1634855] using wordTrace_append hprefix tailTrace_1634855
  have hstable : (prefixWord ++ tailWord_1634855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1634855).length < 2 ^ (prefixWord ++ tailWord_1634855).sum := by decide
  have hdescent : baseEnd_1634855 < baseStart_1634855 := by decide
  rcases family_descends (prefixWord ++ tailWord_1634855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1634881 : List Nat := [1, 2, 5, 1, 1, 2, 1, 2, 2, 6]
def baseStart_1634881 : Nat := 118140960795 + 1634881 * 2 ^ 59
def prefixEnd_1634881 : Nat := 4983230072969 + 3 ^ 40 * 1634881 * 2
def baseEnd_1634881 : Nat := 279826588634441084756275

theorem tailTrace_1634881 : CollatzResearch.WordTrace tailWord_1634881 prefixEnd_1634881 279826588634441084756275 := by
  unfold tailWord_1634881
  simp only [CollatzResearch.WordTrace]
  refine ⟨59629008790112827290432497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39752672526741884860288331 59629008790112827290432497)
  ·
    refine ⟨44721756592584620467824373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59629008790112827290432497 44721756592584620467824373)
    ·
      refine ⟨4192664680554808168858535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 44721756592584620467824373 4192664680554808168858535)
      ·
        refine ⟨6288997020832212253287803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4192664680554808168858535 6288997020832212253287803)
        ·
          refine ⟨9433495531248318379931705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6288997020832212253287803 9433495531248318379931705)
          ·
            refine ⟨7075121648436238784948779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9433495531248318379931705 7075121648436238784948779)
            ·
              refine ⟨10612682472654358177423169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7075121648436238784948779 10612682472654358177423169)
              ·
                refine ⟨7959511854490768633067377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10612682472654358177423169 7959511854490768633067377)
                ·
                  refine ⟨5969633890868076474800533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7959511854490768633067377 5969633890868076474800533)
                  ·
                    refine ⟨279826588634441084756275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5969633890868076474800533 279826588634441084756275)
                    ·
                      rfl

theorem cell23_1634881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 2, 2, 6].length) (baseStart_1634881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1634881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1634881 prefixEnd_1634881 := by exact prefixLift 1634881
  have htrace : WordTrace (prefixWord ++ tailWord_1634881) baseStart_1634881 baseEnd_1634881 := by
    simpa [prefixWord, tailWord_1634881, baseEnd_1634881] using wordTrace_append hprefix tailTrace_1634881
  have hstable : (prefixWord ++ tailWord_1634881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1634881).length < 2 ^ (prefixWord ++ tailWord_1634881).sum := by decide
  have hdescent : baseEnd_1634881 < baseStart_1634881 := by decide
  rcases family_descends (prefixWord ++ tailWord_1634881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1634901 : List Nat := [1, 3, 2, 2, 1, 1, 4, 1, 2, 2, 4]
def baseStart_1634901 : Nat := 118140960795 + 1634901 * 2 ^ 59
def prefixEnd_1634901 : Nat := 4983230072969 + 3 ^ 40 * 1634901 * 2
def baseEnd_1634901 : Nat := 839490035516413176018733

theorem tailTrace_1634901 : CollatzResearch.WordTrace tailWord_1634901 prefixEnd_1634901 839490035516413176018733 := by
  unfold tailWord_1634901
  simp only [CollatzResearch.WordTrace]
  refine ⟨59629738250040370706160557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39753158833360247137440371 59629738250040370706160557)
  ·
    refine ⟨22361151843765139014810209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59629738250040370706160557 22361151843765139014810209)
    ·
      refine ⟨16770863882823854261107657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22361151843765139014810209 16770863882823854261107657)
      ·
        refine ⟨12578147912117890695830743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16770863882823854261107657 12578147912117890695830743)
        ·
          refine ⟨18867221868176836043746115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12578147912117890695830743 18867221868176836043746115)
          ·
            refine ⟨28300832802265254065619173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18867221868176836043746115 28300832802265254065619173)
            ·
              refine ⟨5306406150424735137303595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28300832802265254065619173 5306406150424735137303595)
              ·
                refine ⟨7959609225637102705955393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5306406150424735137303595 7959609225637102705955393)
                ·
                  refine ⟨5969706919227827029466545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7959609225637102705955393 5969706919227827029466545)
                  ·
                    refine ⟨4477280189420870272099909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5969706919227827029466545 4477280189420870272099909)
                    ·
                      refine ⟨839490035516413176018733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4477280189420870272099909 839490035516413176018733)
                      ·
                        rfl

theorem cell23_1634901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 4, 1, 2, 2, 4].length) (baseStart_1634901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1634901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1634901 prefixEnd_1634901 := by exact prefixLift 1634901
  have htrace : WordTrace (prefixWord ++ tailWord_1634901) baseStart_1634901 baseEnd_1634901 := by
    simpa [prefixWord, tailWord_1634901, baseEnd_1634901] using wordTrace_append hprefix tailTrace_1634901
  have hstable : (prefixWord ++ tailWord_1634901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1634901).length < 2 ^ (prefixWord ++ tailWord_1634901).sum := by decide
  have hdescent : baseEnd_1634901 < baseStart_1634901 := by decide
  rcases family_descends (prefixWord ++ tailWord_1634901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1634945 : List Nat := [1, 2, 4, 2, 1, 1, 5, 2, 5]
def baseStart_1634945 : Nat := 118140960795 + 1634945 * 2 ^ 59
def prefixEnd_1634945 : Nat := 4983230072969 + 3 ^ 40 * 1634945 * 2
def baseEnd_1634945 : Nat := 93279180962801222652059

theorem tailTrace_1634945 : CollatzResearch.WordTrace tailWord_1634945 prefixEnd_1634945 93279180962801222652059 := by
  unfold tailWord_1634945
  simp only [CollatzResearch.WordTrace]
  refine ⟨59631343061880966220762289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39754228707920644147174859 59631343061880966220762289)
  ·
    refine ⟨44723507296410724665571717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59631343061880966220762289 44723507296410724665571717)
    ·
      refine ⟨8385657618077010874794697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44723507296410724665571717 8385657618077010874794697)
      ·
        refine ⟨6289243213557758156096023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8385657618077010874794697 6289243213557758156096023)
        ·
          refine ⟨9433864820336637234144035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6289243213557758156096023 9433864820336637234144035)
          ·
            refine ⟨14150797230504955851216053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9433864820336637234144035 14150797230504955851216053)
            ·
              refine ⟨1326637240359839611051505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14150797230504955851216053 1326637240359839611051505)
              ·
                refine ⟨994977930269879708288629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1326637240359839611051505 994977930269879708288629)
                ·
                  refine ⟨93279180962801222652059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 994977930269879708288629 93279180962801222652059)
                  ·
                    rfl

theorem cell23_1634945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 5, 2, 5].length) (baseStart_1634945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1634945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1634945 prefixEnd_1634945 := by exact prefixLift 1634945
  have htrace : WordTrace (prefixWord ++ tailWord_1634945) baseStart_1634945 baseEnd_1634945 := by
    simpa [prefixWord, tailWord_1634945, baseEnd_1634945] using wordTrace_append hprefix tailTrace_1634945
  have hstable : (prefixWord ++ tailWord_1634945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1634945).length < 2 ^ (prefixWord ++ tailWord_1634945).sum := by decide
  have hdescent : baseEnd_1634945 < baseStart_1634945 := by decide
  rcases family_descends (prefixWord ++ tailWord_1634945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1634951 : List Nat := [1, 1, 4, 2, 1, 2, 3, 1, 1, 2, 5]
def baseStart_1634951 : Nat := 118140960795 + 1634951 * 2 ^ 59
def prefixEnd_1634951 : Nat := 4983230072969 + 3 ^ 40 * 1634951 * 2
def baseEnd_1634951 : Nat := 839515709549137980393503

theorem tailTrace_1634951 : CollatzResearch.WordTrace tailWord_1634951 prefixEnd_1634951 839515709549137980393503 := by
  unfold tailWord_1634951
  simp only [CollatzResearch.WordTrace]
  refine ⟨59631561899859229245480707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39754374599906152830320471 59631561899859229245480707)
  ·
    refine ⟨89447342849788843868221061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59631561899859229245480707 89447342849788843868221061)
    ·
      refine ⟨16771376784335408225291449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 89447342849788843868221061 16771376784335408225291449)
      ·
        refine ⟨12578532588251556168968587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16771376784335408225291449 12578532588251556168968587)
        ·
          refine ⟨18867798882377334253452881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12578532588251556168968587 18867798882377334253452881)
          ·
            refine ⟨14150849161783000690089661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18867798882377334253452881 14150849161783000690089661)
            ·
              refine ⟨5306568435668625258783623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14150849161783000690089661 5306568435668625258783623)
              ·
                refine ⟨7959852653502937888175435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5306568435668625258783623 7959852653502937888175435)
                ·
                  refine ⟨11939778980254406832263153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7959852653502937888175435 11939778980254406832263153)
                  ·
                    refine ⟨8954834235190805124197365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11939778980254406832263153 8954834235190805124197365)
                    ·
                      refine ⟨839515709549137980393503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8954834235190805124197365 839515709549137980393503)
                      ·
                        rfl

theorem cell23_1634951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 3, 1, 1, 2, 5].length) (baseStart_1634951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1634951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1634951 prefixEnd_1634951 := by exact prefixLift 1634951
  have htrace : WordTrace (prefixWord ++ tailWord_1634951) baseStart_1634951 baseEnd_1634951 := by
    simpa [prefixWord, tailWord_1634951, baseEnd_1634951] using wordTrace_append hprefix tailTrace_1634951
  have hstable : (prefixWord ++ tailWord_1634951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1634951).length < 2 ^ (prefixWord ++ tailWord_1634951).sum := by decide
  have hdescent : baseEnd_1634951 < baseStart_1634951 := by decide
  rcases family_descends (prefixWord ++ tailWord_1634951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1634971 : List Nat := [1, 1, 1, 1, 1, 1, 2, 2, 9, 4]
def baseStart_1634971 : Nat := 118140960795 + 1634971 * 2 ^ 59
def prefixEnd_1634971 : Nat := 4983230072969 + 3 ^ 40 * 1634971 * 2
def baseEnd_1634971 : Nat := 279841993054075967381137

theorem tailTrace_1634971 : CollatzResearch.WordTrace tailWord_1634971 prefixEnd_1634971 279841993054075967381137 := by
  unfold tailWord_1634971
  simp only [CollatzResearch.WordTrace]
  refine ⟨59632291359786772661208767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39754860906524515107472511 59632291359786772661208767)
  ·
    refine ⟨89448437039680158991813151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59632291359786772661208767 89448437039680158991813151)
    ·
      refine ⟨134172655559520238487719727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89448437039680158991813151 134172655559520238487719727)
      ·
        refine ⟨201258983339280357731579591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134172655559520238487719727 201258983339280357731579591)
        ·
          refine ⟨301888475008920536597369387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 201258983339280357731579591 301888475008920536597369387)
          ·
            refine ⟨452832712513380804896054081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 301888475008920536597369387 452832712513380804896054081)
            ·
              refine ⟨339624534385035603672040561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 452832712513380804896054081 339624534385035603672040561)
              ·
                refine ⟨254718400788776702754030421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 339624534385035603672040561 254718400788776702754030421)
                ·
                  refine ⟨1492490629621738492699397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 254718400788776702754030421 1492490629621738492699397)
                  ·
                    refine ⟨279841993054075967381137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1492490629621738492699397 279841993054075967381137)
                    ·
                      rfl

theorem cell23_1634971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 9, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 9, 4].length) (baseStart_1634971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1634971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1634971 prefixEnd_1634971 := by exact prefixLift 1634971
  have htrace : WordTrace (prefixWord ++ tailWord_1634971) baseStart_1634971 baseEnd_1634971 := by
    simpa [prefixWord, tailWord_1634971, baseEnd_1634971] using wordTrace_append hprefix tailTrace_1634971
  have hstable : (prefixWord ++ tailWord_1634971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1634971).length < 2 ^ (prefixWord ++ tailWord_1634971).sum := by decide
  have hdescent : baseEnd_1634971 < baseStart_1634971 := by decide
  rcases family_descends (prefixWord ++ tailWord_1634971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1635018 : List Nat := [3, 1, 2, 1, 4, 1, 2, 3, 6]
def baseStart_1635018 : Nat := 118140960795 + 1635018 * 2 ^ 59
def prefixEnd_1635018 : Nat := 4983230072969 + 3 ^ 40 * 1635018 * 2
def baseEnd_1635018 : Nat := 93283345861443246472855

theorem tailTrace_1635018 : CollatzResearch.WordTrace tailWord_1635018 prefixEnd_1635018 93283345861443246472855 := by
  unfold tailWord_1635018
  simp only [CollatzResearch.WordTrace]
  refine ⟨14908501397654124922042427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39756003727077666458779805 14908501397654124922042427)
  ·
    refine ⟨22362752096481187383063641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14908501397654124922042427 22362752096481187383063641)
    ·
      refine ⟨16772064072360890537297731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22362752096481187383063641 16772064072360890537297731)
      ·
        refine ⟨25158096108541335805946597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16772064072360890537297731 25158096108541335805946597)
        ·
          refine ⟨4717143020351500463614987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25158096108541335805946597 4717143020351500463614987)
          ·
            refine ⟨7075714530527250695422481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4717143020351500463614987 7075714530527250695422481)
            ·
              refine ⟨5306785897895438021566861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7075714530527250695422481 5306785897895438021566861)
              ·
                refine ⟨1990044711710789258087573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5306785897895438021566861 1990044711710789258087573)
                ·
                  refine ⟨93283345861443246472855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1990044711710789258087573 93283345861443246472855)
                  ·
                    rfl

theorem cell23_1635018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 2, 3, 6].length) (baseStart_1635018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1635018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1635018 prefixEnd_1635018 := by exact prefixLift 1635018
  have htrace : WordTrace (prefixWord ++ tailWord_1635018) baseStart_1635018 baseEnd_1635018 := by
    simpa [prefixWord, tailWord_1635018, baseEnd_1635018] using wordTrace_append hprefix tailTrace_1635018
  have hstable : (prefixWord ++ tailWord_1635018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1635018).length < 2 ^ (prefixWord ++ tailWord_1635018).sum := by decide
  have hdescent : baseEnd_1635018 < baseStart_1635018 := by decide
  rcases family_descends (prefixWord ++ tailWord_1635018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1635029 : List Nat := [1, 3, 2, 5, 2, 1, 1, 1, 2, 1, 4]
def baseStart_1635029 : Nat := 118140960795 + 1635029 * 2 ^ 59
def prefixEnd_1635029 : Nat := 4983230072969 + 3 ^ 40 * 1635029 * 2
def baseEnd_1635029 : Nat := 839555761040188675218145

theorem tailTrace_1635029 : CollatzResearch.WordTrace tailWord_1635029 prefixEnd_1635029 839555761040188675218145 := by
  unfold tailWord_1635029
  simp only [CollatzResearch.WordTrace]
  refine ⟨59634406793576648566820141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39756271195717765711213427 59634406793576648566820141)
  ·
    refine ⟨22362902547591243212557553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59634406793576648566820141 22362902547591243212557553)
    ·
      refine ⟨16772176910693432409418165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22362902547591243212557553 16772176910693432409418165)
      ·
        refine ⟨1572391585377509288382953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 16772176910693432409418165 1572391585377509288382953)
        ·
          refine ⟨1179293689033131966287215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1572391585377509288382953 1179293689033131966287215)
          ·
            refine ⟨1768940533549697949430823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1179293689033131966287215 1768940533549697949430823)
            ·
              refine ⟨2653410800324546924146235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1768940533549697949430823 2653410800324546924146235)
              ·
                refine ⟨3980116200486820386219353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2653410800324546924146235 3980116200486820386219353)
                ·
                  refine ⟨2985087150365115289664515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3980116200486820386219353 2985087150365115289664515)
                  ·
                    refine ⟨4477630725547672934496773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2985087150365115289664515 4477630725547672934496773)
                    ·
                      refine ⟨839555761040188675218145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4477630725547672934496773 839555761040188675218145)
                      ·
                        rfl

theorem cell23_1635029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 2, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 2, 1, 1, 1, 2, 1, 4].length) (baseStart_1635029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1635029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1635029 prefixEnd_1635029 := by exact prefixLift 1635029
  have htrace : WordTrace (prefixWord ++ tailWord_1635029) baseStart_1635029 baseEnd_1635029 := by
    simpa [prefixWord, tailWord_1635029, baseEnd_1635029] using wordTrace_append hprefix tailTrace_1635029
  have hstable : (prefixWord ++ tailWord_1635029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1635029).length < 2 ^ (prefixWord ++ tailWord_1635029).sum := by decide
  have hdescent : baseEnd_1635029 < baseStart_1635029 := by decide
  rcases family_descends (prefixWord ++ tailWord_1635029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1635062 : List Nat := [5, 1, 1, 1, 1, 2, 4, 1, 3, 1, 3]
def baseStart_1635062 : Nat := 118140960795 + 1635062 * 2 ^ 59
def prefixEnd_1635062 : Nat := 4983230072969 + 3 ^ 40 * 1635062 * 2
def baseEnd_1635062 : Nat := 839572705901787046105493

theorem tailTrace_1635062 : CollatzResearch.WordTrace tailWord_1635062 prefixEnd_1635062 839572705901787046105493 := by
  unfold tailWord_1635062
  simp only [CollatzResearch.WordTrace]
  refine ⟨3727225650153568450173215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 39757073601638063468514293 3727225650153568450173215)
  ·
    refine ⟨5590838475230352675259823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3727225650153568450173215 5590838475230352675259823)
    ·
      refine ⟨8386257712845529012889735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5590838475230352675259823 8386257712845529012889735)
      ·
        refine ⟨12579386569268293519334603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8386257712845529012889735 12579386569268293519334603)
        ·
          refine ⟨18869079853902440279001905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12579386569268293519334603 18869079853902440279001905)
          ·
            refine ⟨14151809890426830209251429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18869079853902440279001905 14151809890426830209251429)
            ·
              refine ⟨2653464354455030664234643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14151809890426830209251429 2653464354455030664234643)
              ·
                refine ⟨3980196531682545996351965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2653464354455030664234643 3980196531682545996351965)
                ·
                  refine ⟨1492573699380954748631987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3980196531682545996351965 1492573699380954748631987)
                  ·
                    refine ⟨2238860549071432122947981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1492573699380954748631987 2238860549071432122947981)
                    ·
                      refine ⟨839572705901787046105493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2238860549071432122947981 839572705901787046105493)
                      ·
                        rfl

theorem cell23_1635062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 4, 1, 3, 1, 3].length) (baseStart_1635062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1635062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1635062 prefixEnd_1635062 := by exact prefixLift 1635062
  have htrace : WordTrace (prefixWord ++ tailWord_1635062) baseStart_1635062 baseEnd_1635062 := by
    simpa [prefixWord, tailWord_1635062, baseEnd_1635062] using wordTrace_append hprefix tailTrace_1635062
  have hstable : (prefixWord ++ tailWord_1635062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1635062).length < 2 ^ (prefixWord ++ tailWord_1635062).sum := by decide
  have hdescent : baseEnd_1635062 < baseStart_1635062 := by decide
  rcases family_descends (prefixWord ++ tailWord_1635062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1635091 : List Nat := [1, 1, 1, 2, 1, 3, 5, 9]
def baseStart_1635091 : Nat := 118140960795 + 1635091 * 2 ^ 59
def prefixEnd_1635091 : Nat := 4983230072969 + 3 ^ 40 * 1635091 * 2
def baseEnd_1635091 : Nat := 31095836920028423431217

theorem tailTrace_1635091 : CollatzResearch.WordTrace tailWord_1635091 prefixEnd_1635091 31095836920028423431217 := by
  unfold tailWord_1635091
  simp only [CollatzResearch.WordTrace]
  refine ⟨59636668119352033155577127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39757778746234688770384751 59636668119352033155577127)
  ·
    refine ⟨89455002179028049733365691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59636668119352033155577127 89455002179028049733365691)
    ·
      refine ⟨134182503268542074600048537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89455002179028049733365691 134182503268542074600048537)
      ·
        refine ⟨100636877451406555950036403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134182503268542074600048537 100636877451406555950036403)
        ·
          refine ⟨150955316177109833925054605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100636877451406555950036403 150955316177109833925054605)
          ·
            refine ⟨56608243566416187721895477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 150955316177109833925054605 56608243566416187721895477)
            ·
              refine ⟨5307022834351517598927701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 56608243566416187721895477 5307022834351517598927701)
              ·
                refine ⟨31095836920028423431217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 5307022834351517598927701 31095836920028423431217)
                ·
                  rfl

theorem cell23_1635091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 5, 9].length) (baseStart_1635091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1635091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1635091 prefixEnd_1635091 := by exact prefixLift 1635091
  have htrace : WordTrace (prefixWord ++ tailWord_1635091) baseStart_1635091 baseEnd_1635091 := by
    simpa [prefixWord, tailWord_1635091, baseEnd_1635091] using wordTrace_append hprefix tailTrace_1635091
  have hstable : (prefixWord ++ tailWord_1635091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1635091).length < 2 ^ (prefixWord ++ tailWord_1635091).sum := by decide
  have hdescent : baseEnd_1635091 < baseStart_1635091 := by decide
  rcases family_descends (prefixWord ++ tailWord_1635091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1635098 : List Nat := [3, 1, 1, 3, 2, 1, 2, 1, 3, 2, 4]
def baseStart_1635098 : Nat := 118140960795 + 1635098 * 2 ^ 59
def prefixEnd_1635098 : Nat := 4983230072969 + 3 ^ 40 * 1635098 * 2
def baseEnd_1635098 : Nat := 839591191205348905255327

theorem tailTrace_1635098 : CollatzResearch.WordTrace tailWord_1635098 prefixEnd_1635098 839591191205348905255327 := by
  unfold tailWord_1635098
  simp only [CollatzResearch.WordTrace]
  refine ⟨14909230857581668337770487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39757948953551115567387965 14909230857581668337770487)
  ·
    refine ⟨22363846286372502506655731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14909230857581668337770487 22363846286372502506655731)
    ·
      refine ⟨33545769429558753759983597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22363846286372502506655731 33545769429558753759983597)
      ·
        refine ⟨12579663536084532659993849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33545769429558753759983597 12579663536084532659993849)
        ·
          refine ⟨9434747652063399494995387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12579663536084532659993849 9434747652063399494995387)
          ·
            refine ⟨14152121478095099242493081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9434747652063399494995387 14152121478095099242493081)
            ·
              refine ⟨10614091108571324431869811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14152121478095099242493081 10614091108571324431869811)
              ·
                refine ⟨15921136662856986647804717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10614091108571324431869811 15921136662856986647804717)
                ·
                  refine ⟨5970426248571369992926769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15921136662856986647804717 5970426248571369992926769)
                  ·
                    refine ⟨4477819686428527494695077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5970426248571369992926769 4477819686428527494695077)
                    ·
                      refine ⟨839591191205348905255327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4477819686428527494695077 839591191205348905255327)
                      ·
                        rfl

theorem cell23_1635098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 1, 3, 2, 4].length) (baseStart_1635098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1635098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1635098 prefixEnd_1635098 := by exact prefixLift 1635098
  have htrace : WordTrace (prefixWord ++ tailWord_1635098) baseStart_1635098 baseEnd_1635098 := by
    simpa [prefixWord, tailWord_1635098, baseEnd_1635098] using wordTrace_append hprefix tailTrace_1635098
  have hstable : (prefixWord ++ tailWord_1635098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1635098).length < 2 ^ (prefixWord ++ tailWord_1635098).sum := by decide
  have hdescent : baseEnd_1635098 < baseStart_1635098 := by decide
  rcases family_descends (prefixWord ++ tailWord_1635098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1635105 : List Nat := [1, 2, 3, 2, 1, 2, 1, 5, 1, 2, 3]
def baseStart_1635105 : Nat := 118140960795 + 1635105 * 2 ^ 59
def prefixEnd_1635105 : Nat := 4983230072969 + 3 ^ 40 * 1635105 * 2
def baseEnd_1635105 : Nat := 839594785569930377867795

theorem tailTrace_1635105 : CollatzResearch.WordTrace tailWord_1635105 prefixEnd_1635105 839594785569930377867795 := by
  unfold tailWord_1635105
  simp only [CollatzResearch.WordTrace]
  refine ⟨59637178741301313546586769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39758119160867542364391179 59637178741301313546586769)
  ·
    refine ⟨44727884055975985159940077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59637178741301313546586769 44727884055975985159940077)
    ·
      refine ⟨16772956520990994434977529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44727884055975985159940077 16772956520990994434977529)
      ·
        refine ⟨12579717390743245826233147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16772956520990994434977529 12579717390743245826233147)
        ·
          refine ⟨18869576086114868739349721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12579717390743245826233147 18869576086114868739349721)
          ·
            refine ⟨14152182064586151554512291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18869576086114868739349721 14152182064586151554512291)
            ·
              refine ⟨21228273096879227331768437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14152182064586151554512291 21228273096879227331768437)
              ·
                refine ⟨1990150602832427562353291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21228273096879227331768437 1990150602832427562353291)
                ·
                  refine ⟨2985225904248641343529937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1990150602832427562353291 2985225904248641343529937)
                  ·
                    refine ⟨2238919428186481007647453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2985225904248641343529937 2238919428186481007647453)
                    ·
                      refine ⟨839594785569930377867795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2238919428186481007647453 839594785569930377867795)
                      ·
                        rfl

theorem cell23_1635105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 5, 1, 2, 3].length) (baseStart_1635105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1635105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1635105 prefixEnd_1635105 := by exact prefixLift 1635105
  have htrace : WordTrace (prefixWord ++ tailWord_1635105) baseStart_1635105 baseEnd_1635105 := by
    simpa [prefixWord, tailWord_1635105, baseEnd_1635105] using wordTrace_append hprefix tailTrace_1635105
  have hstable : (prefixWord ++ tailWord_1635105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1635105).length < 2 ^ (prefixWord ++ tailWord_1635105).sum := by decide
  have hdescent : baseEnd_1635105 < baseStart_1635105 := by decide
  rcases family_descends (prefixWord ++ tailWord_1635105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1635168 : List Nat := [2, 1, 1, 3, 3, 1, 2, 2, 2, 6]
def baseStart_1635168 : Nat := 118140960795 + 1635168 * 2 ^ 59
def prefixEnd_1635168 : Nat := 4983230072969 + 3 ^ 40 * 1635168 * 2
def baseEnd_1635168 : Nat := 279875711617054543793335

theorem tailTrace_1635168 : CollatzResearch.WordTrace tailWord_1635168 prefixEnd_1635168 279875711617054543793335 := by
  unfold tailWord_1635168
  simp only [CollatzResearch.WordTrace]
  refine ⟨29819738270036537653065079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39759651026715383537420105 29819738270036537653065079)
  ·
    refine ⟨44729607405054806479597619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29819738270036537653065079 44729607405054806479597619)
    ·
      refine ⟨67094411107582209719396429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44729607405054806479597619 67094411107582209719396429)
      ·
        refine ⟨25160404165343328644773661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67094411107582209719396429 25160404165343328644773661)
        ·
          refine ⟨9435151562003748241790123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25160404165343328644773661 9435151562003748241790123)
          ·
            refine ⟨14152727343005622362685185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9435151562003748241790123 14152727343005622362685185)
            ·
              refine ⟨10614545507254216772013889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14152727343005622362685185 10614545507254216772013889)
              ·
                refine ⟨7960909130440662579010417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10614545507254216772013889 7960909130440662579010417)
                ·
                  refine ⟨5970681847830496934257813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7960909130440662579010417 5970681847830496934257813)
                  ·
                    refine ⟨279875711617054543793335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5970681847830496934257813 279875711617054543793335)
                    ·
                      rfl

theorem cell23_1635168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 2, 2, 6].length) (baseStart_1635168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1635168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1635168 prefixEnd_1635168 := by exact prefixLift 1635168
  have htrace : WordTrace (prefixWord ++ tailWord_1635168) baseStart_1635168 baseEnd_1635168 := by
    simpa [prefixWord, tailWord_1635168, baseEnd_1635168] using wordTrace_append hprefix tailTrace_1635168
  have hstable : (prefixWord ++ tailWord_1635168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1635168).length < 2 ^ (prefixWord ++ tailWord_1635168).sum := by decide
  have hdescent : baseEnd_1635168 < baseStart_1635168 := by decide
  rcases family_descends (prefixWord ++ tailWord_1635168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1635170 : List Nat := [3, 3, 2, 1, 3, 2, 2, 2, 1, 2, 2]
def baseStart_1635170 : Nat := 118140960795 + 1635170 * 2 ^ 59
def prefixEnd_1635170 : Nat := 4983230072969 + 3 ^ 40 * 1635170 * 2
def baseEnd_1635170 : Nat := 839628161812472623554997

theorem tailTrace_1635170 : CollatzResearch.WordTrace tailWord_1635170 prefixEnd_1635170 839628161812472623554997 := by
  unfold tailWord_1635170
  simp only [CollatzResearch.WordTrace]
  refine ⟨14909887371516457411925741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39759699657377219765135309 14909887371516457411925741)
  ·
    refine ⟨5591207764318671529472153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14909887371516457411925741 5591207764318671529472153)
    ·
      refine ⟨4193405823239003647104115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5591207764318671529472153 4193405823239003647104115)
      ·
        refine ⟨6290108734858505470656173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4193405823239003647104115 6290108734858505470656173)
        ·
          refine ⟨2358790775571939551496065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6290108734858505470656173 2358790775571939551496065)
          ·
            refine ⟨1769093081678954663622049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2358790775571939551496065 1769093081678954663622049)
            ·
              refine ⟨1326819811259215997716537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1769093081678954663622049 1326819811259215997716537)
              ·
                refine ⟨995114858444411998287403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1326819811259215997716537 995114858444411998287403)
                ·
                  refine ⟨1492672287666617997431105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 995114858444411998287403 1492672287666617997431105)
                  ·
                    refine ⟨1119504215749963498073329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1492672287666617997431105 1119504215749963498073329)
                    ·
                      refine ⟨839628161812472623554997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1119504215749963498073329 839628161812472623554997)
                      ·
                        rfl

theorem cell23_1635170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 2, 2, 2, 1, 2, 2].length) (baseStart_1635170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1635170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1635170 prefixEnd_1635170 := by exact prefixLift 1635170
  have htrace : WordTrace (prefixWord ++ tailWord_1635170) baseStart_1635170 baseEnd_1635170 := by
    simpa [prefixWord, tailWord_1635170, baseEnd_1635170] using wordTrace_append hprefix tailTrace_1635170
  have hstable : (prefixWord ++ tailWord_1635170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1635170).length < 2 ^ (prefixWord ++ tailWord_1635170).sum := by decide
  have hdescent : baseEnd_1635170 < baseStart_1635170 := by decide
  rcases family_descends (prefixWord ++ tailWord_1635170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1635235 : List Nat := [1, 1, 1, 4, 1, 2, 2, 1, 1, 7, 2]
def baseStart_1635235 : Nat := 118140960795 + 1635235 * 2 ^ 59
def prefixEnd_1635235 : Nat := 4983230072969 + 3 ^ 40 * 1635235 * 2
def baseEnd_1635235 : Nat := 839661538055014869242197

theorem tailTrace_1635235 : CollatzResearch.WordTrace tailWord_1635235 prefixEnd_1635235 839661538055014869242197 := by
  unfold tailWord_1635235
  simp only [CollatzResearch.WordTrace]
  refine ⟨59641920230830345748819159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39761280153886897165879439 59641920230830345748819159)
  ·
    refine ⟨89462880346245518623228739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59641920230830345748819159 89462880346245518623228739)
    ·
      refine ⟨134194320519368277934843109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89462880346245518623228739 134194320519368277934843109)
      ·
        refine ⟨25161435097381552112783083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 134194320519368277934843109 25161435097381552112783083)
        ·
          refine ⟨37742152646072328169174625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25161435097381552112783083 37742152646072328169174625)
          ·
            refine ⟨28306614484554246126880969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37742152646072328169174625 28306614484554246126880969)
            ·
              refine ⟨21229960863415684595160727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28306614484554246126880969 21229960863415684595160727)
              ·
                refine ⟨31844941295123526892741091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21229960863415684595160727 31844941295123526892741091)
                ·
                  refine ⟨47767411942685290339111637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31844941295123526892741091 47767411942685290339111637)
                  ·
                    refine ⟨1119548717406686492322929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 47767411942685290339111637 1119548717406686492322929)
                    ·
                      refine ⟨839661538055014869242197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1119548717406686492322929 839661538055014869242197)
                      ·
                        rfl

theorem cell23_1635235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 1, 1, 7, 2].length) (baseStart_1635235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1635235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1635235 prefixEnd_1635235 := by exact prefixLift 1635235
  have htrace : WordTrace (prefixWord ++ tailWord_1635235) baseStart_1635235 baseEnd_1635235 := by
    simpa [prefixWord, tailWord_1635235, baseEnd_1635235] using wordTrace_append hprefix tailTrace_1635235
  have hstable : (prefixWord ++ tailWord_1635235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1635235).length < 2 ^ (prefixWord ++ tailWord_1635235).sum := by decide
  have hdescent : baseEnd_1635235 < baseStart_1635235 := by decide
  rcases family_descends (prefixWord ++ tailWord_1635235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1635258 : List Nat := [3, 1, 1, 1, 2, 1, 3, 1, 2, 8]
def baseStart_1635258 : Nat := 118140960795 + 1635258 * 2 ^ 59
def prefixEnd_1635258 : Nat := 4983230072969 + 3 ^ 40 * 1635258 * 2
def baseEnd_1635258 : Nat := 279891116036689426418197

theorem tailTrace_1635258 : CollatzResearch.WordTrace tailWord_1635258 prefixEnd_1635258 279891116036689426418197 := by
  unfold tailWord_1635258
  simp only [CollatzResearch.WordTrace]
  refine ⟨14910689777436755169226607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39761839406498013784604285 14910689777436755169226607)
  ·
    refine ⟨22366034666155132753839911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14910689777436755169226607 22366034666155132753839911)
    ·
      refine ⟨33549051999232699130759867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22366034666155132753839911 33549051999232699130759867)
      ·
        refine ⟨50323577998849048696139801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33549051999232699130759867 50323577998849048696139801)
        ·
          refine ⟨37742683499136786522104851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50323577998849048696139801 37742683499136786522104851)
          ·
            refine ⟨56614025248705179783157277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37742683499136786522104851 56614025248705179783157277)
            ·
              refine ⟨21230259468264442418683979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56614025248705179783157277 21230259468264442418683979)
              ·
                refine ⟨31845389202396663628025969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21230259468264442418683979 31845389202396663628025969)
                ·
                  refine ⟨23884041901797497721019477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31845389202396663628025969 23884041901797497721019477)
                  ·
                    refine ⟨279891116036689426418197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 23884041901797497721019477 279891116036689426418197)
                    ·
                      rfl

theorem cell23_1635258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 1, 2, 8].length) (baseStart_1635258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1635258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1635258 prefixEnd_1635258 := by exact prefixLift 1635258
  have htrace : WordTrace (prefixWord ++ tailWord_1635258) baseStart_1635258 baseEnd_1635258 := by
    simpa [prefixWord, tailWord_1635258, baseEnd_1635258] using wordTrace_append hprefix tailTrace_1635258
  have hstable : (prefixWord ++ tailWord_1635258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1635258).length < 2 ^ (prefixWord ++ tailWord_1635258).sum := by decide
  have hdescent : baseEnd_1635258 < baseStart_1635258 := by decide
  rcases family_descends (prefixWord ++ tailWord_1635258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1635282 : List Nat := [3, 2, 2, 3, 1, 1, 1, 1, 4, 1, 4]
def baseStart_1635282 : Nat := 118140960795 + 1635282 * 2 ^ 59
def prefixEnd_1635282 : Nat := 4983230072969 + 3 ^ 40 * 1635282 * 2
def baseEnd_1635282 : Nat := 839685671645776185354481

theorem tailTrace_1635282 : CollatzResearch.WordTrace tailWord_1635282 prefixEnd_1635282 839685671645776185354481 := by
  unfold tailWord_1635282
  simp only [CollatzResearch.WordTrace]
  refine ⟨14910908615415018193945025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39762422974440048517186733 14910908615415018193945025)
  ·
    refine ⟨11183181461561263645458769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14910908615415018193945025 11183181461561263645458769)
    ·
      refine ⟨8387386096170947734094077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11183181461561263645458769 8387386096170947734094077)
      ·
        refine ⟨3145269786064105400285279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8387386096170947734094077 3145269786064105400285279)
        ·
          refine ⟨4717904679096158100427919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3145269786064105400285279 4717904679096158100427919)
          ·
            refine ⟨7076857018644237150641879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4717904679096158100427919 7076857018644237150641879)
            ·
              refine ⟨10615285527966355725962819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7076857018644237150641879 10615285527966355725962819)
              ·
                refine ⟨15922928291949533588944229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10615285527966355725962819 15922928291949533588944229)
                ·
                  refine ⟨2985549054740537547927043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15922928291949533588944229 2985549054740537547927043)
                  ·
                    refine ⟨4478323582110806321890565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2985549054740537547927043 4478323582110806321890565)
                    ·
                      refine ⟨839685671645776185354481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4478323582110806321890565 839685671645776185354481)
                      ·
                        rfl

theorem cell23_1635282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 1, 4, 1, 4].length) (baseStart_1635282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1635282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1635282 prefixEnd_1635282 := by exact prefixLift 1635282
  have htrace : WordTrace (prefixWord ++ tailWord_1635282) baseStart_1635282 baseEnd_1635282 := by
    simpa [prefixWord, tailWord_1635282, baseEnd_1635282] using wordTrace_append hprefix tailTrace_1635282
  have hstable : (prefixWord ++ tailWord_1635282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1635282).length < 2 ^ (prefixWord ++ tailWord_1635282).sum := by decide
  have hdescent : baseEnd_1635282 < baseStart_1635282 := by decide
  rcases family_descends (prefixWord ++ tailWord_1635282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1635372 : List Nat := [2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 4]
def baseStart_1635372 : Nat := 118140960795 + 1635372 * 2 ^ 59
def prefixEnd_1635372 : Nat := 4983230072969 + 3 ^ 40 * 1635372 * 2
def baseEnd_1635372 : Nat := 839731884904680833229067

theorem tailTrace_1635372 : CollatzResearch.WordTrace tailWord_1635372 prefixEnd_1635372 839731884904680833229067 := by
  unfold tailWord_1635372
  simp only [CollatzResearch.WordTrace]
  refine ⟨29823458515667009073278185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39764611354222678764370913 29823458515667009073278185)
  ·
    refine ⟨22367593886750256804958639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29823458515667009073278185 22367593886750256804958639)
    ·
      refine ⟨33551390830125385207437959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22367593886750256804958639 33551390830125385207437959)
      ·
        refine ⟨50327086245188077811156939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33551390830125385207437959 50327086245188077811156939)
        ·
          refine ⟨75490629367782116716735409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50327086245188077811156939 75490629367782116716735409)
          ·
            refine ⟨56617972025836587537551557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75490629367782116716735409 56617972025836587537551557)
            ·
              refine ⟨10615869754844360163290917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 56617972025836587537551557 10615869754844360163290917)
              ·
                refine ⟨1990475579033317530617047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10615869754844360163290917 1990475579033317530617047)
                ·
                  refine ⟨2985713368549976295925571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1990475579033317530617047 2985713368549976295925571)
                  ·
                    refine ⟨4478570052824964443888357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2985713368549976295925571 4478570052824964443888357)
                    ·
                      refine ⟨839731884904680833229067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4478570052824964443888357 839731884904680833229067)
                      ·
                        rfl

theorem cell23_1635372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 4].length) (baseStart_1635372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1635372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1635372 prefixEnd_1635372 := by exact prefixLift 1635372
  have htrace : WordTrace (prefixWord ++ tailWord_1635372) baseStart_1635372 baseEnd_1635372 := by
    simpa [prefixWord, tailWord_1635372, baseEnd_1635372] using wordTrace_append hprefix tailTrace_1635372
  have hstable : (prefixWord ++ tailWord_1635372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1635372).length < 2 ^ (prefixWord ++ tailWord_1635372).sum := by decide
  have hdescent : baseEnd_1635372 < baseStart_1635372 := by decide
  rcases family_descends (prefixWord ++ tailWord_1635372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1635389 : List Nat := [1, 4, 1, 3, 1, 3, 1, 3, 1, 1, 4]
def baseStart_1635389 : Nat := 118140960795 + 1635389 * 2 ^ 59
def prefixEnd_1635389 : Nat := 4983230072969 + 3 ^ 40 * 1635389 * 2
def baseEnd_1635389 : Nat := 839740614075807266716489

theorem tailTrace_1635389 : CollatzResearch.WordTrace tailWord_1635389 prefixEnd_1635389 839740614075807266716489 := by
  unfold tailWord_1635389
  simp only [CollatzResearch.WordTrace]
  refine ⟨59647537072272430049925221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39765024714848286699950147 59647537072272430049925221)
  ·
    refine ⟨11183913201051080634360979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 59647537072272430049925221 11183913201051080634360979)
    ·
      refine ⟨16775869801576620951541469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11183913201051080634360979 16775869801576620951541469)
      ·
        refine ⟨6290951175591232856828051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16775869801576620951541469 6290951175591232856828051)
        ·
          refine ⟨9436426763386849285242077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6290951175591232856828051 9436426763386849285242077)
          ·
            refine ⟨3538660036270068481965779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9436426763386849285242077 3538660036270068481965779)
            ·
              refine ⟨5307990054405102722948669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3538660036270068481965779 5307990054405102722948669)
              ·
                refine ⟨1990496270401913521105751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5307990054405102722948669 1990496270401913521105751)
                ·
                  refine ⟨2985744405602870281658627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1990496270401913521105751 2985744405602870281658627)
                  ·
                    refine ⟨4478616608404305422487941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2985744405602870281658627 4478616608404305422487941)
                    ·
                      refine ⟨839740614075807266716489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4478616608404305422487941 839740614075807266716489)
                      ·
                        rfl

theorem cell23_1635389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 1, 3, 1, 1, 4].length) (baseStart_1635389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1635389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1635389 prefixEnd_1635389 := by exact prefixLift 1635389
  have htrace : WordTrace (prefixWord ++ tailWord_1635389) baseStart_1635389 baseEnd_1635389 := by
    simpa [prefixWord, tailWord_1635389, baseEnd_1635389] using wordTrace_append hprefix tailTrace_1635389
  have hstable : (prefixWord ++ tailWord_1635389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1635389).length < 2 ^ (prefixWord ++ tailWord_1635389).sum := by decide
  have hdescent : baseEnd_1635389 < baseStart_1635389 := by decide
  rcases family_descends (prefixWord ++ tailWord_1635389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1635399 : List Nat := [1, 1, 4, 1, 3, 2, 3, 2, 2, 4]
def baseStart_1635399 : Nat := 118140960795 + 1635399 * 2 ^ 59
def prefixEnd_1635399 : Nat := 4983230072969 + 3 ^ 40 * 1635399 * 2
def baseEnd_1635399 : Nat := 279915249627450742530481

theorem tailTrace_1635399 : CollatzResearch.WordTrace tailWord_1635399 prefixEnd_1635399 279915249627450742530481 := by
  unfold tailWord_1635399
  simp only [CollatzResearch.WordTrace]
  refine ⟨59647901802236201757789251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39765267868157467838526167 59647901802236201757789251)
  ·
    refine ⟨89471852703354302636683877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59647901802236201757789251 89471852703354302636683877)
    ·
      refine ⟨16775972381878931744378227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 89471852703354302636683877 16775972381878931744378227)
      ·
        refine ⟨25163958572818397616567341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16775972381878931744378227 25163958572818397616567341)
        ·
          refine ⟨9436484464806899106212753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25163958572818397616567341 9436484464806899106212753)
          ·
            refine ⟨7077363348605174329659565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9436484464806899106212753 7077363348605174329659565)
            ·
              refine ⟨2654011255726940373622337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7077363348605174329659565 2654011255726940373622337)
              ·
                refine ⟨1990508441795205280216753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2654011255726940373622337 1990508441795205280216753)
                ·
                  refine ⟨1492881331346403960162565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1990508441795205280216753 1492881331346403960162565)
                  ·
                    refine ⟨279915249627450742530481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1492881331346403960162565 279915249627450742530481)
                    ·
                      rfl

theorem cell23_1635399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 3, 2, 2, 4].length) (baseStart_1635399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1635399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1635399 prefixEnd_1635399 := by exact prefixLift 1635399
  have htrace : WordTrace (prefixWord ++ tailWord_1635399) baseStart_1635399 baseEnd_1635399 := by
    simpa [prefixWord, tailWord_1635399, baseEnd_1635399] using wordTrace_append hprefix tailTrace_1635399
  have hstable : (prefixWord ++ tailWord_1635399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1635399).length < 2 ^ (prefixWord ++ tailWord_1635399).sum := by decide
  have hdescent : baseEnd_1635399 < baseStart_1635399 := by decide
  rcases family_descends (prefixWord ++ tailWord_1635399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1635406 : List Nat := [4, 1, 1, 1, 1, 3, 4, 1, 3, 2, 2]
def baseStart_1635406 : Nat := 118140960795 + 1635406 * 2 ^ 59
def prefixEnd_1635406 : Nat := 4983230072969 + 3 ^ 40 * 1635406 * 2
def baseEnd_1635406 : Nat := 839749343246933700203911

theorem tailTrace_1635406 : CollatzResearch.WordTrace tailWord_1635406 prefixEnd_1635406 839749343246933700203911 := by
  unfold tailWord_1635406
  simp only [CollatzResearch.WordTrace]
  refine ⟨7456019639151355244161759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39765438075473894635529381 7456019639151355244161759)
  ·
    refine ⟨11184029458727032866242639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7456019639151355244161759 11184029458727032866242639)
    ·
      refine ⟨16776044188090549299363959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11184029458727032866242639 16776044188090549299363959)
      ·
        refine ⟨25164066282135823949045939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16776044188090549299363959 25164066282135823949045939)
        ·
          refine ⟨37746099423203735923568909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25164066282135823949045939 37746099423203735923568909)
          ·
            refine ⟨14154787283701400971338341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37746099423203735923568909 14154787283701400971338341)
            ·
              refine ⟨2654022615694012682125939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14154787283701400971338341 2654022615694012682125939)
              ·
                refine ⟨3981033923541019023188909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2654022615694012682125939 3981033923541019023188909)
                ·
                  refine ⟨1492887721327882133695841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3981033923541019023188909 1492887721327882133695841)
                  ·
                    refine ⟨1119665790995911600271881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1492887721327882133695841 1119665790995911600271881)
                    ·
                      refine ⟨839749343246933700203911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1119665790995911600271881 839749343246933700203911)
                      ·
                        rfl

theorem cell23_1635406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 4, 1, 3, 2, 2].length) (baseStart_1635406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1635406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1635406 prefixEnd_1635406 := by exact prefixLift 1635406
  have htrace : WordTrace (prefixWord ++ tailWord_1635406) baseStart_1635406 baseEnd_1635406 := by
    simpa [prefixWord, tailWord_1635406, baseEnd_1635406] using wordTrace_append hprefix tailTrace_1635406
  have hstable : (prefixWord ++ tailWord_1635406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1635406).length < 2 ^ (prefixWord ++ tailWord_1635406).sum := by decide
  have hdescent : baseEnd_1635406 < baseStart_1635406 := by decide
  rcases family_descends (prefixWord ++ tailWord_1635406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1635425 : List Nat := [1, 2, 3, 1, 1, 2, 2, 2, 2, 7]
def baseStart_1635425 : Nat := 118140960795 + 1635425 * 2 ^ 59
def prefixEnd_1635425 : Nat := 4983230072969 + 3 ^ 40 * 1635425 * 2
def baseEnd_1635425 : Nat := 279919699793123041955441

theorem tailTrace_1635425 : CollatzResearch.WordTrace tailWord_1635425 prefixEnd_1635425 279919699793123041955441 := by
  unfold tailWord_1635425
  simp only [CollatzResearch.WordTrace]
  refine ⟨59648850100142008198235729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39765900066761338798823819 59648850100142008198235729)
  ·
    refine ⟨44736637575106506148676797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59648850100142008198235729 44736637575106506148676797)
    ·
      refine ⟨16776239090664939805753799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44736637575106506148676797 16776239090664939805753799)
      ·
        refine ⟨25164358635997409708630699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16776239090664939805753799 25164358635997409708630699)
        ·
          refine ⟨37746537953996114562946049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25164358635997409708630699 37746537953996114562946049)
          ·
            refine ⟨28309903465497085922209537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37746537953996114562946049 28309903465497085922209537)
            ·
              refine ⟨21232427599122814441657153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28309903465497085922209537 21232427599122814441657153)
              ·
                refine ⟨15924320699342110831242865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21232427599122814441657153 15924320699342110831242865)
                ·
                  refine ⟨11943240524506583123432149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15924320699342110831242865 11943240524506583123432149)
                  ·
                    refine ⟨279919699793123041955441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 11943240524506583123432149 279919699793123041955441)
                    ·
                      rfl

theorem cell23_1635425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 2, 2, 7].length) (baseStart_1635425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1635425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1635425 prefixEnd_1635425 := by exact prefixLift 1635425
  have htrace : WordTrace (prefixWord ++ tailWord_1635425) baseStart_1635425 baseEnd_1635425 := by
    simpa [prefixWord, tailWord_1635425, baseEnd_1635425] using wordTrace_append hprefix tailTrace_1635425
  have hstable : (prefixWord ++ tailWord_1635425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1635425).length < 2 ^ (prefixWord ++ tailWord_1635425).sum := by decide
  have hdescent : baseEnd_1635425 < baseStart_1635425 := by decide
  rcases family_descends (prefixWord ++ tailWord_1635425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1635426 : List Nat := [3, 3, 2, 2, 1, 1, 1, 4, 1, 2, 3]
def baseStart_1635426 : Nat := 118140960795 + 1635426 * 2 ^ 59
def prefixEnd_1635426 : Nat := 4983230072969 + 3 ^ 40 * 1635426 * 2
def baseEnd_1635426 : Nat := 839759612860023621953819

theorem tailTrace_1635426 : CollatzResearch.WordTrace tailWord_1635426 prefixEnd_1635426 839759612860023621953819 := by
  unfold tailWord_1635426
  simp only [CollatzResearch.WordTrace]
  refine ⟨14912221643284596342255533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39765924382092256912681421 14912221643284596342255533)
  ·
    refine ⟨5592083116231723628345825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14912221643284596342255533 5592083116231723628345825)
    ·
      refine ⟨4194062337173792721259369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5592083116231723628345825 4194062337173792721259369)
      ·
        refine ⟨3145546752880344540944527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4194062337173792721259369 3145546752880344540944527)
        ·
          refine ⟨4718320129320516811416791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3145546752880344540944527 4718320129320516811416791)
          ·
            refine ⟨7077480193980775217125187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4718320129320516811416791 7077480193980775217125187)
            ·
              refine ⟨10616220290971162825687781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7077480193980775217125187 10616220290971162825687781)
              ·
                refine ⟨1990541304557093029816459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10616220290971162825687781 1990541304557093029816459)
                ·
                  refine ⟨2985811956835639544724689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1990541304557093029816459 2985811956835639544724689)
                  ·
                    refine ⟨2239358967626729658543517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2985811956835639544724689 2239358967626729658543517)
                    ·
                      refine ⟨839759612860023621953819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2239358967626729658543517 839759612860023621953819)
                      ·
                        rfl

theorem cell23_1635426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 4, 1, 2, 3].length) (baseStart_1635426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1635426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1635426 prefixEnd_1635426 := by exact prefixLift 1635426
  have htrace : WordTrace (prefixWord ++ tailWord_1635426) baseStart_1635426 baseEnd_1635426 := by
    simpa [prefixWord, tailWord_1635426, baseEnd_1635426] using wordTrace_append hprefix tailTrace_1635426
  have hstable : (prefixWord ++ tailWord_1635426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1635426).length < 2 ^ (prefixWord ++ tailWord_1635426).sum := by decide
  have hdescent : baseEnd_1635426 < baseStart_1635426 := by decide
  rcases family_descends (prefixWord ++ tailWord_1635426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1635513 : List Nat := [1, 2, 1, 4, 1, 4, 2, 2, 2, 2, 2]
def baseStart_1635513 : Nat := 118140960795 + 1635513 * 2 ^ 59
def prefixEnd_1635513 : Nat := 4983230072969 + 3 ^ 40 * 1635513 * 2
def baseEnd_1635513 : Nat := 839804285676964781565919

theorem tailTrace_1635513 : CollatzResearch.WordTrace tailWord_1635513 prefixEnd_1635513 839804285676964781565919 := by
  unfold tailWord_1635513
  simp only [CollatzResearch.WordTrace]
  refine ⟨59652059723823199227439193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39768039815882132818292795 59652059723823199227439193)
  ·
    refine ⟨44739044792867399420579395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59652059723823199227439193 44739044792867399420579395)
    ·
      refine ⟨67108567189301099130869093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44739044792867399420579395 67108567189301099130869093)
      ·
        refine ⟨12582856347993956087037955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 67108567189301099130869093 12582856347993956087037955)
        ·
          refine ⟨18874284521990934130556933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12582856347993956087037955 18874284521990934130556933)
          ·
            refine ⟨3538928347873300149479425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18874284521990934130556933 3538928347873300149479425)
            ·
              refine ⟨2654196260904975112109569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3538928347873300149479425 2654196260904975112109569)
              ·
                refine ⟨1990647195678731334082177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2654196260904975112109569 1990647195678731334082177)
                ·
                  refine ⟨1492985396759048500561633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1990647195678731334082177 1492985396759048500561633)
                  ·
                    refine ⟨1119739047569286375421225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1492985396759048500561633 1119739047569286375421225)
                    ·
                      refine ⟨839804285676964781565919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1119739047569286375421225 839804285676964781565919)
                      ·
                        rfl

theorem cell23_1635513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 2, 2, 2, 2, 2].length) (baseStart_1635513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1635513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1635513 prefixEnd_1635513 := by exact prefixLift 1635513
  have htrace : WordTrace (prefixWord ++ tailWord_1635513) baseStart_1635513 baseEnd_1635513 := by
    simpa [prefixWord, tailWord_1635513, baseEnd_1635513] using wordTrace_append hprefix tailTrace_1635513
  have hstable : (prefixWord ++ tailWord_1635513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1635513).length < 2 ^ (prefixWord ++ tailWord_1635513).sum := by decide
  have hdescent : baseEnd_1635513 < baseStart_1635513 := by decide
  rcases family_descends (prefixWord ++ tailWord_1635513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1635669 : List Nat := [1, 3, 2, 2, 3, 1, 1, 1, 3, 6]
def baseStart_1635669 : Nat := 118140960795 + 1635669 * 2 ^ 59
def prefixEnd_1635669 : Nat := 4983230072969 + 3 ^ 40 * 1635669 * 2
def baseEnd_1635669 : Nat := 279961462886355390405067

theorem tailTrace_1635669 : CollatzResearch.WordTrace tailWord_1635669 prefixEnd_1635669 279961462886355390405067 := by
  unfold tailWord_1635669
  simp only [CollatzResearch.WordTrace]
  refine ⟨59657749511258037870118061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39771833007505358580078707 59657749511258037870118061)
  ·
    refine ⟨22371656066721764201294273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59657749511258037870118061 22371656066721764201294273)
    ·
      refine ⟨16778742050041323150970705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22371656066721764201294273 16778742050041323150970705)
      ·
        refine ⟨12584056537530992363228029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16778742050041323150970705 12584056537530992363228029)
        ·
          refine ⟨4719021201574122136210511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12584056537530992363228029 4719021201574122136210511)
          ·
            refine ⟨7078531802361183204315767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4719021201574122136210511 7078531802361183204315767)
            ·
              refine ⟨10617797703541774806473651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7078531802361183204315767 10617797703541774806473651)
              ·
                refine ⟨15926696555312662209710477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10617797703541774806473651 15926696555312662209710477)
                ·
                  refine ⟨5972511208242248328641429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15926696555312662209710477 5972511208242248328641429)
                  ·
                    refine ⟨279961462886355390405067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5972511208242248328641429 279961462886355390405067)
                    ·
                      rfl

theorem cell23_1635669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 1, 3, 6].length) (baseStart_1635669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1635669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1635669 prefixEnd_1635669 := by exact prefixLift 1635669
  have htrace : WordTrace (prefixWord ++ tailWord_1635669) baseStart_1635669 baseEnd_1635669 := by
    simpa [prefixWord, tailWord_1635669, baseEnd_1635669] using wordTrace_append hprefix tailTrace_1635669
  have hstable : (prefixWord ++ tailWord_1635669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1635669).length < 2 ^ (prefixWord ++ tailWord_1635669).sum := by decide
  have hdescent : baseEnd_1635669 < baseStart_1635669 := by decide
  rcases family_descends (prefixWord ++ tailWord_1635669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1635716 : List Nat := [2, 3, 2, 1, 1, 4, 3, 7]
def baseStart_1635716 : Nat := 118140960795 + 1635716 * 2 ^ 59
def prefixEnd_1635716 : Nat := 4983230072969 + 3 ^ 40 * 1635716 * 2
def baseEnd_1635716 : Nat := 31107723046289906938055

theorem tailTrace_1635716 : CollatzResearch.WordTrace tailWord_1635716 prefixEnd_1635716 31107723046289906938055 := by
  unfold tailWord_1635716
  simp only [CollatzResearch.WordTrace]
  refine ⟨29829731871043882448539501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39772975828058509931386001 29829731871043882448539501)
  ·
    refine ⟨11186149451641455918202313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29829731871043882448539501 11186149451641455918202313)
    ·
      refine ⟨8389612088731091938651735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11186149451641455918202313 8389612088731091938651735)
      ·
        refine ⟨12584418133096637907977603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8389612088731091938651735 12584418133096637907977603)
        ·
          refine ⟨18876627199644956861966405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12584418133096637907977603 18876627199644956861966405)
          ·
            refine ⟨3539367599933429411618701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18876627199644956861966405 3539367599933429411618701)
            ·
              refine ⟨1327262849975036029357013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3539367599933429411618701 1327262849975036029357013)
              ·
                refine ⟨31107723046289906938055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1327262849975036029357013 31107723046289906938055)
                ·
                  rfl

theorem cell23_1635716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 3, 7].length) (baseStart_1635716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1635716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1635716 prefixEnd_1635716 := by exact prefixLift 1635716
  have htrace : WordTrace (prefixWord ++ tailWord_1635716) baseStart_1635716 baseEnd_1635716 := by
    simpa [prefixWord, tailWord_1635716, baseEnd_1635716] using wordTrace_append hprefix tailTrace_1635716
  have hstable : (prefixWord ++ tailWord_1635716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1635716).length < 2 ^ (prefixWord ++ tailWord_1635716).sum := by decide
  have hdescent : baseEnd_1635716 < baseStart_1635716 := by decide
  rcases family_descends (prefixWord ++ tailWord_1635716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1635743 : List Nat := [1, 1, 2, 5, 1, 3, 1, 1, 4, 1, 3]
def baseStart_1635743 : Nat := 118140960795 + 1635743 * 2 ^ 59
def prefixEnd_1635743 : Nat := 4983230072969 + 3 ^ 40 * 1635743 * 2
def baseEnd_1635743 : Nat := 839922386227498881689861

theorem tailTrace_1635743 : CollatzResearch.WordTrace tailWord_1635743 prefixEnd_1635743 839922386227498881689861 := by
  unfold tailWord_1635743
  simp only [CollatzResearch.WordTrace]
  refine ⟨59660448512989948508311883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39773632341993299005541255 59660448512989948508311883)
  ·
    refine ⟨89490672769484922762467825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59660448512989948508311883 89490672769484922762467825)
    ·
      refine ⟨67118004577113692071850869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89490672769484922762467825 67118004577113692071850869)
      ·
        refine ⟨6292312929104408631736019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 67118004577113692071850869 6292312929104408631736019)
        ·
          refine ⟨9438469393656612947604029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6292312929104408631736019 9438469393656612947604029)
          ·
            refine ⟨3539426022621229855351511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9438469393656612947604029 3539426022621229855351511)
            ·
              refine ⟨5309139033931844783027267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3539426022621229855351511 5309139033931844783027267)
              ·
                refine ⟨7963708550897767174540901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5309139033931844783027267 7963708550897767174540901)
                ·
                  refine ⟨1493195353293331345226419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7963708550897767174540901 1493195353293331345226419)
                  ·
                    refine ⟨2239793029939997017839629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1493195353293331345226419 2239793029939997017839629)
                    ·
                      refine ⟨839922386227498881689861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2239793029939997017839629 839922386227498881689861)
                      ·
                        rfl

theorem cell23_1635743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 1, 1, 4, 1, 3].length) (baseStart_1635743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1635743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1635743 prefixEnd_1635743 := by exact prefixLift 1635743
  have htrace : WordTrace (prefixWord ++ tailWord_1635743) baseStart_1635743 baseEnd_1635743 := by
    simpa [prefixWord, tailWord_1635743, baseEnd_1635743] using wordTrace_append hprefix tailTrace_1635743
  have hstable : (prefixWord ++ tailWord_1635743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1635743).length < 2 ^ (prefixWord ++ tailWord_1635743).sum := by decide
  have hdescent : baseEnd_1635743 < baseStart_1635743 := by decide
  rcases family_descends (prefixWord ++ tailWord_1635743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1635749 : List Nat := [1, 3, 1, 2, 1, 1, 2, 3, 2, 3, 4]
def baseStart_1635749 : Nat := 118140960795 + 1635749 * 2 ^ 59
def prefixEnd_1635749 : Nat := 4983230072969 + 3 ^ 40 * 1635749 * 2
def baseEnd_1635749 : Nat := 839925467111425858214833

theorem tailTrace_1635749 : CollatzResearch.WordTrace tailWord_1635749 prefixEnd_1635749 839925467111425858214833 := by
  unfold tailWord_1635749
  simp only [CollatzResearch.WordTrace]
  refine ⟨59660667350968211533030301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39773778233978807688686867 59660667350968211533030301)
  ·
    refine ⟨22372750256613079324886363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59660667350968211533030301 22372750256613079324886363)
    ·
      refine ⟨33559125384919618987329545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22372750256613079324886363 33559125384919618987329545)
      ·
        refine ⟨25169344038689714240497159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33559125384919618987329545 25169344038689714240497159)
        ·
          refine ⟨37754016058034571360745739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25169344038689714240497159 37754016058034571360745739)
          ·
            refine ⟨56631024087051857041118609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37754016058034571360745739 56631024087051857041118609)
            ·
              refine ⟨42473268065288892780838957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56631024087051857041118609 42473268065288892780838957)
              ·
                refine ⟨15927475524483334792814609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42473268065288892780838957 15927475524483334792814609)
                ·
                  refine ⟨11945606643362501094610957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15927475524483334792814609 11945606643362501094610957)
                  ·
                    refine ⟨4479602491260937910479109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11945606643362501094610957 4479602491260937910479109)
                    ·
                      refine ⟨839925467111425858214833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4479602491260937910479109 839925467111425858214833)
                      ·
                        rfl

theorem cell23_1635749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 3, 2, 3, 4].length) (baseStart_1635749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1635749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1635749 prefixEnd_1635749 := by exact prefixLift 1635749
  have htrace : WordTrace (prefixWord ++ tailWord_1635749) baseStart_1635749 baseEnd_1635749 := by
    simpa [prefixWord, tailWord_1635749, baseEnd_1635749] using wordTrace_append hprefix tailTrace_1635749
  have hstable : (prefixWord ++ tailWord_1635749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1635749).length < 2 ^ (prefixWord ++ tailWord_1635749).sum := by decide
  have hdescent : baseEnd_1635749 < baseStart_1635749 := by decide
  rcases family_descends (prefixWord ++ tailWord_1635749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1635779 : List Nat := [1, 1, 1, 3, 1, 1, 4, 2, 1, 4, 4]
def baseStart_1635779 : Nat := 118140960795 + 1635779 * 2 ^ 59
def prefixEnd_1635779 : Nat := 4983230072969 + 3 ^ 40 * 1635779 * 2
def baseEnd_1635779 : Nat := 839940871531060740839695

theorem tailTrace_1635779 : CollatzResearch.WordTrace tailWord_1635779 prefixEnd_1635779 839940871531060740839695 := by
  unfold tailWord_1635779
  simp only [CollatzResearch.WordTrace]
  refine ⟨59661761540859526656622391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39774507693906351104414927 59661761540859526656622391)
  ·
    refine ⟨89492642311289289984933587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59661761540859526656622391 89492642311289289984933587)
    ·
      refine ⟨134238963466933934977400381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89492642311289289984933587 134238963466933934977400381)
      ·
        refine ⟨50339611300100225616525143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 134238963466933934977400381 50339611300100225616525143)
        ·
          refine ⟨75509416950150338424787715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50339611300100225616525143 75509416950150338424787715)
          ·
            refine ⟨113264125425225507637181573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75509416950150338424787715 113264125425225507637181573)
            ·
              refine ⟨21237023517229782681971545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 113264125425225507637181573 21237023517229782681971545)
              ·
                refine ⟨15927767637922337011478659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21237023517229782681971545 15927767637922337011478659)
                ·
                  refine ⟨23891651456883505517217989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15927767637922337011478659 23891651456883505517217989)
                  ·
                    refine ⟨4479684648165657284478373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23891651456883505517217989 4479684648165657284478373)
                    ·
                      refine ⟨839940871531060740839695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4479684648165657284478373 839940871531060740839695)
                      ·
                        rfl

theorem cell23_1635779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 2, 1, 4, 4].length) (baseStart_1635779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1635779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1635779 prefixEnd_1635779 := by exact prefixLift 1635779
  have htrace : WordTrace (prefixWord ++ tailWord_1635779) baseStart_1635779 baseEnd_1635779 := by
    simpa [prefixWord, tailWord_1635779, baseEnd_1635779] using wordTrace_append hprefix tailTrace_1635779
  have hstable : (prefixWord ++ tailWord_1635779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1635779).length < 2 ^ (prefixWord ++ tailWord_1635779).sum := by decide
  have hdescent : baseEnd_1635779 < baseStart_1635779 := by decide
  rcases family_descends (prefixWord ++ tailWord_1635779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1635783 : List Nat := [1, 1, 4, 1, 1, 3, 1, 1, 6, 2, 2]
def baseStart_1635783 : Nat := 118140960795 + 1635783 * 2 ^ 59
def prefixEnd_1635783 : Nat := 4983230072969 + 3 ^ 40 * 1635783 * 2
def baseEnd_1635783 : Nat := 839942925453678725189677

theorem tailTrace_1635783 : CollatzResearch.WordTrace tailWord_1635783 prefixEnd_1635783 839942925453678725189677 := by
  unfold tailWord_1635783
  simp only [CollatzResearch.WordTrace]
  refine ⟨59661907432845035339768003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39774604955230023559845335 59661907432845035339768003)
  ·
    refine ⟨89492861149267553009652005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59661907432845035339768003 89492861149267553009652005)
    ·
      refine ⟨16779911465487666189309751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 89492861149267553009652005 16779911465487666189309751)
      ·
        refine ⟨25169867198231499283964627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16779911465487666189309751 25169867198231499283964627)
        ·
          refine ⟨37754800797347248925946941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25169867198231499283964627 37754800797347248925946941)
          ·
            refine ⟨14158050299005218347230103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37754800797347248925946941 14158050299005218347230103)
            ·
              refine ⟨21237075448507827520845155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14158050299005218347230103 21237075448507827520845155)
              ·
                refine ⟨31855613172761741281267733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21237075448507827520845155 31855613172761741281267733)
                ·
                  refine ⟨1493231867473206622559425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 31855613172761741281267733 1493231867473206622559425)
                  ·
                    refine ⟨1119923900604904966919569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1493231867473206622559425 1119923900604904966919569)
                    ·
                      refine ⟨839942925453678725189677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1119923900604904966919569 839942925453678725189677)
                      ·
                        rfl

theorem cell23_1635783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 1, 6, 2, 2].length) (baseStart_1635783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1635783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1635783 prefixEnd_1635783 := by exact prefixLift 1635783
  have htrace : WordTrace (prefixWord ++ tailWord_1635783) baseStart_1635783 baseEnd_1635783 := by
    simpa [prefixWord, tailWord_1635783, baseEnd_1635783] using wordTrace_append hprefix tailTrace_1635783
  have hstable : (prefixWord ++ tailWord_1635783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1635783).length < 2 ^ (prefixWord ++ tailWord_1635783).sum := by decide
  have hdescent : baseEnd_1635783 < baseStart_1635783 := by decide
  rcases family_descends (prefixWord ++ tailWord_1635783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1635786 : List Nat := [3, 1, 2, 1, 2, 4, 1, 1, 2, 1, 5]
def baseStart_1635786 : Nat := 118140960795 + 1635786 * 2 ^ 59
def prefixEnd_1635786 : Nat := 4983230072969 + 3 ^ 40 * 1635786 * 2
def baseEnd_1635786 : Nat := 839944465895642213452163

theorem tailTrace_1635786 : CollatzResearch.WordTrace tailWord_1635786 prefixEnd_1635786 839944465895642213452163 := by
  unfold tailWord_1635786
  simp only [CollatzResearch.WordTrace]
  refine ⟨14915504212958541713031803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39774677901222777901418141 14915504212958541713031803)
  ·
    refine ⟨22373256319437812569547705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14915504212958541713031803 22373256319437812569547705)
    ·
      refine ⟨16779942239578359427160779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22373256319437812569547705 16779942239578359427160779)
      ·
        refine ⟨25169913359367539140741169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16779942239578359427160779 25169913359367539140741169)
        ·
          refine ⟨18877435019525654355555877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25169913359367539140741169 18877435019525654355555877)
          ·
            refine ⟨3539519066161060191666727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18877435019525654355555877 3539519066161060191666727)
            ·
              refine ⟨5309278599241590287500091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3539519066161060191666727 5309278599241590287500091)
              ·
                refine ⟨7963917898862385431250137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5309278599241590287500091 7963917898862385431250137)
                ·
                  refine ⟨5972938424146789073437603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7963917898862385431250137 5972938424146789073437603)
                  ·
                    refine ⟨8959407636220183610156405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5972938424146789073437603 8959407636220183610156405)
                    ·
                      refine ⟨839944465895642213452163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8959407636220183610156405 839944465895642213452163)
                      ·
                        rfl

theorem cell23_1635786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 1, 1, 2, 1, 5].length) (baseStart_1635786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1635786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1635786 prefixEnd_1635786 := by exact prefixLift 1635786
  have htrace : WordTrace (prefixWord ++ tailWord_1635786) baseStart_1635786 baseEnd_1635786 := by
    simpa [prefixWord, tailWord_1635786, baseEnd_1635786] using wordTrace_append hprefix tailTrace_1635786
  have hstable : (prefixWord ++ tailWord_1635786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1635786).length < 2 ^ (prefixWord ++ tailWord_1635786).sum := by decide
  have hdescent : baseEnd_1635786 < baseStart_1635786 := by decide
  rcases family_descends (prefixWord ++ tailWord_1635786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1635816 : List Nat := [2, 1, 4, 1, 1, 2, 2, 1, 1, 5, 3]
def baseStart_1635816 : Nat := 118140960795 + 1635816 * 2 ^ 59
def prefixEnd_1635816 : Nat := 4983230072969 + 3 ^ 40 * 1635816 * 2
def baseEnd_1635816 : Nat := 839959870315277096077025

theorem tailTrace_1635816 : CollatzResearch.WordTrace tailWord_1635816 prefixEnd_1635816 839959870315277096077025 := by
  unfold tailWord_1635816
  simp only [CollatzResearch.WordTrace]
  refine ⟨29831555520862740987859651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39775407361150321317146201 29831555520862740987859651)
  ·
    refine ⟨44747333281294111481789477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29831555520862740987859651 44747333281294111481789477)
    ·
      refine ⟨8390124990242645902835527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44747333281294111481789477 8390124990242645902835527)
      ·
        refine ⟨12585187485363968854253291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8390124990242645902835527 12585187485363968854253291)
        ·
          refine ⟨18877781228045953281379937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12585187485363968854253291 18877781228045953281379937)
          ·
            refine ⟨14158335921034464961034953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18877781228045953281379937 14158335921034464961034953)
            ·
              refine ⟨10618751940775848720776215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14158335921034464961034953 10618751940775848720776215)
              ·
                refine ⟨15928127911163773081164323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10618751940775848720776215 15928127911163773081164323)
                ·
                  refine ⟨23892191866745659621746485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15928127911163773081164323 23892191866745659621746485)
                  ·
                    refine ⟨2239892987507405589538733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 23892191866745659621746485 2239892987507405589538733)
                    ·
                      refine ⟨839959870315277096077025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2239892987507405589538733 839959870315277096077025)
                      ·
                        rfl

theorem cell23_1635816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 1, 1, 5, 3].length) (baseStart_1635816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1635816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1635816 prefixEnd_1635816 := by exact prefixLift 1635816
  have htrace : WordTrace (prefixWord ++ tailWord_1635816) baseStart_1635816 baseEnd_1635816 := by
    simpa [prefixWord, tailWord_1635816, baseEnd_1635816] using wordTrace_append hprefix tailTrace_1635816
  have hstable : (prefixWord ++ tailWord_1635816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1635816).length < 2 ^ (prefixWord ++ tailWord_1635816).sum := by decide
  have hdescent : baseEnd_1635816 < baseStart_1635816 := by decide
  rcases family_descends (prefixWord ++ tailWord_1635816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1635819 : List Nat := [1, 1, 1, 1, 2, 3, 2, 4, 1, 7]
def baseStart_1635819 : Nat := 118140960795 + 1635819 * 2 ^ 59
def prefixEnd_1635819 : Nat := 4983230072969 + 3 ^ 40 * 1635819 * 2
def baseEnd_1635819 : Nat := 279987136919080194779837

theorem tailTrace_1635819 : CollatzResearch.WordTrace tailWord_1635819 prefixEnd_1635819 279987136919080194779837 := by
  unfold tailWord_1635819
  simp only [CollatzResearch.WordTrace]
  refine ⟨59663220460714613488078511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39775480307143075658719007 59663220460714613488078511)
  ·
    refine ⟨89494830691071920232117767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59663220460714613488078511 89494830691071920232117767)
    ·
      refine ⟨134242246036607880348176651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89494830691071920232117767 134242246036607880348176651)
      ·
        refine ⟨201363369054911820522264977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134242246036607880348176651 201363369054911820522264977)
        ·
          refine ⟨151022526791183865391698733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 201363369054911820522264977 151022526791183865391698733)
          ·
            refine ⟨56633447546693949521887025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 151022526791183865391698733 56633447546693949521887025)
            ·
              refine ⟨42475085660020462141415269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56633447546693949521887025 42475085660020462141415269)
              ·
                refine ⟨7964078561253836651515363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42475085660020462141415269 7964078561253836651515363)
                ·
                  refine ⟨11946117841880754977273045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7964078561253836651515363 11946117841880754977273045)
                  ·
                    refine ⟨279987136919080194779837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 11946117841880754977273045 279987136919080194779837)
                    ·
                      rfl

theorem cell23_1635819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 4, 1, 7].length) (baseStart_1635819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1635819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1635819 prefixEnd_1635819 := by exact prefixLift 1635819
  have htrace : WordTrace (prefixWord ++ tailWord_1635819) baseStart_1635819 baseEnd_1635819 := by
    simpa [prefixWord, tailWord_1635819, baseEnd_1635819] using wordTrace_append hprefix tailTrace_1635819
  have hstable : (prefixWord ++ tailWord_1635819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1635819).length < 2 ^ (prefixWord ++ tailWord_1635819).sum := by decide
  have hdescent : baseEnd_1635819 < baseStart_1635819 := by decide
  rcases family_descends (prefixWord ++ tailWord_1635819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1635836 : List Nat := [2, 2, 2, 1, 2, 1, 3, 3, 2, 5]
def baseStart_1635836 : Nat := 118140960795 + 1635836 * 2 ^ 59
def prefixEnd_1635836 : Nat := 4983230072969 + 3 ^ 40 * 1635836 * 2
def baseEnd_1635836 : Nat := 279990046642789005942311

theorem tailTrace_1635836 : CollatzResearch.WordTrace tailWord_1635836 prefixEnd_1635836 279990046642789005942311 := by
  unfold tailWord_1635836
  simp only [CollatzResearch.WordTrace]
  refine ⟨29831920250826512695723681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39775893667768683594298241 29831920250826512695723681)
  ·
    refine ⟨22373940188119884521792761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29831920250826512695723681 22373940188119884521792761)
    ·
      refine ⟨16780455141089913391344571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22373940188119884521792761 16780455141089913391344571)
      ·
        refine ⟨25170682711634870087016857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16780455141089913391344571 25170682711634870087016857)
        ·
          refine ⟨18878012033726152565262643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25170682711634870087016857 18878012033726152565262643)
          ·
            refine ⟨28317018050589228847893965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18878012033726152565262643 28317018050589228847893965)
            ·
              refine ⟨10618881768970960817960237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28317018050589228847893965 10618881768970960817960237)
              ·
                refine ⟨3982080663364110306735089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10618881768970960817960237 3982080663364110306735089)
                ·
                  refine ⟨2986560497523082730051317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3982080663364110306735089 2986560497523082730051317)
                  ·
                    refine ⟨279990046642789005942311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2986560497523082730051317 279990046642789005942311)
                    ·
                      rfl

theorem cell23_1635836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 3, 2, 5].length) (baseStart_1635836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1635836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1635836 prefixEnd_1635836 := by exact prefixLift 1635836
  have htrace : WordTrace (prefixWord ++ tailWord_1635836) baseStart_1635836 baseEnd_1635836 := by
    simpa [prefixWord, tailWord_1635836, baseEnd_1635836] using wordTrace_append hprefix tailTrace_1635836
  have hstable : (prefixWord ++ tailWord_1635836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1635836).length < 2 ^ (prefixWord ++ tailWord_1635836).sum := by decide
  have hdescent : baseEnd_1635836 < baseStart_1635836 := by decide
  rcases family_descends (prefixWord ++ tailWord_1635836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1635873 : List Nat := [1, 2, 3, 2, 2, 2, 1, 1, 1, 6, 2]
def baseStart_1635873 : Nat := 118140960795 + 1635873 * 2 ^ 59
def prefixEnd_1635873 : Nat := 4983230072969 + 3 ^ 40 * 1635873 * 2
def baseEnd_1635873 : Nat := 839989138712583373064263

theorem tailTrace_1635873 : CollatzResearch.WordTrace tailWord_1635873 prefixEnd_1635873 839989138712583373064263 := by
  unfold tailWord_1635873
  simp only [CollatzResearch.WordTrace]
  refine ⟨59665190002518980710544273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39776793335012653807029515 59665190002518980710544273)
  ·
    refine ⟨44748892501889235532908205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59665190002518980710544273 44748892501889235532908205)
    ·
      refine ⟨16780834688208463324840577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44748892501889235532908205 16780834688208463324840577)
      ·
        refine ⟨12585626016156347493630433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16780834688208463324840577 12585626016156347493630433)
        ·
          refine ⟨9439219512117260620222825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12585626016156347493630433 9439219512117260620222825)
          ·
            refine ⟨7079414634087945465167119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9439219512117260620222825 7079414634087945465167119)
            ·
              refine ⟨10619121951131918197750679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7079414634087945465167119 10619121951131918197750679)
              ·
                refine ⟨15928682926697877296626019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10619121951131918197750679 15928682926697877296626019)
                ·
                  refine ⟨23893024390046815944939029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15928682926697877296626019 23893024390046815944939029)
                  ·
                    refine ⟨1119985518283444497419017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23893024390046815944939029 1119985518283444497419017)
                    ·
                      refine ⟨839989138712583373064263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1119985518283444497419017 839989138712583373064263)
                      ·
                        rfl

theorem cell23_1635873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 1, 1, 6, 2].length) (baseStart_1635873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1635873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1635873 prefixEnd_1635873 := by exact prefixLift 1635873
  have htrace : WordTrace (prefixWord ++ tailWord_1635873) baseStart_1635873 baseEnd_1635873 := by
    simpa [prefixWord, tailWord_1635873, baseEnd_1635873] using wordTrace_append hprefix tailTrace_1635873
  have hstable : (prefixWord ++ tailWord_1635873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1635873).length < 2 ^ (prefixWord ++ tailWord_1635873).sum := by decide
  have hdescent : baseEnd_1635873 < baseStart_1635873 := by decide
  rcases family_descends (prefixWord ++ tailWord_1635873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1635893 : List Nat := [1, 3, 3, 1, 1, 4, 1, 1, 1, 4, 3]
def baseStart_1635893 : Nat := 118140960795 + 1635893 * 2 ^ 59
def prefixEnd_1635893 : Nat := 4983230072969 + 3 ^ 40 * 1635893 * 2
def baseEnd_1635893 : Nat := 839999408325673294814171

theorem tailTrace_1635893 : CollatzResearch.WordTrace tailWord_1635893 prefixEnd_1635893 839999408325673294814171 := by
  unfold tailWord_1635893
  simp only [CollatzResearch.WordTrace]
  refine ⟨59665919462446524126272333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39777279641631016084181555 59665919462446524126272333)
  ·
    refine ⟨22374719798417446547352125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59665919462446524126272333 22374719798417446547352125)
    ·
      refine ⟨8390519924406542455257047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22374719798417446547352125 8390519924406542455257047)
      ·
        refine ⟨12585779886609813682885571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8390519924406542455257047 12585779886609813682885571)
        ·
          refine ⟨18878669829914720524328357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12585779886609813682885571 18878669829914720524328357)
          ·
            refine ⟨3539750593109010098311567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18878669829914720524328357 3539750593109010098311567)
            ·
              refine ⟨5309625889663515147467351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3539750593109010098311567 5309625889663515147467351)
              ·
                refine ⟨7964438834495272721201027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5309625889663515147467351 7964438834495272721201027)
                ·
                  refine ⟨11946658251742909081801541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7964438834495272721201027 11946658251742909081801541)
                  ·
                    refine ⟨2239998422201795452837789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11946658251742909081801541 2239998422201795452837789)
                    ·
                      refine ⟨839999408325673294814171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2239998422201795452837789 839999408325673294814171)
                      ·
                        rfl

theorem cell23_1635893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 1, 1, 1, 4, 3].length) (baseStart_1635893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1635893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1635893 prefixEnd_1635893 := by exact prefixLift 1635893
  have htrace : WordTrace (prefixWord ++ tailWord_1635893) baseStart_1635893 baseEnd_1635893 := by
    simpa [prefixWord, tailWord_1635893, baseEnd_1635893] using wordTrace_append hprefix tailTrace_1635893
  have hstable : (prefixWord ++ tailWord_1635893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1635893).length < 2 ^ (prefixWord ++ tailWord_1635893).sum := by decide
  have hdescent : baseEnd_1635893 < baseStart_1635893 := by decide
  rcases family_descends (prefixWord ++ tailWord_1635893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1635916 : List Nat := [2, 2, 1, 3, 1, 3, 1, 1, 1, 2, 6]
def baseStart_1635916 : Nat := 118140960795 + 1635916 * 2 ^ 59
def prefixEnd_1635916 : Nat := 4983230072969 + 3 ^ 40 * 1635916 * 2
def baseEnd_1635916 : Nat := 840011218380726704826565

theorem tailTrace_1635916 : CollatzResearch.WordTrace tailWord_1635916 prefixEnd_1635916 840011218380726704826565 := by
  unfold tailWord_1635916
  simp only [CollatzResearch.WordTrace]
  refine ⟨29833379170681599527179801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39777838894242132702906401 29833379170681599527179801)
  ·
    refine ⟨22375034378011199645384851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29833379170681599527179801 22375034378011199645384851)
    ·
      refine ⟨33562551567016799468077277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22375034378011199645384851 33562551567016799468077277)
      ·
        refine ⟨12585956837631299800528979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33562551567016799468077277 12585956837631299800528979)
        ·
          refine ⟨18878935256446949700793469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12585956837631299800528979 18878935256446949700793469)
          ·
            refine ⟨7079600721167606137797551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18878935256446949700793469 7079600721167606137797551)
            ·
              refine ⟨10619401081751409206696327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7079600721167606137797551 10619401081751409206696327)
              ·
                refine ⟨15929101622627113810044491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10619401081751409206696327 15929101622627113810044491)
                ·
                  refine ⟨23893652433940670715066737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15929101622627113810044491 23893652433940670715066737)
                  ·
                    refine ⟨17920239325455503036300053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23893652433940670715066737 17920239325455503036300053)
                    ·
                      refine ⟨840011218380726704826565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 17920239325455503036300053 840011218380726704826565)
                      ·
                        rfl

theorem cell23_1635916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 1, 1, 2, 6].length) (baseStart_1635916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1635916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1635916 prefixEnd_1635916 := by exact prefixLift 1635916
  have htrace : WordTrace (prefixWord ++ tailWord_1635916) baseStart_1635916 baseEnd_1635916 := by
    simpa [prefixWord, tailWord_1635916, baseEnd_1635916] using wordTrace_append hprefix tailTrace_1635916
  have hstable : (prefixWord ++ tailWord_1635916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1635916).length < 2 ^ (prefixWord ++ tailWord_1635916).sum := by decide
  have hdescent : baseEnd_1635916 < baseStart_1635916 := by decide
  rcases family_descends (prefixWord ++ tailWord_1635916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1635917 : List Nat := [1, 6, 1, 1, 3, 1, 2, 1, 3, 4]
def baseStart_1635917 : Nat := 118140960795 + 1635917 * 2 ^ 59
def prefixEnd_1635917 : Nat := 4983230072969 + 3 ^ 40 * 1635917 * 2
def baseEnd_1635917 : Nat := 280003910620460400304687

theorem tailTrace_1635917 : CollatzResearch.WordTrace tailWord_1635917 prefixEnd_1635917 280003910620460400304687 := by
  unfold tailWord_1635917
  simp only [CollatzResearch.WordTrace]
  refine ⟨59666794814359576225146005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39777863209573050816764003 59666794814359576225146005)
  ·
    refine ⟨2796881006923105135553719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 59666794814359576225146005 2796881006923105135553719)
    ·
      refine ⟨4195321510384657703330579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2796881006923105135553719 4195321510384657703330579)
      ·
        refine ⟨6292982265576986554995869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4195321510384657703330579 6292982265576986554995869)
        ·
          refine ⟨2359868349591369958123451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6292982265576986554995869 2359868349591369958123451)
          ·
            refine ⟨3539802524387054937185177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2359868349591369958123451 3539802524387054937185177)
            ·
              refine ⟨2654851893290291202888883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3539802524387054937185177 2654851893290291202888883)
              ·
                refine ⟨3982277839935436804333325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2654851893290291202888883 3982277839935436804333325)
                ·
                  refine ⟨1493354189975788801624997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3982277839935436804333325 1493354189975788801624997)
                  ·
                    refine ⟨280003910620460400304687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1493354189975788801624997 280003910620460400304687)
                    ·
                      rfl

theorem cell23_1635917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 2, 1, 3, 4].length) (baseStart_1635917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1635917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1635917 prefixEnd_1635917 := by exact prefixLift 1635917
  have htrace : WordTrace (prefixWord ++ tailWord_1635917) baseStart_1635917 baseEnd_1635917 := by
    simpa [prefixWord, tailWord_1635917, baseEnd_1635917] using wordTrace_append hprefix tailTrace_1635917
  have hstable : (prefixWord ++ tailWord_1635917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1635917).length < 2 ^ (prefixWord ++ tailWord_1635917).sum := by decide
  have hdescent : baseEnd_1635917 < baseStart_1635917 := by decide
  rcases family_descends (prefixWord ++ tailWord_1635917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1635940 : List Nat := [2, 3, 1, 1, 2, 3, 2, 2, 3, 1, 3]
def baseStart_1635940 : Nat := 118140960795 + 1635940 * 2 ^ 59
def prefixEnd_1635940 : Nat := 4983230072969 + 3 ^ 40 * 1635940 * 2
def baseEnd_1635940 : Nat := 840023541916434610926455

theorem tailTrace_1635940 : CollatzResearch.WordTrace tailWord_1635940 prefixEnd_1635940 840023541916434610926455 := by
  unfold tailWord_1635940
  simp only [CollatzResearch.WordTrace]
  refine ⟨29833816846638125576616637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39778422462184167435488849 29833816846638125576616637)
  ·
    refine ⟨11187681317489297091231239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29833816846638125576616637 11187681317489297091231239)
    ·
      refine ⟨16781521976233945636846859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11187681317489297091231239 16781521976233945636846859)
      ·
        refine ⟨25172282964350918455270289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16781521976233945636846859 25172282964350918455270289)
        ·
          refine ⟨18879212223263188841452717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25172282964350918455270289 18879212223263188841452717)
          ·
            refine ⟨7079704583723695815544769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18879212223263188841452717 7079704583723695815544769)
            ·
              refine ⟨5309778437792771861658577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7079704583723695815544769 5309778437792771861658577)
              ·
                refine ⟨3982333828344578896243933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5309778437792771861658577 3982333828344578896243933)
                ·
                  refine ⟨1493375185629217086091475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3982333828344578896243933 1493375185629217086091475)
                  ·
                    refine ⟨2240062778443825629137213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1493375185629217086091475 2240062778443825629137213)
                    ·
                      refine ⟨840023541916434610926455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2240062778443825629137213 840023541916434610926455)
                      ·
                        rfl

theorem cell23_1635940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 2, 2, 3, 1, 3].length) (baseStart_1635940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1635940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1635940 prefixEnd_1635940 := by exact prefixLift 1635940
  have htrace : WordTrace (prefixWord ++ tailWord_1635940) baseStart_1635940 baseEnd_1635940 := by
    simpa [prefixWord, tailWord_1635940, baseEnd_1635940] using wordTrace_append hprefix tailTrace_1635940
  have hstable : (prefixWord ++ tailWord_1635940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1635940).length < 2 ^ (prefixWord ++ tailWord_1635940).sum := by decide
  have hdescent : baseEnd_1635940 < baseStart_1635940 := by decide
  rcases family_descends (prefixWord ++ tailWord_1635940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1635943 : List Nat := [1, 1, 5, 1, 1, 1, 3, 4, 1, 5]
def baseStart_1635943 : Nat := 118140960795 + 1635943 * 2 ^ 59
def prefixEnd_1635943 : Nat := 4983230072969 + 3 ^ 40 * 1635943 * 2
def baseEnd_1635943 : Nat := 280008360786132699729647

theorem tailTrace_1635943 : CollatzResearch.WordTrace tailWord_1635943 prefixEnd_1635943 280008360786132699729647 := by
  unfold tailWord_1635943
  simp only [CollatzResearch.WordTrace]
  refine ⟨59667743112265382665592483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39778495408176921777061655 59667743112265382665592483)
  ·
    refine ⟨89501614668398073998388725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59667743112265382665592483 89501614668398073998388725)
    ·
      refine ⟨8390776375162319437348943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 89501614668398073998388725 8390776375162319437348943)
      ·
        refine ⟨12586164562743479156023415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8390776375162319437348943 12586164562743479156023415)
        ·
          refine ⟨18879246844115218734035123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12586164562743479156023415 18879246844115218734035123)
          ·
            refine ⟨28318870266172828101052685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18879246844115218734035123 28318870266172828101052685)
            ·
              refine ⟨10619576349814810537894757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28318870266172828101052685 10619576349814810537894757)
              ·
                refine ⟨1991170565590276975855267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10619576349814810537894757 1991170565590276975855267)
                ·
                  refine ⟨2986755848385415463782901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1991170565590276975855267 2986755848385415463782901)
                  ·
                    refine ⟨280008360786132699729647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2986755848385415463782901 280008360786132699729647)
                    ·
                      rfl

theorem cell23_1635943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 4, 1, 5].length) (baseStart_1635943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1635943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1635943 prefixEnd_1635943 := by exact prefixLift 1635943
  have htrace : WordTrace (prefixWord ++ tailWord_1635943) baseStart_1635943 baseEnd_1635943 := by
    simpa [prefixWord, tailWord_1635943, baseEnd_1635943] using wordTrace_append hprefix tailTrace_1635943
  have hstable : (prefixWord ++ tailWord_1635943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1635943).length < 2 ^ (prefixWord ++ tailWord_1635943).sum := by decide
  have hdescent : baseEnd_1635943 < baseStart_1635943 := by decide
  rcases family_descends (prefixWord ++ tailWord_1635943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1635963 : List Nat := [1, 1, 1, 1, 1, 4, 3, 5, 1, 1, 4]
def baseStart_1635963 : Nat := 118140960795 + 1635963 * 2 ^ 59
def prefixEnd_1635963 : Nat := 4983230072969 + 3 ^ 40 * 1635963 * 2
def baseEnd_1635963 : Nat := 840035351971488020938849

theorem tailTrace_1635963 : CollatzResearch.WordTrace tailWord_1635963 prefixEnd_1635963 840035351971488020938849 := by
  unfold tailWord_1635963
  simp only [CollatzResearch.WordTrace]
  refine ⟨59668472572192926081320543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39778981714795284054213695 59668472572192926081320543)
  ·
    refine ⟨89502708858289389121980815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59668472572192926081320543 89502708858289389121980815)
    ·
      refine ⟨134254063287434083682971223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89502708858289389121980815 134254063287434083682971223)
      ·
        refine ⟨201381094931151125524456835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134254063287434083682971223 201381094931151125524456835)
        ·
          refine ⟨302071642396726688286685253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 201381094931151125524456835 302071642396726688286685253)
          ·
            refine ⟨56638432949386254053753485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 302071642396726688286685253 56638432949386254053753485)
            ·
              refine ⟨21239412356019845270157557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56638432949386254053753485 21239412356019845270157557)
              ·
                refine ⟨1991194908376860494077271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21239412356019845270157557 1991194908376860494077271)
                ·
                  refine ⟨2986792362565290741115907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1991194908376860494077271 2986792362565290741115907)
                  ·
                    refine ⟨4480188543847936111673861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2986792362565290741115907 4480188543847936111673861)
                    ·
                      refine ⟨840035351971488020938849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4480188543847936111673861 840035351971488020938849)
                      ·
                        rfl

theorem cell23_1635963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 5, 1, 1, 4].length) (baseStart_1635963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1635963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1635963 prefixEnd_1635963 := by exact prefixLift 1635963
  have htrace : WordTrace (prefixWord ++ tailWord_1635963) baseStart_1635963 baseEnd_1635963 := by
    simpa [prefixWord, tailWord_1635963, baseEnd_1635963] using wordTrace_append hprefix tailTrace_1635963
  have hstable : (prefixWord ++ tailWord_1635963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1635963).length < 2 ^ (prefixWord ++ tailWord_1635963).sum := by decide
  have hdescent : baseEnd_1635963 < baseStart_1635963 := by decide
  rcases family_descends (prefixWord ++ tailWord_1635963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1635973 : List Nat := [1, 3, 1, 1, 4, 1, 1, 3, 4, 4]
def baseStart_1635973 : Nat := 118140960795 + 1635973 * 2 ^ 59
def prefixEnd_1635973 : Nat := 4983230072969 + 3 ^ 40 * 1635973 * 2
def baseEnd_1635973 : Nat := 280013495592677660604601

theorem tailTrace_1635973 : CollatzResearch.WordTrace tailWord_1635973 prefixEnd_1635973 280013495592677660604601 := by
  unfold tailWord_1635973
  simp only [CollatzResearch.WordTrace]
  refine ⟨59668837302156697789184573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39779224868104465192789715 59668837302156697789184573)
  ·
    refine ⟨22375813988308761670944215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59668837302156697789184573 22375813988308761670944215)
    ·
      refine ⟨33563720982463142506416323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22375813988308761670944215 33563720982463142506416323)
      ·
        refine ⟨50345581473694713759624485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33563720982463142506416323 50345581473694713759624485)
        ·
          refine ⟨9439796526317758829929591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50345581473694713759624485 9439796526317758829929591)
          ·
            refine ⟨14159694789476638244894387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9439796526317758829929591 14159694789476638244894387)
            ·
              refine ⟨21239542184214957367341581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14159694789476638244894387 21239542184214957367341581)
              ·
                refine ⟨7964828319080609012753093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21239542184214957367341581 7964828319080609012753093)
                ·
                  refine ⟨1493405309827614189891205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7964828319080609012753093 1493405309827614189891205)
                  ·
                    refine ⟨280013495592677660604601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1493405309827614189891205 280013495592677660604601)
                    ·
                      rfl

theorem cell23_1635973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 3, 4, 4].length) (baseStart_1635973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1635973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1635973 prefixEnd_1635973 := by exact prefixLift 1635973
  have htrace : WordTrace (prefixWord ++ tailWord_1635973) baseStart_1635973 baseEnd_1635973 := by
    simpa [prefixWord, tailWord_1635973, baseEnd_1635973] using wordTrace_append hprefix tailTrace_1635973
  have hstable : (prefixWord ++ tailWord_1635973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1635973).length < 2 ^ (prefixWord ++ tailWord_1635973).sum := by decide
  have hdescent : baseEnd_1635973 < baseStart_1635973 := by decide
  rcases family_descends (prefixWord ++ tailWord_1635973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1636000 : List Nat := [2, 1, 1, 4, 3, 2, 1, 1, 3, 2, 3]
def baseStart_1636000 : Nat := 118140960795 + 1636000 * 2 ^ 59
def prefixEnd_1636000 : Nat := 4983230072969 + 3 ^ 40 * 1636000 * 2
def baseEnd_1636000 : Nat := 840054350755704376176179

theorem tailTrace_1636000 : CollatzResearch.WordTrace tailWord_1636000 prefixEnd_1636000 840054350755704376176179 := by
  unfold tailWord_1636000
  simp only [CollatzResearch.WordTrace]
  refine ⟨29834911036529440700208727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39779881382039254266944969 29834911036529440700208727)
  ·
    refine ⟨44752366554794161050313091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29834911036529440700208727 44752366554794161050313091)
    ·
      refine ⟨67128549832191241575469637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44752366554794161050313091 67128549832191241575469637)
      ·
        refine ⟨12586603093535857795400557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 67128549832191241575469637 12586603093535857795400557)
        ·
          refine ⟨4719976160075946673275209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12586603093535857795400557 4719976160075946673275209)
          ·
            refine ⟨3539982120056960004956407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4719976160075946673275209 3539982120056960004956407)
            ·
              refine ⟨5309973180085440007434611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3539982120056960004956407 5309973180085440007434611)
              ·
                refine ⟨7964959770128160011151917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5309973180085440007434611 7964959770128160011151917)
                ·
                  refine ⟨2986859913798060004181969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7964959770128160011151917 2986859913798060004181969)
                  ·
                    refine ⟨2240144935348545003136477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2986859913798060004181969 2240144935348545003136477)
                    ·
                      refine ⟨840054350755704376176179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2240144935348545003136477 840054350755704376176179)
                      ·
                        rfl

theorem cell23_1636000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 1, 1, 3, 2, 3].length) (baseStart_1636000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1636000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1636000 prefixEnd_1636000 := by exact prefixLift 1636000
  have htrace : WordTrace (prefixWord ++ tailWord_1636000) baseStart_1636000 baseEnd_1636000 := by
    simpa [prefixWord, tailWord_1636000, baseEnd_1636000] using wordTrace_append hprefix tailTrace_1636000
  have hstable : (prefixWord ++ tailWord_1636000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1636000).length < 2 ^ (prefixWord ++ tailWord_1636000).sum := by decide
  have hdescent : baseEnd_1636000 < baseStart_1636000 := by decide
  rcases family_descends (prefixWord ++ tailWord_1636000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1636040 : List Nat := [2, 1, 3, 1, 2, 2, 1, 1, 5, 3, 2]
def baseStart_1636040 : Nat := 118140960795 + 1636040 * 2 ^ 59
def prefixEnd_1636040 : Nat := 4983230072969 + 3 ^ 40 * 1636040 * 2
def baseEnd_1636040 : Nat := 840074889981884219675995

theorem tailTrace_1636040 : CollatzResearch.WordTrace tailWord_1636040 prefixEnd_1636040 840074889981884219675995 := by
  unfold tailWord_1636040
  simp only [CollatzResearch.WordTrace]
  refine ⟨29835640496456984115936787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39780853995275978821249049 29835640496456984115936787)
  ·
    refine ⟨44753460744685476173905181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29835640496456984115936787 44753460744685476173905181)
    ·
      refine ⟨16782547779257053565214443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44753460744685476173905181 16782547779257053565214443)
      ·
        refine ⟨25173821668885580347821665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16782547779257053565214443 25173821668885580347821665)
        ·
          refine ⟨18880366251664185260866249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25173821668885580347821665 18880366251664185260866249)
          ·
            refine ⟨14160274688748138945649687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18880366251664185260866249 14160274688748138945649687)
            ·
              refine ⟨21240412033122208418474531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14160274688748138945649687 21240412033122208418474531)
              ·
                refine ⟨31860618049683312627711797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21240412033122208418474531 31860618049683312627711797)
                ·
                  refine ⟨2986932942157810558847981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 31860618049683312627711797 2986932942157810558847981)
                  ·
                    refine ⟨1120099853309178959567993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2986932942157810558847981 1120099853309178959567993)
                    ·
                      refine ⟨840074889981884219675995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1120099853309178959567993 840074889981884219675995)
                      ·
                        rfl

theorem cell23_1636040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 1, 5, 3, 2].length) (baseStart_1636040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1636040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1636040 prefixEnd_1636040 := by exact prefixLift 1636040
  have htrace : WordTrace (prefixWord ++ tailWord_1636040) baseStart_1636040 baseEnd_1636040 := by
    simpa [prefixWord, tailWord_1636040, baseEnd_1636040] using wordTrace_append hprefix tailTrace_1636040
  have hstable : (prefixWord ++ tailWord_1636040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1636040).length < 2 ^ (prefixWord ++ tailWord_1636040).sum := by decide
  have hdescent : baseEnd_1636040 < baseStart_1636040 := by decide
  rcases family_descends (prefixWord ++ tailWord_1636040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1636054 : List Nat := [5, 2, 1, 3, 1, 1, 3, 7]
def baseStart_1636054 : Nat := 118140960795 + 1636054 * 2 ^ 59
def prefixEnd_1636054 : Nat := 4983230072969 + 3 ^ 40 * 1636054 * 2
def baseEnd_1636054 : Nat := 31114151063372117218553

theorem tailTrace_1636054 : CollatzResearch.WordTrace tailWord_1636054 prefixEnd_1636054 31114151063372117218553 := by
  unfold tailWord_1636054
  simp only [CollatzResearch.WordTrace]
  refine ⟨3729486975928953038930201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 39781194409908832415255477 3729486975928953038930201)
  ·
    refine ⟨2797115231946714779197651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3729486975928953038930201 2797115231946714779197651)
    ·
      refine ⟨4195672847920072168796477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2797115231946714779197651 4195672847920072168796477)
      ·
        refine ⟨1573377317970027063298679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4195672847920072168796477 1573377317970027063298679)
        ·
          refine ⟨2360065976955040594948019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1573377317970027063298679 2360065976955040594948019)
          ·
            refine ⟨3540098965432560892422029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2360065976955040594948019 3540098965432560892422029)
            ·
              refine ⟨1327537112037210334658261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3540098965432560892422029 1327537112037210334658261)
              ·
                refine ⟨31114151063372117218553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1327537112037210334658261 31114151063372117218553)
                ·
                  rfl

theorem cell23_1636054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 3, 7].length) (baseStart_1636054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1636054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1636054 prefixEnd_1636054 := by exact prefixLift 1636054
  have htrace : WordTrace (prefixWord ++ tailWord_1636054) baseStart_1636054 baseEnd_1636054 := by
    simpa [prefixWord, tailWord_1636054, baseEnd_1636054] using wordTrace_append hprefix tailTrace_1636054
  have hstable : (prefixWord ++ tailWord_1636054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1636054).length < 2 ^ (prefixWord ++ tailWord_1636054).sum := by decide
  have hdescent : baseEnd_1636054 < baseStart_1636054 := by decide
  rcases family_descends (prefixWord ++ tailWord_1636054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1636074 : List Nat := [3, 1, 3, 1, 1, 1, 6, 1, 1, 3, 2]
def baseStart_1636074 : Nat := 118140960795 + 1636074 * 2 ^ 59
def prefixEnd_1636074 : Nat := 4983230072969 + 3 ^ 40 * 1636074 * 2
def baseEnd_1636074 : Nat := 840092348324137086650839

theorem tailTrace_1636074 : CollatzResearch.WordTrace tailWord_1636074 prefixEnd_1636074 840092348324137086650839 := by
  unfold tailWord_1636074
  simp only [CollatzResearch.WordTrace]
  refine ⟨14918130268697698009652819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39781680716527194692407517 14918130268697698009652819)
  ·
    refine ⟨22377195403046547014479229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14918130268697698009652819 22377195403046547014479229)
    ·
      refine ⟨8391448276142455130429711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22377195403046547014479229 8391448276142455130429711)
      ·
        refine ⟨12587172414213682695644567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8391448276142455130429711 12587172414213682695644567)
        ·
          refine ⟨18880758621320524043466851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12587172414213682695644567 18880758621320524043466851)
          ·
            refine ⟨28321137931980786065200277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18880758621320524043466851 28321137931980786065200277)
            ·
              refine ⟨1327553340561599346806263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 28321137931980786065200277 1327553340561599346806263)
              ·
                refine ⟨1991330010842399020209395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1327553340561599346806263 1991330010842399020209395)
                ·
                  refine ⟨2986995016263598530314093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1991330010842399020209395 2986995016263598530314093)
                  ·
                    refine ⟨1120123131098849448867785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2986995016263598530314093 1120123131098849448867785)
                    ·
                      refine ⟨840092348324137086650839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1120123131098849448867785 840092348324137086650839)
                      ·
                        rfl

theorem cell23_1636074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 6, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 6, 1, 1, 3, 2].length) (baseStart_1636074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1636074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1636074 prefixEnd_1636074 := by exact prefixLift 1636074
  have htrace : WordTrace (prefixWord ++ tailWord_1636074) baseStart_1636074 baseEnd_1636074 := by
    simpa [prefixWord, tailWord_1636074, baseEnd_1636074] using wordTrace_append hprefix tailTrace_1636074
  have hstable : (prefixWord ++ tailWord_1636074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1636074).length < 2 ^ (prefixWord ++ tailWord_1636074).sum := by decide
  have hdescent : baseEnd_1636074 < baseStart_1636074 := by decide
  rcases family_descends (prefixWord ++ tailWord_1636074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1636083 : List Nat := [1, 1, 1, 2, 2, 3, 3, 2, 2, 2, 4]
def baseStart_1636083 : Nat := 118140960795 + 1636083 * 2 ^ 59
def prefixEnd_1636083 : Nat := 4983230072969 + 3 ^ 40 * 1636083 * 2
def baseEnd_1636083 : Nat := 840096969650027551438297

theorem tailTrace_1636083 : CollatzResearch.WordTrace tailWord_1636083 prefixEnd_1636083 840096969650027551438297 := by
  unfold tailWord_1636083
  simp only [CollatzResearch.WordTrace]
  refine ⟨59672849331758186575688903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39781899554505457717125935 59672849331758186575688903)
  ·
    refine ⟨89509273997637279863533355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59672849331758186575688903 89509273997637279863533355)
    ·
      refine ⟨134263910996455919795300033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89509273997637279863533355 134263910996455919795300033)
      ·
        refine ⟨100697933247341939846475025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134263910996455919795300033 100697933247341939846475025)
        ·
          refine ⟨75523449935506454884856269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100697933247341939846475025 75523449935506454884856269)
          ·
            refine ⟨28321293725814920581821101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75523449935506454884856269 28321293725814920581821101)
            ·
              refine ⟨10620485147180595218182913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28321293725814920581821101 10620485147180595218182913)
              ·
                refine ⟨7965363860385446413637185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10620485147180595218182913 7965363860385446413637185)
                ·
                  refine ⟨5974022895289084810227889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7965363860385446413637185 5974022895289084810227889)
                  ·
                    refine ⟨4480517171466813607670917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5974022895289084810227889 4480517171466813607670917)
                    ·
                      refine ⟨840096969650027551438297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4480517171466813607670917 840096969650027551438297)
                      ·
                        rfl

theorem cell23_1636083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 2, 2, 2, 4].length) (baseStart_1636083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1636083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1636083 prefixEnd_1636083 := by exact prefixLift 1636083
  have htrace : WordTrace (prefixWord ++ tailWord_1636083) baseStart_1636083 baseEnd_1636083 := by
    simpa [prefixWord, tailWord_1636083, baseEnd_1636083] using wordTrace_append hprefix tailTrace_1636083
  have hstable : (prefixWord ++ tailWord_1636083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1636083).length < 2 ^ (prefixWord ++ tailWord_1636083).sum := by decide
  have hdescent : baseEnd_1636083 < baseStart_1636083 := by decide
  rcases family_descends (prefixWord ++ tailWord_1636083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1636100 : List Nat := [2, 3, 2, 2, 1, 2, 2, 1, 2, 2, 4]
def baseStart_1636100 : Nat := 118140960795 + 1636100 * 2 ^ 59
def prefixEnd_1636100 : Nat := 4983230072969 + 3 ^ 40 * 1636100 * 2
def baseEnd_1636100 : Nat := 840105698821153984925719

theorem tailTrace_1636100 : CollatzResearch.WordTrace tailWord_1636100 prefixEnd_1636100 840105698821153984925719 := by
  unfold tailWord_1636100
  simp only [CollatzResearch.WordTrace]
  refine ⟨29836734686348299239528877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39782312915131065652705169 29836734686348299239528877)
  ·
    refine ⟨11188775507380612214823329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29836734686348299239528877 11188775507380612214823329)
    ·
      refine ⟨8391581630535459161117497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11188775507380612214823329 8391581630535459161117497)
      ·
        refine ⟨6293686222901594370838123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8391581630535459161117497 6293686222901594370838123)
        ·
          refine ⟨9440529334352391556257185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6293686222901594370838123 9440529334352391556257185)
          ·
            refine ⟨7080397000764293667192889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9440529334352391556257185 7080397000764293667192889)
            ·
              refine ⟨5310297750573220250394667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7080397000764293667192889 5310297750573220250394667)
              ·
                refine ⟨7965446625859830375592001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5310297750573220250394667 7965446625859830375592001)
                ·
                  refine ⟨5974084969394872781694001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7965446625859830375592001 5974084969394872781694001)
                  ·
                    refine ⟨4480563727046154586270501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5974084969394872781694001 4480563727046154586270501)
                    ·
                      refine ⟨840105698821153984925719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4480563727046154586270501 840105698821153984925719)
                      ·
                        rfl

theorem cell23_1636100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 2, 1, 2, 2, 4].length) (baseStart_1636100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1636100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1636100 prefixEnd_1636100 := by exact prefixLift 1636100
  have htrace : WordTrace (prefixWord ++ tailWord_1636100) baseStart_1636100 baseEnd_1636100 := by
    simpa [prefixWord, tailWord_1636100, baseEnd_1636100] using wordTrace_append hprefix tailTrace_1636100
  have hstable : (prefixWord ++ tailWord_1636100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1636100).length < 2 ^ (prefixWord ++ tailWord_1636100).sum := by decide
  have hdescent : baseEnd_1636100 < baseStart_1636100 := by decide
  rcases family_descends (prefixWord ++ tailWord_1636100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1636140 : List Nat := [2, 2, 1, 1, 1, 6, 1, 2, 2, 5]
def baseStart_1636140 : Nat := 118140960795 + 1636140 * 2 ^ 59
def prefixEnd_1636140 : Nat := 4983230072969 + 3 ^ 40 * 1636140 * 2
def baseEnd_1636140 : Nat := 280042079349111276141845

theorem tailTrace_1636140 : CollatzResearch.WordTrace tailWord_1636140 prefixEnd_1636140 280042079349111276141845 := by
  unfold tailWord_1636140
  simp only [CollatzResearch.WordTrace]
  refine ⟨29837464146275842655256937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39783285528367790207009249 29837464146275842655256937)
  ·
    refine ⟨22378098109706881991442703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29837464146275842655256937 22378098109706881991442703)
    ·
      refine ⟨33567147164560322987164055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22378098109706881991442703 33567147164560322987164055)
      ·
        refine ⟨50350720746840484480746083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33567147164560322987164055 50350720746840484480746083)
        ·
          refine ⟨75526081120260726721119125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50350720746840484480746083 75526081120260726721119125)
          ·
            refine ⟨3540285052512221565052459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 75526081120260726721119125 3540285052512221565052459)
            ·
              refine ⟨5310427578768332347578689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3540285052512221565052459 5310427578768332347578689)
              ·
                refine ⟨3982820684076249260684017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5310427578768332347578689 3982820684076249260684017)
                ·
                  refine ⟨2987115513057186945513013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3982820684076249260684017 2987115513057186945513013)
                  ·
                    refine ⟨280042079349111276141845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2987115513057186945513013 280042079349111276141845)
                    ·
                      rfl

theorem cell23_1636140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 5].length) (baseStart_1636140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1636140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1636140 prefixEnd_1636140 := by exact prefixLift 1636140
  have htrace : WordTrace (prefixWord ++ tailWord_1636140) baseStart_1636140 baseEnd_1636140 := by
    simpa [prefixWord, tailWord_1636140, baseEnd_1636140] using wordTrace_append hprefix tailTrace_1636140
  have hstable : (prefixWord ++ tailWord_1636140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1636140).length < 2 ^ (prefixWord ++ tailWord_1636140).sum := by decide
  have hdescent : baseEnd_1636140 < baseStart_1636140 := by decide
  rcases family_descends (prefixWord ++ tailWord_1636140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1636170 : List Nat := [3, 1, 2, 1, 1, 1, 4, 1, 5, 4]
def baseStart_1636170 : Nat := 118140960795 + 1636170 * 2 ^ 59
def prefixEnd_1636170 : Nat := 4983230072969 + 3 ^ 40 * 1636170 * 2
def baseEnd_1636170 : Nat := 280047214155656237016799

theorem tailTrace_1636170 : CollatzResearch.WordTrace tailWord_1636170 prefixEnd_1636170 280047214155656237016799 := by
  unfold tailWord_1636170
  simp only [CollatzResearch.WordTrace]
  refine ⟨14919005620610750108526491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39784014988295333622737309 14919005620610750108526491)
  ·
    refine ⟨22378508430916125162789737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14919005620610750108526491 22378508430916125162789737)
    ·
      refine ⟨16783881323187093872092303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22378508430916125162789737 16783881323187093872092303)
      ·
        refine ⟨25175821984780640808138455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16783881323187093872092303 25175821984780640808138455)
        ·
          refine ⟨37763732977170961212207683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25175821984780640808138455 37763732977170961212207683)
          ·
            refine ⟨56645599465756441818311525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37763732977170961212207683 56645599465756441818311525)
            ·
              refine ⟨10621049899829332840933411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 56645599465756441818311525 10621049899829332840933411)
              ·
                refine ⟨15931574849743999261400117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10621049899829332840933411 15931574849743999261400117)
                ·
                  refine ⟨1493585142163499930756261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 15931574849743999261400117 1493585142163499930756261)
                  ·
                    refine ⟨280047214155656237016799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1493585142163499930756261 280047214155656237016799)
                    ·
                      rfl

theorem cell23_1636170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 1, 5, 4].length) (baseStart_1636170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1636170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1636170 prefixEnd_1636170 := by exact prefixLift 1636170
  have htrace : WordTrace (prefixWord ++ tailWord_1636170) baseStart_1636170 baseEnd_1636170 := by
    simpa [prefixWord, tailWord_1636170, baseEnd_1636170] using wordTrace_append hprefix tailTrace_1636170
  have hstable : (prefixWord ++ tailWord_1636170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1636170).length < 2 ^ (prefixWord ++ tailWord_1636170).sum := by decide
  have hdescent : baseEnd_1636170 < baseStart_1636170 := by decide
  rcases family_descends (prefixWord ++ tailWord_1636170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1636177 : List Nat := [1, 2, 2, 1, 5, 2, 2, 1, 2, 1, 4]
def baseStart_1636177 : Nat := 118140960795 + 1636177 * 2 ^ 59
def prefixEnd_1636177 : Nat := 4983230072969 + 3 ^ 40 * 1636177 * 2
def baseEnd_1636177 : Nat := 840145236831550183662865

theorem tailTrace_1636177 : CollatzResearch.WordTrace tailWord_1636177 prefixEnd_1636177 840145236831550183662865 := by
  unfold tailWord_1636177
  simp only [CollatzResearch.WordTrace]
  refine ⟨59676277793417640629610785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39784185195611760419740523 59676277793417640629610785)
  ·
    refine ⟨44757208345063230472208089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59676277793417640629610785 44757208345063230472208089)
    ·
      refine ⟨33567906258797422854156067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44757208345063230472208089 33567906258797422854156067)
      ·
        refine ⟨50351859388196134281234101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33567906258797422854156067 50351859388196134281234101)
        ·
          refine ⟨4720486817643387588865697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 50351859388196134281234101 4720486817643387588865697)
          ·
            refine ⟨3540365113232540691649273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4720486817643387588865697 3540365113232540691649273)
            ·
              refine ⟨2655273834924405518736955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3540365113232540691649273 2655273834924405518736955)
              ·
                refine ⟨3982910752386608278105433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2655273834924405518736955 3982910752386608278105433)
                ·
                  refine ⟨2987183064289956208579075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3982910752386608278105433 2987183064289956208579075)
                  ·
                    refine ⟨4480774596434934312868613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2987183064289956208579075 4480774596434934312868613)
                    ·
                      refine ⟨840145236831550183662865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4480774596434934312868613 840145236831550183662865)
                      ·
                        rfl

theorem cell23_1636177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 2, 1, 2, 1, 4].length) (baseStart_1636177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1636177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1636177 prefixEnd_1636177 := by exact prefixLift 1636177
  have htrace : WordTrace (prefixWord ++ tailWord_1636177) baseStart_1636177 baseEnd_1636177 := by
    simpa [prefixWord, tailWord_1636177, baseEnd_1636177] using wordTrace_append hprefix tailTrace_1636177
  have hstable : (prefixWord ++ tailWord_1636177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1636177).length < 2 ^ (prefixWord ++ tailWord_1636177).sum := by decide
  have hdescent : baseEnd_1636177 < baseStart_1636177 := by decide
  rcases family_descends (prefixWord ++ tailWord_1636177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1636203 : List Nat := [1, 1, 1, 1, 2, 2, 3, 3, 1, 2, 6]
def baseStart_1636203 : Nat := 118140960795 + 1636203 * 2 ^ 59
def prefixEnd_1636203 : Nat := 4983230072969 + 3 ^ 40 * 1636203 * 2
def baseEnd_1636203 : Nat := 840158587328567081937745

theorem tailTrace_1636203 : CollatzResearch.WordTrace tailWord_1636203 prefixEnd_1636203 840158587328567081937745 := by
  unfold tailWord_1636203
  simp only [CollatzResearch.WordTrace]
  refine ⟨59677226091323447070057263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39784817394215631380038175 59677226091323447070057263)
  ·
    refine ⟨89515839136985170605085895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59677226091323447070057263 89515839136985170605085895)
    ·
      refine ⟨134273758705477755907628843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89515839136985170605085895 134273758705477755907628843)
      ·
        refine ⟨201410638058216633861443265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134273758705477755907628843 201410638058216633861443265)
        ·
          refine ⟨151057978543662475396082449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 201410638058216633861443265 151057978543662475396082449)
          ·
            refine ⟨113293483907746856547061837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 151057978543662475396082449 113293483907746856547061837)
            ·
              refine ⟨42485056465405071205148189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 113293483907746856547061837 42485056465405071205148189)
              ·
                refine ⟨15931896174526901701930571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42485056465405071205148189 15931896174526901701930571)
                ·
                  refine ⟨23897844261790352552895857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15931896174526901701930571 23897844261790352552895857)
                  ·
                    refine ⟨17923383196342764414671893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23897844261790352552895857 17923383196342764414671893)
                    ·
                      refine ⟨840158587328567081937745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 17923383196342764414671893 840158587328567081937745)
                      ·
                        rfl

theorem cell23_1636203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 3, 1, 2, 6].length) (baseStart_1636203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1636203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1636203 prefixEnd_1636203 := by exact prefixLift 1636203
  have htrace : WordTrace (prefixWord ++ tailWord_1636203) baseStart_1636203 baseEnd_1636203 := by
    simpa [prefixWord, tailWord_1636203, baseEnd_1636203] using wordTrace_append hprefix tailTrace_1636203
  have hstable : (prefixWord ++ tailWord_1636203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1636203).length < 2 ^ (prefixWord ++ tailWord_1636203).sum := by decide
  have hdescent : baseEnd_1636203 < baseStart_1636203 := by decide
  rcases family_descends (prefixWord ++ tailWord_1636203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1636204 : List Nat := [2, 2, 1, 1, 4, 3, 1, 4, 1, 4]
def baseStart_1636204 : Nat := 118140960795 + 1636204 * 2 ^ 59
def prefixEnd_1636204 : Nat := 4983230072969 + 3 ^ 40 * 1636204 * 2
def baseEnd_1636204 : Nat := 280053033603073859341747

theorem tailTrace_1636204 : CollatzResearch.WordTrace tailWord_1636204 prefixEnd_1636204 280053033603073859341747 := by
  unfold tailWord_1636204
  simp only [CollatzResearch.WordTrace]
  refine ⟨29838631282159912120421833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39784841709546549493895777 29838631282159912120421833)
  ·
    refine ⟨22378973461619934090316375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29838631282159912120421833 22378973461619934090316375)
    ·
      refine ⟨33568460192429901135474563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22378973461619934090316375 33568460192429901135474563)
      ·
        refine ⟨50352690288644851703211845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33568460192429901135474563 50352690288644851703211845)
        ·
          refine ⟨9441129429120909694352221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50352690288644851703211845 9441129429120909694352221)
          ·
            refine ⟨3540423535920341135382083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9441129429120909694352221 3540423535920341135382083)
            ·
              refine ⟨5310635303880511703073125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3540423535920341135382083 5310635303880511703073125)
              ·
                refine ⟨995744119477595944326211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5310635303880511703073125 995744119477595944326211)
                ·
                  refine ⟨1493616179216393916489317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 995744119477595944326211 1493616179216393916489317)
                  ·
                    refine ⟨280053033603073859341747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1493616179216393916489317 280053033603073859341747)
                    ·
                      rfl

theorem cell23_1636204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 1, 4, 1, 4].length) (baseStart_1636204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1636204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1636204 prefixEnd_1636204 := by exact prefixLift 1636204
  have htrace : WordTrace (prefixWord ++ tailWord_1636204) baseStart_1636204 baseEnd_1636204 := by
    simpa [prefixWord, tailWord_1636204, baseEnd_1636204] using wordTrace_append hprefix tailTrace_1636204
  have hstable : (prefixWord ++ tailWord_1636204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1636204).length < 2 ^ (prefixWord ++ tailWord_1636204).sum := by decide
  have hdescent : baseEnd_1636204 < baseStart_1636204 := by decide
  rcases family_descends (prefixWord ++ tailWord_1636204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1636210 : List Nat := [3, 2, 1, 2, 1, 1, 1, 2, 2, 5, 3]
def baseStart_1636210 : Nat := 118140960795 + 1636210 * 2 ^ 59
def prefixEnd_1636210 : Nat := 4983230072969 + 3 ^ 40 * 1636210 * 2
def baseEnd_1636210 : Nat := 840162181693148554550213

theorem tailTrace_1636210 : CollatzResearch.WordTrace tailWord_1636210 prefixEnd_1636210 840162181693148554550213 := by
  unfold tailWord_1636210
  simp only [CollatzResearch.WordTrace]
  refine ⟨14919370350574521816390521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39784987601532058177041389 14919370350574521816390521)
  ·
    refine ⟨11189527762930891362292891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14919370350574521816390521 11189527762930891362292891)
    ·
      refine ⟨16784291644396337043439337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11189527762930891362292891 16784291644396337043439337)
      ·
        refine ⟨12588218733297252782579503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16784291644396337043439337 12588218733297252782579503)
        ·
          refine ⟨18882328099945879173869255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12588218733297252782579503 18882328099945879173869255)
          ·
            refine ⟨28323492149918818760803883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18882328099945879173869255 28323492149918818760803883)
            ·
              refine ⟨42485238224878228141205825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28323492149918818760803883 42485238224878228141205825)
              ·
                refine ⟨31863928668658671105904369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42485238224878228141205825 31863928668658671105904369)
                ·
                  refine ⟨23897946501494003329428277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31863928668658671105904369 23897946501494003329428277)
                  ·
                    refine ⟨2240432484515062812133901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 23897946501494003329428277 2240432484515062812133901)
                    ·
                      refine ⟨840162181693148554550213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2240432484515062812133901 840162181693148554550213)
                      ·
                        rfl

theorem cell23_1636210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 2, 2, 5, 3].length) (baseStart_1636210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1636210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1636210 prefixEnd_1636210 := by exact prefixLift 1636210
  have htrace : WordTrace (prefixWord ++ tailWord_1636210) baseStart_1636210 baseEnd_1636210 := by
    simpa [prefixWord, tailWord_1636210, baseEnd_1636210] using wordTrace_append hprefix tailTrace_1636210
  have hstable : (prefixWord ++ tailWord_1636210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1636210).length < 2 ^ (prefixWord ++ tailWord_1636210).sum := by decide
  have hdescent : baseEnd_1636210 < baseStart_1636210 := by decide
  rcases family_descends (prefixWord ++ tailWord_1636210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1636223 : List Nat := [1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 7]
def baseStart_1636223 : Nat := 118140960795 + 1636223 * 2 ^ 59
def prefixEnd_1636223 : Nat := 4983230072969 + 3 ^ 40 * 1636223 * 2
def baseEnd_1636223 : Nat := 840168856941657003687653

theorem tailTrace_1636223 : CollatzResearch.WordTrace tailWord_1636223 prefixEnd_1636223 840168856941657003687653 := by
  unfold tailWord_1636223
  simp only [CollatzResearch.WordTrace]
  refine ⟨59677955551250990485785323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39785303700833993657190215 59677955551250990485785323)
  ·
    refine ⟨89516933326876485728677985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59677955551250990485785323 89516933326876485728677985)
    ·
      refine ⟨67137699995157364296508489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89516933326876485728677985 67137699995157364296508489)
      ·
        refine ⟨50353274996368023222381367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67137699995157364296508489 50353274996368023222381367)
        ·
          refine ⟨75529912494552034833572051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50353274996368023222381367 75529912494552034833572051)
          ·
            refine ⟨113294868741828052250358077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75529912494552034833572051 113294868741828052250358077)
            ·
              refine ⟨42485575778185519593884279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 113294868741828052250358077 42485575778185519593884279)
              ·
                refine ⟨63728363667278279390826419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42485575778185519593884279 63728363667278279390826419)
                ·
                  refine ⟨95592545500917419086239629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63728363667278279390826419 95592545500917419086239629)
                  ·
                    refine ⟨35847204562844032157339861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 95592545500917419086239629 35847204562844032157339861)
                    ·
                      refine ⟨840168856941657003687653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 35847204562844032157339861 840168856941657003687653)
                      ·
                        rfl

theorem cell23_1636223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 7].length) (baseStart_1636223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1636223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1636223 prefixEnd_1636223 := by exact prefixLift 1636223
  have htrace : WordTrace (prefixWord ++ tailWord_1636223) baseStart_1636223 baseEnd_1636223 := by
    simpa [prefixWord, tailWord_1636223, baseEnd_1636223] using wordTrace_append hprefix tailTrace_1636223
  have hstable : (prefixWord ++ tailWord_1636223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1636223).length < 2 ^ (prefixWord ++ tailWord_1636223).sum := by decide
  have hdescent : baseEnd_1636223 < baseStart_1636223 := by decide
  rcases family_descends (prefixWord ++ tailWord_1636223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1636227 : List Nat := [1, 1, 1, 3, 4, 2, 1, 1, 5, 1, 3]
def baseStart_1636227 : Nat := 118140960795 + 1636227 * 2 ^ 59
def prefixEnd_1636227 : Nat := 4983230072969 + 3 ^ 40 * 1636227 * 2
def baseEnd_1636227 : Nat := 840170910864274988037635

theorem tailTrace_1636227 : CollatzResearch.WordTrace tailWord_1636227 prefixEnd_1636227 840170910864274988037635 := by
  unfold tailWord_1636227
  simp only [CollatzResearch.WordTrace]
  refine ⟨59678101443236499168930935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39785400962157666112620623 59678101443236499168930935)
  ·
    refine ⟨89517152164854748753396403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59678101443236499168930935 89517152164854748753396403)
    ·
      refine ⟨134275728247282123130094605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89517152164854748753396403 134275728247282123130094605)
      ·
        refine ⟨50353398092730796173785477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 134275728247282123130094605 50353398092730796173785477)
        ·
          refine ⟨9441262142387024282584777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50353398092730796173785477 9441262142387024282584777)
          ·
            refine ⟨7080946606790268211938583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9441262142387024282584777 7080946606790268211938583)
            ·
              refine ⟨10621419910185402317907875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7080946606790268211938583 10621419910185402317907875)
              ·
                refine ⟨15932129865278103476861813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10621419910185402317907875 15932129865278103476861813)
                ·
                  refine ⟨1493637174869822200955795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 15932129865278103476861813 1493637174869822200955795)
                  ·
                    refine ⟨2240455762304733301433693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1493637174869822200955795 2240455762304733301433693)
                    ·
                      refine ⟨840170910864274988037635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2240455762304733301433693 840170910864274988037635)
                      ·
                        rfl

theorem cell23_1636227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 1, 5, 1, 3].length) (baseStart_1636227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1636227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1636227 prefixEnd_1636227 := by exact prefixLift 1636227
  have htrace : WordTrace (prefixWord ++ tailWord_1636227) baseStart_1636227 baseEnd_1636227 := by
    simpa [prefixWord, tailWord_1636227, baseEnd_1636227] using wordTrace_append hprefix tailTrace_1636227
  have hstable : (prefixWord ++ tailWord_1636227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1636227).length < 2 ^ (prefixWord ++ tailWord_1636227).sum := by decide
  have hdescent : baseEnd_1636227 < baseStart_1636227 := by decide
  rcases family_descends (prefixWord ++ tailWord_1636227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1636231 : List Nat := [1, 1, 4, 2, 5, 1, 1, 1, 2, 2, 3]
def baseStart_1636231 : Nat := 118140960795 + 1636231 * 2 ^ 59
def prefixEnd_1636231 : Nat := 4983230072969 + 3 ^ 40 * 1636231 * 2
def baseEnd_1636231 : Nat := 840172964786892972387617

theorem tailTrace_1636231 : CollatzResearch.WordTrace tailWord_1636231 prefixEnd_1636231 840172964786892972387617 := by
  unfold tailWord_1636231
  simp only [CollatzResearch.WordTrace]
  refine ⟨59678247335222007852076547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39785498223481338568051031 59678247335222007852076547)
  ·
    refine ⟨89517371002833011778114821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59678247335222007852076547 89517371002833011778114821)
    ·
      refine ⟨16784507063031189708396529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 89517371002833011778114821 16784507063031189708396529)
      ·
        refine ⟨12588380297273392281297397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16784507063031189708396529 12588380297273392281297397)
        ·
          refine ⟨1180160652869380526371631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 12588380297273392281297397 1180160652869380526371631)
          ·
            refine ⟨1770240979304070789557447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1180160652869380526371631 1770240979304070789557447)
            ·
              refine ⟨2655361468956106184336171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1770240979304070789557447 2655361468956106184336171)
              ·
                refine ⟨3983042203434159276504257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2655361468956106184336171 3983042203434159276504257)
                ·
                  refine ⟨2987281652575619457378193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3983042203434159276504257 2987281652575619457378193)
                  ·
                    refine ⟨2240461239431714593033645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2987281652575619457378193 2240461239431714593033645)
                    ·
                      refine ⟨840172964786892972387617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2240461239431714593033645 840172964786892972387617)
                      ·
                        rfl

theorem cell23_1636231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 5, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 5, 1, 1, 1, 2, 2, 3].length) (baseStart_1636231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1636231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1636231 prefixEnd_1636231 := by exact prefixLift 1636231
  have htrace : WordTrace (prefixWord ++ tailWord_1636231) baseStart_1636231 baseEnd_1636231 := by
    simpa [prefixWord, tailWord_1636231, baseEnd_1636231] using wordTrace_append hprefix tailTrace_1636231
  have hstable : (prefixWord ++ tailWord_1636231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1636231).length < 2 ^ (prefixWord ++ tailWord_1636231).sum := by decide
  have hdescent : baseEnd_1636231 < baseStart_1636231 := by decide
  rcases family_descends (prefixWord ++ tailWord_1636231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1636238 : List Nat := [4, 1, 1, 5, 1, 1, 2, 3, 1, 4]
def baseStart_1636238 : Nat := 118140960795 + 1636238 * 2 ^ 59
def prefixEnd_1636238 : Nat := 4983230072969 + 3 ^ 40 * 1636238 * 2
def baseEnd_1636238 : Nat := 280058853050491481666695

theorem tailTrace_1636238 : CollatzResearch.WordTrace tailWord_1636238 prefixEnd_1636238 280058853050491481666695 := by
  unfold tailWord_1636238
  simp only [CollatzResearch.WordTrace]
  refine ⟨7459812830774581005947671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39785668430797765365054245 7459812830774581005947671)
  ·
    refine ⟨11189719246161871508921507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7459812830774581005947671 11189719246161871508921507)
    ·
      refine ⟨16784578869242807263382261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11189719246161871508921507 16784578869242807263382261)
      ·
        refine ⟨1573554268991513180942087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 16784578869242807263382261 1573554268991513180942087)
        ·
          refine ⟨2360331403487269771413131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1573554268991513180942087 2360331403487269771413131)
          ·
            refine ⟨3540497105230904657119697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2360331403487269771413131 3540497105230904657119697)
            ·
              refine ⟨2655372828923178492839773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3540497105230904657119697 2655372828923178492839773)
              ·
                refine ⟨995764810846191934814915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2655372828923178492839773 995764810846191934814915)
                ·
                  refine ⟨1493647216269287902222373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 995764810846191934814915 1493647216269287902222373)
                  ·
                    refine ⟨280058853050491481666695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1493647216269287902222373 280058853050491481666695)
                    ·
                      rfl

theorem cell23_1636238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 2, 3, 1, 4].length) (baseStart_1636238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1636238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1636238 prefixEnd_1636238 := by exact prefixLift 1636238
  have htrace : WordTrace (prefixWord ++ tailWord_1636238) baseStart_1636238 baseEnd_1636238 := by
    simpa [prefixWord, tailWord_1636238, baseEnd_1636238] using wordTrace_append hprefix tailTrace_1636238
  have hstable : (prefixWord ++ tailWord_1636238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1636238).length < 2 ^ (prefixWord ++ tailWord_1636238).sum := by decide
  have hdescent : baseEnd_1636238 < baseStart_1636238 := by decide
  rcases family_descends (prefixWord ++ tailWord_1636238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1636243 : List Nat := [1, 1, 1, 2, 1, 2, 1, 2, 2, 10]
def baseStart_1636243 : Nat := 118140960795 + 1636243 * 2 ^ 59
def prefixEnd_1636243 : Nat := 4983230072969 + 3 ^ 40 * 1636243 * 2
def baseEnd_1636243 : Nat := 280059708851582308479187

theorem tailTrace_1636243 : CollatzResearch.WordTrace tailWord_1636243 prefixEnd_1636243 280059708851582308479187 := by
  unfold tailWord_1636243
  simp only [CollatzResearch.WordTrace]
  refine ⟨59678685011178533901513383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39785790007452355934342255 59678685011178533901513383)
  ·
    refine ⟨89518027516767800852270075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59678685011178533901513383 89518027516767800852270075)
    ·
      refine ⟨134277041275151701278405113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89518027516767800852270075 134277041275151701278405113)
      ·
        refine ⟨100707780956363775958803835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134277041275151701278405113 100707780956363775958803835)
        ·
          refine ⟨151061671434545663938205753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100707780956363775958803835 151061671434545663938205753)
          ·
            refine ⟨113296253575909247953654315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 151061671434545663938205753 113296253575909247953654315)
            ·
              refine ⟨169944380363863871930481473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113296253575909247953654315 169944380363863871930481473)
              ·
                refine ⟨127458285272897903947861105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 169944380363863871930481473 127458285272897903947861105)
                ·
                  refine ⟨95593713954673427960895829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 127458285272897903947861105 95593713954673427960895829)
                  ·
                    refine ⟨280059708851582308479187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 95593713954673427960895829 280059708851582308479187)
                    ·
                      rfl

theorem cell23_1636243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 2, 2, 10].length) (baseStart_1636243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1636243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1636243 prefixEnd_1636243 := by exact prefixLift 1636243
  have htrace : WordTrace (prefixWord ++ tailWord_1636243) baseStart_1636243 baseEnd_1636243 := by
    simpa [prefixWord, tailWord_1636243, baseEnd_1636243] using wordTrace_append hprefix tailTrace_1636243
  have hstable : (prefixWord ++ tailWord_1636243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1636243).length < 2 ^ (prefixWord ++ tailWord_1636243).sum := by decide
  have hdescent : baseEnd_1636243 < baseStart_1636243 := by decide
  rcases family_descends (prefixWord ++ tailWord_1636243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1636247 : List Nat := [1, 1, 3, 3, 1, 4, 1, 3, 1, 5]
def baseStart_1636247 : Nat := 118140960795 + 1636247 * 2 ^ 59
def prefixEnd_1636247 : Nat := 4983230072969 + 3 ^ 40 * 1636247 * 2
def baseEnd_1636247 : Nat := 280060393492454969929181

theorem tailTrace_1636247 : CollatzResearch.WordTrace tailWord_1636247 prefixEnd_1636247 280060393492454969929181 := by
  unfold tailWord_1636247
  simp only [CollatzResearch.WordTrace]
  refine ⟨59678830903164042584658995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39785887268776028389772663 59678830903164042584658995)
  ·
    refine ⟨89518246354746063876988493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59678830903164042584658995 89518246354746063876988493)
    ·
      refine ⟨33569342383029773953870685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89518246354746063876988493 33569342383029773953870685)
      ·
        refine ⟨12588503393636165232701507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33569342383029773953870685 12588503393636165232701507)
        ·
          refine ⟨18882755090454247849052261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12588503393636165232701507 18882755090454247849052261)
          ·
            refine ⟨3540516579460171471697299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18882755090454247849052261 3540516579460171471697299)
            ·
              refine ⟨5310774869190257207545949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3540516579460171471697299 5310774869190257207545949)
              ·
                refine ⟨1991540575946346452829731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5310774869190257207545949 1991540575946346452829731)
                ·
                  refine ⟨2987310863919519679244597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1991540575946346452829731 2987310863919519679244597)
                  ·
                    refine ⟨280060393492454969929181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2987310863919519679244597 280060393492454969929181)
                    ·
                      rfl

theorem cell23_1636247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 1, 3, 1, 5].length) (baseStart_1636247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1636247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1636247 prefixEnd_1636247 := by exact prefixLift 1636247
  have htrace : WordTrace (prefixWord ++ tailWord_1636247) baseStart_1636247 baseEnd_1636247 := by
    simpa [prefixWord, tailWord_1636247, baseEnd_1636247] using wordTrace_append hprefix tailTrace_1636247
  have hstable : (prefixWord ++ tailWord_1636247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1636247).length < 2 ^ (prefixWord ++ tailWord_1636247).sum := by decide
  have hdescent : baseEnd_1636247 < baseStart_1636247 := by decide
  rcases family_descends (prefixWord ++ tailWord_1636247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1636277 : List Nat := [1, 3, 3, 2, 1, 2, 3, 1, 1, 6]
def baseStart_1636277 : Nat := 118140960795 + 1636277 * 2 ^ 59
def prefixEnd_1636277 : Nat := 4983230072969 + 3 ^ 40 * 1636277 * 2
def baseEnd_1636277 : Nat := 280065528298999930804135

theorem tailTrace_1636277 : CollatzResearch.WordTrace tailWord_1636277 prefixEnd_1636277 280065528298999930804135 := by
  unfold tailWord_1636277
  simp only [CollatzResearch.WordTrace]
  refine ⟨59679925093055357708251085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39786616728703571805500723 59679925093055357708251085)
  ·
    refine ⟨22379971909895759140594157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59679925093055357708251085 22379971909895759140594157)
    ·
      refine ⟨8392489466210909677722809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22379971909895759140594157 8392489466210909677722809)
      ·
        refine ⟨6294367099658182258292107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8392489466210909677722809 6294367099658182258292107)
        ·
          refine ⟨9441550649487273387438161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6294367099658182258292107 9441550649487273387438161)
          ·
            refine ⟨7081162987115455040578621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9441550649487273387438161 7081162987115455040578621)
            ·
              refine ⟨2655436120168295640216983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7081162987115455040578621 2655436120168295640216983)
              ·
                refine ⟨3983154180252443460325475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2655436120168295640216983 3983154180252443460325475)
                ·
                  refine ⟨5974731270378665190488213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3983154180252443460325475 5974731270378665190488213)
                  ·
                    refine ⟨280065528298999930804135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5974731270378665190488213 280065528298999930804135)
                    ·
                      rfl

theorem cell23_1636277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 3, 1, 1, 6].length) (baseStart_1636277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1636277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1636277 prefixEnd_1636277 := by exact prefixLift 1636277
  have htrace : WordTrace (prefixWord ++ tailWord_1636277) baseStart_1636277 baseEnd_1636277 := by
    simpa [prefixWord, tailWord_1636277, baseEnd_1636277] using wordTrace_append hprefix tailTrace_1636277
  have hstable : (prefixWord ++ tailWord_1636277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1636277).length < 2 ^ (prefixWord ++ tailWord_1636277).sum := by decide
  have hdescent : baseEnd_1636277 < baseStart_1636277 := by decide
  rcases family_descends (prefixWord ++ tailWord_1636277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1636280 : List Nat := [2, 1, 2, 1, 2, 3, 3, 1, 1, 1, 6]
def baseStart_1636280 : Nat := 118140960795 + 1636280 * 2 ^ 59
def prefixEnd_1636280 : Nat := 4983230072969 + 3 ^ 40 * 1636280 * 2
def baseEnd_1636280 : Nat := 840198125338963280674891

theorem tailTrace_1636280 : CollatzResearch.WordTrace tailWord_1636280 prefixEnd_1636280 840198125338963280674891 := by
  unfold tailWord_1636280
  simp only [CollatzResearch.WordTrace]
  refine ⟨29840017256022244610305147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39786689674696326147073529 29840017256022244610305147)
  ·
    refine ⟨44760025884033366915457721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29840017256022244610305147 44760025884033366915457721)
    ·
      refine ⟨33570019413025025186593291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44760025884033366915457721 33570019413025025186593291)
      ·
        refine ⟨50355029119537537779889937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33570019413025025186593291 50355029119537537779889937)
        ·
          refine ⟨37766271839653153334917453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50355029119537537779889937 37766271839653153334917453)
          ·
            refine ⟨14162351939869932500594045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37766271839653153334917453 14162351939869932500594045)
            ·
              refine ⟨5310881977451224687722767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14162351939869932500594045 5310881977451224687722767)
              ·
                refine ⟨7966322966176837031584151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5310881977451224687722767 7966322966176837031584151)
                ·
                  refine ⟨11949484449265255547376227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7966322966176837031584151 11949484449265255547376227)
                  ·
                    refine ⟨17924226673897883321064341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11949484449265255547376227 17924226673897883321064341)
                    ·
                      refine ⟨840198125338963280674891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 17924226673897883321064341 840198125338963280674891)
                      ·
                        rfl

theorem cell23_1636280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 3, 1, 1, 1, 6].length) (baseStart_1636280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1636280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1636280 prefixEnd_1636280 := by exact prefixLift 1636280
  have htrace : WordTrace (prefixWord ++ tailWord_1636280) baseStart_1636280 baseEnd_1636280 := by
    simpa [prefixWord, tailWord_1636280, baseEnd_1636280] using wordTrace_append hprefix tailTrace_1636280
  have hstable : (prefixWord ++ tailWord_1636280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1636280).length < 2 ^ (prefixWord ++ tailWord_1636280).sum := by decide
  have hdescent : baseEnd_1636280 < baseStart_1636280 := by decide
  rcases family_descends (prefixWord ++ tailWord_1636280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1636358 : List Nat := [6, 2, 1, 2, 2, 10]
def baseStart_1636358 : Nat := 118140960795 + 1636358 * 2 ^ 59
def prefixEnd_1636358 : Nat := 4983230072969 + 3 ^ 40 * 1636358 * 2
def baseEnd_1636358 : Nat := 3457770275020633644031

theorem tailTrace_1636358 : CollatzResearch.WordTrace tailWord_1636358 prefixEnd_1636358 3457770275020633644031 := by
  unfold tailWord_1636358
  simp only [CollatzResearch.WordTrace]
  refine ⟨1865089981430059641935929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 39788586270507939027966485 1865089981430059641935929)
  ·
    refine ⟨1398817486072544731451947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1865089981430059641935929 1398817486072544731451947)
    ·
      refine ⟨2098226229108817097177921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1398817486072544731451947 2098226229108817097177921)
      ·
        refine ⟨1573669671831612822883441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2098226229108817097177921 1573669671831612822883441)
        ·
          refine ⟨1180252253873709617162581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1573669671831612822883441 1180252253873709617162581)
          ·
            refine ⟨3457770275020633644031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 1180252253873709617162581 3457770275020633644031)
            ·
              rfl

theorem cell23_1636358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 2, 10].length) (baseStart_1636358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1636358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1636358 prefixEnd_1636358 := by exact prefixLift 1636358
  have htrace : WordTrace (prefixWord ++ tailWord_1636358) baseStart_1636358 baseEnd_1636358 := by
    simpa [prefixWord, tailWord_1636358, baseEnd_1636358] using wordTrace_append hprefix tailTrace_1636358
  have hstable : (prefixWord ++ tailWord_1636358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1636358).length < 2 ^ (prefixWord ++ tailWord_1636358).sum := by decide
  have hdescent : baseEnd_1636358 < baseStart_1636358 := by decide
  rcases family_descends (prefixWord ++ tailWord_1636358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1636387 : List Nat := [1, 1, 1, 4, 3, 1, 3, 1, 2, 2, 4]
def baseStart_1636387 : Nat := 118140960795 + 1636387 * 2 ^ 59
def prefixEnd_1636387 : Nat := 4983230072969 + 3 ^ 40 * 1636387 * 2
def baseEnd_1636387 : Nat := 840253067768994362036899

theorem tailTrace_1636387 : CollatzResearch.WordTrace tailWord_1636387 prefixEnd_1636387 840253067768994362036899 := by
  unfold tailWord_1636387
  simp only [CollatzResearch.WordTrace]
  refine ⟨59683937122656846494755415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39789291415104564329836943 59683937122656846494755415)
  ·
    refine ⟨89525905683985269742133123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59683937122656846494755415 89525905683985269742133123)
    ·
      refine ⟨134288858525977904613199685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89525905683985269742133123 134288858525977904613199685)
      ·
        refine ⟨25179160973620857114974941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 134288858525977904613199685 25179160973620857114974941)
        ·
          refine ⟨9442185365107821418115603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25179160973620857114974941 9442185365107821418115603)
          ·
            refine ⟨14163278047661732127173405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9442185365107821418115603 14163278047661732127173405)
            ·
              refine ⟨5311229267873149547690027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14163278047661732127173405 5311229267873149547690027)
              ·
                refine ⟨7966843901809724321535041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5311229267873149547690027 7966843901809724321535041)
                ·
                  refine ⟨5975132926357293241151281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7966843901809724321535041 5975132926357293241151281)
                  ·
                    refine ⟨4481349694767969930863461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5975132926357293241151281 4481349694767969930863461)
                    ·
                      refine ⟨840253067768994362036899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4481349694767969930863461 840253067768994362036899)
                      ·
                        rfl

theorem cell23_1636387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 3, 1, 2, 2, 4].length) (baseStart_1636387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1636387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1636387 prefixEnd_1636387 := by exact prefixLift 1636387
  have htrace : WordTrace (prefixWord ++ tailWord_1636387) baseStart_1636387 baseEnd_1636387 := by
    simpa [prefixWord, tailWord_1636387, baseEnd_1636387] using wordTrace_append hprefix tailTrace_1636387
  have hstable : (prefixWord ++ tailWord_1636387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1636387).length < 2 ^ (prefixWord ++ tailWord_1636387).sum := by decide
  have hdescent : baseEnd_1636387 < baseStart_1636387 := by decide
  rcases family_descends (prefixWord ++ tailWord_1636387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1636447 : List Nat := [1, 1, 2, 3, 1, 1, 2, 1, 6, 1, 4]
def baseStart_1636447 : Nat := 118140960795 + 1636447 * 2 ^ 59
def prefixEnd_1636447 : Nat := 4983230072969 + 3 ^ 40 * 1636447 * 2
def baseEnd_1636447 : Nat := 840283876608264127286623

theorem tailTrace_1636447 : CollatzResearch.WordTrace tailWord_1636447 prefixEnd_1636447 840283876608264127286623 := by
  unfold tailWord_1636447
  simp only [CollatzResearch.WordTrace]
  refine ⟨59686125502439476741939595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39790750334959651161293063 59686125502439476741939595)
  ·
    refine ⟨89529188253659215112909393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59686125502439476741939595 89529188253659215112909393)
    ·
      refine ⟨67146891190244411334682045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89529188253659215112909393 67146891190244411334682045)
      ·
        refine ⟨25180084196341654250505767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67146891190244411334682045 25180084196341654250505767)
        ·
          refine ⟨37770126294512481375758651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25180084196341654250505767 37770126294512481375758651)
          ·
            refine ⟨56655189441768722063637977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37770126294512481375758651 56655189441768722063637977)
            ·
              refine ⟨42491392081326541547728483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56655189441768722063637977 42491392081326541547728483)
              ·
                refine ⟨63737088121989812321592725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42491392081326541547728483 63737088121989812321592725)
                ·
                  refine ⟨2987676005718272452574659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 63737088121989812321592725 2987676005718272452574659)
                  ·
                    refine ⟨4481514008577408678861989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2987676005718272452574659 4481514008577408678861989)
                    ·
                      refine ⟨840283876608264127286623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4481514008577408678861989 840283876608264127286623)
                      ·
                        rfl

theorem cell23_1636447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 1, 6, 1, 4].length) (baseStart_1636447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1636447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1636447 prefixEnd_1636447 := by exact prefixLift 1636447
  have htrace : WordTrace (prefixWord ++ tailWord_1636447) baseStart_1636447 baseEnd_1636447 := by
    simpa [prefixWord, tailWord_1636447, baseEnd_1636447] using wordTrace_append hprefix tailTrace_1636447
  have hstable : (prefixWord ++ tailWord_1636447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1636447).length < 2 ^ (prefixWord ++ tailWord_1636447).sum := by decide
  have hdescent : baseEnd_1636447 < baseStart_1636447 := by decide
  rcases family_descends (prefixWord ++ tailWord_1636447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1636481 : List Nat := [1, 2, 4, 2, 3, 1, 1, 2, 2, 1, 4]
def baseStart_1636481 : Nat := 118140960795 + 1636481 * 2 ^ 59
def prefixEnd_1636481 : Nat := 4983230072969 + 3 ^ 40 * 1636481 * 2
def baseEnd_1636481 : Nat := 840301334950516994261467

theorem tailTrace_1636481 : CollatzResearch.WordTrace tailWord_1636481 prefixEnd_1636481 840301334950516994261467 := by
  unfold tailWord_1636481
  simp only [CollatzResearch.WordTrace]
  refine ⟨59687365584316300548677297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39791577056210867032451531 59687365584316300548677297)
  ·
    refine ⟨44765524188237225411507973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59687365584316300548677297 44765524188237225411507973)
    ·
      refine ⟨8393535785294479764657745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44765524188237225411507973 8393535785294479764657745)
      ·
        refine ⟨6295151838970859823493309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8393535785294479764657745 6295151838970859823493309)
        ·
          refine ⟨2360681939614072433809991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6295151838970859823493309 2360681939614072433809991)
          ·
            refine ⟨3541022909421108650714987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2360681939614072433809991 3541022909421108650714987)
            ·
              refine ⟨5311534364131662976072481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3541022909421108650714987 5311534364131662976072481)
              ·
                refine ⟨3983650773098747232054361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5311534364131662976072481 3983650773098747232054361)
                ·
                  refine ⟨2987738079824060424040771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3983650773098747232054361 2987738079824060424040771)
                  ·
                    refine ⟨4481607119736090636061157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2987738079824060424040771 4481607119736090636061157)
                    ·
                      refine ⟨840301334950516994261467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4481607119736090636061157 840301334950516994261467)
                      ·
                        rfl

theorem cell23_1636481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 1, 2, 2, 1, 4].length) (baseStart_1636481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1636481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1636481 prefixEnd_1636481 := by exact prefixLift 1636481
  have htrace : WordTrace (prefixWord ++ tailWord_1636481) baseStart_1636481 baseEnd_1636481 := by
    simpa [prefixWord, tailWord_1636481, baseEnd_1636481] using wordTrace_append hprefix tailTrace_1636481
  have hstable : (prefixWord ++ tailWord_1636481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1636481).length < 2 ^ (prefixWord ++ tailWord_1636481).sum := by decide
  have hdescent : baseEnd_1636481 < baseStart_1636481 := by decide
  rcases family_descends (prefixWord ++ tailWord_1636481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1636487 : List Nat := [1, 1, 4, 2, 1, 1, 4, 1, 8]
def baseStart_1636487 : Nat := 118140960795 + 1636487 * 2 ^ 59
def prefixEnd_1636487 : Nat := 4983230072969 + 3 ^ 40 * 1636487 * 2
def baseEnd_1636487 : Nat := 93367157314938218976271

theorem tailTrace_1636487 : CollatzResearch.WordTrace tailWord_1636487 prefixEnd_1636487 93367157314938218976271 := by
  unfold tailWord_1636487
  simp only [CollatzResearch.WordTrace]
  refine ⟨59687584422294563573395715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39791722948196375715597143 59687584422294563573395715)
  ·
    refine ⟨89531376633441845360093573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59687584422294563573395715 89531376633441845360093573)
    ·
      refine ⟨16787133118770346005017545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 89531376633441845360093573 16787133118770346005017545)
      ·
        refine ⟨12590349839077759503763159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16787133118770346005017545 12590349839077759503763159)
        ·
          refine ⟨18885524758616639255644739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12590349839077759503763159 18885524758616639255644739)
          ·
            refine ⟨28328287137924958883467109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18885524758616639255644739 28328287137924958883467109)
            ·
              refine ⟨5311553838360929790650083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28328287137924958883467109 5311553838360929790650083)
              ·
                refine ⟨7967330757541394685975125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5311553838360929790650083 7967330757541394685975125)
                ·
                  refine ⟨93367157314938218976271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 7967330757541394685975125 93367157314938218976271)
                  ·
                    rfl

theorem cell23_1636487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 4, 1, 8].length) (baseStart_1636487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1636487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1636487 prefixEnd_1636487 := by exact prefixLift 1636487
  have htrace : WordTrace (prefixWord ++ tailWord_1636487) baseStart_1636487 baseEnd_1636487 := by
    simpa [prefixWord, tailWord_1636487, baseEnd_1636487] using wordTrace_append hprefix tailTrace_1636487
  have hstable : (prefixWord ++ tailWord_1636487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1636487).length < 2 ^ (prefixWord ++ tailWord_1636487).sum := by decide
  have hdescent : baseEnd_1636487 < baseStart_1636487 := by decide
  rcases family_descends (prefixWord ++ tailWord_1636487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1636524 : List Nat := [2, 2, 1, 1, 1, 1, 1, 2, 5, 5, 2]
def baseStart_1636524 : Nat := 118140960795 + 1636524 * 2 ^ 59
def prefixEnd_1636524 : Nat := 4983230072969 + 3 ^ 40 * 1636524 * 2
def baseEnd_1636524 : Nat := 840323414618660326023769

theorem tailTrace_1636524 : CollatzResearch.WordTrace tailWord_1636524 prefixEnd_1636524 840323414618660326023769 := by
  unfold tailWord_1636524
  simp only [CollatzResearch.WordTrace]
  refine ⟨29844466961580259446246313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39792622615440345928328417 29844466961580259446246313)
  ·
    refine ⟨22383350221185194584684735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29844466961580259446246313 22383350221185194584684735)
    ·
      refine ⟨33575025331777791877027103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22383350221185194584684735 33575025331777791877027103)
      ·
        refine ⟨50362537997666687815540655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33575025331777791877027103 50362537997666687815540655)
        ·
          refine ⟨75543806996500031723310983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50362537997666687815540655 75543806996500031723310983)
          ·
            refine ⟨113315710494750047584966475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75543806996500031723310983 113315710494750047584966475)
            ·
              refine ⟨169973565742125071377449713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113315710494750047584966475 169973565742125071377449713)
              ·
                refine ⟨127480174306593803533087285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 169973565742125071377449713 127480174306593803533087285)
                ·
                  refine ⟨11951266341243169081226933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 127480174306593803533087285 11951266341243169081226933)
                  ·
                    refine ⟨1120431219491547101365025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11951266341243169081226933 1120431219491547101365025)
                    ·
                      refine ⟨840323414618660326023769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1120431219491547101365025 840323414618660326023769)
                      ·
                        rfl

theorem cell23_1636524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 5, 2].length) (baseStart_1636524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1636524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1636524 prefixEnd_1636524 := by exact prefixLift 1636524
  have htrace : WordTrace (prefixWord ++ tailWord_1636524) baseStart_1636524 baseEnd_1636524 := by
    simpa [prefixWord, tailWord_1636524, baseEnd_1636524] using wordTrace_append hprefix tailTrace_1636524
  have hstable : (prefixWord ++ tailWord_1636524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1636524).length < 2 ^ (prefixWord ++ tailWord_1636524).sum := by decide
  have hdescent : baseEnd_1636524 < baseStart_1636524 := by decide
  rcases family_descends (prefixWord ++ tailWord_1636524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1636542 : List Nat := [4, 2, 1, 1, 4, 2, 2, 2, 1, 4]
def baseStart_1636542 : Nat := 118140960795 + 1636542 * 2 ^ 59
def prefixEnd_1636542 : Nat := 4983230072969 + 3 ^ 40 * 1636542 * 2
def baseEnd_1636542 : Nat := 280110885756813751866229

theorem tailTrace_1636542 : CollatzResearch.WordTrace tailWord_1636542 prefixEnd_1636542 280110885756813751866229 := by
  unfold tailWord_1636542
  simp only [CollatzResearch.WordTrace]
  refine ⟨7461198804636913495830985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39793060291396871977765253 7461198804636913495830985)
  ·
    refine ⟨5595899103477685121873239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7461198804636913495830985 5595899103477685121873239)
    ·
      refine ⟨8393848655216527682809859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5595899103477685121873239 8393848655216527682809859)
      ·
        refine ⟨12590772982824791524214789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8393848655216527682809859 12590772982824791524214789)
        ·
          refine ⟨2360769934279648410790273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12590772982824791524214789 2360769934279648410790273)
          ·
            refine ⟨1770577450709736308092705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2360769934279648410790273 1770577450709736308092705)
            ·
              refine ⟨1327933088032302231069529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1770577450709736308092705 1327933088032302231069529)
              ·
                refine ⟨995949816024226673302147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1327933088032302231069529 995949816024226673302147)
                ·
                  refine ⟨1493924724036340009953221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 995949816024226673302147 1493924724036340009953221)
                  ·
                    refine ⟨280110885756813751866229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1493924724036340009953221 280110885756813751866229)
                    ·
                      rfl

theorem cell23_1636542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 2, 2, 2, 1, 4].length) (baseStart_1636542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1636542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1636542 prefixEnd_1636542 := by exact prefixLift 1636542
  have htrace : WordTrace (prefixWord ++ tailWord_1636542) baseStart_1636542 baseEnd_1636542 := by
    simpa [prefixWord, tailWord_1636542, baseEnd_1636542] using wordTrace_append hprefix tailTrace_1636542
  have hstable : (prefixWord ++ tailWord_1636542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1636542).length < 2 ^ (prefixWord ++ tailWord_1636542).sum := by decide
  have hdescent : baseEnd_1636542 < baseStart_1636542 := by decide
  rcases family_descends (prefixWord ++ tailWord_1636542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1636554 : List Nat := [3, 1, 2, 1, 3, 1, 1, 1, 5, 1, 4]
def baseStart_1636554 : Nat := 118140960795 + 1636554 * 2 ^ 59
def prefixEnd_1636554 : Nat := 4983230072969 + 3 ^ 40 * 1636554 * 2
def baseEnd_1636554 : Nat := 840338819038295208648631

theorem tailTrace_1636554 : CollatzResearch.WordTrace tailWord_1636554 prefixEnd_1636554 840338819038295208648631 := by
  unfold tailWord_1636554
  simp only [CollatzResearch.WordTrace]
  refine ⟨14922507028262958504021179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39793352075367889344056477 14922507028262958504021179)
  ·
    refine ⟨22383760542394437756031769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14922507028262958504021179 22383760542394437756031769)
    ·
      refine ⟨16787820406795828317023827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22383760542394437756031769 16787820406795828317023827)
      ·
        refine ⟨25181730610193742475535741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16787820406795828317023827 25181730610193742475535741)
        ·
          refine ⟨9443148978822653428325903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25181730610193742475535741 9443148978822653428325903)
          ·
            refine ⟨14164723468233980142488855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9443148978822653428325903 14164723468233980142488855)
            ·
              refine ⟨21247085202350970213733283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14164723468233980142488855 21247085202350970213733283)
              ·
                refine ⟨31870627803526455320599925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21247085202350970213733283 31870627803526455320599925)
                ·
                  refine ⟨2987871356580605186306243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 31870627803526455320599925 2987871356580605186306243)
                  ·
                    refine ⟨4481807034870907779459365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2987871356580605186306243 4481807034870907779459365)
                    ·
                      refine ⟨840338819038295208648631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4481807034870907779459365 840338819038295208648631)
                      ·
                        rfl

theorem cell23_1636554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 1, 5, 1, 4].length) (baseStart_1636554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1636554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1636554 prefixEnd_1636554 := by exact prefixLift 1636554
  have htrace : WordTrace (prefixWord ++ tailWord_1636554) baseStart_1636554 baseEnd_1636554 := by
    simpa [prefixWord, tailWord_1636554, baseEnd_1636554] using wordTrace_append hprefix tailTrace_1636554
  have hstable : (prefixWord ++ tailWord_1636554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1636554).length < 2 ^ (prefixWord ++ tailWord_1636554).sum := by decide
  have hdescent : baseEnd_1636554 < baseStart_1636554 := by decide
  rcases family_descends (prefixWord ++ tailWord_1636554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1636571 : List Nat := [1, 1, 1, 1, 1, 1, 1, 7, 5, 2, 2]
def baseStart_1636571 : Nat := 118140960795 + 1636571 * 2 ^ 59
def prefixEnd_1636571 : Nat := 4983230072969 + 3 ^ 40 * 1636571 * 2
def baseEnd_1636571 : Nat := 840347548209421642136053

theorem tailTrace_1636571 : CollatzResearch.WordTrace tailWord_1636571 prefixEnd_1636571 840347548209421642136053 := by
  unfold tailWord_1636571
  simp only [CollatzResearch.WordTrace]
  refine ⟨59690648153990245919453567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39793765435993497279635711 59690648153990245919453567)
  ·
    refine ⟨89535972230985368879180351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59690648153990245919453567 89535972230985368879180351)
    ·
      refine ⟨134303958346478053318770527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89535972230985368879180351 134303958346478053318770527)
      ·
        refine ⟨201455937519717079978155791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134303958346478053318770527 201455937519717079978155791)
        ·
          refine ⟨302183906279575619967233687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 201455937519717079978155791 302183906279575619967233687)
          ·
            refine ⟨453275859419363429950850531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 302183906279575619967233687 453275859419363429950850531)
            ·
              refine ⟨679913789129045144926275797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 453275859419363429950850531 679913789129045144926275797)
              ·
                refine ⟨15935479432711995584209589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 679913789129045144926275797 15935479432711995584209589)
                ·
                  refine ⟨1493951196816749586019649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 15935479432711995584209589 1493951196816749586019649)
                  ·
                    refine ⟨1120463397612562189514737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1493951196816749586019649 1120463397612562189514737)
                    ·
                      refine ⟨840347548209421642136053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1120463397612562189514737 840347548209421642136053)
                      ·
                        rfl

theorem cell23_1636571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 7, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 7, 5, 2, 2].length) (baseStart_1636571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1636571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1636571 prefixEnd_1636571 := by exact prefixLift 1636571
  have htrace : WordTrace (prefixWord ++ tailWord_1636571) baseStart_1636571 baseEnd_1636571 := by
    simpa [prefixWord, tailWord_1636571, baseEnd_1636571] using wordTrace_append hprefix tailTrace_1636571
  have hstable : (prefixWord ++ tailWord_1636571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1636571).length < 2 ^ (prefixWord ++ tailWord_1636571).sum := by decide
  have hdescent : baseEnd_1636571 < baseStart_1636571 := by decide
  rcases family_descends (prefixWord ++ tailWord_1636571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1636594 : List Nat := [3, 2, 1, 3, 2, 2, 10]
def baseStart_1636594 : Nat := 118140960795 + 1636594 * 2 ^ 59
def prefixEnd_1636594 : Nat := 4983230072969 + 3 ^ 40 * 1636594 * 2
def baseEnd_1636594 : Nat := 10374806892154012989487

theorem tailTrace_1636594 : CollatzResearch.WordTrace tailWord_1636594 prefixEnd_1636594 10374806892154012989487 := by
  unfold tailWord_1636594
  simp only [CollatzResearch.WordTrace]
  refine ⟨14922871758226730211885209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39794324688604613898360557 14922871758226730211885209)
  ·
    refine ⟨11192153818670047658913907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14922871758226730211885209 11192153818670047658913907)
    ·
      refine ⟨16788230728005071488370861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11192153818670047658913907 16788230728005071488370861)
      ·
        refine ⟨6295586523001901808139073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16788230728005071488370861 6295586523001901808139073)
        ·
          refine ⟨4721689892251426356104305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6295586523001901808139073 4721689892251426356104305)
          ·
            refine ⟨3541267419188569767078229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4721689892251426356104305 3541267419188569767078229)
            ·
              refine ⟨10374806892154012989487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 3541267419188569767078229 10374806892154012989487)
              ·
                rfl

theorem cell23_1636594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 10].length) (baseStart_1636594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1636594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1636594 prefixEnd_1636594 := by exact prefixLift 1636594
  have htrace : WordTrace (prefixWord ++ tailWord_1636594) baseStart_1636594 baseEnd_1636594 := by
    simpa [prefixWord, tailWord_1636594, baseEnd_1636594] using wordTrace_append hprefix tailTrace_1636594
  have hstable : (prefixWord ++ tailWord_1636594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1636594).length < 2 ^ (prefixWord ++ tailWord_1636594).sum := by decide
  have hdescent : baseEnd_1636594 < baseStart_1636594 := by decide
  rcases family_descends (prefixWord ++ tailWord_1636594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1636598 : List Nat := [5, 1, 1, 1, 1, 1, 5, 2, 2, 4]
def baseStart_1636598 : Nat := 118140960795 + 1636598 * 2 ^ 59
def prefixEnd_1636598 : Nat := 4983230072969 + 3 ^ 40 * 1636598 * 2
def baseEnd_1636598 : Nat := 280120470729031012166143

theorem tailTrace_1636598 : CollatzResearch.WordTrace tailWord_1636598 prefixEnd_1636598 280120470729031012166143 := by
  unfold tailWord_1636598
  simp only [CollatzResearch.WordTrace]
  refine ⟨3730727057805776845667903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 39794421949928286353790965 3730727057805776845667903)
  ·
    refine ⟨5596090586708665268501855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3730727057805776845667903 5596090586708665268501855)
    ·
      refine ⟨8394135880062997902752783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5596090586708665268501855 8394135880062997902752783)
      ·
        refine ⟨12591203820094496854129175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8394135880062997902752783 12591203820094496854129175)
        ·
          refine ⟨18886805730141745281193763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12591203820094496854129175 18886805730141745281193763)
          ·
            refine ⟨28330208595212617921790645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18886805730141745281193763 28330208595212617921790645)
            ·
              refine ⟨2655957055801182930167873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 28330208595212617921790645 2655957055801182930167873)
              ·
                refine ⟨1991967791850887197625905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2655957055801182930167873 1991967791850887197625905)
                ·
                  refine ⟨1493975843888165398219429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1991967791850887197625905 1493975843888165398219429)
                  ·
                    refine ⟨280120470729031012166143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1493975843888165398219429 280120470729031012166143)
                    ·
                      rfl

theorem cell23_1636598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 5, 2, 2, 4].length) (baseStart_1636598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1636598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1636598 prefixEnd_1636598 := by exact prefixLift 1636598
  have htrace : WordTrace (prefixWord ++ tailWord_1636598) baseStart_1636598 baseEnd_1636598 := by
    simpa [prefixWord, tailWord_1636598, baseEnd_1636598] using wordTrace_append hprefix tailTrace_1636598
  have hstable : (prefixWord ++ tailWord_1636598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1636598).length < 2 ^ (prefixWord ++ tailWord_1636598).sum := by decide
  have hdescent : baseEnd_1636598 < baseStart_1636598 := by decide
  rcases family_descends (prefixWord ++ tailWord_1636598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1636615 : List Nat := [1, 1, 4, 5, 2, 1, 1, 1, 1, 6]
def baseStart_1636615 : Nat := 118140960795 + 1636615 * 2 ^ 59
def prefixEnd_1636615 : Nat := 4983230072969 + 3 ^ 40 * 1636615 * 2
def baseEnd_1636615 : Nat := 280123380452739823328617

theorem tailTrace_1636615 : CollatzResearch.WordTrace tailWord_1636615 prefixEnd_1636615 280123380452739823328617 := by
  unfold tailWord_1636615
  simp only [CollatzResearch.WordTrace]
  refine ⟨59692252965830841434055299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39794835310553894289370199 59692252965830841434055299)
  ·
    refine ⟨89538379448746262151082949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59692252965830841434055299 89538379448746262151082949)
    ·
      refine ⟨16788446146639924153328053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 89538379448746262151082949 16788446146639924153328053)
      ·
        refine ⟨1573916826247492889374505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 16788446146639924153328053 1573916826247492889374505)
        ·
          refine ⟨1180437619685619667030879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1573916826247492889374505 1180437619685619667030879)
          ·
            refine ⟨1770656429528429500546319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1180437619685619667030879 1770656429528429500546319)
            ·
              refine ⟨2655984644292644250819479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1770656429528429500546319 2655984644292644250819479)
              ·
                refine ⟨3983976966438966376229219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2655984644292644250819479 3983976966438966376229219)
                ·
                  refine ⟨5975965449658449564343829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3983976966438966376229219 5975965449658449564343829)
                  ·
                    refine ⟨280123380452739823328617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5975965449658449564343829 280123380452739823328617)
                    ·
                      rfl

theorem cell23_1636615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 2, 1, 1, 1, 1, 6].length) (baseStart_1636615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1636615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1636615 prefixEnd_1636615 := by exact prefixLift 1636615
  have htrace : WordTrace (prefixWord ++ tailWord_1636615) baseStart_1636615 baseEnd_1636615 := by
    simpa [prefixWord, tailWord_1636615, baseEnd_1636615] using wordTrace_append hprefix tailTrace_1636615
  have hstable : (prefixWord ++ tailWord_1636615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1636615).length < 2 ^ (prefixWord ++ tailWord_1636615).sum := by decide
  have hdescent : baseEnd_1636615 < baseStart_1636615 := by decide
  rcases family_descends (prefixWord ++ tailWord_1636615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1636684 : List Nat := [2, 2, 1, 3, 2, 1, 2, 1, 9]
def baseStart_1636684 : Nat := 118140960795 + 1636684 * 2 ^ 59
def prefixEnd_1636684 : Nat := 4983230072969 + 3 ^ 40 * 1636684 * 2
def baseEnd_1636684 : Nat := 93378396835931077780337

theorem tailTrace_1636684 : CollatzResearch.WordTrace tailWord_1636684 prefixEnd_1636684 93378396835931077780337 := by
  unfold tailWord_1636684
  simp only [CollatzResearch.WordTrace]
  refine ⟨29847384801290433109158553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39796513068387244145544737 29847384801290433109158553)
  ·
    refine ⟨22385538600967824831868915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29847384801290433109158553 22385538600967824831868915)
    ·
      refine ⟨33578307901451737247803373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22385538600967824831868915 33578307901451737247803373)
      ·
        refine ⟨12591865463044401467926265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33578307901451737247803373 12591865463044401467926265)
        ·
          refine ⟨9443899097283301100944699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12591865463044401467926265 9443899097283301100944699)
          ·
            refine ⟨14165848645924951651417049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9443899097283301100944699 14165848645924951651417049)
            ·
              refine ⟨10624386484443713738562787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14165848645924951651417049 10624386484443713738562787)
              ·
                refine ⟨15936579726665570607844181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10624386484443713738562787 15936579726665570607844181)
                ·
                  refine ⟨93378396835931077780337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 15936579726665570607844181 93378396835931077780337)
                  ·
                    rfl

theorem cell23_1636684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 1, 9].length) (baseStart_1636684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1636684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1636684 prefixEnd_1636684 := by exact prefixLift 1636684
  have htrace : WordTrace (prefixWord ++ tailWord_1636684) baseStart_1636684 baseEnd_1636684 := by
    simpa [prefixWord, tailWord_1636684, baseEnd_1636684] using wordTrace_append hprefix tailTrace_1636684
  have hstable : (prefixWord ++ tailWord_1636684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1636684).length < 2 ^ (prefixWord ++ tailWord_1636684).sum := by decide
  have hdescent : baseEnd_1636684 < baseStart_1636684 := by decide
  rcases family_descends (prefixWord ++ tailWord_1636684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1636712 : List Nat := [2, 1, 4, 2, 2, 2, 2, 2, 2, 2, 2]
def baseStart_1636712 : Nat := 118140960795 + 1636712 * 2 ^ 59
def prefixEnd_1636712 : Nat := 4983230072969 + 3 ^ 40 * 1636712 * 2
def baseEnd_1636712 : Nat := 840419948981705590472905

theorem tailTrace_1636712 : CollatzResearch.WordTrace tailWord_1636712 prefixEnd_1636712 840419948981705590472905 := by
  unfold tailWord_1636712
  simp only [CollatzResearch.WordTrace]
  refine ⟨29847895423239713500168195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39797193897652951333557593 29847895423239713500168195)
  ·
    refine ⟨44771843134859570250252293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29847895423239713500168195 44771843134859570250252293)
    ·
      refine ⟨8394720587786169421922305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44771843134859570250252293 8394720587786169421922305)
      ·
        refine ⟨6296040440839627066441729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8394720587786169421922305 6296040440839627066441729)
        ·
          refine ⟨4722030330629720299831297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6296040440839627066441729 4722030330629720299831297)
          ·
            refine ⟨3541522747972290224873473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4722030330629720299831297 3541522747972290224873473)
            ·
              refine ⟨2656142060979217668655105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3541522747972290224873473 2656142060979217668655105)
              ·
                refine ⟨1992106545734413251491329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2656142060979217668655105 1992106545734413251491329)
                ·
                  refine ⟨1494079909300809938618497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1992106545734413251491329 1494079909300809938618497)
                  ·
                    refine ⟨1120559931975607453963873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1494079909300809938618497 1120559931975607453963873)
                    ·
                      refine ⟨840419948981705590472905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1120559931975607453963873 840419948981705590472905)
                      ·
                        rfl

theorem cell23_1636712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 2, 2, 2, 2, 2].length) (baseStart_1636712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1636712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1636712 prefixEnd_1636712 := by exact prefixLift 1636712
  have htrace : WordTrace (prefixWord ++ tailWord_1636712) baseStart_1636712 baseEnd_1636712 := by
    simpa [prefixWord, tailWord_1636712, baseEnd_1636712] using wordTrace_append hprefix tailTrace_1636712
  have hstable : (prefixWord ++ tailWord_1636712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1636712).length < 2 ^ (prefixWord ++ tailWord_1636712).sum := by decide
  have hdescent : baseEnd_1636712 < baseStart_1636712 := by decide
  rcases family_descends (prefixWord ++ tailWord_1636712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1636748 : List Nat := [2, 2, 1, 2, 1, 6, 1, 1, 2, 5]
def baseStart_1636748 : Nat := 118140960795 + 1636748 * 2 ^ 59
def prefixEnd_1636748 : Nat := 4983230072969 + 3 ^ 40 * 1636748 * 2
def baseEnd_1636748 : Nat := 280146144761755816540913

theorem tailTrace_1636748 : CollatzResearch.WordTrace tailWord_1636748 prefixEnd_1636748 280146144761755816540913 := by
  unfold tailWord_1636748
  simp only [CollatzResearch.WordTrace]
  refine ⟨29848551937174502574323449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39798069249566003432431265 29848551937174502574323449)
  ·
    refine ⟨22386413952880876930742587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29848551937174502574323449 22386413952880876930742587)
    ·
      refine ⟨33579620929321315396113881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22386413952880876930742587 33579620929321315396113881)
      ·
        refine ⟨25184715696990986547085411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33579620929321315396113881 25184715696990986547085411)
        ·
          refine ⟨37777073545486479820628117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25184715696990986547085411 37777073545486479820628117)
          ·
            refine ⟨1770800322444678741591943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 37777073545486479820628117 1770800322444678741591943)
            ·
              refine ⟨2656200483667018112387915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1770800322444678741591943 2656200483667018112387915)
              ·
                refine ⟨3984300725500527168581873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2656200483667018112387915 3984300725500527168581873)
                ·
                  refine ⟨2988225544125395376436405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3984300725500527168581873 2988225544125395376436405)
                  ·
                    refine ⟨280146144761755816540913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2988225544125395376436405 280146144761755816540913)
                    ·
                      rfl

theorem cell23_1636748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 6, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 6, 1, 1, 2, 5].length) (baseStart_1636748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1636748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1636748 prefixEnd_1636748 := by exact prefixLift 1636748
  have htrace : WordTrace (prefixWord ++ tailWord_1636748) baseStart_1636748 baseEnd_1636748 := by
    simpa [prefixWord, tailWord_1636748, baseEnd_1636748] using wordTrace_append hprefix tailTrace_1636748
  have hstable : (prefixWord ++ tailWord_1636748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1636748).length < 2 ^ (prefixWord ++ tailWord_1636748).sum := by decide
  have hdescent : baseEnd_1636748 < baseStart_1636748 := by decide
  rcases family_descends (prefixWord ++ tailWord_1636748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1636761 : List Nat := [1, 2, 1, 2, 1, 4, 1, 2, 5, 4]
def baseStart_1636761 : Nat := 118140960795 + 1636761 * 2 ^ 59
def prefixEnd_1636761 : Nat := 4983230072969 + 3 ^ 40 * 1636761 * 2
def baseEnd_1636761 : Nat := 280148369844591966253393

theorem tailTrace_1636761 : CollatzResearch.WordTrace tailWord_1636761 prefixEnd_1636761 280148369844591966253393 := by
  unfold tailWord_1636761
  simp only [CollatzResearch.WordTrace]
  refine ⟨59697578023301908368870137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39798385348867938912580091 59697578023301908368870137)
  ·
    refine ⟨44773183517476431276652603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59697578023301908368870137 44773183517476431276652603)
    ·
      refine ⟨67159775276214646914978905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44773183517476431276652603 67159775276214646914978905)
      ·
        refine ⟨50369831457160985186234179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67159775276214646914978905 50369831457160985186234179)
        ·
          refine ⟨75554747185741477779351269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50369831457160985186234179 75554747185741477779351269)
          ·
            refine ⟨14166515097326527083628363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 75554747185741477779351269 14166515097326527083628363)
            ·
              refine ⟨21249772645989790625442545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14166515097326527083628363 21249772645989790625442545)
              ·
                refine ⟨15937329484492342969081909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21249772645989790625442545 15937329484492342969081909)
                ·
                  refine ⟨1494124639171157153351429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 15937329484492342969081909 1494124639171157153351429)
                  ·
                    refine ⟨280148369844591966253393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1494124639171157153351429 280148369844591966253393)
                    ·
                      rfl

theorem cell23_1636761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 2, 5, 4].length) (baseStart_1636761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1636761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1636761 prefixEnd_1636761 := by exact prefixLift 1636761
  have htrace : WordTrace (prefixWord ++ tailWord_1636761) baseStart_1636761 baseEnd_1636761 := by
    simpa [prefixWord, tailWord_1636761, baseEnd_1636761] using wordTrace_append hprefix tailTrace_1636761
  have hstable : (prefixWord ++ tailWord_1636761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1636761).length < 2 ^ (prefixWord ++ tailWord_1636761).sum := by decide
  have hdescent : baseEnd_1636761 < baseStart_1636761 := by decide
  rcases family_descends (prefixWord ++ tailWord_1636761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1636768 : List Nat := [2, 1, 1, 4, 1, 3, 1, 2, 2, 4, 2]
def baseStart_1636768 : Nat := 118140960795 + 1636768 * 2 ^ 59
def prefixEnd_1636768 : Nat := 4983230072969 + 3 ^ 40 * 1636768 * 2
def baseEnd_1636768 : Nat := 840448703898357371372647

theorem tailTrace_1636768 : CollatzResearch.WordTrace tailWord_1636768 prefixEnd_1636768 840448703898357371372647 := by
  unfold tailWord_1636768
  simp only [CollatzResearch.WordTrace]
  refine ⟨29848916667138274282187479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39798555556184365709583305 29848916667138274282187479)
  ·
    refine ⟨44773375000707411423281219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29848916667138274282187479 44773375000707411423281219)
    ·
      refine ⟨67160062501061117134921829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44773375000707411423281219 67160062501061117134921829)
      ·
        refine ⟨12592511718948959462797843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 67160062501061117134921829 12592511718948959462797843)
        ·
          refine ⟨18888767578423439194196765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12592511718948959462797843 18888767578423439194196765)
          ·
            refine ⟨7083287841908789697823787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18888767578423439194196765 7083287841908789697823787)
            ·
              refine ⟨10624931762863184546735681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7083287841908789697823787 10624931762863184546735681)
              ·
                refine ⟨7968698822147388410051761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10624931762863184546735681 7968698822147388410051761)
                ·
                  refine ⟨5976524116610541307538821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7968698822147388410051761 5976524116610541307538821)
                  ·
                    refine ⟨1120598271864476495163529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5976524116610541307538821 1120598271864476495163529)
                    ·
                      refine ⟨840448703898357371372647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1120598271864476495163529 840448703898357371372647)
                      ·
                        rfl

theorem cell23_1636768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 2, 2, 4, 2].length) (baseStart_1636768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1636768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1636768 prefixEnd_1636768 := by exact prefixLift 1636768
  have htrace : WordTrace (prefixWord ++ tailWord_1636768) baseStart_1636768 baseEnd_1636768 := by
    simpa [prefixWord, tailWord_1636768, baseEnd_1636768] using wordTrace_append hprefix tailTrace_1636768
  have hstable : (prefixWord ++ tailWord_1636768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1636768).length < 2 ^ (prefixWord ++ tailWord_1636768).sum := by decide
  have hdescent : baseEnd_1636768 < baseStart_1636768 := by decide
  rcases family_descends (prefixWord ++ tailWord_1636768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1636784 : List Nat := [2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 9]
def baseStart_1636784 : Nat := 118140960795 + 1636784 * 2 ^ 59
def prefixEnd_1636784 : Nat := 4983230072969 + 3 ^ 40 * 1636784 * 2
def baseEnd_1636784 : Nat := 840456919588829308772573

theorem tailTrace_1636784 : CollatzResearch.WordTrace tailWord_1636784 prefixEnd_1636784 840456919588829308772573 := by
  unfold tailWord_1636784
  simp only [CollatzResearch.WordTrace]
  refine ⟨29849208451109291648478703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39798944601479055531304937 29849208451109291648478703)
  ·
    refine ⟨44773812676663937472718055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29849208451109291648478703 44773812676663937472718055)
    ·
      refine ⟨67160719014995906209077083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44773812676663937472718055 67160719014995906209077083)
      ·
        refine ⟨100741078522493859313615625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67160719014995906209077083 100741078522493859313615625)
        ·
          refine ⟨75555808891870394485211719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100741078522493859313615625 75555808891870394485211719)
          ·
            refine ⟨113333713337805591727817579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75555808891870394485211719 113333713337805591727817579)
            ·
              refine ⟨170000570006708387591726369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113333713337805591727817579 170000570006708387591726369)
              ·
                refine ⟨127500427505031290693794777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 170000570006708387591726369 127500427505031290693794777)
                ·
                  refine ⟨95625320628773468020346083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 127500427505031290693794777 95625320628773468020346083)
                  ·
                    refine ⟨143437980943160202030519125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 95625320628773468020346083 143437980943160202030519125)
                    ·
                      refine ⟨840456919588829308772573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 143437980943160202030519125 840456919588829308772573)
                      ·
                        rfl

theorem cell23_1636784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 9].length) (baseStart_1636784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1636784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1636784 prefixEnd_1636784 := by exact prefixLift 1636784
  have htrace : WordTrace (prefixWord ++ tailWord_1636784) baseStart_1636784 baseEnd_1636784 := by
    simpa [prefixWord, tailWord_1636784, baseEnd_1636784] using wordTrace_append hprefix tailTrace_1636784
  have hstable : (prefixWord ++ tailWord_1636784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1636784).length < 2 ^ (prefixWord ++ tailWord_1636784).sum := by decide
  have hdescent : baseEnd_1636784 < baseStart_1636784 := by decide
  rcases family_descends (prefixWord ++ tailWord_1636784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1636851 : List Nat := [1, 1, 1, 2, 2, 2, 4, 3, 1, 6]
def baseStart_1636851 : Nat := 118140960795 + 1636851 * 2 ^ 59
def prefixEnd_1636851 : Nat := 4983230072969 + 3 ^ 40 * 1636851 * 2
def baseEnd_1636851 : Nat := 280163774264226848878255

theorem tailTrace_1636851 : CollatzResearch.WordTrace tailWord_1636851 prefixEnd_1636851 280163774264226848878255 := by
  unfold tailWord_1636851
  simp only [CollatzResearch.WordTrace]
  refine ⟨59700860592975853739646407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39800573728650569159764271 59700860592975853739646407)
  ·
    refine ⟨89551290889463780609469611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59700860592975853739646407 89551290889463780609469611)
    ·
      refine ⟨134326936334195670914204417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89551290889463780609469611 134326936334195670914204417)
      ·
        refine ⟨100745202250646753185653313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134326936334195670914204417 100745202250646753185653313)
        ·
          refine ⟨75558901687985064889239985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100745202250646753185653313 75558901687985064889239985)
          ·
            refine ⟨56669176265988798666929989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75558901687985064889239985 56669176265988798666929989)
            ·
              refine ⟨10625470549872899750049373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 56669176265988798666929989 10625470549872899750049373)
              ·
                refine ⟨3984551456202337406268515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10625470549872899750049373 3984551456202337406268515)
                ·
                  refine ⟨5976827184303506109402773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3984551456202337406268515 5976827184303506109402773)
                  ·
                    refine ⟨280163774264226848878255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5976827184303506109402773 280163774264226848878255)
                    ·
                      rfl

theorem cell23_1636851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 3, 1, 6].length) (baseStart_1636851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1636851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1636851 prefixEnd_1636851 := by exact prefixLift 1636851
  have htrace : WordTrace (prefixWord ++ tailWord_1636851) baseStart_1636851 baseEnd_1636851 := by
    simpa [prefixWord, tailWord_1636851, baseEnd_1636851] using wordTrace_append hprefix tailTrace_1636851
  have hstable : (prefixWord ++ tailWord_1636851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1636851).length < 2 ^ (prefixWord ++ tailWord_1636851).sum := by decide
  have hdescent : baseEnd_1636851 < baseStart_1636851 := by decide
  rcases family_descends (prefixWord ++ tailWord_1636851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1636858 : List Nat := [3, 1, 1, 1, 1, 2, 2, 6, 1, 1, 4]
def baseStart_1636858 : Nat := 118140960795 + 1636858 * 2 ^ 59
def prefixEnd_1636858 : Nat := 4983230072969 + 3 ^ 40 * 1636858 * 2
def baseEnd_1636858 : Nat := 840494917157262019247233

theorem tailTrace_1636858 : CollatzResearch.WordTrace tailWord_1636858 prefixEnd_1636858 840494917157262019247233 := by
  unfold tailWord_1636858
  simp only [CollatzResearch.WordTrace]
  refine ⟨14925278975987623483787807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39800743935966995956767485 14925278975987623483787807)
  ·
    refine ⟨22387918463981435225681711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14925278975987623483787807 22387918463981435225681711)
    ·
      refine ⟨33581877695972152838522567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22387918463981435225681711 33581877695972152838522567)
      ·
        refine ⟨50372816543958229257783851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33581877695972152838522567 50372816543958229257783851)
        ·
          refine ⟨75559224815937343886675777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50372816543958229257783851 75559224815937343886675777)
          ·
            refine ⟨56669418611953007915006833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75559224815937343886675777 56669418611953007915006833)
            ·
              refine ⟨42502063958964755936255125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56669418611953007915006833 42502063958964755936255125)
              ·
                refine ⟨1992284248076472934511959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 42502063958964755936255125 1992284248076472934511959)
                ·
                  refine ⟨2988426372114709401767939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1992284248076472934511959 2988426372114709401767939)
                  ·
                    refine ⟨4482639558172064102651909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2988426372114709401767939 4482639558172064102651909)
                    ·
                      refine ⟨840494917157262019247233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4482639558172064102651909 840494917157262019247233)
                      ·
                        rfl

theorem cell23_1636858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 6, 1, 1, 4].length) (baseStart_1636858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1636858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1636858 prefixEnd_1636858 := by exact prefixLift 1636858
  have htrace : WordTrace (prefixWord ++ tailWord_1636858) baseStart_1636858 baseEnd_1636858 := by
    simpa [prefixWord, tailWord_1636858, baseEnd_1636858] using wordTrace_append hprefix tailTrace_1636858
  have hstable : (prefixWord ++ tailWord_1636858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1636858).length < 2 ^ (prefixWord ++ tailWord_1636858).sum := by decide
  have hdescent : baseEnd_1636858 < baseStart_1636858 := by decide
  rcases family_descends (prefixWord ++ tailWord_1636858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1636868 : List Nat := [2, 3, 2, 3, 1, 1, 1, 1, 3, 6]
def baseStart_1636868 : Nat := 118140960795 + 1636868 * 2 ^ 59
def prefixEnd_1636868 : Nat := 4983230072969 + 3 ^ 40 * 1636868 * 2
def baseEnd_1636868 : Nat := 280166683987935660040729

theorem tailTrace_1636868 : CollatzResearch.WordTrace tailWord_1636868 prefixEnd_1636868 280166683987935660040729 := by
  unfold tailWord_1636868
  simp only [CollatzResearch.WordTrace]
  refine ⟨29850740316957132821507629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39800987089276177095343505 29850740316957132821507629)
  ·
    refine ⟨11194027618858924808065361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29850740316957132821507629 11194027618858924808065361)
    ·
      refine ⟨8395520714144193606049021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11194027618858924808065361 8395520714144193606049021)
      ·
        refine ⟨3148320267804072602268383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8395520714144193606049021 3148320267804072602268383)
        ·
          refine ⟨4722480401706108903402575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3148320267804072602268383 4722480401706108903402575)
          ·
            refine ⟨7083720602559163355103863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4722480401706108903402575 7083720602559163355103863)
            ·
              refine ⟨10625580903838745032655795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7083720602559163355103863 10625580903838745032655795)
              ·
                refine ⟨15938371355758117548983693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10625580903838745032655795 15938371355758117548983693)
                ·
                  refine ⟨5976889258409294080868885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15938371355758117548983693 5976889258409294080868885)
                  ·
                    refine ⟨280166683987935660040729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5976889258409294080868885 280166683987935660040729)
                    ·
                      rfl

theorem cell23_1636868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 1, 3, 6].length) (baseStart_1636868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1636868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1636868 prefixEnd_1636868 := by exact prefixLift 1636868
  have htrace : WordTrace (prefixWord ++ tailWord_1636868) baseStart_1636868 baseEnd_1636868 := by
    simpa [prefixWord, tailWord_1636868, baseEnd_1636868] using wordTrace_append hprefix tailTrace_1636868
  have hstable : (prefixWord ++ tailWord_1636868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1636868).length < 2 ^ (prefixWord ++ tailWord_1636868).sum := by decide
  have hdescent : baseEnd_1636868 < baseStart_1636868 := by decide
  rcases family_descends (prefixWord ++ tailWord_1636868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1636885 : List Nat := [1, 3, 2, 1, 3, 1, 4, 2, 2, 4]
def baseStart_1636885 : Nat := 118140960795 + 1636885 * 2 ^ 59
def prefixEnd_1636885 : Nat := 4983230072969 + 3 ^ 40 * 1636885 * 2
def baseEnd_1636885 : Nat := 280169593711644471203203

theorem tailTrace_1636885 : CollatzResearch.WordTrace tailWord_1636885 prefixEnd_1636885 280169593711644471203203 := by
  unfold tailWord_1636885
  simp only [CollatzResearch.WordTrace]
  refine ⟨59702100674852677546384109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39801400449901785030922739 59702100674852677546384109)
  ·
    refine ⟨22388287753069754079894041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59702100674852677546384109 22388287753069754079894041)
    ·
      refine ⟨16791215814802315559920531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22388287753069754079894041 16791215814802315559920531)
      ·
        refine ⟨25186823722203473339880797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16791215814802315559920531 25186823722203473339880797)
        ·
          refine ⟨9445058895826302502455299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25186823722203473339880797 9445058895826302502455299)
          ·
            refine ⟨14167588343739453753682949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9445058895826302502455299 14167588343739453753682949)
            ·
              refine ⟨2656422814451147578815553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14167588343739453753682949 2656422814451147578815553)
              ·
                refine ⟨1992317110838360684111665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2656422814451147578815553 1992317110838360684111665)
                ·
                  refine ⟨1494237833128770513083749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1992317110838360684111665 1494237833128770513083749)
                  ·
                    refine ⟨280169593711644471203203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1494237833128770513083749 280169593711644471203203)
                    ·
                      rfl

theorem cell23_1636885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 4, 2, 2, 4].length) (baseStart_1636885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1636885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1636885 prefixEnd_1636885 := by exact prefixLift 1636885
  have htrace : WordTrace (prefixWord ++ tailWord_1636885) baseStart_1636885 baseEnd_1636885 := by
    simpa [prefixWord, tailWord_1636885, baseEnd_1636885] using wordTrace_append hprefix tailTrace_1636885
  have hstable : (prefixWord ++ tailWord_1636885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1636885).length < 2 ^ (prefixWord ++ tailWord_1636885).sum := by decide
  have hdescent : baseEnd_1636885 < baseStart_1636885 := by decide
  rcases family_descends (prefixWord ++ tailWord_1636885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1636901 : List Nat := [1, 3, 1, 2, 2, 1, 2, 1, 2, 2, 6]
def baseStart_1636901 : Nat := 118140960795 + 1636901 * 2 ^ 59
def prefixEnd_1636901 : Nat := 4983230072969 + 3 ^ 40 * 1636901 * 2
def baseEnd_1636901 : Nat := 840516996825405351009535

theorem tailTrace_1636901 : CollatzResearch.WordTrace tailWord_1636901 prefixEnd_1636901 840516996825405351009535 := by
  unfold tailWord_1636901
  simp only [CollatzResearch.WordTrace]
  refine ⟨59702684242794712278966557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39801789495196474852644371 59702684242794712278966557)
  ·
    refine ⟨22388506591048017104612459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59702684242794712278966557 22388506591048017104612459)
    ·
      refine ⟨33582759886572025656918689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22388506591048017104612459 33582759886572025656918689)
      ·
        refine ⟨25187069914929019242689017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33582759886572025656918689 25187069914929019242689017)
        ·
          refine ⟨18890302436196764432016763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25187069914929019242689017 18890302436196764432016763)
          ·
            refine ⟨28335453654295146648025145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18890302436196764432016763 28335453654295146648025145)
            ·
              refine ⟨21251590240721359986018859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28335453654295146648025145 21251590240721359986018859)
              ·
                refine ⟨31877385361082039979028289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21251590240721359986018859 31877385361082039979028289)
                ·
                  refine ⟨23908039020811529984271217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31877385361082039979028289 23908039020811529984271217)
                  ·
                    refine ⟨17931029265608647488203413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23908039020811529984271217 17931029265608647488203413)
                    ·
                      refine ⟨840516996825405351009535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 17931029265608647488203413 840516996825405351009535)
                      ·
                        rfl

theorem cell23_1636901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 1, 2, 2, 6].length) (baseStart_1636901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1636901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1636901 prefixEnd_1636901 := by exact prefixLift 1636901
  have htrace : WordTrace (prefixWord ++ tailWord_1636901) baseStart_1636901 baseEnd_1636901 := by
    simpa [prefixWord, tailWord_1636901, baseEnd_1636901] using wordTrace_append hprefix tailTrace_1636901
  have hstable : (prefixWord ++ tailWord_1636901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1636901).length < 2 ^ (prefixWord ++ tailWord_1636901).sum := by decide
  have hdescent : baseEnd_1636901 < baseStart_1636901 := by decide
  rcases family_descends (prefixWord ++ tailWord_1636901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1636925 : List Nat := [1, 4, 1, 3, 2, 1, 2, 2, 1, 3, 3]
def baseStart_1636925 : Nat := 118140960795 + 1636925 * 2 ^ 59
def prefixEnd_1636925 : Nat := 4983230072969 + 3 ^ 40 * 1636925 * 2
def baseEnd_1636925 : Nat := 840529320361113257109425

theorem tailTrace_1636925 : CollatzResearch.WordTrace tailWord_1636925 prefixEnd_1636925 840529320361113257109425 := by
  unfold tailWord_1636925
  simp only [CollatzResearch.WordTrace]
  refine ⟨59703559594707764377840229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39802373063138509585226819 59703559594707764377840229)
  ·
    refine ⟨11194417424007705820845043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 59703559594707764377840229 11194417424007705820845043)
    ·
      refine ⟨16791626136011558731267565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11194417424007705820845043 16791626136011558731267565)
      ·
        refine ⟨6296859801004334524225337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16791626136011558731267565 6296859801004334524225337)
        ·
          refine ⟨4722644850753250893169003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6296859801004334524225337 4722644850753250893169003)
          ·
            refine ⟨7083967276129876339753505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4722644850753250893169003 7083967276129876339753505)
            ·
              refine ⟨5312975457097407254815129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7083967276129876339753505 5312975457097407254815129)
              ·
                refine ⟨3984731592823055441111347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5312975457097407254815129 3984731592823055441111347)
                ·
                  refine ⟨5977097389234583161667021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3984731592823055441111347 5977097389234583161667021)
                  ·
                    refine ⟨2241411520962968685625133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5977097389234583161667021 2241411520962968685625133)
                    ·
                      refine ⟨840529320361113257109425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2241411520962968685625133 840529320361113257109425)
                      ·
                        rfl

theorem cell23_1636925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 2, 2, 1, 3, 3].length) (baseStart_1636925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1636925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1636925 prefixEnd_1636925 := by exact prefixLift 1636925
  have htrace : WordTrace (prefixWord ++ tailWord_1636925) baseStart_1636925 baseEnd_1636925 := by
    simpa [prefixWord, tailWord_1636925, baseEnd_1636925] using wordTrace_append hprefix tailTrace_1636925
  have hstable : (prefixWord ++ tailWord_1636925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1636925).length < 2 ^ (prefixWord ++ tailWord_1636925).sum := by decide
  have hdescent : baseEnd_1636925 < baseStart_1636925 := by decide
  rcases family_descends (prefixWord ++ tailWord_1636925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1636926 : List Nat := [4, 2, 1, 4, 1, 2, 2, 1, 1, 1, 4]
def baseStart_1636926 : Nat := 118140960795 + 1636926 * 2 ^ 59
def prefixEnd_1636926 : Nat := 4983230072969 + 3 ^ 40 * 1636926 * 2
def baseEnd_1636926 : Nat := 840529833841767753196921

theorem tailTrace_1636926 : CollatzResearch.WordTrace tailWord_1636926 prefixEnd_1636926 840529833841767753196921 := by
  unfold tailWord_1636926
  simp only [CollatzResearch.WordTrace]
  refine ⟨7462949508463017693578329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39802397378469427699084421 7462949508463017693578329)
  ·
    refine ⟨5597212131347263270183747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7462949508463017693578329 5597212131347263270183747)
    ·
      refine ⟨8395818197020894905275621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5597212131347263270183747 8395818197020894905275621)
      ·
        refine ⟨1574215911941417794739179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8395818197020894905275621 1574215911941417794739179)
        ·
          refine ⟨2361323867912126692108769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1574215911941417794739179 2361323867912126692108769)
          ·
            refine ⟨1770992900934095019081577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2361323867912126692108769 1770992900934095019081577)
            ·
              refine ⟨1328244675700571264311183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1770992900934095019081577 1328244675700571264311183)
              ·
                refine ⟨1992367013550856896466775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1328244675700571264311183 1992367013550856896466775)
                ·
                  refine ⟨2988550520326285344700163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1992367013550856896466775 2988550520326285344700163)
                  ·
                    refine ⟨4482825780489428017050245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2988550520326285344700163 4482825780489428017050245)
                    ·
                      refine ⟨840529833841767753196921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4482825780489428017050245 840529833841767753196921)
                      ·
                        rfl

theorem cell23_1636926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 2, 2, 1, 1, 1, 4].length) (baseStart_1636926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1636926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1636926 prefixEnd_1636926 := by exact prefixLift 1636926
  have htrace : WordTrace (prefixWord ++ tailWord_1636926) baseStart_1636926 baseEnd_1636926 := by
    simpa [prefixWord, tailWord_1636926, baseEnd_1636926] using wordTrace_append hprefix tailTrace_1636926
  have hstable : (prefixWord ++ tailWord_1636926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1636926).length < 2 ^ (prefixWord ++ tailWord_1636926).sum := by decide
  have hdescent : baseEnd_1636926 < baseStart_1636926 := by decide
  rcases family_descends (prefixWord ++ tailWord_1636926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1636929 : List Nat := [1, 2, 5, 1, 1, 4, 2, 1, 1, 2, 3]
def baseStart_1636929 : Nat := 118140960795 + 1636929 * 2 ^ 59
def prefixEnd_1636929 : Nat := 4983230072969 + 3 ^ 40 * 1636929 * 2
def baseEnd_1636929 : Nat := 840531374283731241459407

theorem tailTrace_1636929 : CollatzResearch.WordTrace tailWord_1636929 prefixEnd_1636929 840531374283731241459407 := by
  unfold tailWord_1636929
  simp only [CollatzResearch.WordTrace]
  refine ⟨59703705486693273060985841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39802470324462182040657227 59703705486693273060985841)
  ·
    refine ⟨44777779115019954795739381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59703705486693273060985841 44777779115019954795739381)
    ·
      refine ⟨4197916792033120762100567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 44777779115019954795739381 4197916792033120762100567)
      ·
        refine ⟨6296875188049681143150851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4197916792033120762100567 6296875188049681143150851)
        ·
          refine ⟨9445312782074521714726277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6296875188049681143150851 9445312782074521714726277)
          ·
            refine ⟨1770996146638972821511177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9445312782074521714726277 1770996146638972821511177)
            ·
              refine ⟨1328247109979229616133383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1770996146638972821511177 1328247109979229616133383)
              ·
                refine ⟨1992370664968844424200075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1328247109979229616133383 1992370664968844424200075)
                ·
                  refine ⟨2988555997453266636300113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1992370664968844424200075 2988555997453266636300113)
                  ·
                    refine ⟨2241416998089949977225085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2988555997453266636300113 2241416998089949977225085)
                    ·
                      refine ⟨840531374283731241459407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2241416998089949977225085 840531374283731241459407)
                      ·
                        rfl

theorem cell23_1636929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 4, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 4, 2, 1, 1, 2, 3].length) (baseStart_1636929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1636929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1636929 prefixEnd_1636929 := by exact prefixLift 1636929
  have htrace : WordTrace (prefixWord ++ tailWord_1636929) baseStart_1636929 baseEnd_1636929 := by
    simpa [prefixWord, tailWord_1636929, baseEnd_1636929] using wordTrace_append hprefix tailTrace_1636929
  have hstable : (prefixWord ++ tailWord_1636929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1636929).length < 2 ^ (prefixWord ++ tailWord_1636929).sum := by decide
  have hdescent : baseEnd_1636929 < baseStart_1636929 := by decide
  rcases family_descends (prefixWord ++ tailWord_1636929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1636932 : List Nat := [2, 3, 5, 1, 1, 1, 10]
def baseStart_1636932 : Nat := 118140960795 + 1636932 * 2 ^ 59
def prefixEnd_1636932 : Nat := 4983230072969 + 3 ^ 40 * 1636932 * 2
def baseEnd_1636932 : Nat := 10376949564514749749653

theorem tailTrace_1636932 : CollatzResearch.WordTrace tailWord_1636932 prefixEnd_1636932 10376949564514749749653 := by
  unfold tailWord_1636932
  simp only [CollatzResearch.WordTrace]
  refine ⟨29851907452841202286672525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39802543270454936382230033 29851907452841202286672525)
  ·
    refine ⟨11194465294815450857502197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29851907452841202286672525 11194465294815450857502197)
    ·
      refine ⟨1049481121388948517890831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 11194465294815450857502197 1049481121388948517890831)
      ·
        refine ⟨1574221682083422776836247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1049481121388948517890831 1574221682083422776836247)
        ·
          refine ⟨2361332523125134165254371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1574221682083422776836247 2361332523125134165254371)
          ·
            refine ⟨3541998784687701247881557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2361332523125134165254371 3541998784687701247881557)
            ·
              refine ⟨10376949564514749749653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 3541998784687701247881557 10376949564514749749653)
              ·
                rfl

theorem cell23_1636932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 10].length) (baseStart_1636932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1636932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1636932 prefixEnd_1636932 := by exact prefixLift 1636932
  have htrace : WordTrace (prefixWord ++ tailWord_1636932) baseStart_1636932 baseEnd_1636932 := by
    simpa [prefixWord, tailWord_1636932, baseEnd_1636932] using wordTrace_append hprefix tailTrace_1636932
  have hstable : (prefixWord ++ tailWord_1636932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1636932).length < 2 ^ (prefixWord ++ tailWord_1636932).sum := by decide
  have hdescent : baseEnd_1636932 < baseStart_1636932 := by decide
  rcases family_descends (prefixWord ++ tailWord_1636932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1636942 : List Nat := [4, 1, 1, 1, 1, 2, 5, 2, 2, 1, 3]
def baseStart_1636942 : Nat := 118140960795 + 1636942 * 2 ^ 59
def prefixEnd_1636942 : Nat := 4983230072969 + 3 ^ 40 * 1636942 * 2
def baseEnd_1636942 : Nat := 840538049532239690596847

theorem tailTrace_1636942 : CollatzResearch.WordTrace tailWord_1636942 prefixEnd_1636942 840538049532239690596847 := by
  unfold tailWord_1636942
  simp only [CollatzResearch.WordTrace]
  refine ⟨7463022454455772035151135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39802786423764117520806053 7463022454455772035151135)
  ·
    refine ⟨11194533681683658052726703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7463022454455772035151135 11194533681683658052726703)
    ·
      refine ⟨16791800522525487079090055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11194533681683658052726703 16791800522525487079090055)
      ·
        refine ⟨25187700783788230618635083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16791800522525487079090055 25187700783788230618635083)
        ·
          refine ⟨37781551175682345927952625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25187700783788230618635083 37781551175682345927952625)
          ·
            refine ⟨28336163381761759445964469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37781551175682345927952625 28336163381761759445964469)
            ·
              refine ⟨2656515317040164948059169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 28336163381761759445964469 2656515317040164948059169)
              ·
                refine ⟨1992386487780123711044377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2656515317040164948059169 1992386487780123711044377)
                ·
                  refine ⟨1494289865835092783283283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1992386487780123711044377 1494289865835092783283283)
                  ·
                    refine ⟨2241434798752639174924925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1494289865835092783283283 2241434798752639174924925)
                    ·
                      refine ⟨840538049532239690596847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2241434798752639174924925 840538049532239690596847)
                      ·
                        rfl

theorem cell23_1636942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 5, 2, 2, 1, 3].length) (baseStart_1636942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1636942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1636942 prefixEnd_1636942 := by exact prefixLift 1636942
  have htrace : WordTrace (prefixWord ++ tailWord_1636942) baseStart_1636942 baseEnd_1636942 := by
    simpa [prefixWord, tailWord_1636942, baseEnd_1636942] using wordTrace_append hprefix tailTrace_1636942
  have hstable : (prefixWord ++ tailWord_1636942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1636942).length < 2 ^ (prefixWord ++ tailWord_1636942).sum := by decide
  have hdescent : baseEnd_1636942 < baseStart_1636942 := by decide
  rcases family_descends (prefixWord ++ tailWord_1636942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1636971 : List Nat := [1, 1, 1, 1, 2, 2, 1, 5, 9]
def baseStart_1636971 : Nat := 118140960795 + 1636971 * 2 ^ 59
def prefixEnd_1636971 : Nat := 4983230072969 + 3 ^ 40 * 1636971 * 2
def baseEnd_1636971 : Nat := 93394771163468897459357

theorem tailTrace_1636971 : CollatzResearch.WordTrace tailWord_1636971 prefixEnd_1636971 93394771163468897459357 := by
  unfold tailWord_1636971
  simp only [CollatzResearch.WordTrace]
  refine ⟨59705237352541114234014767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39803491568360742822676511 59705237352541114234014767)
  ·
    refine ⟨89557856028811671351022151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59705237352541114234014767 89557856028811671351022151)
    ·
      refine ⟨134336784043217507026533227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89557856028811671351022151 134336784043217507026533227)
      ·
        refine ⟨201505176064826260539799841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134336784043217507026533227 201505176064826260539799841)
        ·
          refine ⟨151128882048619695404849881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 201505176064826260539799841 151128882048619695404849881)
          ·
            refine ⟨113346661536464771553637411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 151128882048619695404849881 113346661536464771553637411)
            ·
              refine ⟨170019992304697157330456117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113346661536464771553637411 170019992304697157330456117)
              ·
                refine ⟨15939374278565358499730261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 170019992304697157330456117 15939374278565358499730261)
                ·
                  refine ⟨93394771163468897459357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 15939374278565358499730261 93394771163468897459357)
                  ·
                    rfl

theorem cell23_1636971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 5, 9].length) (baseStart_1636971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1636971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1636971 prefixEnd_1636971 := by exact prefixLift 1636971
  have htrace : WordTrace (prefixWord ++ tailWord_1636971) baseStart_1636971 baseEnd_1636971 := by
    simpa [prefixWord, tailWord_1636971, baseEnd_1636971] using wordTrace_append hprefix tailTrace_1636971
  have hstable : (prefixWord ++ tailWord_1636971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1636971).length < 2 ^ (prefixWord ++ tailWord_1636971).sum := by decide
  have hdescent : baseEnd_1636971 < baseStart_1636971 := by decide
  rcases family_descends (prefixWord ++ tailWord_1636971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1637028 : List Nat := [2, 3, 1, 2, 2, 1, 1, 2, 1, 1, 7]
def baseStart_1637028 : Nat := 118140960795 + 1637028 * 2 ^ 59
def prefixEnd_1637028 : Nat := 4983230072969 + 3 ^ 40 * 1637028 * 2
def baseEnd_1637028 : Nat := 840582208868526354121451

theorem tailTrace_1637028 : CollatzResearch.WordTrace tailWord_1637028 prefixEnd_1637028 840582208868526354121451 := by
  unfold tailWord_1637028
  simp only [CollatzResearch.WordTrace]
  refine ⟨29853658156667306484419869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39804877542223075312559825 29853658156667306484419869)
  ·
    refine ⟨11195121808750239931657451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29853658156667306484419869 11195121808750239931657451)
    ·
      refine ⟨16792682713125359897486177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11195121808750239931657451 16792682713125359897486177)
      ·
        refine ⟨12594512034844019923114633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16792682713125359897486177 12594512034844019923114633)
        ·
          refine ⟨9445884026133014942335975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12594512034844019923114633 9445884026133014942335975)
          ·
            refine ⟨14168826039199522413503963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9445884026133014942335975 14168826039199522413503963)
            ·
              refine ⟨21253239058799283620255945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14168826039199522413503963 21253239058799283620255945)
              ·
                refine ⟨15939929294099462715191959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21253239058799283620255945 15939929294099462715191959)
                ·
                  refine ⟨23909893941149194072787939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15939929294099462715191959 23909893941149194072787939)
                  ·
                    refine ⟨35864840911723791109181909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23909893941149194072787939 35864840911723791109181909)
                    ·
                      refine ⟨840582208868526354121451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 35864840911723791109181909 840582208868526354121451)
                      ·
                        rfl

theorem cell23_1637028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 2, 1, 1, 7].length) (baseStart_1637028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1637028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1637028 prefixEnd_1637028 := by exact prefixLift 1637028
  have htrace : WordTrace (prefixWord ++ tailWord_1637028) baseStart_1637028 baseEnd_1637028 := by
    simpa [prefixWord, tailWord_1637028, baseEnd_1637028] using wordTrace_append hprefix tailTrace_1637028
  have hstable : (prefixWord ++ tailWord_1637028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1637028).length < 2 ^ (prefixWord ++ tailWord_1637028).sum := by decide
  have hdescent : baseEnd_1637028 < baseStart_1637028 := by decide
  rcases family_descends (prefixWord ++ tailWord_1637028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1637045 : List Nat := [1, 3, 3, 3, 1, 1, 1, 2, 1, 2, 5]
def baseStart_1637045 : Nat := 118140960795 + 1637045 * 2 ^ 59
def prefixEnd_1637045 : Nat := 4983230072969 + 3 ^ 40 * 1637045 * 2
def baseEnd_1637045 : Nat := 840590938039652787608873

theorem tailTrace_1637045 : CollatzResearch.WordTrace tailWord_1637045 prefixEnd_1637045 840590938039652787608873 := by
  unfold tailWord_1637045
  simp only [CollatzResearch.WordTrace]
  refine ⟨59707936354273024872208589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39805290902848683248139059 59707936354273024872208589)
  ·
    refine ⟨22390476132852384327078221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59707936354273024872208589 22390476132852384327078221)
    ·
      refine ⟨8396428549819644122654333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22390476132852384327078221 8396428549819644122654333)
      ·
        refine ⟨3148660706182366545995375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8396428549819644122654333 3148660706182366545995375)
        ·
          refine ⟨4722991059273549818993063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3148660706182366545995375 4722991059273549818993063)
          ·
            refine ⟨7084486588910324728489595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4722991059273549818993063 7084486588910324728489595)
            ·
              refine ⟨10626729883365487092734393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7084486588910324728489595 10626729883365487092734393)
              ·
                refine ⟨7970047412524115319550795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10626729883365487092734393 7970047412524115319550795)
                ·
                  refine ⟨11955071118786172979326193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7970047412524115319550795 11955071118786172979326193)
                  ·
                    refine ⟨8966303339089629734494645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11955071118786172979326193 8966303339089629734494645)
                    ·
                      refine ⟨840590938039652787608873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8966303339089629734494645 840590938039652787608873)
                      ·
                        rfl

theorem cell23_1637045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 2, 1, 2, 5].length) (baseStart_1637045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1637045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1637045 prefixEnd_1637045 := by exact prefixLift 1637045
  have htrace : WordTrace (prefixWord ++ tailWord_1637045) baseStart_1637045 baseEnd_1637045 := by
    simpa [prefixWord, tailWord_1637045, baseEnd_1637045] using wordTrace_append hprefix tailTrace_1637045
  have hstable : (prefixWord ++ tailWord_1637045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1637045).length < 2 ^ (prefixWord ++ tailWord_1637045).sum := by decide
  have hdescent : baseEnd_1637045 < baseStart_1637045 := by decide
  rcases family_descends (prefixWord ++ tailWord_1637045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1637055 : List Nat := [1, 1, 2, 2, 2, 4, 2, 2, 2, 1, 4]
def baseStart_1637055 : Nat := 118140960795 + 1637055 * 2 ^ 59
def prefixEnd_1637055 : Nat := 4983230072969 + 3 ^ 40 * 1637055 * 2
def baseEnd_1637055 : Nat := 840596072846197748483827

theorem tailTrace_1637055 : CollatzResearch.WordTrace tailWord_1637055 prefixEnd_1637055 840596072846197748483827 := by
  unfold tailWord_1637055
  simp only [CollatzResearch.WordTrace]
  refine ⟨59708301084236796580072619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39805534056157864386715079 59708301084236796580072619)
  ·
    refine ⟨89562451626355194870108929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59708301084236796580072619 89562451626355194870108929)
    ·
      refine ⟨67171838719766396152581697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89562451626355194870108929 67171838719766396152581697)
      ·
        refine ⟨50378879039824797114436273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67171838719766396152581697 50378879039824797114436273)
        ·
          refine ⟨37784159279868597835827205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50378879039824797114436273 37784159279868597835827205)
          ·
            refine ⟨7084529864975362094217601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37784159279868597835827205 7084529864975362094217601)
            ·
              refine ⟨5313397398731521570663201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7084529864975362094217601 5313397398731521570663201)
              ·
                refine ⟨3985048049048641177997401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5313397398731521570663201 3985048049048641177997401)
                ·
                  refine ⟨2988786036786480883498051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3985048049048641177997401 2988786036786480883498051)
                  ·
                    refine ⟨4483179055179721325247077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2988786036786480883498051 4483179055179721325247077)
                    ·
                      refine ⟨840596072846197748483827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4483179055179721325247077 840596072846197748483827)
                      ·
                        rfl

theorem cell23_1637055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 2, 2, 2, 1, 4].length) (baseStart_1637055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1637055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1637055 prefixEnd_1637055 := by exact prefixLift 1637055
  have htrace : WordTrace (prefixWord ++ tailWord_1637055) baseStart_1637055 baseEnd_1637055 := by
    simpa [prefixWord, tailWord_1637055, baseEnd_1637055] using wordTrace_append hprefix tailTrace_1637055
  have hstable : (prefixWord ++ tailWord_1637055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1637055).length < 2 ^ (prefixWord ++ tailWord_1637055).sum := by decide
  have hdescent : baseEnd_1637055 < baseStart_1637055 := by decide
  rcases family_descends (prefixWord ++ tailWord_1637055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1637092 : List Nat := [2, 3, 1, 1, 1, 4, 3, 1, 2, 2, 3]
def baseStart_1637092 : Nat := 118140960795 + 1637092 * 2 ^ 59
def prefixEnd_1637092 : Nat := 4983230072969 + 3 ^ 40 * 1637092 * 2
def baseEnd_1637092 : Nat := 840615071630414103721157

theorem tailTrace_1637092 : CollatzResearch.WordTrace tailWord_1637092 prefixEnd_1637092 840615071630414103721157 := by
  unfold tailWord_1637092
  simp only [CollatzResearch.WordTrace]
  refine ⟨29854825292551375949584765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39806433723401834599446353 29854825292551375949584765)
  ·
    refine ⟨11195559484706765981094287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29854825292551375949584765 11195559484706765981094287)
    ·
      refine ⟨16793339227060148971641431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11195559484706765981094287 16793339227060148971641431)
      ·
        refine ⟨25190008840590223457462147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16793339227060148971641431 25190008840590223457462147)
        ·
          refine ⟨37785013260885335186193221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25190008840590223457462147 37785013260885335186193221)
          ·
            refine ⟨7084689986416000347411229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37785013260885335186193221 7084689986416000347411229)
            ·
              refine ⟨2656758744906000130279211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7084689986416000347411229 2656758744906000130279211)
              ·
                refine ⟨3985138117359000195418817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2656758744906000130279211 3985138117359000195418817)
                ·
                  refine ⟨2988853588019250146564113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3985138117359000195418817 2988853588019250146564113)
                  ·
                    refine ⟨2241640191014437609923085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2988853588019250146564113 2241640191014437609923085)
                    ·
                      refine ⟨840615071630414103721157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2241640191014437609923085 840615071630414103721157)
                      ·
                        rfl

theorem cell23_1637092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 3, 1, 2, 2, 3].length) (baseStart_1637092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1637092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1637092 prefixEnd_1637092 := by exact prefixLift 1637092
  have htrace : WordTrace (prefixWord ++ tailWord_1637092) baseStart_1637092 baseEnd_1637092 := by
    simpa [prefixWord, tailWord_1637092, baseEnd_1637092] using wordTrace_append hprefix tailTrace_1637092
  have hstable : (prefixWord ++ tailWord_1637092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1637092).length < 2 ^ (prefixWord ++ tailWord_1637092).sum := by decide
  have hdescent : baseEnd_1637092 < baseStart_1637092 := by decide
  rcases family_descends (prefixWord ++ tailWord_1637092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1637166 : List Nat := [4, 1, 3, 2, 1, 2, 1, 2, 2, 3, 2]
def baseStart_1637166 : Nat := 118140960795 + 1637166 * 2 ^ 59
def prefixEnd_1637166 : Nat := 4983230072969 + 3 ^ 40 * 1637166 * 2
def baseEnd_1637166 : Nat := 840653069198846814195817

theorem tailTrace_1637166 : CollatzResearch.WordTrace tailWord_1637166 prefixEnd_1637166 840653069198846814195817 := by
  unfold tailWord_1637166
  simp only [CollatzResearch.WordTrace]
  refine ⟨7464043698354332817170419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39808233057889775024908901 7464043698354332817170419)
  ·
    refine ⟨11196065547531499225755629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7464043698354332817170419 11196065547531499225755629)
    ·
      refine ⟨4198524580324312209658361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11196065547531499225755629 4198524580324312209658361)
      ·
        refine ⟨3148893435243234157243771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4198524580324312209658361 3148893435243234157243771)
        ·
          refine ⟨4723340152864851235865657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3148893435243234157243771 4723340152864851235865657)
          ·
            refine ⟨3542505114648638426899243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4723340152864851235865657 3542505114648638426899243)
            ·
              refine ⟨5313757671972957640348865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3542505114648638426899243 5313757671972957640348865)
              ·
                refine ⟨3985318253979718230261649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5313757671972957640348865 3985318253979718230261649)
                ·
                  refine ⟨2988988690484788672696237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3985318253979718230261649 2988988690484788672696237)
                  ·
                    refine ⟨1120870758931795752261089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2988988690484788672696237 1120870758931795752261089)
                    ·
                      refine ⟨840653069198846814195817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1120870758931795752261089 840653069198846814195817)
                      ·
                        rfl

theorem cell23_1637166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 1, 2, 2, 3, 2].length) (baseStart_1637166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1637166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1637166 prefixEnd_1637166 := by exact prefixLift 1637166
  have htrace : WordTrace (prefixWord ++ tailWord_1637166) baseStart_1637166 baseEnd_1637166 := by
    simpa [prefixWord, tailWord_1637166, baseEnd_1637166] using wordTrace_append hprefix tailTrace_1637166
  have hstable : (prefixWord ++ tailWord_1637166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1637166).length < 2 ^ (prefixWord ++ tailWord_1637166).sum := by decide
  have hdescent : baseEnd_1637166 < baseStart_1637166 := by decide
  rcases family_descends (prefixWord ++ tailWord_1637166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1637173 : List Nat := [1, 3, 3, 1, 3, 2, 3, 2, 1, 1, 3]
def baseStart_1637173 : Nat := 118140960795 + 1637173 * 2 ^ 59
def prefixEnd_1637173 : Nat := 4983230072969 + 3 ^ 40 * 1637173 * 2
def baseEnd_1637173 : Nat := 840656663563428286808285

theorem tailTrace_1637173 : CollatzResearch.WordTrace tailWord_1637173 prefixEnd_1637173 840656663563428286808285 := by
  unfold tailWord_1637173
  simp only [CollatzResearch.WordTrace]
  refine ⟨59712604897809302732868173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39808403265206201821912115 59712604897809302732868173)
  ·
    refine ⟨22392226836678488524825565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59712604897809302732868173 22392226836678488524825565)
    ·
      refine ⟨8397085063754433196809587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22392226836678488524825565 8397085063754433196809587)
      ·
        refine ⟨12595627595631649795214381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8397085063754433196809587 12595627595631649795214381)
        ·
          refine ⟨4723360348361868673205393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12595627595631649795214381 4723360348361868673205393)
          ·
            refine ⟨3542520261271401504904045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4723360348361868673205393 3542520261271401504904045)
            ·
              refine ⟨1328445097976775564339017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3542520261271401504904045 1328445097976775564339017)
              ·
                refine ⟨996333823482581673254263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1328445097976775564339017 996333823482581673254263)
                ·
                  refine ⟨1494500735223872509881395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 996333823482581673254263 1494500735223872509881395)
                  ·
                    refine ⟨2241751102835808764822093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1494500735223872509881395 2241751102835808764822093)
                    ·
                      refine ⟨840656663563428286808285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2241751102835808764822093 840656663563428286808285)
                      ·
                        rfl

theorem cell23_1637173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 3, 2, 1, 1, 3].length) (baseStart_1637173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1637173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1637173 prefixEnd_1637173 := by exact prefixLift 1637173
  have htrace : WordTrace (prefixWord ++ tailWord_1637173) baseStart_1637173 baseEnd_1637173 := by
    simpa [prefixWord, tailWord_1637173, baseEnd_1637173] using wordTrace_append hprefix tailTrace_1637173
  have hstable : (prefixWord ++ tailWord_1637173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1637173).length < 2 ^ (prefixWord ++ tailWord_1637173).sum := by decide
  have hdescent : baseEnd_1637173 < baseStart_1637173 := by decide
  rcases family_descends (prefixWord ++ tailWord_1637173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1637195 : List Nat := [1, 1, 1, 1, 3, 1, 1, 1, 7, 3, 3]
def baseStart_1637195 : Nat := 118140960795 + 1637195 * 2 ^ 59
def prefixEnd_1637195 : Nat := 4983230072969 + 3 ^ 40 * 1637195 * 2
def baseEnd_1637195 : Nat := 840667960137827200733183

theorem tailTrace_1637195 : CollatzResearch.WordTrace tailWord_1637195 prefixEnd_1637195 840667960137827200733183 := by
  unfold tailWord_1637195
  simp only [CollatzResearch.WordTrace]
  refine ⟨59713407303729600490169039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39808938202486400326779359 59713407303729600490169039)
  ·
    refine ⟨89570110955594400735253559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59713407303729600490169039 89570110955594400735253559)
    ·
      refine ⟨134355166433391601102880339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89570110955594400735253559 134355166433391601102880339)
      ·
        refine ⟨201532749650087401654320509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134355166433391601102880339 201532749650087401654320509)
        ·
          refine ⟨75574781118782775620370191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 201532749650087401654320509 75574781118782775620370191)
          ·
            refine ⟨113362171678174163430555287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75574781118782775620370191 113362171678174163430555287)
            ·
              refine ⟨170043257517261245145832931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113362171678174163430555287 170043257517261245145832931)
              ·
                refine ⟨255064886275891867718749397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 170043257517261245145832931 255064886275891867718749397)
                ·
                  refine ⟨5978083272091215649658189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 255064886275891867718749397 5978083272091215649658189)
                  ·
                    refine ⟨2241781227034205868621821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5978083272091215649658189 2241781227034205868621821)
                    ·
                      refine ⟨840667960137827200733183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2241781227034205868621821 840667960137827200733183)
                      ·
                        rfl

theorem cell23_1637195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 7, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 7, 3, 3].length) (baseStart_1637195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1637195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1637195 prefixEnd_1637195 := by exact prefixLift 1637195
  have htrace : WordTrace (prefixWord ++ tailWord_1637195) baseStart_1637195 baseEnd_1637195 := by
    simpa [prefixWord, tailWord_1637195, baseEnd_1637195] using wordTrace_append hprefix tailTrace_1637195
  have hstable : (prefixWord ++ tailWord_1637195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1637195).length < 2 ^ (prefixWord ++ tailWord_1637195).sum := by decide
  have hdescent : baseEnd_1637195 < baseStart_1637195 := by decide
  rcases family_descends (prefixWord ++ tailWord_1637195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1637230 : List Nat := [4, 1, 2, 3, 2, 1, 1, 4, 1, 2, 2]
def baseStart_1637230 : Nat := 118140960795 + 1637230 * 2 ^ 59
def prefixEnd_1637230 : Nat := 4983230072969 + 3 ^ 40 * 1637230 * 2
def baseEnd_1637230 : Nat := 840685931960734563795523

theorem tailTrace_1637230 : CollatzResearch.WordTrace tailWord_1637230 prefixEnd_1637230 840685931960734563795523 := by
  unfold tailWord_1637230
  simp only [CollatzResearch.WordTrace]
  refine ⟨7464335482325350183461643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39809789239068534311795429 7464335482325350183461643)
  ·
    refine ⟨11196503223488025275192465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7464335482325350183461643 11196503223488025275192465)
    ·
      refine ⟨8397377417616018956394349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11196503223488025275192465 8397377417616018956394349)
      ·
        refine ⟨3149016531606007108647881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8397377417616018956394349 3149016531606007108647881)
        ·
          refine ⟨2361762398704505331485911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3149016531606007108647881 2361762398704505331485911)
          ·
            refine ⟨3542643598056757997228867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2361762398704505331485911 3542643598056757997228867)
            ·
              refine ⟨5313965397085136995843301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3542643598056757997228867 5313965397085136995843301)
              ·
                refine ⟨996368511953463186720619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5313965397085136995843301 996368511953463186720619)
                ·
                  refine ⟨1494552767930194780080929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 996368511953463186720619 1494552767930194780080929)
                  ·
                    refine ⟨1120914575947646085060697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1494552767930194780080929 1120914575947646085060697)
                    ·
                      refine ⟨840685931960734563795523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1120914575947646085060697 840685931960734563795523)
                      ·
                        rfl

theorem cell23_1637230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 1, 4, 1, 2, 2].length) (baseStart_1637230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1637230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1637230 prefixEnd_1637230 := by exact prefixLift 1637230
  have htrace : WordTrace (prefixWord ++ tailWord_1637230) baseStart_1637230 baseEnd_1637230 := by
    simpa [prefixWord, tailWord_1637230, baseEnd_1637230] using wordTrace_append hprefix tailTrace_1637230
  have hstable : (prefixWord ++ tailWord_1637230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1637230).length < 2 ^ (prefixWord ++ tailWord_1637230).sum := by decide
  have hdescent : baseEnd_1637230 < baseStart_1637230 := by decide
  rcases family_descends (prefixWord ++ tailWord_1637230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1637235 : List Nat := [1, 1, 1, 2, 2, 1, 5, 1, 2, 3, 4]
def baseStart_1637235 : Nat := 118140960795 + 1637235 * 2 ^ 59
def prefixEnd_1637235 : Nat := 4983230072969 + 3 ^ 40 * 1637235 * 2
def baseEnd_1637235 : Nat := 840688499364007044232999

theorem tailTrace_1637235 : CollatzResearch.WordTrace tailWord_1637235 prefixEnd_1637235 840688499364007044232999 := by
  unfold tailWord_1637235
  simp only [CollatzResearch.WordTrace]
  refine ⟨59714866223584687321625159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39809910815723124881083439 59714866223584687321625159)
  ·
    refine ⟨89572299335377030982437739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59714866223584687321625159 89572299335377030982437739)
    ·
      refine ⟨134358449003065546473656609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89572299335377030982437739 134358449003065546473656609)
      ·
        refine ⟨100768836752299159855242457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134358449003065546473656609 100768836752299159855242457)
        ·
          refine ⟨75576627564224369891431843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100768836752299159855242457 75576627564224369891431843)
          ·
            refine ⟨113364941346336554837147765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75576627564224369891431843 113364941346336554837147765)
            ·
              refine ⟨10627963251219052015982603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 113364941346336554837147765 10627963251219052015982603)
              ·
                refine ⟨15941944876828578023973905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10627963251219052015982603 15941944876828578023973905)
                ·
                  refine ⟨11956458657621433517980429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15941944876828578023973905 11956458657621433517980429)
                  ·
                    refine ⟨4483671996608037569242661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11956458657621433517980429 4483671996608037569242661)
                    ·
                      refine ⟨840688499364007044232999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4483671996608037569242661 840688499364007044232999)
                      ·
                        rfl

theorem cell23_1637235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 1, 2, 3, 4].length) (baseStart_1637235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1637235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1637235 prefixEnd_1637235 := by exact prefixLift 1637235
  have htrace : WordTrace (prefixWord ++ tailWord_1637235) baseStart_1637235 baseEnd_1637235 := by
    simpa [prefixWord, tailWord_1637235, baseEnd_1637235] using wordTrace_append hprefix tailTrace_1637235
  have hstable : (prefixWord ++ tailWord_1637235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1637235).length < 2 ^ (prefixWord ++ tailWord_1637235).sum := by decide
  have hdescent : baseEnd_1637235 < baseStart_1637235 := by decide
  rcases family_descends (prefixWord ++ tailWord_1637235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1637245 : List Nat := [1, 4, 1, 1, 2, 1, 3, 1, 1, 8]
def baseStart_1637245 : Nat := 118140960795 + 1637245 * 2 ^ 59
def prefixEnd_1637245 : Nat := 4983230072969 + 3 ^ 40 * 1637245 * 2
def baseEnd_1637245 : Nat := 280231211390184001702651

theorem tailTrace_1637245 : CollatzResearch.WordTrace tailWord_1637245 prefixEnd_1637245 280231211390184001702651 := by
  unfold tailWord_1637245
  simp only [CollatzResearch.WordTrace]
  refine ⟨59715230953548459029489189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39810153969032306019659459 59715230953548459029489189)
  ·
    refine ⟨11196605803790336068029223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 59715230953548459029489189 11196605803790336068029223)
    ·
      refine ⟨16794908705685504102043835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11196605803790336068029223 16794908705685504102043835)
      ·
        refine ⟨25192363058528256153065753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16794908705685504102043835 25192363058528256153065753)
        ·
          refine ⟨18894272293896192114799315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25192363058528256153065753 18894272293896192114799315)
          ·
            refine ⟨28341408440844288172198973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18894272293896192114799315 28341408440844288172198973)
            ·
              refine ⟨10628028165316608064574615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28341408440844288172198973 10628028165316608064574615)
              ·
                refine ⟨15942042247974912096861923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10628028165316608064574615 15942042247974912096861923)
                ·
                  refine ⟨23913063371962368145292885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15942042247974912096861923 23913063371962368145292885)
                  ·
                    refine ⟨280231211390184001702651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 23913063371962368145292885 280231211390184001702651)
                    ·
                      rfl

theorem cell23_1637245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 1, 1, 8].length) (baseStart_1637245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1637245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1637245 prefixEnd_1637245 := by exact prefixLift 1637245
  have htrace : WordTrace (prefixWord ++ tailWord_1637245) baseStart_1637245 baseEnd_1637245 := by
    simpa [prefixWord, tailWord_1637245, baseEnd_1637245] using wordTrace_append hprefix tailTrace_1637245
  have hstable : (prefixWord ++ tailWord_1637245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1637245).length < 2 ^ (prefixWord ++ tailWord_1637245).sum := by decide
  have hdescent : baseEnd_1637245 < baseStart_1637245 := by decide
  rcases family_descends (prefixWord ++ tailWord_1637245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1637265 : List Nat := [1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 4]
def baseStart_1637265 : Nat := 118140960795 + 1637265 * 2 ^ 59
def prefixEnd_1637265 : Nat := 4983230072969 + 3 ^ 40 * 1637265 * 2
def baseEnd_1637265 : Nat := 840703903783641926857861

theorem tailTrace_1637265 : CollatzResearch.WordTrace tailWord_1637265 prefixEnd_1637265 840703903783641926857861 := by
  unfold tailWord_1637265
  simp only [CollatzResearch.WordTrace]
  refine ⟨59715960413476002445217249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39810640275650668296811499 59715960413476002445217249)
  ·
    refine ⟨44786970310107001833912937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59715960413476002445217249 44786970310107001833912937)
    ·
      refine ⟨33590227732580251375434703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44786970310107001833912937 33590227732580251375434703)
      ·
        refine ⟨50385341598870377063152055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33590227732580251375434703 50385341598870377063152055)
        ·
          refine ⟨75578012398305565594728083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50385341598870377063152055 75578012398305565594728083)
          ·
            refine ⟨113367018597458348392092125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75578012398305565594728083 113367018597458348392092125)
            ·
              refine ⟨42512631974046880647034547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 113367018597458348392092125 42512631974046880647034547)
              ·
                refine ⟨63768947961070320970551821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42512631974046880647034547 63768947961070320970551821)
                ·
                  refine ⟨23913355485401370363956933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 63768947961070320970551821 23913355485401370363956933)
                  ·
                    refine ⟨4483754153512756943241925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23913355485401370363956933 4483754153512756943241925)
                    ·
                      refine ⟨840703903783641926857861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4483754153512756943241925 840703903783641926857861)
                      ·
                        rfl

theorem cell23_1637265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 4].length) (baseStart_1637265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1637265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1637265 prefixEnd_1637265 := by exact prefixLift 1637265
  have htrace : WordTrace (prefixWord ++ tailWord_1637265) baseStart_1637265 baseEnd_1637265 := by
    simpa [prefixWord, tailWord_1637265, baseEnd_1637265] using wordTrace_append hprefix tailTrace_1637265
  have hstable : (prefixWord ++ tailWord_1637265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1637265).length < 2 ^ (prefixWord ++ tailWord_1637265).sum := by decide
  have hdescent : baseEnd_1637265 < baseStart_1637265 := by decide
  rcases family_descends (prefixWord ++ tailWord_1637265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1637269 : List Nat := [1, 3, 2, 1, 1, 4, 2, 2, 1, 4, 2]
def baseStart_1637269 : Nat := 118140960795 + 1637269 * 2 ^ 59
def prefixEnd_1637269 : Nat := 4983230072969 + 3 ^ 40 * 1637269 * 2
def baseEnd_1637269 : Nat := 840705957706259911207843

theorem tailTrace_1637269 : CollatzResearch.WordTrace tailWord_1637269 prefixEnd_1637269 840705957706259911207843 := by
  unfold tailWord_1637269
  simp only [CollatzResearch.WordTrace]
  refine ⟨59716106305461511128362861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39810737536974340752241907 59716106305461511128362861)
  ·
    refine ⟨22393539864548066673136073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59716106305461511128362861 22393539864548066673136073)
    ·
      refine ⟨16795154898411050004852055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22393539864548066673136073 16795154898411050004852055)
      ·
        refine ⟨25192732347616575007278083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16795154898411050004852055 25192732347616575007278083)
        ·
          refine ⟨37789098521424862510917125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25192732347616575007278083 37789098521424862510917125)
          ·
            refine ⟨7085455972767161720796961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37789098521424862510917125 7085455972767161720796961)
            ·
              refine ⟨5314091979575371290597721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7085455972767161720796961 5314091979575371290597721)
              ·
                refine ⟨3985568984681528467948291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5314091979575371290597721 3985568984681528467948291)
                ·
                  refine ⟨5978353477022292701922437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3985568984681528467948291 5978353477022292701922437)
                  ·
                    refine ⟨1120941276941679881610457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5978353477022292701922437 1120941276941679881610457)
                    ·
                      refine ⟨840705957706259911207843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1120941276941679881610457 840705957706259911207843)
                      ·
                        rfl

theorem cell23_1637269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 2, 2, 1, 4, 2].length) (baseStart_1637269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1637269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1637269 prefixEnd_1637269 := by exact prefixLift 1637269
  have htrace : WordTrace (prefixWord ++ tailWord_1637269) baseStart_1637269 baseEnd_1637269 := by
    simpa [prefixWord, tailWord_1637269, baseEnd_1637269] using wordTrace_append hprefix tailTrace_1637269
  have hstable : (prefixWord ++ tailWord_1637269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1637269).length < 2 ^ (prefixWord ++ tailWord_1637269).sum := by decide
  have hdescent : baseEnd_1637269 < baseStart_1637269 := by decide
  rcases family_descends (prefixWord ++ tailWord_1637269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1637315 : List Nat := [1, 1, 1, 3, 1, 1, 2, 4, 1, 1, 7]
def baseStart_1637315 : Nat := 118140960795 + 1637315 * 2 ^ 59
def prefixEnd_1637315 : Nat := 4983230072969 + 3 ^ 40 * 1637315 * 2
def baseEnd_1637315 : Nat := 840729577816366731232631

theorem tailTrace_1637315 : CollatzResearch.WordTrace tailWord_1637315 prefixEnd_1637315 840729577816366731232631 := by
  unfold tailWord_1637315
  simp only [CollatzResearch.WordTrace]
  refine ⟨59717784063294860984537399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39811856042196573989691599 59717784063294860984537399)
  ·
    refine ⟨89576676094942291476806099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59717784063294860984537399 89576676094942291476806099)
    ·
      refine ⟨134365014142413437215209149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89576676094942291476806099 134365014142413437215209149)
      ·
        refine ⟨50386880303405038955703431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 134365014142413437215209149 50386880303405038955703431)
        ·
          refine ⟨75580320455107558433555147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50386880303405038955703431 75580320455107558433555147)
          ·
            refine ⟨113370480682661337650332721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75580320455107558433555147 113370480682661337650332721)
            ·
              refine ⟨85027860511996003237749541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 113370480682661337650332721 85027860511996003237749541)
              ·
                refine ⟨15942723845999250607078039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 85027860511996003237749541 15942723845999250607078039)
                ·
                  refine ⟨23914085768998875910617059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15942723845999250607078039 23914085768998875910617059)
                  ·
                    refine ⟨35871128653498313865925589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23914085768998875910617059 35871128653498313865925589)
                    ·
                      refine ⟨840729577816366731232631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 35871128653498313865925589 840729577816366731232631)
                      ·
                        rfl

theorem cell23_1637315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 1, 1, 7].length) (baseStart_1637315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1637315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1637315 prefixEnd_1637315 := by exact prefixLift 1637315
  have htrace : WordTrace (prefixWord ++ tailWord_1637315) baseStart_1637315 baseEnd_1637315 := by
    simpa [prefixWord, tailWord_1637315, baseEnd_1637315] using wordTrace_append hprefix tailTrace_1637315
  have hstable : (prefixWord ++ tailWord_1637315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1637315).length < 2 ^ (prefixWord ++ tailWord_1637315).sum := by decide
  have hdescent : baseEnd_1637315 < baseStart_1637315 := by decide
  rcases family_descends (prefixWord ++ tailWord_1637315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1637322 : List Nat := [3, 1, 2, 1, 2, 1, 1, 5, 2, 5]
def baseStart_1637322 : Nat := 118140960795 + 1637322 * 2 ^ 59
def prefixEnd_1637322 : Nat := 4983230072969 + 3 ^ 40 * 1637322 * 2
def baseEnd_1637322 : Nat := 280244390726982734615033

theorem tailTrace_1637322 : CollatzResearch.WordTrace tailWord_1637322 prefixEnd_1637322 280244390726982734615033 := by
  unfold tailWord_1637322
  simp only [CollatzResearch.WordTrace]
  refine ⟨14929509843567375295010555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39812026249513000786694813 14929509843567375295010555)
  ·
    refine ⟨22394264765351062942515833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14929509843567375295010555 22394264765351062942515833)
    ·
      refine ⟨16795698574013297206886875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22394264765351062942515833 16795698574013297206886875)
      ·
        refine ⟨25193547861019945810330313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16795698574013297206886875 25193547861019945810330313)
        ·
          refine ⟨18895160895764959357747735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25193547861019945810330313 18895160895764959357747735)
          ·
            refine ⟨28342741343647439036621603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18895160895764959357747735 28342741343647439036621603)
            ·
              refine ⟨42514112015471158554932405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28342741343647439036621603 42514112015471158554932405)
              ·
                refine ⟨3985698001450421114524913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 42514112015471158554932405 3985698001450421114524913)
                ·
                  refine ⟨2989273501087815835893685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3985698001450421114524913 2989273501087815835893685)
                  ·
                    refine ⟨280244390726982734615033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2989273501087815835893685 280244390726982734615033)
                    ·
                      rfl

theorem cell23_1637322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 5, 2, 5].length) (baseStart_1637322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1637322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1637322 prefixEnd_1637322 := by exact prefixLift 1637322
  have htrace : WordTrace (prefixWord ++ tailWord_1637322) baseStart_1637322 baseEnd_1637322 := by
    simpa [prefixWord, tailWord_1637322, baseEnd_1637322] using wordTrace_append hprefix tailTrace_1637322
  have hstable : (prefixWord ++ tailWord_1637322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1637322).length < 2 ^ (prefixWord ++ tailWord_1637322).sum := by decide
  have hdescent : baseEnd_1637322 < baseStart_1637322 := by decide
  rcases family_descends (prefixWord ++ tailWord_1637322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1637326 : List Nat := [4, 1, 1, 1, 2, 5, 1, 3, 5]
def baseStart_1637326 : Nat := 118140960795 + 1637326 * 2 ^ 59
def prefixEnd_1637326 : Nat := 4983230072969 + 3 ^ 40 * 1637326 * 2
def baseEnd_1637326 : Nat := 93415025122618465355009

theorem tailTrace_1637326 : CollatzResearch.WordTrace tailWord_1637326 prefixEnd_1637326 93415025122618465355009 := by
  unfold tailWord_1637326
  simp only [CollatzResearch.WordTrace]
  refine ⟨7464773158281876232898479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39812123510836673242125221 7464773158281876232898479)
  ·
    refine ⟨11197159737422814349347719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7464773158281876232898479 11197159737422814349347719)
    ·
      refine ⟨16795739606134221524021579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11197159737422814349347719 16795739606134221524021579)
      ·
        refine ⟨25193609409201332286032369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16795739606134221524021579 25193609409201332286032369)
        ·
          refine ⟨18895207056900999214524277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25193609409201332286032369 18895207056900999214524277)
          ·
            refine ⟨1771425661584468676361651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 18895207056900999214524277 1771425661584468676361651)
            ·
              refine ⟨2657138492376703014542477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1771425661584468676361651 2657138492376703014542477)
              ·
                refine ⟨996426934641263630453429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2657138492376703014542477 996426934641263630453429)
                ·
                  refine ⟨93415025122618465355009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 996426934641263630453429 93415025122618465355009)
                  ·
                    rfl

theorem cell23_1637326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 5, 1, 3, 5].length) (baseStart_1637326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1637326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1637326 prefixEnd_1637326 := by exact prefixLift 1637326
  have htrace : WordTrace (prefixWord ++ tailWord_1637326) baseStart_1637326 baseEnd_1637326 := by
    simpa [prefixWord, tailWord_1637326, baseEnd_1637326] using wordTrace_append hprefix tailTrace_1637326
  have hstable : (prefixWord ++ tailWord_1637326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1637326).length < 2 ^ (prefixWord ++ tailWord_1637326).sum := by decide
  have hdescent : baseEnd_1637326 < baseStart_1637326 := by decide
  rcases family_descends (prefixWord ++ tailWord_1637326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1637394 : List Nat := [3, 2, 5, 1, 2, 1, 2, 2, 5]
def baseStart_1637394 : Nat := 118140960795 + 1637394 * 2 ^ 59
def prefixEnd_1637394 : Nat := 4983230072969 + 3 ^ 40 * 1637394 * 2
def baseEnd_1637394 : Nat := 93418904754230213571641

theorem tailTrace_1637394 : CollatzResearch.WordTrace tailWord_1637394 prefixEnd_1637394 93418904754230213571641 := by
  unfold tailWord_1637394
  simp only [CollatzResearch.WordTrace]
  refine ⟨14930166357502164369165809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39813776953339104984442157 14930166357502164369165809)
  ·
    refine ⟨11197624768126623276874357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14930166357502164369165809 11197624768126623276874357)
    ·
      refine ⟨1049777322011870932206971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 11197624768126623276874357 1049777322011870932206971)
      ·
        refine ⟨1574665983017806398310457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1049777322011870932206971 1574665983017806398310457)
        ·
          refine ⟨1180999487263354798732843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1574665983017806398310457 1180999487263354798732843)
          ·
            refine ⟨1771499230895032198099265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1180999487263354798732843 1771499230895032198099265)
            ·
              refine ⟨1328624423171274148574449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1771499230895032198099265 1328624423171274148574449)
              ·
                refine ⟨996468317378455611430837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1328624423171274148574449 996468317378455611430837)
                ·
                  refine ⟨93418904754230213571641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 996468317378455611430837 93418904754230213571641)
                  ·
                    rfl

theorem cell23_1637394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 2, 1, 2, 2, 5].length) (baseStart_1637394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1637394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1637394 prefixEnd_1637394 := by exact prefixLift 1637394
  have htrace : WordTrace (prefixWord ++ tailWord_1637394) baseStart_1637394 baseEnd_1637394 := by
    simpa [prefixWord, tailWord_1637394, baseEnd_1637394] using wordTrace_append hprefix tailTrace_1637394
  have hstable : (prefixWord ++ tailWord_1637394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1637394).length < 2 ^ (prefixWord ++ tailWord_1637394).sum := by decide
  have hdescent : baseEnd_1637394 < baseStart_1637394 := by decide
  rcases family_descends (prefixWord ++ tailWord_1637394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1637399 : List Nat := [1, 1, 3, 5, 1, 1, 1, 4, 6]
def baseStart_1637399 : Nat := 118140960795 + 1637399 * 2 ^ 59
def prefixEnd_1637399 : Nat := 4983230072969 + 3 ^ 40 * 1637399 * 2
def baseEnd_1637399 : Nat := 93419190021260489175805

theorem tailTrace_1637399 : CollatzResearch.WordTrace tailWord_1637399 prefixEnd_1637399 93419190021260489175805 := by
  unfold tailWord_1637399
  simp only [CollatzResearch.WordTrace]
  refine ⟨59720847794990543330595251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39813898529993695553730167 59720847794990543330595251)
  ·
    refine ⟨89581271692485814995892877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59720847794990543330595251 89581271692485814995892877)
    ·
      refine ⟨33592976884682180623459829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89581271692485814995892877 33592976884682180623459829)
      ·
        refine ⟨3149341582938954433449359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 33592976884682180623459829 3149341582938954433449359)
        ·
          refine ⟨4724012374408431650174039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3149341582938954433449359 4724012374408431650174039)
          ·
            refine ⟨7086018561612647475261059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4724012374408431650174039 7086018561612647475261059)
            ·
              refine ⟨10629027842418971212891589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7086018561612647475261059 10629027842418971212891589)
              ·
                refine ⟨1992942720453557102417173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10629027842418971212891589 1992942720453557102417173)
                ·
                  refine ⟨93419190021260489175805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1992942720453557102417173 93419190021260489175805)
                  ·
                    rfl

theorem cell23_1637399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 4, 6].length) (baseStart_1637399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1637399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1637399 prefixEnd_1637399 := by exact prefixLift 1637399
  have htrace : WordTrace (prefixWord ++ tailWord_1637399) baseStart_1637399 baseEnd_1637399 := by
    simpa [prefixWord, tailWord_1637399, baseEnd_1637399] using wordTrace_append hprefix tailTrace_1637399
  have hstable : (prefixWord ++ tailWord_1637399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1637399).length < 2 ^ (prefixWord ++ tailWord_1637399).sum := by decide
  have hdescent : baseEnd_1637399 < baseStart_1637399 := by decide
  rcases family_descends (prefixWord ++ tailWord_1637399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1637402 : List Nat := [3, 1, 1, 3, 1, 2, 2, 1, 1, 2, 6]
def baseStart_1637402 : Nat := 118140960795 + 1637402 * 2 ^ 59
def prefixEnd_1637402 : Nat := 4983230072969 + 3 ^ 40 * 1637402 * 2
def baseEnd_1637402 : Nat := 840774250633307890844731

theorem tailTrace_1637402 : CollatzResearch.WordTrace tailWord_1637402 prefixEnd_1637402 840774250633307890844731 := by
  unfold tailWord_1637402
  simp only [CollatzResearch.WordTrace]
  refine ⟨14930239303494918710738615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39813971475986449895302973 14930239303494918710738615)
  ·
    refine ⟨22395358955242378066107923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14930239303494918710738615 22395358955242378066107923)
    ·
      refine ⟨33593038432863567099161885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22395358955242378066107923 33593038432863567099161885)
      ·
        refine ⟨12597389412323837662185707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33593038432863567099161885 12597389412323837662185707)
        ·
          refine ⟨18896084118485756493278561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12597389412323837662185707 18896084118485756493278561)
          ·
            refine ⟨14172063088864317369958921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18896084118485756493278561 14172063088864317369958921)
            ·
              refine ⟨10629047316648238027469191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14172063088864317369958921 10629047316648238027469191)
              ·
                refine ⟨15943570974972357041203787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10629047316648238027469191 15943570974972357041203787)
                ·
                  refine ⟨23915356462458535561805681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15943570974972357041203787 23915356462458535561805681)
                  ·
                    refine ⟨17936517346843901671354261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23915356462458535561805681 17936517346843901671354261)
                    ·
                      refine ⟨840774250633307890844731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 17936517346843901671354261 840774250633307890844731)
                      ·
                        rfl

theorem cell23_1637402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 1, 1, 2, 6].length) (baseStart_1637402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1637402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1637402 prefixEnd_1637402 := by exact prefixLift 1637402
  have htrace : WordTrace (prefixWord ++ tailWord_1637402) baseStart_1637402 baseEnd_1637402 := by
    simpa [prefixWord, tailWord_1637402, baseEnd_1637402] using wordTrace_append hprefix tailTrace_1637402
  have hstable : (prefixWord ++ tailWord_1637402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1637402).length < 2 ^ (prefixWord ++ tailWord_1637402).sum := by decide
  have hdescent : baseEnd_1637402 < baseStart_1637402 := by decide
  rcases family_descends (prefixWord ++ tailWord_1637402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1637419 : List Nat := [1, 1, 1, 1, 2, 1, 6, 2, 1, 5, 2]
def baseStart_1637419 : Nat := 118140960795 + 1637419 * 2 ^ 59
def prefixEnd_1637419 : Nat := 4983230072969 + 3 ^ 40 * 1637419 * 2
def baseEnd_1637419 : Nat := 840782979804434324332153

theorem tailTrace_1637419 : CollatzResearch.WordTrace tailWord_1637419 prefixEnd_1637419 840782979804434324332153 := by
  unfold tailWord_1637419
  simp only [CollatzResearch.WordTrace]
  refine ⟨59721577254918086746323311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39814384836612057830882207 59721577254918086746323311)
  ·
    refine ⟨89582365882377130119484967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59721577254918086746323311 89582365882377130119484967)
    ·
      refine ⟨134373548823565695179227451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89582365882377130119484967 134373548823565695179227451)
      ·
        refine ⟨201560323235348542768841177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134373548823565695179227451 201560323235348542768841177)
        ·
          refine ⟨151170242426511407076630883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 201560323235348542768841177 151170242426511407076630883)
          ·
            refine ⟨226755363639767110614946325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 151170242426511407076630883 226755363639767110614946325)
            ·
              refine ⟨10629157670614083310075609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 226755363639767110614946325 10629157670614083310075609)
              ·
                refine ⟨7971868252960562482556707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10629157670614083310075609 7971868252960562482556707)
                ·
                  refine ⟨11957802379440843723835061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7971868252960562482556707 11957802379440843723835061)
                  ·
                    refine ⟨1121043973072579099109537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11957802379440843723835061 1121043973072579099109537)
                    ·
                      refine ⟨840782979804434324332153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1121043973072579099109537 840782979804434324332153)
                      ·
                        rfl

theorem cell23_1637419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 2, 1, 5, 2].length) (baseStart_1637419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1637419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1637419 prefixEnd_1637419 := by exact prefixLift 1637419
  have htrace : WordTrace (prefixWord ++ tailWord_1637419) baseStart_1637419 baseEnd_1637419 := by
    simpa [prefixWord, tailWord_1637419, baseEnd_1637419] using wordTrace_append hprefix tailTrace_1637419
  have hstable : (prefixWord ++ tailWord_1637419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1637419).length < 2 ^ (prefixWord ++ tailWord_1637419).sum := by decide
  have hdescent : baseEnd_1637419 < baseStart_1637419 := by decide
  rcases family_descends (prefixWord ++ tailWord_1637419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1637426 : List Nat := [3, 2, 1, 1, 2, 2, 3, 2, 3, 1, 3]
def baseStart_1637426 : Nat := 118140960795 + 1637426 * 2 ^ 59
def prefixEnd_1637426 : Nat := 4983230072969 + 3 ^ 40 * 1637426 * 2
def baseEnd_1637426 : Nat := 840786574169015796944621

theorem tailTrace_1637426 : CollatzResearch.WordTrace tailWord_1637426 prefixEnd_1637426 840786574169015796944621 := by
  unfold tailWord_1637426
  simp only [CollatzResearch.WordTrace]
  refine ⟨14930458141473181735457033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39814555043928484627885421 14930458141473181735457033)
  ·
    refine ⟨11197843606104886301592775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14930458141473181735457033 11197843606104886301592775)
    ·
      refine ⟨16796765409157329452389163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11197843606104886301592775 16796765409157329452389163)
      ·
        refine ⟨25195148113735994178583745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16796765409157329452389163 25195148113735994178583745)
        ·
          refine ⟨18896361085301995633937809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25195148113735994178583745 18896361085301995633937809)
          ·
            refine ⟨14172270813976496725453357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18896361085301995633937809 14172270813976496725453357)
            ·
              refine ⟨5314601555241186272045009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14172270813976496725453357 5314601555241186272045009)
              ·
                refine ⟨3985951166430889704033757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5314601555241186272045009 3985951166430889704033757)
                ·
                  refine ⟨1494731687411583639012659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3985951166430889704033757 1494731687411583639012659)
                  ·
                    refine ⟨2242097531117375458518989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1494731687411583639012659 2242097531117375458518989)
                    ·
                      refine ⟨840786574169015796944621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2242097531117375458518989 840786574169015796944621)
                      ·
                        rfl

theorem cell23_1637426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 3, 2, 3, 1, 3].length) (baseStart_1637426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1637426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1637426 prefixEnd_1637426 := by exact prefixLift 1637426
  have htrace : WordTrace (prefixWord ++ tailWord_1637426) baseStart_1637426 baseEnd_1637426 := by
    simpa [prefixWord, tailWord_1637426, baseEnd_1637426] using wordTrace_append hprefix tailTrace_1637426
  have hstable : (prefixWord ++ tailWord_1637426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1637426).length < 2 ^ (prefixWord ++ tailWord_1637426).sum := by decide
  have hdescent : baseEnd_1637426 < baseStart_1637426 := by decide
  rcases family_descends (prefixWord ++ tailWord_1637426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1637429 : List Nat := [1, 3, 3, 1, 1, 1, 1, 6, 1, 5]
def baseStart_1637429 : Nat := 118140960795 + 1637429 * 2 ^ 59
def prefixEnd_1637429 : Nat := 4983230072969 + 3 ^ 40 * 1637429 * 2
def baseEnd_1637429 : Nat := 280262704870326428402369

theorem tailTrace_1637429 : CollatzResearch.WordTrace tailWord_1637429 prefixEnd_1637429 280262704870326428402369 := by
  unfold tailWord_1637429
  simp only [CollatzResearch.WordTrace]
  refine ⟨59721941984881858454187341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39814627989921238969458227 59721941984881858454187341)
  ·
    refine ⟨22395728244330696920320253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59721941984881858454187341 22395728244330696920320253)
    ·
      refine ⟨8398398091624011345120095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22395728244330696920320253 8398398091624011345120095)
      ·
        refine ⟨12597597137436017017680143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8398398091624011345120095 12597597137436017017680143)
        ·
          refine ⟨18896395706154025526520215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12597597137436017017680143 18896395706154025526520215)
          ·
            refine ⟨28344593559231038289780323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18896395706154025526520215 28344593559231038289780323)
            ·
              refine ⟨42516890338846557434670485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28344593559231038289780323 42516890338846557434670485)
              ·
                refine ⟨1992979234633432379750179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 42516890338846557434670485 1992979234633432379750179)
                ·
                  refine ⟨2989468851950148569625269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1992979234633432379750179 2989468851950148569625269)
                  ·
                    refine ⟨280262704870326428402369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2989468851950148569625269 280262704870326428402369)
                    ·
                      rfl

theorem cell23_1637429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 6, 1, 5].length) (baseStart_1637429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1637429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1637429 prefixEnd_1637429 := by exact prefixLift 1637429
  have htrace : WordTrace (prefixWord ++ tailWord_1637429) baseStart_1637429 baseEnd_1637429 := by
    simpa [prefixWord, tailWord_1637429, baseEnd_1637429] using wordTrace_append hprefix tailTrace_1637429
  have hstable : (prefixWord ++ tailWord_1637429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1637429).length < 2 ^ (prefixWord ++ tailWord_1637429).sum := by decide
  have hdescent : baseEnd_1637429 < baseStart_1637429 := by decide
  rcases family_descends (prefixWord ++ tailWord_1637429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1637436 : List Nat := [2, 2, 2, 2, 2, 3, 1, 1, 1, 5, 2]
def baseStart_1637436 : Nat := 118140960795 + 1637436 * 2 ^ 59
def prefixEnd_1637436 : Nat := 4983230072969 + 3 ^ 40 * 1637436 * 2
def baseEnd_1637436 : Nat := 840791708975560757819575

theorem tailTrace_1637436 : CollatzResearch.WordTrace tailWord_1637436 prefixEnd_1637436 840791708975560757819575 := by
  unfold tailWord_1637436
  simp only [CollatzResearch.WordTrace]
  refine ⟨29861098647928249324846081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39814798197237665766461441 29861098647928249324846081)
  ·
    refine ⟨22395823985946186993634561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29861098647928249324846081 22395823985946186993634561)
    ·
      refine ⟨16796867989459640245225921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22395823985946186993634561 16796867989459640245225921)
      ·
        refine ⟨12597650992094730183919441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16796867989459640245225921 12597650992094730183919441)
        ·
          refine ⟨9448238244071047637939581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12597650992094730183919441 9448238244071047637939581)
          ·
            refine ⟨3543089341526642864227343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9448238244071047637939581 3543089341526642864227343)
            ·
              refine ⟨5314634012289964296341015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3543089341526642864227343 5314634012289964296341015)
              ·
                refine ⟨7971951018434946444511523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5314634012289964296341015 7971951018434946444511523)
                ·
                  refine ⟨11957926527652419666767285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7971951018434946444511523 11957926527652419666767285)
                  ·
                    refine ⟨1121055611967414343759433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11957926527652419666767285 1121055611967414343759433)
                    ·
                      refine ⟨840791708975560757819575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1121055611967414343759433 840791708975560757819575)
                      ·
                        rfl

theorem cell23_1637436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 1, 1, 1, 5, 2].length) (baseStart_1637436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1637436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1637436 prefixEnd_1637436 := by exact prefixLift 1637436
  have htrace : WordTrace (prefixWord ++ tailWord_1637436) baseStart_1637436 baseEnd_1637436 := by
    simpa [prefixWord, tailWord_1637436, baseEnd_1637436] using wordTrace_append hprefix tailTrace_1637436
  have hstable : (prefixWord ++ tailWord_1637436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1637436).length < 2 ^ (prefixWord ++ tailWord_1637436).sum := by decide
  have hdescent : baseEnd_1637436 < baseStart_1637436 := by decide
  rcases family_descends (prefixWord ++ tailWord_1637436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1637443 : List Nat := [1, 1, 1, 3, 1, 2, 6, 3, 1, 1, 3]
def baseStart_1637443 : Nat := 118140960795 + 1637443 * 2 ^ 59
def prefixEnd_1637443 : Nat := 4983230072969 + 3 ^ 40 * 1637443 * 2
def baseEnd_1637443 : Nat := 840795303340142230432043

theorem tailTrace_1637443 : CollatzResearch.WordTrace tailWord_1637443 prefixEnd_1637443 840795303340142230432043 := by
  unfold tailWord_1637443
  simp only [CollatzResearch.WordTrace]
  refine ⟨59722452606831138845196983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39814968404554092563464655 59722452606831138845196983)
  ·
    refine ⟨89583678910246708267795475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59722452606831138845196983 89583678910246708267795475)
    ·
      refine ⟨134375518365370062401693213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89583678910246708267795475 134375518365370062401693213)
      ·
        refine ⟨50390819387013773400634955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 134375518365370062401693213 50390819387013773400634955)
        ·
          refine ⟨75586229080520660100952433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50390819387013773400634955 75586229080520660100952433)
          ·
            refine ⟨56689671810390495075714325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75586229080520660100952433 56689671810390495075714325)
            ·
              refine ⟨2657328366112054456674109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 56689671810390495075714325 2657328366112054456674109)
              ·
                refine ⟨996498137292020421252791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2657328366112054456674109 996498137292020421252791)
                ·
                  refine ⟨1494747205938030631879187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 996498137292020421252791 1494747205938030631879187)
                  ·
                    refine ⟨2242120808907045947818781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1494747205938030631879187 2242120808907045947818781)
                    ·
                      refine ⟨840795303340142230432043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2242120808907045947818781 840795303340142230432043)
                      ·
                        rfl

theorem cell23_1637443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 6, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 6, 3, 1, 1, 3].length) (baseStart_1637443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1637443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1637443 prefixEnd_1637443 := by exact prefixLift 1637443
  have htrace : WordTrace (prefixWord ++ tailWord_1637443) baseStart_1637443 baseEnd_1637443 := by
    simpa [prefixWord, tailWord_1637443, baseEnd_1637443] using wordTrace_append hprefix tailTrace_1637443
  have hstable : (prefixWord ++ tailWord_1637443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1637443).length < 2 ^ (prefixWord ++ tailWord_1637443).sum := by decide
  have hdescent : baseEnd_1637443 < baseStart_1637443 := by decide
  rcases family_descends (prefixWord ++ tailWord_1637443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1637470 : List Nat := [4, 4, 1, 1, 1, 1, 1, 2, 1, 5, 2]
def baseStart_1637470 : Nat := 118140960795 + 1637470 * 2 ^ 59
def prefixEnd_1637470 : Nat := 4983230072969 + 3 ^ 40 * 1637470 * 2
def baseEnd_1637470 : Nat := 840809167317813624794419

theorem tailTrace_1637470 : CollatzResearch.WordTrace tailWord_1637470 prefixEnd_1637470 840809167317813624794419 := by
  unfold tailWord_1637470
  simp only [CollatzResearch.WordTrace]
  refine ⟨7465429672216665307053733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39815624918488881637619909 7465429672216665307053733)
  ·
    refine ⟨1399768063540624745072575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7465429672216665307053733 1399768063540624745072575)
    ·
      refine ⟨2099652095310937117608863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1399768063540624745072575 2099652095310937117608863)
      ·
        refine ⟨3149478142966405676413295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2099652095310937117608863 3149478142966405676413295)
        ·
          refine ⟨4724217214449608514619943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3149478142966405676413295 4724217214449608514619943)
          ·
            refine ⟨7086325821674412771929915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4724217214449608514619943 7086325821674412771929915)
            ·
              refine ⟨10629488732511619157894873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7086325821674412771929915 10629488732511619157894873)
              ·
                refine ⟨7972116549383714368421155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10629488732511619157894873 7972116549383714368421155)
                ·
                  refine ⟨11958174824075571552631733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7972116549383714368421155 11958174824075571552631733)
                  ·
                    refine ⟨1121078889757084833059225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11958174824075571552631733 1121078889757084833059225)
                    ·
                      refine ⟨840809167317813624794419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1121078889757084833059225 840809167317813624794419)
                      ·
                        rfl

theorem cell23_1637470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 2, 1, 5, 2].length) (baseStart_1637470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1637470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1637470 prefixEnd_1637470 := by exact prefixLift 1637470
  have htrace : WordTrace (prefixWord ++ tailWord_1637470) baseStart_1637470 baseEnd_1637470 := by
    simpa [prefixWord, tailWord_1637470, baseEnd_1637470] using wordTrace_append hprefix tailTrace_1637470
  have hstable : (prefixWord ++ tailWord_1637470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1637470).length < 2 ^ (prefixWord ++ tailWord_1637470).sum := by decide
  have hdescent : baseEnd_1637470 < baseStart_1637470 := by decide
  rcases family_descends (prefixWord ++ tailWord_1637470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1637472 : List Nat := [2, 1, 1, 3, 2, 2, 2, 10]
def baseStart_1637472 : Nat := 118140960795 + 1637472 * 2 ^ 59
def prefixEnd_1637472 : Nat := 4983230072969 + 3 ^ 40 * 1637472 * 2
def baseEnd_1637472 : Nat := 31141118306634170998867

theorem tailTrace_1637472 : CollatzResearch.WordTrace tailWord_1637472 prefixEnd_1637472 31141118306634170998867 := by
  unfold tailWord_1637472
  simp only [CollatzResearch.WordTrace]
  refine ⟨29861755161863038399001335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39815673549150717865335113 29861755161863038399001335)
  ·
    refine ⟨44792632742794557598502003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29861755161863038399001335 44792632742794557598502003)
    ·
      refine ⟨67188949114191836397753005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44792632742794557598502003 67188949114191836397753005)
      ·
        refine ⟨25195855917821938649157377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67188949114191836397753005 25195855917821938649157377)
        ·
          refine ⟨18896891938366453986868033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25195855917821938649157377 18896891938366453986868033)
          ·
            refine ⟨14172668953774840490151025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18896891938366453986868033 14172668953774840490151025)
            ·
              refine ⟨10629501715331130367613269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14172668953774840490151025 10629501715331130367613269)
              ·
                refine ⟨31141118306634170998867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 10629501715331130367613269 31141118306634170998867)
                ·
                  rfl

theorem cell23_1637472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 10].length) (baseStart_1637472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1637472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1637472 prefixEnd_1637472 := by exact prefixLift 1637472
  have htrace : WordTrace (prefixWord ++ tailWord_1637472) baseStart_1637472 baseEnd_1637472 := by
    simpa [prefixWord, tailWord_1637472, baseEnd_1637472] using wordTrace_append hprefix tailTrace_1637472
  have hstable : (prefixWord ++ tailWord_1637472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1637472).length < 2 ^ (prefixWord ++ tailWord_1637472).sum := by decide
  have hdescent : baseEnd_1637472 < baseStart_1637472 := by decide
  rcases family_descends (prefixWord ++ tailWord_1637472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1637479 : List Nat := [1, 1, 5, 1, 1, 4, 1, 1, 1, 1, 6]
def baseStart_1637479 : Nat := 118140960795 + 1637479 * 2 ^ 59
def prefixEnd_1637479 : Nat := 4983230072969 + 3 ^ 40 * 1637479 * 2
def baseEnd_1637479 : Nat := 840813788643704089581877

theorem tailTrace_1637479 : CollatzResearch.WordTrace tailWord_1637479 prefixEnd_1637479 840813788643704089581877 := by
  unfold tailWord_1637479
  simp only [CollatzResearch.WordTrace]
  refine ⟨59723765634700716993507491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39815843756467144662338327 59723765634700716993507491)
  ·
    refine ⟨89585648452051075490261237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59723765634700716993507491 89585648452051075490261237)
    ·
      refine ⟨8398654542379788327211991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 89585648452051075490261237 8398654542379788327211991)
      ·
        refine ⟨12597981813569682490817987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8398654542379788327211991 12597981813569682490817987)
        ·
          refine ⟨18896972720354523736226981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12597981813569682490817987 18896972720354523736226981)
          ·
            refine ⟨3543182385066473200542559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18896972720354523736226981 3543182385066473200542559)
            ·
              refine ⟨5314773577599709800813839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3543182385066473200542559 5314773577599709800813839)
              ·
                refine ⟨7972160366399564701220759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5314773577599709800813839 7972160366399564701220759)
                ·
                  refine ⟨11958240549599347051831139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7972160366399564701220759 11958240549599347051831139)
                  ·
                    refine ⟨17937360824399020577746709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11958240549599347051831139 17937360824399020577746709)
                    ·
                      refine ⟨840813788643704089581877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 17937360824399020577746709 840813788643704089581877)
                      ·
                        rfl

theorem cell23_1637479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 1, 1, 1, 1, 6].length) (baseStart_1637479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1637479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1637479 prefixEnd_1637479 := by exact prefixLift 1637479
  have htrace : WordTrace (prefixWord ++ tailWord_1637479) baseStart_1637479 baseEnd_1637479 := by
    simpa [prefixWord, tailWord_1637479, baseEnd_1637479] using wordTrace_append hprefix tailTrace_1637479
  have hstable : (prefixWord ++ tailWord_1637479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1637479).length < 2 ^ (prefixWord ++ tailWord_1637479).sum := by decide
  have hdescent : baseEnd_1637479 < baseStart_1637479 := by decide
  rcases family_descends (prefixWord ++ tailWord_1637479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1637499 : List Nat := [1, 1, 1, 1, 1, 4, 1, 6, 1, 3, 3]
def baseStart_1637499 : Nat := 118140960795 + 1637499 * 2 ^ 59
def prefixEnd_1637499 : Nat := 4983230072969 + 3 ^ 40 * 1637499 * 2
def baseEnd_1637499 : Nat := 840824058256794011331785

theorem tailTrace_1637499 : CollatzResearch.WordTrace tailWord_1637499 prefixEnd_1637499 840824058256794011331785 := by
  unfold tailWord_1637499
  simp only [CollatzResearch.WordTrace]
  refine ⟨59724495094628260409235551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39816330063085506939490367 59724495094628260409235551)
  ·
    refine ⟨89586742641942390613853327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59724495094628260409235551 89586742641942390613853327)
    ·
      refine ⟨134380113962913585920779991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89586742641942390613853327 134380113962913585920779991)
      ·
        refine ⟨201570170944370378881169987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134380113962913585920779991 201570170944370378881169987)
        ·
          refine ⟨302355256416555568321754981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 201570170944370378881169987 302355256416555568321754981)
          ·
            refine ⟨56691610578104169060329059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 302355256416555568321754981 56691610578104169060329059)
            ·
              refine ⟨85037415867156253590493589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56691610578104169060329059 85037415867156253590493589)
              ·
                refine ⟨3986128868772949387054387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 85037415867156253590493589 3986128868772949387054387)
                ·
                  refine ⟨5979193303159424080581581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3986128868772949387054387 5979193303159424080581581)
                  ·
                    refine ⟨2242197488684784030218093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5979193303159424080581581 2242197488684784030218093)
                    ·
                      refine ⟨840824058256794011331785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2242197488684784030218093 840824058256794011331785)
                      ·
                        rfl

theorem cell23_1637499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 6, 1, 3, 3].length) (baseStart_1637499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1637499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1637499 prefixEnd_1637499 := by exact prefixLift 1637499
  have htrace : WordTrace (prefixWord ++ tailWord_1637499) baseStart_1637499 baseEnd_1637499 := by
    simpa [prefixWord, tailWord_1637499, baseEnd_1637499] using wordTrace_append hprefix tailTrace_1637499
  have hstable : (prefixWord ++ tailWord_1637499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1637499).length < 2 ^ (prefixWord ++ tailWord_1637499).sum := by decide
  have hdescent : baseEnd_1637499 < baseStart_1637499 := by decide
  rcases family_descends (prefixWord ++ tailWord_1637499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1637533 : List Nat := [1, 4, 2, 1, 1, 2, 3, 3, 2, 1, 3]
def baseStart_1637533 : Nat := 118140960795 + 1637533 * 2 ^ 59
def prefixEnd_1637533 : Nat := 4983230072969 + 3 ^ 40 * 1637533 * 2
def baseEnd_1637533 : Nat := 840841516599046878306629

theorem tailTrace_1637533 : CollatzResearch.WordTrace tailWord_1637533 prefixEnd_1637533 840841516599046878306629 := by
  unfold tailWord_1637533
  simp only [CollatzResearch.WordTrace]
  refine ⟨59725735176505084215973253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39817156784336722810648835 59725735176505084215973253)
  ·
    refine ⟨11198575345594703290494985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 59725735176505084215973253 11198575345594703290494985)
    ·
      refine ⟨8398931509196027467871239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11198575345594703290494985 8398931509196027467871239)
      ·
        refine ⟨12598397263794041201806859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8398931509196027467871239 12598397263794041201806859)
        ·
          refine ⟨18897595895691061802710289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12598397263794041201806859 18897595895691061802710289)
          ·
            refine ⟨14173196921768296352032717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18897595895691061802710289 14173196921768296352032717)
            ·
              refine ⟨5314948845663111132012269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14173196921768296352032717 5314948845663111132012269)
              ·
                refine ⟨1993105817123666674504601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5314948845663111132012269 1993105817123666674504601)
                ·
                  refine ⟨1494829362842750005878451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1993105817123666674504601 1494829362842750005878451)
                  ·
                    refine ⟨2242244044264125008817677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1494829362842750005878451 2242244044264125008817677)
                    ·
                      refine ⟨840841516599046878306629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2242244044264125008817677 840841516599046878306629)
                      ·
                        rfl

theorem cell23_1637533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 3, 3, 2, 1, 3].length) (baseStart_1637533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1637533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1637533 prefixEnd_1637533 := by exact prefixLift 1637533
  have htrace : WordTrace (prefixWord ++ tailWord_1637533) baseStart_1637533 baseEnd_1637533 := by
    simpa [prefixWord, tailWord_1637533, baseEnd_1637533] using wordTrace_append hprefix tailTrace_1637533
  have hstable : (prefixWord ++ tailWord_1637533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1637533).length < 2 ^ (prefixWord ++ tailWord_1637533).sum := by decide
  have hdescent : baseEnd_1637533 < baseStart_1637533 := by decide
  rcases family_descends (prefixWord ++ tailWord_1637533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1637559 : List Nat := [1, 1, 3, 1, 4, 1, 1, 3, 2, 1, 5]
def baseStart_1637559 : Nat := 118140960795 + 1637559 * 2 ^ 59
def prefixEnd_1637559 : Nat := 4983230072969 + 3 ^ 40 * 1637559 * 2
def baseEnd_1637559 : Nat := 840854867096063776581509

theorem tailTrace_1637559 : CollatzResearch.WordTrace tailWord_1637559 prefixEnd_1637559 840854867096063776581509 := by
  unfold tailWord_1637559
  simp only [CollatzResearch.WordTrace]
  refine ⟨59726683474410890656419731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39817788982940593770946487 59726683474410890656419731)
  ·
    refine ⟨89590025211616335984629597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59726683474410890656419731 89590025211616335984629597)
    ·
      refine ⟨33596259454356125994236099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89590025211616335984629597 33596259454356125994236099)
      ·
        refine ⟨50394389181534188991354149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33596259454356125994236099 50394389181534188991354149)
        ·
          refine ⟨9448947971537660435878903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50394389181534188991354149 9448947971537660435878903)
          ·
            refine ⟨14173421957306490653818355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9448947971537660435878903 14173421957306490653818355)
            ·
              refine ⟨21260132935959735980727533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14173421957306490653818355 21260132935959735980727533)
              ·
                refine ⟨7972549850984900992772825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21260132935959735980727533 7972549850984900992772825)
                ·
                  refine ⟨5979412388238675744579619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7972549850984900992772825 5979412388238675744579619)
                  ·
                    refine ⟨8969118582358013616869429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5979412388238675744579619 8969118582358013616869429)
                    ·
                      refine ⟨840854867096063776581509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8969118582358013616869429 840854867096063776581509)
                      ·
                        rfl

theorem cell23_1637559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 3, 2, 1, 5].length) (baseStart_1637559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1637559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1637559 prefixEnd_1637559 := by exact prefixLift 1637559
  have htrace : WordTrace (prefixWord ++ tailWord_1637559) baseStart_1637559 baseEnd_1637559 := by
    simpa [prefixWord, tailWord_1637559, baseEnd_1637559] using wordTrace_append hprefix tailTrace_1637559
  have hstable : (prefixWord ++ tailWord_1637559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1637559).length < 2 ^ (prefixWord ++ tailWord_1637559).sum := by decide
  have hdescent : baseEnd_1637559 < baseStart_1637559 := by decide
  rcases family_descends (prefixWord ++ tailWord_1637559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1637586 : List Nat := [3, 2, 2, 2, 1, 1, 3, 1, 2, 2, 4]
def baseStart_1637586 : Nat := 118140960795 + 1637586 * 2 ^ 59
def prefixEnd_1637586 : Nat := 4983230072969 + 3 ^ 40 * 1637586 * 2
def baseEnd_1637586 : Nat := 840868731073735170943885

theorem tailTrace_1637586 : CollatzResearch.WordTrace tailWord_1637586 prefixEnd_1637586 840868731073735170943885 := by
  unfold tailWord_1637586
  simp only [CollatzResearch.WordTrace]
  refine ⟨14931917061328268566913153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39818445496875382845101741 14931917061328268566913153)
  ·
    refine ⟨11198937795996201425184865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14931917061328268566913153 11198937795996201425184865)
    ·
      refine ⟨8399203346997151068888649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11198937795996201425184865 8399203346997151068888649)
      ·
        refine ⟨6299402510247863301666487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8399203346997151068888649 6299402510247863301666487)
        ·
          refine ⟨9449103765371794952499731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6299402510247863301666487 9449103765371794952499731)
          ·
            refine ⟨14173655648057692428749597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9449103765371794952499731 14173655648057692428749597)
            ·
              refine ⟨5315120868021634660781099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14173655648057692428749597 5315120868021634660781099)
              ·
                refine ⟨7972681302032451991171649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5315120868021634660781099 7972681302032451991171649)
                ·
                  refine ⟨5979510976524338993378737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7972681302032451991171649 5979510976524338993378737)
                  ·
                    refine ⟨4484633232393254245034053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5979510976524338993378737 4484633232393254245034053)
                    ·
                      refine ⟨840868731073735170943885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4484633232393254245034053 840868731073735170943885)
                      ·
                        rfl

theorem cell23_1637586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 3, 1, 2, 2, 4].length) (baseStart_1637586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1637586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1637586 prefixEnd_1637586 := by exact prefixLift 1637586
  have htrace : WordTrace (prefixWord ++ tailWord_1637586) baseStart_1637586 baseEnd_1637586 := by
    simpa [prefixWord, tailWord_1637586, baseEnd_1637586] using wordTrace_append hprefix tailTrace_1637586
  have hstable : (prefixWord ++ tailWord_1637586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1637586).length < 2 ^ (prefixWord ++ tailWord_1637586).sum := by decide
  have hdescent : baseEnd_1637586 < baseStart_1637586 := by decide
  rcases family_descends (prefixWord ++ tailWord_1637586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1637613 : List Nat := [1, 5, 1, 2, 2, 1, 1, 5, 5]
def baseStart_1637613 : Nat := 118140960795 + 1637613 * 2 ^ 59
def prefixEnd_1637613 : Nat := 4983230072969 + 3 ^ 40 * 1637613 * 2
def baseEnd_1637613 : Nat := 93431399450156285034029

theorem tailTrace_1637613 : CollatzResearch.WordTrace tailWord_1637613 prefixEnd_1637613 93431399450156285034029 := by
  unfold tailWord_1637613
  simp only [CollatzResearch.WordTrace]
  refine ⟨59728653016215257878885493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39819102010810171919256995 59728653016215257878885493)
  ·
    refine ⟨5599561220270180426145515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 59728653016215257878885493 5599561220270180426145515)
    ·
      refine ⟨8399341830405270639218273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5599561220270180426145515 8399341830405270639218273)
      ·
        refine ⟨6299506372803952979413705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8399341830405270639218273 6299506372803952979413705)
        ·
          refine ⟨4724629779602964734560279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6299506372803952979413705 4724629779602964734560279)
          ·
            refine ⟨7086944669404447101840419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4724629779602964734560279 7086944669404447101840419)
            ·
              refine ⟨10630417004106670652760629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7086944669404447101840419 10630417004106670652760629)
              ·
                refine ⟨996601594135000373696309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10630417004106670652760629 996601594135000373696309)
                ·
                  refine ⟨93431399450156285034029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 996601594135000373696309 93431399450156285034029)
                  ·
                    rfl

theorem cell23_1637613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 5, 5].length) (baseStart_1637613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1637613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1637613 prefixEnd_1637613 := by exact prefixLift 1637613
  have htrace : WordTrace (prefixWord ++ tailWord_1637613) baseStart_1637613 baseEnd_1637613 := by
    simpa [prefixWord, tailWord_1637613, baseEnd_1637613] using wordTrace_append hprefix tailTrace_1637613
  have hstable : (prefixWord ++ tailWord_1637613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1637613).length < 2 ^ (prefixWord ++ tailWord_1637613).sum := by decide
  have hdescent : baseEnd_1637613 < baseStart_1637613 := by decide
  rcases family_descends (prefixWord ++ tailWord_1637613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1637646 : List Nat := [4, 1, 1, 2, 1, 3, 1, 2, 1, 3, 4]
def baseStart_1637646 : Nat := 118140960795 + 1637646 * 2 ^ 59
def prefixEnd_1637646 : Nat := 4983230072969 + 3 ^ 40 * 1637646 * 2
def baseEnd_1637646 : Nat := 840899539913004936193609

theorem tailTrace_1637646 : CollatzResearch.WordTrace tailWord_1637646 prefixEnd_1637646 840899539913004936193609 := by
  unfold tailWord_1637646
  simp only [CollatzResearch.WordTrace]
  refine ⟨7466232078136963064354599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39819904416730469676557861 7466232078136963064354599)
  ·
    refine ⟨11199348117205444596531899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7466232078136963064354599 11199348117205444596531899)
    ·
      refine ⟨16799022175808166894797849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11199348117205444596531899 16799022175808166894797849)
      ·
        refine ⟨12599266631856125171098387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16799022175808166894797849 12599266631856125171098387)
        ·
          refine ⟨18898899947784187756647581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12599266631856125171098387 18898899947784187756647581)
          ·
            refine ⟨7087087480419070408742843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18898899947784187756647581 7087087480419070408742843)
            ·
              refine ⟨10630631220628605613114265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7087087480419070408742843 10630631220628605613114265)
              ·
                refine ⟨7972973415471454209835699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10630631220628605613114265 7972973415471454209835699)
                ·
                  refine ⟨11959460123207181314753549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7972973415471454209835699 11959460123207181314753549)
                  ·
                    refine ⟨4484797546202692993032581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11959460123207181314753549 4484797546202692993032581)
                    ·
                      refine ⟨840899539913004936193609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4484797546202692993032581 840899539913004936193609)
                      ·
                        rfl

theorem cell23_1637646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 2, 1, 3, 4].length) (baseStart_1637646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1637646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1637646 prefixEnd_1637646 := by exact prefixLift 1637646
  have htrace : WordTrace (prefixWord ++ tailWord_1637646) baseStart_1637646 baseEnd_1637646 := by
    simpa [prefixWord, tailWord_1637646, baseEnd_1637646] using wordTrace_append hprefix tailTrace_1637646
  have hstable : (prefixWord ++ tailWord_1637646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1637646).length < 2 ^ (prefixWord ++ tailWord_1637646).sum := by decide
  have hdescent : baseEnd_1637646 < baseStart_1637646 := by decide
  rcases family_descends (prefixWord ++ tailWord_1637646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1637659 : List Nat := [1, 1, 1, 1, 1, 1, 5, 1, 1, 6, 4]
def baseStart_1637659 : Nat := 118140960795 + 1637659 * 2 ^ 59
def prefixEnd_1637659 : Nat := 4983230072969 + 3 ^ 40 * 1637659 * 2
def baseEnd_1637659 : Nat := 840906215161513385331049

theorem tailTrace_1637659 : CollatzResearch.WordTrace tailWord_1637659 prefixEnd_1637659 840906215161513385331049 := by
  unfold tailWord_1637659
  simp only [CollatzResearch.WordTrace]
  refine ⟨59730330774048607735060031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39820220516032405156706687 59730330774048607735060031)
  ·
    refine ⟨89595496161072911602590047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59730330774048607735060031 89595496161072911602590047)
    ·
      refine ⟨134393244241609367403885071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89595496161072911602590047 134393244241609367403885071)
      ·
        refine ⟨201589866362414051105827607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134393244241609367403885071 201589866362414051105827607)
        ·
          refine ⟨302384799543621076658741411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 201589866362414051105827607 302384799543621076658741411)
          ·
            refine ⟨453577199315431614988112117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 302384799543621076658741411 453577199315431614988112117)
            ·
              refine ⟨42522862435821713905135511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 453577199315431614988112117 42522862435821713905135511)
              ·
                refine ⟨63784293653732570857703267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42522862435821713905135511 63784293653732570857703267)
                ·
                  refine ⟨95676440480598856286554901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63784293653732570857703267 95676440480598856286554901)
                  ·
                    refine ⟨4484833147528071388432261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 95676440480598856286554901 4484833147528071388432261)
                    ·
                      refine ⟨840906215161513385331049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4484833147528071388432261 840906215161513385331049)
                      ·
                        rfl

theorem cell23_1637659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 1, 1, 6, 4].length) (baseStart_1637659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1637659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1637659 prefixEnd_1637659 := by exact prefixLift 1637659
  have htrace : WordTrace (prefixWord ++ tailWord_1637659) baseStart_1637659 baseEnd_1637659 := by
    simpa [prefixWord, tailWord_1637659, baseEnd_1637659] using wordTrace_append hprefix tailTrace_1637659
  have hstable : (prefixWord ++ tailWord_1637659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1637659).length < 2 ^ (prefixWord ++ tailWord_1637659).sum := by decide
  have hdescent : baseEnd_1637659 < baseStart_1637659 := by decide
  rcases family_descends (prefixWord ++ tailWord_1637659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1637683 : List Nat := [1, 1, 1, 2, 5, 3, 1, 2, 2, 2, 3]
def baseStart_1637683 : Nat := 118140960795 + 1637683 * 2 ^ 59
def prefixEnd_1637683 : Nat := 4983230072969 + 3 ^ 40 * 1637683 * 2
def baseEnd_1637683 : Nat := 840918538697221291430939

theorem tailTrace_1637683 : CollatzResearch.WordTrace tailWord_1637683 prefixEnd_1637683 840918538697221291430939 := by
  unfold tailWord_1637683
  simp only [CollatzResearch.WordTrace]
  refine ⟨59731206125961659833933703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39820804083974439889289135 59731206125961659833933703)
  ·
    refine ⟨89596809188942489750900555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59731206125961659833933703 89596809188942489750900555)
    ·
      refine ⟨134395213783413734626350833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89596809188942489750900555 134395213783413734626350833)
      ·
        refine ⟨100796410337560300969763125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134395213783413734626350833 100796410337560300969763125)
        ·
          refine ⟨9449663469146278215915293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 100796410337560300969763125 9449663469146278215915293)
          ·
            refine ⟨3543623800929854330968235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9449663469146278215915293 3543623800929854330968235)
            ·
              refine ⟨5315435701394781496452353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3543623800929854330968235 5315435701394781496452353)
              ·
                refine ⟨3986576776046086122339265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5315435701394781496452353 3986576776046086122339265)
                ·
                  refine ⟨2989932582034564591754449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3986576776046086122339265 2989932582034564591754449)
                  ·
                    refine ⟨2242449436525923443815837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2989932582034564591754449 2242449436525923443815837)
                    ·
                      refine ⟨840918538697221291430939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2242449436525923443815837 840918538697221291430939)
                      ·
                        rfl

theorem cell23_1637683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 1, 2, 2, 2, 3].length) (baseStart_1637683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1637683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1637683 prefixEnd_1637683 := by exact prefixLift 1637683
  have htrace : WordTrace (prefixWord ++ tailWord_1637683) baseStart_1637683 baseEnd_1637683 := by
    simpa [prefixWord, tailWord_1637683, baseEnd_1637683] using wordTrace_append hprefix tailTrace_1637683
  have hstable : (prefixWord ++ tailWord_1637683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1637683).length < 2 ^ (prefixWord ++ tailWord_1637683).sum := by decide
  have hdescent : baseEnd_1637683 < baseStart_1637683 := by decide
  rcases family_descends (prefixWord ++ tailWord_1637683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1637699 : List Nat := [1, 1, 1, 3, 1, 3, 1, 1, 2, 9]
def baseStart_1637699 : Nat := 118140960795 + 1637699 * 2 ^ 59
def prefixEnd_1637699 : Nat := 4983230072969 + 3 ^ 40 * 1637699 * 2
def baseEnd_1637699 : Nat := 280308918129231076276955

theorem tailTrace_1637699 : CollatzResearch.WordTrace tailWord_1637699 prefixEnd_1637699 280308918129231076276955 := by
  unfold tailWord_1637699
  simp only [CollatzResearch.WordTrace]
  refine ⟨59731789693903694566516151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39821193129269129711010767 59731789693903694566516151)
  ·
    refine ⟨89597684540855541849774227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59731789693903694566516151 89597684540855541849774227)
    ·
      refine ⟨134396526811283312774661341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89597684540855541849774227 134396526811283312774661341)
      ·
        refine ⟨50398697554231242290498003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 134396526811283312774661341 50398697554231242290498003)
        ·
          refine ⟨75598046331346863435747005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50398697554231242290498003 75598046331346863435747005)
          ·
            refine ⟨28349267374255073788405127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75598046331346863435747005 28349267374255073788405127)
            ·
              refine ⟨42523901061382610682607691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28349267374255073788405127 42523901061382610682607691)
              ·
                refine ⟨63785851592073916023911537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42523901061382610682607691 63785851592073916023911537)
                ·
                  refine ⟨47839388694055437017933653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63785851592073916023911537 47839388694055437017933653)
                  ·
                    refine ⟨280308918129231076276955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 47839388694055437017933653 280308918129231076276955)
                    ·
                      rfl

theorem cell23_1637699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 1, 2, 9].length) (baseStart_1637699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1637699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1637699 prefixEnd_1637699 := by exact prefixLift 1637699
  have htrace : WordTrace (prefixWord ++ tailWord_1637699) baseStart_1637699 baseEnd_1637699 := by
    simpa [prefixWord, tailWord_1637699, baseEnd_1637699] using wordTrace_append hprefix tailTrace_1637699
  have hstable : (prefixWord ++ tailWord_1637699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1637699).length < 2 ^ (prefixWord ++ tailWord_1637699).sum := by decide
  have hdescent : baseEnd_1637699 < baseStart_1637699 := by decide
  rcases family_descends (prefixWord ++ tailWord_1637699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1637703 : List Nat := [1, 1, 4, 1, 2, 3, 4, 1, 6]
def baseStart_1637703 : Nat := 118140960795 + 1637703 * 2 ^ 59
def prefixEnd_1637703 : Nat := 4983230072969 + 3 ^ 40 * 1637703 * 2
def baseEnd_1637703 : Nat := 93436534256701245908983

theorem tailTrace_1637703 : CollatzResearch.WordTrace tailWord_1637703 prefixEnd_1637703 93436534256701245908983 := by
  unfold tailWord_1637703
  simp only [CollatzResearch.WordTrace]
  refine ⟨59731935585889203249661763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39821290390592802166441175 59731935585889203249661763)
  ·
    refine ⟨89597903378833804874492645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59731935585889203249661763 89597903378833804874492645)
    ·
      refine ⟨16799606883531338413967371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 89597903378833804874492645 16799606883531338413967371)
      ·
        refine ⟨25199410325297007620951057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16799606883531338413967371 25199410325297007620951057)
        ·
          refine ⟨18899557743972755715713293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25199410325297007620951057 18899557743972755715713293)
          ·
            refine ⟨7087334153989783393392485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18899557743972755715713293 7087334153989783393392485)
            ·
              refine ⟨1328875153873084386261091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7087334153989783393392485 1328875153873084386261091)
              ·
                refine ⟨1993312730809626579391637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1328875153873084386261091 1993312730809626579391637)
                ·
                  refine ⟨93436534256701245908983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1993312730809626579391637 93436534256701245908983)
                  ·
                    rfl

theorem cell23_1637703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 4, 1, 6].length) (baseStart_1637703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1637703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1637703 prefixEnd_1637703 := by exact prefixLift 1637703
  have htrace : WordTrace (prefixWord ++ tailWord_1637703) baseStart_1637703 baseEnd_1637703 := by
    simpa [prefixWord, tailWord_1637703, baseEnd_1637703] using wordTrace_append hprefix tailTrace_1637703
  have hstable : (prefixWord ++ tailWord_1637703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1637703).length < 2 ^ (prefixWord ++ tailWord_1637703).sum := by decide
  have hdescent : baseEnd_1637703 < baseStart_1637703 := by decide
  rcases family_descends (prefixWord ++ tailWord_1637703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1637713 : List Nat := [1, 2, 2, 1, 4, 1, 2, 1, 5, 1, 3]
def baseStart_1637713 : Nat := 118140960795 + 1637713 * 2 ^ 59
def prefixEnd_1637713 : Nat := 4983230072969 + 3 ^ 40 * 1637713 * 2
def baseEnd_1637713 : Nat := 840933943116856174055801

theorem tailTrace_1637713 : CollatzResearch.WordTrace tailWord_1637713 prefixEnd_1637713 840933943116856174055801 := by
  unfold tailWord_1637713
  simp only [CollatzResearch.WordTrace]
  refine ⟨59732300315852974957525793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39821533543901983305017195 59732300315852974957525793)
  ·
    refine ⟨44799225236889731218144345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59732300315852974957525793 44799225236889731218144345)
    ·
      refine ⟨33599418927667298413608259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44799225236889731218144345 33599418927667298413608259)
      ·
        refine ⟨50399128391500947620412389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33599418927667298413608259 50399128391500947620412389)
        ·
          refine ⟨9449836573406427678827323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50399128391500947620412389 9449836573406427678827323)
          ·
            refine ⟨14174754860109641518240985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9449836573406427678827323 14174754860109641518240985)
            ·
              refine ⟨10631066145082231138680739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14174754860109641518240985 10631066145082231138680739)
              ·
                refine ⟨15946599217623346708021109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10631066145082231138680739 15946599217623346708021109)
                ·
                  refine ⟨1494993676652188753876979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 15946599217623346708021109 1494993676652188753876979)
                  ·
                    refine ⟨2242490514978283130815469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1494993676652188753876979 2242490514978283130815469)
                    ·
                      refine ⟨840933943116856174055801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2242490514978283130815469 840933943116856174055801)
                      ·
                        rfl

theorem cell23_1637713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 1, 5, 1, 3].length) (baseStart_1637713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1637713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1637713 prefixEnd_1637713 := by exact prefixLift 1637713
  have htrace : WordTrace (prefixWord ++ tailWord_1637713) baseStart_1637713 baseEnd_1637713 := by
    simpa [prefixWord, tailWord_1637713, baseEnd_1637713] using wordTrace_append hprefix tailTrace_1637713
  have hstable : (prefixWord ++ tailWord_1637713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1637713).length < 2 ^ (prefixWord ++ tailWord_1637713).sum := by decide
  have hdescent : baseEnd_1637713 < baseStart_1637713 := by decide
  rcases family_descends (prefixWord ++ tailWord_1637713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1637740 : List Nat := [2, 2, 1, 1, 5, 1, 2, 2, 2, 3, 2]
def baseStart_1637740 : Nat := 118140960795 + 1637740 * 2 ^ 59
def prefixEnd_1637740 : Nat := 4983230072969 + 3 ^ 40 * 1637740 * 2
def baseEnd_1637740 : Nat := 840947807094527568418177

theorem tailTrace_1637740 : CollatzResearch.WordTrace tailWord_1637740 prefixEnd_1637740 840947807094527568418177 := by
  unfold tailWord_1637740
  simp only [CollatzResearch.WordTrace]
  refine ⟨29866642543377579284379337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39822190057836772379172449 29866642543377579284379337)
  ·
    refine ⟨22399981907533184463284503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29866642543377579284379337 22399981907533184463284503)
    ·
      refine ⟨33599972861299776694926755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22399981907533184463284503 33599972861299776694926755)
      ·
        refine ⟨50399959291949665042390133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33599972861299776694926755 50399959291949665042390133)
        ·
          refine ⟨4724996183620281097724075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 50399959291949665042390133 4724996183620281097724075)
          ·
            refine ⟨7087494275430421646586113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4724996183620281097724075 7087494275430421646586113)
            ·
              refine ⟨5315620706572816234939585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7087494275430421646586113 5315620706572816234939585)
              ·
                refine ⟨3986715529929612176204689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5315620706572816234939585 3986715529929612176204689)
                ·
                  refine ⟨2990036647447209132153517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3986715529929612176204689 2990036647447209132153517)
                  ·
                    refine ⟨1121263742792703424557569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2990036647447209132153517 1121263742792703424557569)
                    ·
                      refine ⟨840947807094527568418177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1121263742792703424557569 840947807094527568418177)
                      ·
                        rfl

theorem cell23_1637740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 3, 2].length) (baseStart_1637740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1637740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1637740 prefixEnd_1637740 := by exact prefixLift 1637740
  have htrace : WordTrace (prefixWord ++ tailWord_1637740) baseStart_1637740 baseEnd_1637740 := by
    simpa [prefixWord, tailWord_1637740, baseEnd_1637740] using wordTrace_append hprefix tailTrace_1637740
  have hstable : (prefixWord ++ tailWord_1637740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1637740).length < 2 ^ (prefixWord ++ tailWord_1637740).sum := by decide
  have hdescent : baseEnd_1637740 < baseStart_1637740 := by decide
  rcases family_descends (prefixWord ++ tailWord_1637740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1637746 : List Nat := [3, 2, 1, 2, 1, 2, 1, 2, 3, 6]
def baseStart_1637746 : Nat := 118140960795 + 1637746 * 2 ^ 59
def prefixEnd_1637746 : Nat := 4983230072969 + 3 ^ 40 * 1637746 * 2
def baseEnd_1637746 : Nat := 280316962659484848314383

theorem tailTrace_1637746 : CollatzResearch.WordTrace tailWord_1637746 prefixEnd_1637746 280316962659484848314383 := by
  unfold tailWord_1637746
  simp only [CollatzResearch.WordTrace]
  refine ⟨14933375981183355398369273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39822335949822281062318061 14933375981183355398369273)
  ·
    refine ⟨11200031985887516548776955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14933375981183355398369273 11200031985887516548776955)
    ·
      refine ⟨16800047978831274823165433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11200031985887516548776955 16800047978831274823165433)
      ·
        refine ⟨12600035984123456117374075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16800047978831274823165433 12600035984123456117374075)
        ·
          refine ⟨18900053976185184176061113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12600035984123456117374075 18900053976185184176061113)
          ·
            refine ⟨14175040482138888132045835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18900053976185184176061113 14175040482138888132045835)
            ·
              refine ⟨21262560723208332198068753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14175040482138888132045835 21262560723208332198068753)
              ·
                refine ⟨15946920542406249148551565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21262560723208332198068753 15946920542406249148551565)
                ·
                  refine ⟨5980095203402343430706837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15946920542406249148551565 5980095203402343430706837)
                  ·
                    refine ⟨280316962659484848314383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5980095203402343430706837 280316962659484848314383)
                    ·
                      rfl

theorem cell23_1637746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 2, 3, 6].length) (baseStart_1637746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1637746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1637746 prefixEnd_1637746 := by exact prefixLift 1637746
  have htrace : WordTrace (prefixWord ++ tailWord_1637746) baseStart_1637746 baseEnd_1637746 := by
    simpa [prefixWord, tailWord_1637746, baseEnd_1637746] using wordTrace_append hprefix tailTrace_1637746
  have hstable : (prefixWord ++ tailWord_1637746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1637746).length < 2 ^ (prefixWord ++ tailWord_1637746).sum := by decide
  have hdescent : baseEnd_1637746 < baseStart_1637746 := by decide
  rcases family_descends (prefixWord ++ tailWord_1637746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1637756 : List Nat := [2, 2, 2, 1, 1, 1, 4, 1, 3, 1, 5]
def baseStart_1637756 : Nat := 118140960795 + 1637756 * 2 ^ 59
def prefixEnd_1637756 : Nat := 4983230072969 + 3 ^ 40 * 1637756 * 2
def baseEnd_1637756 : Nat := 840956022784999505818103

theorem tailTrace_1637756 : CollatzResearch.WordTrace tailWord_1637756 prefixEnd_1637756 840956022784999505818103 := by
  unfold tailWord_1637756
  simp only [CollatzResearch.WordTrace]
  refine ⟨29866934327348596650670561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39822579103131462200894081 29866934327348596650670561)
  ·
    refine ⟨22400200745511447488002921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29866934327348596650670561 22400200745511447488002921)
    ·
      refine ⟨16800150559133585616002191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22400200745511447488002921 16800150559133585616002191)
      ·
        refine ⟨25200225838700378424003287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16800150559133585616002191 25200225838700378424003287)
        ·
          refine ⟨37800338758050567636004931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25200225838700378424003287 37800338758050567636004931)
          ·
            refine ⟨56700508137075851454007397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37800338758050567636004931 56700508137075851454007397)
            ·
              refine ⟨10631345275701722147626387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 56700508137075851454007397 10631345275701722147626387)
              ·
                refine ⟨15947017913552583221439581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10631345275701722147626387 15947017913552583221439581)
                ·
                  refine ⟨5980131717582218708039843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15947017913552583221439581 5980131717582218708039843)
                  ·
                    refine ⟨8970197576373328062059765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5980131717582218708039843 8970197576373328062059765)
                    ·
                      refine ⟨840956022784999505818103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8970197576373328062059765 840956022784999505818103)
                      ·
                        rfl

theorem cell23_1637756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 1, 3, 1, 5].length) (baseStart_1637756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1637756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1637756 prefixEnd_1637756 := by exact prefixLift 1637756
  have htrace : WordTrace (prefixWord ++ tailWord_1637756) baseStart_1637756 baseEnd_1637756 := by
    simpa [prefixWord, tailWord_1637756, baseEnd_1637756] using wordTrace_append hprefix tailTrace_1637756
  have hstable : (prefixWord ++ tailWord_1637756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1637756).length < 2 ^ (prefixWord ++ tailWord_1637756).sum := by decide
  have hdescent : baseEnd_1637756 < baseStart_1637756 := by decide
  rcases family_descends (prefixWord ++ tailWord_1637756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1637763 : List Nat := [1, 1, 1, 3, 5, 2, 2, 1, 1, 6]
def baseStart_1637763 : Nat := 118140960795 + 1637763 * 2 ^ 59
def prefixEnd_1637763 : Nat := 4983230072969 + 3 ^ 40 * 1637763 * 2
def baseEnd_1637763 : Nat := 280319872383193659476857

theorem tailTrace_1637763 : CollatzResearch.WordTrace tailWord_1637763 prefixEnd_1637763 280319872383193659476857 := by
  unfold tailWord_1637763
  simp only [CollatzResearch.WordTrace]
  refine ⟨59734123965671833496845943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39822749310447888997897295 59734123965671833496845943)
  ·
    refine ⟨89601185948507750245268915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59734123965671833496845943 89601185948507750245268915)
    ·
      refine ⟨134401778922761625367903373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89601185948507750245268915 134401778922761625367903373)
      ·
        refine ⟨50400667096035609512963765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 134401778922761625367903373 50400667096035609512963765)
        ·
          refine ⟨4725062540253338391840353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 50400667096035609512963765 4725062540253338391840353)
          ·
            refine ⟨3543796905190003793880265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4725062540253338391840353 3543796905190003793880265)
            ·
              refine ⟨2657847678892502845410199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3543796905190003793880265 2657847678892502845410199)
              ·
                refine ⟨3986771518338754268115299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2657847678892502845410199 3986771518338754268115299)
                ·
                  refine ⟨5980157277508131402172949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3986771518338754268115299 5980157277508131402172949)
                  ·
                    refine ⟨280319872383193659476857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5980157277508131402172949 280319872383193659476857)
                    ·
                      rfl

theorem cell23_1637763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 2, 1, 1, 6].length) (baseStart_1637763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1637763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1637763 prefixEnd_1637763 := by exact prefixLift 1637763
  have htrace : WordTrace (prefixWord ++ tailWord_1637763) baseStart_1637763 baseEnd_1637763 := by
    simpa [prefixWord, tailWord_1637763, baseEnd_1637763] using wordTrace_append hprefix tailTrace_1637763
  have hstable : (prefixWord ++ tailWord_1637763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1637763).length < 2 ^ (prefixWord ++ tailWord_1637763).sum := by decide
  have hdescent : baseEnd_1637763 < baseStart_1637763 := by decide
  rcases family_descends (prefixWord ++ tailWord_1637763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1637774 : List Nat := [4, 1, 1, 4, 2, 2, 1, 1, 2, 3, 2]
def baseStart_1637774 : Nat := 118140960795 + 1637774 * 2 ^ 59
def prefixEnd_1637774 : Nat := 4983230072969 + 3 ^ 40 * 1637774 * 2
def baseEnd_1637774 : Nat := 840965265436780435393021

theorem tailTrace_1637774 : CollatzResearch.WordTrace tailWord_1637774 prefixEnd_1637774 840965265436780435393021 := by
  unfold tailWord_1637774
  simp only [CollatzResearch.WordTrace]
  refine ⟨7466815646078997796937047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39823016779087988250330917 7466815646078997796937047)
  ·
    refine ⟨11200223469118496695405571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7466815646078997796937047 11200223469118496695405571)
    ·
      refine ⟨16800335203677745043108357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11200223469118496695405571 16800335203677745043108357)
      ·
        refine ⟨3150062850689577195582817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16800335203677745043108357 3150062850689577195582817)
        ·
          refine ⟨2362547138017182896687113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3150062850689577195582817 2362547138017182896687113)
          ·
            refine ⟨1771910353512887172515335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2362547138017182896687113 1771910353512887172515335)
            ·
              refine ⟨2657865530269330758773003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1771910353512887172515335 2657865530269330758773003)
              ·
                refine ⟨3986798295403996138159505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2657865530269330758773003 3986798295403996138159505)
                ·
                  refine ⟨2990098721552997103619629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3986798295403996138159505 2990098721552997103619629)
                  ·
                    refine ⟨1121287020582373913857361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2990098721552997103619629 1121287020582373913857361)
                    ·
                      refine ⟨840965265436780435393021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1121287020582373913857361 840965265436780435393021)
                      ·
                        rfl

theorem cell23_1637774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 2, 1, 1, 2, 3, 2].length) (baseStart_1637774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1637774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1637774 prefixEnd_1637774 := by exact prefixLift 1637774
  have htrace : WordTrace (prefixWord ++ tailWord_1637774) baseStart_1637774 baseEnd_1637774 := by
    simpa [prefixWord, tailWord_1637774, baseEnd_1637774] using wordTrace_append hprefix tailTrace_1637774
  have hstable : (prefixWord ++ tailWord_1637774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1637774).length < 2 ^ (prefixWord ++ tailWord_1637774).sum := by decide
  have hdescent : baseEnd_1637774 < baseStart_1637774 := by decide
  rcases family_descends (prefixWord ++ tailWord_1637774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1637784 : List Nat := [2, 1, 2, 5, 3, 1, 2, 1, 1, 5]
def baseStart_1637784 : Nat := 118140960795 + 1637784 * 2 ^ 59
def prefixEnd_1637784 : Nat := 4983230072969 + 3 ^ 40 * 1637784 * 2
def baseEnd_1637784 : Nat := 280323466747775132089325

theorem tailTrace_1637784 : CollatzResearch.WordTrace tailWord_1637784 prefixEnd_1637784 280323466747775132089325 := by
  unfold tailWord_1637784
  simp only [CollatzResearch.WordTrace]
  refine ⟨29867444949297877041680203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39823259932397169388906937 29867444949297877041680203)
  ·
    refine ⟨44801167423946815562520305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29867444949297877041680203 44801167423946815562520305)
    ·
      refine ⟨33600875567960111671890229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44801167423946815562520305 33600875567960111671890229)
      ·
        refine ⟨3150082084496260469239709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 33600875567960111671890229 3150082084496260469239709)
        ·
          refine ⟨1181280781686097675964891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3150082084496260469239709 1181280781686097675964891)
          ·
            refine ⟨1771921172529146513947337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1181280781686097675964891 1771921172529146513947337)
            ·
              refine ⟨1328940879396859885460503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1771921172529146513947337 1328940879396859885460503)
              ·
                refine ⟨1993411319095289828190755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1328940879396859885460503 1993411319095289828190755)
                ·
                  refine ⟨2990116978642934742286133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1993411319095289828190755 2990116978642934742286133)
                  ·
                    refine ⟨280323466747775132089325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2990116978642934742286133 280323466747775132089325)
                    ·
                      rfl

theorem cell23_1637784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 3, 1, 2, 1, 1, 5].length) (baseStart_1637784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1637784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1637784 prefixEnd_1637784 := by exact prefixLift 1637784
  have htrace : WordTrace (prefixWord ++ tailWord_1637784) baseStart_1637784 baseEnd_1637784 := by
    simpa [prefixWord, tailWord_1637784, baseEnd_1637784] using wordTrace_append hprefix tailTrace_1637784
  have hstable : (prefixWord ++ tailWord_1637784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1637784).length < 2 ^ (prefixWord ++ tailWord_1637784).sum := by decide
  have hdescent : baseEnd_1637784 < baseStart_1637784 := by decide
  rcases family_descends (prefixWord ++ tailWord_1637784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1637796 : List Nat := [2, 3, 1, 2, 1, 1, 1, 2, 2, 2, 6]
def baseStart_1637796 : Nat := 118140960795 + 1637796 * 2 ^ 59
def prefixEnd_1637796 : Nat := 4983230072969 + 3 ^ 40 * 1637796 * 2
def baseEnd_1637796 : Nat := 840976562011179349317919

theorem tailTrace_1637796 : CollatzResearch.WordTrace tailWord_1637796 prefixEnd_1637796 840976562011179349317919 := by
  unfold tailWord_1637796
  simp only [CollatzResearch.WordTrace]
  refine ⟨29867663787276140066398621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39823551716368186755198161 29867663787276140066398621)
  ·
    refine ⟨11200373920228552524899483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29867663787276140066398621 11200373920228552524899483)
    ·
      refine ⟨16800560880342828787349225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11200373920228552524899483 16800560880342828787349225)
      ·
        refine ⟨12600420660257121590511919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16800560880342828787349225 12600420660257121590511919)
        ·
          refine ⟨18900630990385682385767879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12600420660257121590511919 18900630990385682385767879)
          ·
            refine ⟨28350946485578523578651819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18900630990385682385767879 28350946485578523578651819)
            ·
              refine ⟨42526419728367785367977729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28350946485578523578651819 42526419728367785367977729)
              ·
                refine ⟨31894814796275839025983297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42526419728367785367977729 31894814796275839025983297)
                ·
                  refine ⟨23921111097206879269487473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31894814796275839025983297 23921111097206879269487473)
                  ·
                    refine ⟨17940833322905159452115605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23921111097206879269487473 17940833322905159452115605)
                    ·
                      refine ⟨840976562011179349317919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 17940833322905159452115605 840976562011179349317919)
                      ·
                        rfl

theorem cell23_1637796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 2, 2, 2, 6].length) (baseStart_1637796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1637796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1637796 prefixEnd_1637796 := by exact prefixLift 1637796
  have htrace : WordTrace (prefixWord ++ tailWord_1637796) baseStart_1637796 baseEnd_1637796 := by
    simpa [prefixWord, tailWord_1637796, baseEnd_1637796] using wordTrace_append hprefix tailTrace_1637796
  have hstable : (prefixWord ++ tailWord_1637796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1637796).length < 2 ^ (prefixWord ++ tailWord_1637796).sum := by decide
  have hdescent : baseEnd_1637796 < baseStart_1637796 := by decide
  rcases family_descends (prefixWord ++ tailWord_1637796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1637817 : List Nat := [1, 2, 1, 4, 5, 1, 1, 1, 1, 2, 4]
def baseStart_1637817 : Nat := 118140960795 + 1637817 * 2 ^ 59
def prefixEnd_1637817 : Nat := 4983230072969 + 3 ^ 40 * 1637817 * 2
def baseEnd_1637817 : Nat := 840987345104923767155323

theorem tailTrace_1637817 : CollatzResearch.WordTrace tailWord_1637817 prefixEnd_1637817 840987345104923767155323 := by
  unfold tailWord_1637817
  simp only [CollatzResearch.WordTrace]
  refine ⟨59736093507476200719311705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39824062338317467146207803 59736093507476200719311705)
  ·
    refine ⟨44802070130607150539483779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59736093507476200719311705 44802070130607150539483779)
    ·
      refine ⟨67203105195910725809225669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44802070130607150539483779 67203105195910725809225669)
      ·
        refine ⟨12600582224233261089229813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 67203105195910725809225669 12600582224233261089229813)
        ·
          refine ⟨1181304583521868227115295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 12600582224233261089229813 1181304583521868227115295)
          ·
            refine ⟨1771956875282802340672943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1181304583521868227115295 1771956875282802340672943)
            ·
              refine ⟨2657935312924203511009415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1771956875282802340672943 2657935312924203511009415)
              ·
                refine ⟨3986902969386305266514123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2657935312924203511009415 3986902969386305266514123)
                ·
                  refine ⟨5980354454079457899771185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3986902969386305266514123 5980354454079457899771185)
                  ·
                    refine ⟨4485265840559593424828389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5980354454079457899771185 4485265840559593424828389)
                    ·
                      refine ⟨840987345104923767155323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4485265840559593424828389 840987345104923767155323)
                      ·
                        rfl

theorem cell23_1637817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 5, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 5, 1, 1, 1, 1, 2, 4].length) (baseStart_1637817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1637817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1637817 prefixEnd_1637817 := by exact prefixLift 1637817
  have htrace : WordTrace (prefixWord ++ tailWord_1637817) baseStart_1637817 baseEnd_1637817 := by
    simpa [prefixWord, tailWord_1637817, baseEnd_1637817] using wordTrace_append hprefix tailTrace_1637817
  have hstable : (prefixWord ++ tailWord_1637817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1637817).length < 2 ^ (prefixWord ++ tailWord_1637817).sum := by decide
  have hdescent : baseEnd_1637817 < baseStart_1637817 := by decide
  rcases family_descends (prefixWord ++ tailWord_1637817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1637856 : List Nat := [2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 6]
def baseStart_1637856 : Nat := 118140960795 + 1637856 * 2 ^ 59
def prefixEnd_1637856 : Nat := 4983230072969 + 3 ^ 40 * 1637856 * 2
def baseEnd_1637856 : Nat := 841007370850449114567643

theorem tailTrace_1637856 : CollatzResearch.WordTrace tailWord_1637856 prefixEnd_1637856 841007370850449114567643 := by
  unfold tailWord_1637856
  simp only [CollatzResearch.WordTrace]
  refine ⟨29868757977167455189990711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39825010636223273586654281 29868757977167455189990711)
  ·
    refine ⟨44803136965751182784986067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29868757977167455189990711 44803136965751182784986067)
    ·
      refine ⟨67204705448626774177479101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44803136965751182784986067 67204705448626774177479101)
      ·
        refine ⟨25201764543235040316554663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67204705448626774177479101 25201764543235040316554663)
        ·
          refine ⟨37802646814852560474831995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25201764543235040316554663 37802646814852560474831995)
          ·
            refine ⟨56703970222278840712247993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37802646814852560474831995 56703970222278840712247993)
            ·
              refine ⟨42527977666709130534185995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56703970222278840712247993 42527977666709130534185995)
              ·
                refine ⟨63791966500063695801278993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42527977666709130534185995 63791966500063695801278993)
                ·
                  refine ⟨47843974875047771850959245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63791966500063695801278993 47843974875047771850959245)
                  ·
                    refine ⟨17941490578142914444109717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 47843974875047771850959245 17941490578142914444109717)
                    ·
                      refine ⟨841007370850449114567643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 17941490578142914444109717 841007370850449114567643)
                      ·
                        rfl

theorem cell23_1637856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 6].length) (baseStart_1637856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1637856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1637856 prefixEnd_1637856 := by exact prefixLift 1637856
  have htrace : WordTrace (prefixWord ++ tailWord_1637856) baseStart_1637856 baseEnd_1637856 := by
    simpa [prefixWord, tailWord_1637856, baseEnd_1637856] using wordTrace_append hprefix tailTrace_1637856
  have hstable : (prefixWord ++ tailWord_1637856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1637856).length < 2 ^ (prefixWord ++ tailWord_1637856).sum := by decide
  have hdescent : baseEnd_1637856 < baseStart_1637856 := by decide
  rcases family_descends (prefixWord ++ tailWord_1637856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1637893 : List Nat := [1, 3, 1, 1, 2, 2, 1, 2, 4, 3, 3]
def baseStart_1637893 : Nat := 118140960795 + 1637893 * 2 ^ 59
def prefixEnd_1637893 : Nat := 4983230072969 + 3 ^ 40 * 1637893 * 2
def baseEnd_1637893 : Nat := 841026369634665469804973

theorem tailTrace_1637893 : CollatzResearch.WordTrace tailWord_1637893 prefixEnd_1637893 841026369634665469804973 := by
  unfold tailWord_1637893
  simp only [CollatzResearch.WordTrace]
  refine ⟨59738865455200865699078333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39825910303467243799385555 59738865455200865699078333)
  ·
    refine ⟨22402074545700324637154375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59738865455200865699078333 22402074545700324637154375)
    ·
      refine ⟨33603111818550486955731563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22402074545700324637154375 33603111818550486955731563)
      ·
        refine ⟨50404667727825730433597345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33603111818550486955731563 50404667727825730433597345)
        ·
          refine ⟨37803500795869297825198009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50404667727825730433597345 37803500795869297825198009)
          ·
            refine ⟨28352625596901973368898507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37803500795869297825198009 28352625596901973368898507)
            ·
              refine ⟨42528938395352960053347761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28352625596901973368898507 42528938395352960053347761)
              ·
                refine ⟨31896703796514720040010821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42528938395352960053347761 31896703796514720040010821)
                ·
                  refine ⟨5980631961846510007502029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31896703796514720040010821 5980631961846510007502029)
                  ·
                    refine ⟨2242736985692441252813261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5980631961846510007502029 2242736985692441252813261)
                    ·
                      refine ⟨841026369634665469804973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2242736985692441252813261 841026369634665469804973)
                      ·
                        rfl

theorem cell23_1637893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 2, 4, 3, 3].length) (baseStart_1637893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1637893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1637893 prefixEnd_1637893 := by exact prefixLift 1637893
  have htrace : WordTrace (prefixWord ++ tailWord_1637893) baseStart_1637893 baseEnd_1637893 := by
    simpa [prefixWord, tailWord_1637893, baseEnd_1637893] using wordTrace_append hprefix tailTrace_1637893
  have hstable : (prefixWord ++ tailWord_1637893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1637893).length < 2 ^ (prefixWord ++ tailWord_1637893).sum := by decide
  have hdescent : baseEnd_1637893 < baseStart_1637893 := by decide
  rcases family_descends (prefixWord ++ tailWord_1637893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1638003 : List Nat := [1, 1, 1, 2, 2, 1, 1, 2, 7, 5]
def baseStart_1638003 : Nat := 118140960795 + 1638003 * 2 ^ 59
def prefixEnd_1638003 : Nat := 4983230072969 + 3 ^ 40 * 1638003 * 2
def baseEnd_1638003 : Nat := 280360950835553346476489

theorem tailTrace_1638003 : CollatzResearch.WordTrace tailWord_1638003 prefixEnd_1638003 280360950835553346476489 := by
  unfold tailWord_1638003
  simp only [CollatzResearch.WordTrace]
  refine ⟨59742877484802354485582663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39828584989868236323721775 59742877484802354485582663)
  ·
    refine ⟨89614316227203531728373995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59742877484802354485582663 89614316227203531728373995)
    ·
      refine ⟨134421474340805297592560993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89614316227203531728373995 134421474340805297592560993)
      ·
        refine ⟨100816105755603973194420745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134421474340805297592560993 100816105755603973194420745)
        ·
          refine ⟨75612079316702979895815559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100816105755603973194420745 75612079316702979895815559)
          ·
            refine ⟨113418118975054469843723339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75612079316702979895815559 113418118975054469843723339)
            ·
              refine ⟨170127178462581704765585009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113418118975054469843723339 170127178462581704765585009)
              ·
                refine ⟨127595383846936278574188757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 170127178462581704765585009 127595383846936278574188757)
                ·
                  refine ⟨2990516808912569029082549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 127595383846936278574188757 2990516808912569029082549)
                  ·
                    refine ⟨280360950835553346476489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2990516808912569029082549 280360950835553346476489)
                    ·
                      rfl

theorem cell23_1638003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 2, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 2, 7, 5].length) (baseStart_1638003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1638003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1638003 prefixEnd_1638003 := by exact prefixLift 1638003
  have htrace : WordTrace (prefixWord ++ tailWord_1638003) baseStart_1638003 baseEnd_1638003 := by
    simpa [prefixWord, tailWord_1638003, baseEnd_1638003] using wordTrace_append hprefix tailTrace_1638003
  have hstable : (prefixWord ++ tailWord_1638003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1638003).length < 2 ^ (prefixWord ++ tailWord_1638003).sum := by decide
  have hdescent : baseEnd_1638003 < baseStart_1638003 := by decide
  rcases family_descends (prefixWord ++ tailWord_1638003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1638027 : List Nat := [1, 1, 1, 1, 4, 1, 5, 2, 2, 3, 2]
def baseStart_1638027 : Nat := 118140960795 + 1638027 * 2 ^ 59
def prefixEnd_1638027 : Nat := 4983230072969 + 3 ^ 40 * 1638027 * 2
def baseEnd_1638027 : Nat := 841095176042367945529357

theorem tailTrace_1638027 : CollatzResearch.WordTrace tailWord_1638027 prefixEnd_1638027 841095176042367945529357 := by
  unfold tailWord_1638027
  simp only [CollatzResearch.WordTrace]
  refine ⟨59743752836715406584456335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39829168557810271056304223 59743752836715406584456335)
  ·
    refine ⟨89615629255073109876684503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59743752836715406584456335 89615629255073109876684503)
    ·
      refine ⟨134423443882609664815026755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89615629255073109876684503 134423443882609664815026755)
      ·
        refine ⟨201635165823914497222540133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134423443882609664815026755 201635165823914497222540133)
        ·
          refine ⟨37806593591983968229226275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 201635165823914497222540133 37806593591983968229226275)
          ·
            refine ⟨56709890387975952343839413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37806593591983968229226275 56709890387975952343839413)
            ·
              refine ⟨5316552223872745532234945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 56709890387975952343839413 5316552223872745532234945)
              ·
                refine ⟨3987414167904559149176209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5316552223872745532234945 3987414167904559149176209)
                ·
                  refine ⟨2990560625928419361882157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3987414167904559149176209 2990560625928419361882157)
                  ·
                    refine ⟨1121460234723157260705809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2990560625928419361882157 1121460234723157260705809)
                    ·
                      refine ⟨841095176042367945529357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1121460234723157260705809 841095176042367945529357)
                      ·
                        rfl

theorem cell23_1638027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 5, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 5, 2, 2, 3, 2].length) (baseStart_1638027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1638027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1638027 prefixEnd_1638027 := by exact prefixLift 1638027
  have htrace : WordTrace (prefixWord ++ tailWord_1638027) baseStart_1638027 baseEnd_1638027 := by
    simpa [prefixWord, tailWord_1638027, baseEnd_1638027] using wordTrace_append hprefix tailTrace_1638027
  have hstable : (prefixWord ++ tailWord_1638027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1638027).length < 2 ^ (prefixWord ++ tailWord_1638027).sum := by decide
  have hdescent : baseEnd_1638027 < baseStart_1638027 := by decide
  rcases family_descends (prefixWord ++ tailWord_1638027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1638033 : List Nat := [1, 2, 2, 1, 1, 1, 1, 3, 5, 6]
def baseStart_1638033 : Nat := 118140960795 + 1638033 * 2 ^ 59
def prefixEnd_1638033 : Nat := 4983230072969 + 3 ^ 40 * 1638033 * 2
def baseEnd_1638033 : Nat := 280366085642098307351443

theorem tailTrace_1638033 : CollatzResearch.WordTrace tailWord_1638033 prefixEnd_1638033 280366085642098307351443 := by
  unfold tailWord_1638033
  simp only [CollatzResearch.WordTrace]
  refine ⟨59743971674693669609174753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39829314449795779739449835 59743971674693669609174753)
  ·
    refine ⟨44807978756020252206881065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59743971674693669609174753 44807978756020252206881065)
    ·
      refine ⟨33605984067015189155160799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44807978756020252206881065 33605984067015189155160799)
      ·
        refine ⟨50408976100522783732741199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33605984067015189155160799 50408976100522783732741199)
        ·
          refine ⟨75613464150784175599111799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50408976100522783732741199 75613464150784175599111799)
          ·
            refine ⟨113420196226176263398667699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75613464150784175599111799 113420196226176263398667699)
            ·
              refine ⟨170130294339264395098001549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113420196226176263398667699 170130294339264395098001549)
              ·
                refine ⟨63798860377224148161750581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 170130294339264395098001549 63798860377224148161750581)
                ·
                  refine ⟨5981143160364763890164117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 63798860377224148161750581 5981143160364763890164117)
                  ·
                    refine ⟨280366085642098307351443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5981143160364763890164117 280366085642098307351443)
                    ·
                      rfl

theorem cell23_1638033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 6].length) (baseStart_1638033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1638033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1638033 prefixEnd_1638033 := by exact prefixLift 1638033
  have htrace : WordTrace (prefixWord ++ tailWord_1638033) baseStart_1638033 baseEnd_1638033 := by
    simpa [prefixWord, tailWord_1638033, baseEnd_1638033] using wordTrace_append hprefix tailTrace_1638033
  have hstable : (prefixWord ++ tailWord_1638033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1638033).length < 2 ^ (prefixWord ++ tailWord_1638033).sum := by decide
  have hdescent : baseEnd_1638033 < baseStart_1638033 := by decide
  rcases family_descends (prefixWord ++ tailWord_1638033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1638063 : List Nat := [1, 1, 2, 1, 2, 4, 1, 11]
def baseStart_1638063 : Nat := 118140960795 + 1638063 * 2 ^ 59
def prefixEnd_1638063 : Nat := 4983230072969 + 3 ^ 40 * 1638063 * 2
def baseEnd_1638063 : Nat := 31152357827627029802933

theorem tailTrace_1638063 : CollatzResearch.WordTrace tailWord_1638063 prefixEnd_1638063 31152357827627029802933 := by
  unfold tailWord_1638063
  simp only [CollatzResearch.WordTrace]
  refine ⟨59745065864584984732766843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39830043909723323155177895 59745065864584984732766843)
  ·
    refine ⟨89617598796877477099150265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59745065864584984732766843 89617598796877477099150265)
    ·
      refine ⟨67213199097658107824362699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89617598796877477099150265 67213199097658107824362699)
      ·
        refine ⟨100819798646487161736544049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67213199097658107824362699 100819798646487161736544049)
        ·
          refine ⟨75614848984865371302408037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100819798646487161736544049 75614848984865371302408037)
          ·
            refine ⟨14177784184662257119201507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 75614848984865371302408037 14177784184662257119201507)
            ·
              refine ⟨21266676276993385678802261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14177784184662257119201507 21266676276993385678802261)
              ·
                refine ⟨31152357827627029802933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 21266676276993385678802261 31152357827627029802933)
                ·
                  rfl

theorem cell23_1638063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 11].length) (baseStart_1638063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1638063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1638063 prefixEnd_1638063 := by exact prefixLift 1638063
  have htrace : WordTrace (prefixWord ++ tailWord_1638063) baseStart_1638063 baseEnd_1638063 := by
    simpa [prefixWord, tailWord_1638063, baseEnd_1638063] using wordTrace_append hprefix tailTrace_1638063
  have hstable : (prefixWord ++ tailWord_1638063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1638063).length < 2 ^ (prefixWord ++ tailWord_1638063).sum := by decide
  have hdescent : baseEnd_1638063 < baseStart_1638063 := by decide
  rcases family_descends (prefixWord ++ tailWord_1638063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1638074 : List Nat := [3, 1, 1, 1, 2, 5, 3, 1, 1, 1, 4]
def baseStart_1638074 : Nat := 118140960795 + 1638074 * 2 ^ 59
def prefixEnd_1638074 : Nat := 4983230072969 + 3 ^ 40 * 1638074 * 2
def baseEnd_1638074 : Nat := 841119309633129261641641

theorem tailTrace_1638074 : CollatzResearch.WordTrace tailWord_1638074 prefixEnd_1638074 841119309633129261641641 := by
  unfold tailWord_1638074
  simp only [CollatzResearch.WordTrace]
  refine ⟨14936366766886283402854319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39830311378363422407611517 14936366766886283402854319)
  ·
    refine ⟨22404550150329425104281479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14936366766886283402854319 22404550150329425104281479)
    ·
      refine ⟨33606825225494137656422219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22404550150329425104281479 33606825225494137656422219)
      ·
        refine ⟨50410237838241206484633329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33606825225494137656422219 50410237838241206484633329)
        ·
          refine ⟨37807678378680904863474997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50410237838241206484633329 37807678378680904863474997)
          ·
            refine ⟨3544469848001334830950781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 37807678378680904863474997 3544469848001334830950781)
            ·
              refine ⟨1329176193000500561606543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3544469848001334830950781 1329176193000500561606543)
              ·
                refine ⟨1993764289500750842409815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1329176193000500561606543 1993764289500750842409815)
                ·
                  refine ⟨2990646434251126263614723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1993764289500750842409815 2990646434251126263614723)
                  ·
                    refine ⟨4485969651376689395422085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2990646434251126263614723 4485969651376689395422085)
                    ·
                      refine ⟨841119309633129261641641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4485969651376689395422085 841119309633129261641641)
                      ·
                        rfl

theorem cell23_1638074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 3, 1, 1, 1, 4].length) (baseStart_1638074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1638074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1638074 prefixEnd_1638074 := by exact prefixLift 1638074
  have htrace : WordTrace (prefixWord ++ tailWord_1638074) baseStart_1638074 baseEnd_1638074 := by
    simpa [prefixWord, tailWord_1638074, baseEnd_1638074] using wordTrace_append hprefix tailTrace_1638074
  have hstable : (prefixWord ++ tailWord_1638074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1638074).length < 2 ^ (prefixWord ++ tailWord_1638074).sum := by decide
  have hdescent : baseEnd_1638074 < baseStart_1638074 := by decide
  rcases family_descends (prefixWord ++ tailWord_1638074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1638083 : List Nat := [1, 1, 1, 3, 1, 1, 1, 1, 2, 3, 8]
def baseStart_1638083 : Nat := 118140960795 + 1638083 * 2 ^ 59
def prefixEnd_1638083 : Nat := 4983230072969 + 3 ^ 40 * 1638083 * 2
def baseEnd_1638083 : Nat := 841123930959019726429099

theorem tailTrace_1638083 : CollatzResearch.WordTrace tailWord_1638083 prefixEnd_1638083 841123930959019726429099 := by
  unfold tailWord_1638083
  simp only [CollatzResearch.WordTrace]
  refine ⟨59745795324512528148494903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39830530216341685432329935 59745795324512528148494903)
  ·
    refine ⟨89618692986768792222742355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59745795324512528148494903 89618692986768792222742355)
    ·
      refine ⟨134428039480153188334113533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89618692986768792222742355 134428039480153188334113533)
      ·
        refine ⟨50410514805057445625292575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 134428039480153188334113533 50410514805057445625292575)
        ·
          refine ⟨75615772207586168437938863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50410514805057445625292575 75615772207586168437938863)
          ·
            refine ⟨113423658311379252656908295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75615772207586168437938863 113423658311379252656908295)
            ·
              refine ⟨170135487467068878985362443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113423658311379252656908295 170135487467068878985362443)
              ·
                refine ⟨255203231200603318478043665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 170135487467068878985362443 255203231200603318478043665)
                ·
                  refine ⟨191402423400452488858532749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 255203231200603318478043665 191402423400452488858532749)
                  ·
                    refine ⟨71775908775169683321949781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 191402423400452488858532749 71775908775169683321949781)
                    ·
                      refine ⟨841123930959019726429099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 71775908775169683321949781 841123930959019726429099)
                      ·
                        rfl

theorem cell23_1638083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 2, 3, 8].length) (baseStart_1638083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1638083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1638083 prefixEnd_1638083 := by exact prefixLift 1638083
  have htrace : WordTrace (prefixWord ++ tailWord_1638083) baseStart_1638083 baseEnd_1638083 := by
    simpa [prefixWord, tailWord_1638083, baseEnd_1638083] using wordTrace_append hprefix tailTrace_1638083
  have hstable : (prefixWord ++ tailWord_1638083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1638083).length < 2 ^ (prefixWord ++ tailWord_1638083).sum := by decide
  have hdescent : baseEnd_1638083 < baseStart_1638083 := by decide
  rcases family_descends (prefixWord ++ tailWord_1638083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1638084 : List Nat := [2, 3, 3, 1, 1, 1, 4, 2, 2, 4]
def baseStart_1638084 : Nat := 118140960795 + 1638084 * 2 ^ 59
def prefixEnd_1638084 : Nat := 4983230072969 + 3 ^ 40 * 1638084 * 2
def baseEnd_1638084 : Nat := 280374814813224740838865

theorem tailTrace_1638084 : CollatzResearch.WordTrace tailWord_1638084 prefixEnd_1638084 280374814813224740838865 := by
  unfold tailWord_1638084
  simp only [CollatzResearch.WordTrace]
  refine ⟨29872915898754452659640653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39830554531672603546187537 29872915898754452659640653)
  ·
    refine ⟨11202343462032919747365245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29872915898754452659640653 11202343462032919747365245)
    ·
      refine ⟨4200878798262344905261967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11202343462032919747365245 4200878798262344905261967)
      ·
        refine ⟨6301318197393517357892951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4200878798262344905261967 6301318197393517357892951)
        ·
          refine ⟨9451977296090276036839427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6301318197393517357892951 9451977296090276036839427)
          ·
            refine ⟨14177965944135414055259141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9451977296090276036839427 14177965944135414055259141)
            ·
              refine ⟨2658368614525390135361089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14177965944135414055259141 2658368614525390135361089)
              ·
                refine ⟨1993776460894042601520817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2658368614525390135361089 1993776460894042601520817)
                ·
                  refine ⟨1495332345670531951140613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1993776460894042601520817 1495332345670531951140613)
                  ·
                    refine ⟨280374814813224740838865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1495332345670531951140613 280374814813224740838865)
                    ·
                      rfl

theorem cell23_1638084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 4, 2, 2, 4].length) (baseStart_1638084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1638084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1638084 prefixEnd_1638084 := by exact prefixLift 1638084
  have htrace : WordTrace (prefixWord ++ tailWord_1638084) baseStart_1638084 baseEnd_1638084 := by
    simpa [prefixWord, tailWord_1638084, baseEnd_1638084] using wordTrace_append hprefix tailTrace_1638084
  have hstable : (prefixWord ++ tailWord_1638084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1638084).length < 2 ^ (prefixWord ++ tailWord_1638084).sum := by decide
  have hdescent : baseEnd_1638084 < baseStart_1638084 := by decide
  rcases family_descends (prefixWord ++ tailWord_1638084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1638108 : List Nat := [2, 2, 5, 1, 2, 1, 1, 2, 3, 2, 2]
def baseStart_1638108 : Nat := 118140960795 + 1638108 * 2 ^ 59
def prefixEnd_1638108 : Nat := 4983230072969 + 3 ^ 40 * 1638108 * 2
def baseEnd_1638108 : Nat := 841136767975382128616485

theorem tailTrace_1638108 : CollatzResearch.WordTrace tailWord_1638108 prefixEnd_1638108 841136767975382128616485 := by
  unfold tailWord_1638108
  simp only [CollatzResearch.WordTrace]
  refine ⟨29873353574710978709077489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39831138099614638278769985 29873353574710978709077489)
  ·
    refine ⟨22405015181033234031808117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29873353574710978709077489 22405015181033234031808117)
    ·
      refine ⟨2100470173221865690482011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 22405015181033234031808117 2100470173221865690482011)
      ·
        refine ⟨3150705259832798535723017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2100470173221865690482011 3150705259832798535723017)
        ·
          refine ⟨2363028944874598901792263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3150705259832798535723017 2363028944874598901792263)
          ·
            refine ⟨3544543417311898352688395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2363028944874598901792263 3544543417311898352688395)
            ·
              refine ⟨5316815125967847529032593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3544543417311898352688395 5316815125967847529032593)
              ·
                refine ⟨3987611344475885646774445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5316815125967847529032593 3987611344475885646774445)
                ·
                  refine ⟨1495354254178457117540417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3987611344475885646774445 1495354254178457117540417)
                  ·
                    refine ⟨1121515690633842838155313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1495354254178457117540417 1121515690633842838155313)
                    ·
                      refine ⟨841136767975382128616485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1121515690633842838155313 841136767975382128616485)
                      ·
                        rfl

theorem cell23_1638108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 1, 2, 3, 2, 2].length) (baseStart_1638108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1638108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1638108 prefixEnd_1638108 := by exact prefixLift 1638108
  have htrace : WordTrace (prefixWord ++ tailWord_1638108) baseStart_1638108 baseEnd_1638108 := by
    simpa [prefixWord, tailWord_1638108, baseEnd_1638108] using wordTrace_append hprefix tailTrace_1638108
  have hstable : (prefixWord ++ tailWord_1638108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1638108).length < 2 ^ (prefixWord ++ tailWord_1638108).sum := by decide
  have hdescent : baseEnd_1638108 < baseStart_1638108 := by decide
  rcases family_descends (prefixWord ++ tailWord_1638108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1638140 : List Nat := [2, 2, 2, 1, 3, 1, 1, 1, 4, 6]
def baseStart_1638140 : Nat := 118140960795 + 1638140 * 2 ^ 59
def prefixEnd_1638140 : Nat := 4983230072969 + 3 ^ 40 * 1638140 * 2
def baseEnd_1638140 : Nat := 280384399785442001138779

theorem tailTrace_1638140 : CollatzResearch.WordTrace tailWord_1638140 prefixEnd_1638140 280384399785442001138779 := by
  unfold tailWord_1638140
  simp only [CollatzResearch.WordTrace]
  refine ⟨29873937142653013441659937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39831916190204017922213249 29873937142653013441659937)
  ·
    refine ⟨22405452856989760081244953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29873937142653013441659937 22405452856989760081244953)
    ·
      refine ⟨16804089642742320060933715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22405452856989760081244953 16804089642742320060933715)
      ·
        refine ⟨25206134464113480091400573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16804089642742320060933715 25206134464113480091400573)
        ·
          refine ⟨9452300424042555034275215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25206134464113480091400573 9452300424042555034275215)
          ·
            refine ⟨14178450636063832551412823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9452300424042555034275215 14178450636063832551412823)
            ·
              refine ⟨21267675954095748827119235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14178450636063832551412823 21267675954095748827119235)
              ·
                refine ⟨31901513931143623240678853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21267675954095748827119235 31901513931143623240678853)
                ·
                  refine ⟨5981533862089429357627285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31901513931143623240678853 5981533862089429357627285)
                  ·
                    refine ⟨280384399785442001138779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5981533862089429357627285 280384399785442001138779)
                    ·
                      rfl

theorem cell23_1638140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 1, 4, 6].length) (baseStart_1638140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1638140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1638140 prefixEnd_1638140 := by exact prefixLift 1638140
  have htrace : WordTrace (prefixWord ++ tailWord_1638140) baseStart_1638140 baseEnd_1638140 := by
    simpa [prefixWord, tailWord_1638140, baseEnd_1638140] using wordTrace_append hprefix tailTrace_1638140
  have hstable : (prefixWord ++ tailWord_1638140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1638140).length < 2 ^ (prefixWord ++ tailWord_1638140).sum := by decide
  have hdescent : baseEnd_1638140 < baseStart_1638140 := by decide
  rcases family_descends (prefixWord ++ tailWord_1638140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1638147 : List Nat := [1, 1, 1, 3, 2, 2, 2, 2, 3, 4, 2]
def baseStart_1638147 : Nat := 118140960795 + 1638147 * 2 ^ 59
def prefixEnd_1638147 : Nat := 4983230072969 + 3 ^ 40 * 1638147 * 2
def baseEnd_1638147 : Nat := 841156793720907476028805

theorem tailTrace_1638147 : CollatzResearch.WordTrace tailWord_1638147 prefixEnd_1638147 841156793720907476028805 := by
  unfold tailWord_1638147
  simp only [CollatzResearch.WordTrace]
  refine ⟨59748129596280667078824695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39832086397520444719216463 59748129596280667078824695)
  ·
    refine ⟨89622194394421000618237043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59748129596280667078824695 89622194394421000618237043)
    ·
      refine ⟨134433291591631500927355565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89622194394421000618237043 134433291591631500927355565)
      ·
        refine ⟨50412484346861812847758337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 134433291591631500927355565 50412484346861812847758337)
        ·
          refine ⟨37809363260146359635818753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50412484346861812847758337 37809363260146359635818753)
          ·
            refine ⟨28357022445109769726864065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37809363260146359635818753 28357022445109769726864065)
            ·
              refine ⟨21267766833832327295148049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28357022445109769726864065 21267766833832327295148049)
              ·
                refine ⟨15950825125374245471361037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21267766833832327295148049 15950825125374245471361037)
                ·
                  refine ⟨5981559422015342051760389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15950825125374245471361037 5981559422015342051760389)
                  ·
                    refine ⟨1121542391627876634705073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5981559422015342051760389 1121542391627876634705073)
                    ·
                      refine ⟨841156793720907476028805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1121542391627876634705073 841156793720907476028805)
                      ·
                        rfl

theorem cell23_1638147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 2, 3, 4, 2].length) (baseStart_1638147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1638147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1638147 prefixEnd_1638147 := by exact prefixLift 1638147
  have htrace : WordTrace (prefixWord ++ tailWord_1638147) baseStart_1638147 baseEnd_1638147 := by
    simpa [prefixWord, tailWord_1638147, baseEnd_1638147] using wordTrace_append hprefix tailTrace_1638147
  have hstable : (prefixWord ++ tailWord_1638147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1638147).length < 2 ^ (prefixWord ++ tailWord_1638147).sum := by decide
  have hdescent : baseEnd_1638147 < baseStart_1638147 := by decide
  rcases family_descends (prefixWord ++ tailWord_1638147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1638198 : List Nat := [5, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2]
def baseStart_1638198 : Nat := 118140960795 + 1638198 * 2 ^ 59
def prefixEnd_1638198 : Nat := 4983230072969 + 3 ^ 40 * 1638198 * 2
def baseEnd_1638198 : Nat := 841182981234286776491071

theorem tailTrace_1638198 : CollatzResearch.WordTrace tailWord_1638198 prefixEnd_1638198 841182981234286776491071 := by
  unfold tailWord_1638198
  simp only [CollatzResearch.WordTrace]
  refine ⟨3734374357443493924308203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 39833326479397268525954165 3734374357443493924308203)
  ·
    refine ⟨5601561536165240886462305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3734374357443493924308203 5601561536165240886462305)
    ·
      refine ⟨4201171152123930664846729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5601561536165240886462305 4201171152123930664846729)
      ·
        refine ⟨3150878364092947998635047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4201171152123930664846729 3150878364092947998635047)
        ·
          refine ⟨4726317546139421997952571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3150878364092947998635047 4726317546139421997952571)
          ·
            refine ⟨7089476319209132996928857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4726317546139421997952571 7089476319209132996928857)
            ·
              refine ⟨5317107239406849747696643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7089476319209132996928857 5317107239406849747696643)
              ·
                refine ⟨7975660859110274621544965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5317107239406849747696643 7975660859110274621544965)
                ·
                  refine ⟨1495436411083176491539681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7975660859110274621544965 1495436411083176491539681)
                  ·
                    refine ⟨1121577308312382368654761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1495436411083176491539681 1121577308312382368654761)
                    ·
                      refine ⟨841182981234286776491071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1121577308312382368654761 841182981234286776491071)
                      ·
                        rfl

theorem cell23_1638198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2].length) (baseStart_1638198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1638198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1638198 prefixEnd_1638198 := by exact prefixLift 1638198
  have htrace : WordTrace (prefixWord ++ tailWord_1638198) baseStart_1638198 baseEnd_1638198 := by
    simpa [prefixWord, tailWord_1638198, baseEnd_1638198] using wordTrace_append hprefix tailTrace_1638198
  have hstable : (prefixWord ++ tailWord_1638198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1638198).length < 2 ^ (prefixWord ++ tailWord_1638198).sum := by decide
  have hdescent : baseEnd_1638198 < baseStart_1638198 := by decide
  rcases family_descends (prefixWord ++ tailWord_1638198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1638277 : List Nat := [1, 3, 1, 1, 3, 2, 1, 5, 6]
def baseStart_1638277 : Nat := 118140960795 + 1638277 * 2 ^ 59
def prefixEnd_1638277 : Nat := 4983230072969 + 3 ^ 40 * 1638277 * 2
def baseEnd_1638277 : Nat := 93469282911776885267023

theorem tailTrace_1638277 : CollatzResearch.WordTrace tailWord_1638277 prefixEnd_1638277 93469282911776885267023 := by
  unfold tailWord_1638277
  simp only [CollatzResearch.WordTrace]
  refine ⟨59752871085809699281057085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39835247390539799520704723 59752871085809699281057085)
  ·
    refine ⟨22407326657178637230396407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59752871085809699281057085 22407326657178637230396407)
    ·
      refine ⟨33610989985767955845594611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22407326657178637230396407 33610989985767955845594611)
      ·
        refine ⟨50416484978651933768391917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33610989985767955845594611 50416484978651933768391917)
        ·
          refine ⟨18906181866994475163146969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50416484978651933768391917 18906181866994475163146969)
          ·
            refine ⟨14179636400245856372360227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18906181866994475163146969 14179636400245856372360227)
            ·
              refine ⟨21269454600368784558540341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14179636400245856372360227 21269454600368784558540341)
              ·
                refine ⟨1994011368784573552363157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21269454600368784558540341 1994011368784573552363157)
                ·
                  refine ⟨93469282911776885267023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1994011368784573552363157 93469282911776885267023)
                  ·
                    rfl

theorem cell23_1638277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 5, 6].length) (baseStart_1638277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1638277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1638277 prefixEnd_1638277 := by exact prefixLift 1638277
  have htrace : WordTrace (prefixWord ++ tailWord_1638277) baseStart_1638277 baseEnd_1638277 := by
    simpa [prefixWord, tailWord_1638277, baseEnd_1638277] using wordTrace_append hprefix tailTrace_1638277
  have hstable : (prefixWord ++ tailWord_1638277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1638277).length < 2 ^ (prefixWord ++ tailWord_1638277).sum := by decide
  have hdescent : baseEnd_1638277 < baseStart_1638277 := by decide
  rcases family_descends (prefixWord ++ tailWord_1638277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1638298 : List Nat := [3, 1, 1, 4, 2, 2, 2, 3, 1, 4]
def baseStart_1638298 : Nat := 118140960795 + 1638298 * 2 ^ 59
def prefixEnd_1638298 : Nat := 4983230072969 + 3 ^ 40 * 1638298 * 2
def baseEnd_1638298 : Nat := 280411443099912128413537

theorem tailTrace_1638298 : CollatzResearch.WordTrace tailWord_1638298 prefixEnd_1638298 280411443099912128413537 := by
  unfold tailWord_1638298
  simp only [CollatzResearch.WordTrace]
  refine ⟨14938409254683404966892887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39835758012489079911714365 14938409254683404966892887)
  ·
    refine ⟨22407613882025107450339331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14938409254683404966892887 22407613882025107450339331)
    ·
      refine ⟨33611420823037661175508997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22407613882025107450339331 33611420823037661175508997)
      ·
        refine ⟨6302141404319561470407937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33611420823037661175508997 6302141404319561470407937)
        ·
          refine ⟨4726606053239671102805953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6302141404319561470407937 4726606053239671102805953)
          ·
            refine ⟨3544954539929753327104465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4726606053239671102805953 3544954539929753327104465)
            ·
              refine ⟨2658715904947314995328349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3544954539929753327104465 2658715904947314995328349)
              ·
                refine ⟨997018464355243123248131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2658715904947314995328349 997018464355243123248131)
                ·
                  refine ⟨1495527696532864684872197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 997018464355243123248131 1495527696532864684872197)
                  ·
                    refine ⟨280411443099912128413537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1495527696532864684872197 280411443099912128413537)
                    ·
                      rfl

theorem cell23_1638298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 2, 3, 1, 4].length) (baseStart_1638298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1638298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1638298 prefixEnd_1638298 := by exact prefixLift 1638298
  have htrace : WordTrace (prefixWord ++ tailWord_1638298) baseStart_1638298 baseEnd_1638298 := by
    simpa [prefixWord, tailWord_1638298, baseEnd_1638298] using wordTrace_append hprefix tailTrace_1638298
  have hstable : (prefixWord ++ tailWord_1638298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1638298).length < 2 ^ (prefixWord ++ tailWord_1638298).sum := by decide
  have hdescent : baseEnd_1638298 < baseStart_1638298 := by decide
  rcases family_descends (prefixWord ++ tailWord_1638298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1638304 : List Nat := [2, 1, 1, 4, 1, 1, 1, 1, 7, 1, 3]
def baseStart_1638304 : Nat := 118140960795 + 1638304 * 2 ^ 59
def prefixEnd_1638304 : Nat := 4983230072969 + 3 ^ 40 * 1638304 * 2
def baseEnd_1638304 : Nat := 841237410183663361765583

theorem tailTrace_1638304 : CollatzResearch.WordTrace tailWord_1638304 prefixEnd_1638304 841237410183663361765583 := by
  unfold tailWord_1638304
  simp only [CollatzResearch.WordTrace]
  refine ⟨29876927928355941446144983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39835903904474588594859977 29876927928355941446144983)
  ·
    refine ⟨44815391892533912169217475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29876927928355941446144983 44815391892533912169217475)
    ·
      refine ⟨67223087838800868253826213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44815391892533912169217475 67223087838800868253826213)
      ·
        refine ⟨12604328969775162797592415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 67223087838800868253826213 12604328969775162797592415)
        ·
          refine ⟨18906493454662744196388623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12604328969775162797592415 18906493454662744196388623)
          ·
            refine ⟨28359740181994116294582935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18906493454662744196388623 28359740181994116294582935)
            ·
              refine ⟨42539610272991174441874403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28359740181994116294582935 42539610272991174441874403)
              ·
                refine ⟨63809415409486761662811605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42539610272991174441874403 63809415409486761662811605)
                ·
                  refine ⟨1495533173659845976472147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 63809415409486761662811605 1495533173659845976472147)
                  ·
                    refine ⟨2243299760489768964708221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1495533173659845976472147 2243299760489768964708221)
                    ·
                      refine ⟨841237410183663361765583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2243299760489768964708221 841237410183663361765583)
                      ·
                        rfl

theorem cell23_1638304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 1, 7, 1, 3].length) (baseStart_1638304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1638304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1638304 prefixEnd_1638304 := by exact prefixLift 1638304
  have htrace : WordTrace (prefixWord ++ tailWord_1638304) baseStart_1638304 baseEnd_1638304 := by
    simpa [prefixWord, tailWord_1638304, baseEnd_1638304] using wordTrace_append hprefix tailTrace_1638304
  have hstable : (prefixWord ++ tailWord_1638304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1638304).length < 2 ^ (prefixWord ++ tailWord_1638304).sum := by decide
  have hdescent : baseEnd_1638304 < baseStart_1638304 := by decide
  rcases family_descends (prefixWord ++ tailWord_1638304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1638311 : List Nat := [1, 1, 6, 1, 2, 3, 1, 2, 6]
def baseStart_1638311 : Nat := 118140960795 + 1638311 * 2 ^ 59
def prefixEnd_1638311 : Nat := 4983230072969 + 3 ^ 40 * 1638311 * 2
def baseEnd_1638311 : Nat := 93471222727582759375339

theorem tailTrace_1638311 : CollatzResearch.WordTrace tailWord_1638311 prefixEnd_1638311 93471222727582759375339 := by
  unfold tailWord_1638311
  simp only [CollatzResearch.WordTrace]
  refine ⟨59754111167686523087794787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39836074111791015391863191 59754111167686523087794787)
  ·
    refine ⟨89631166751529784631692181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59754111167686523087794787 89631166751529784631692181)
    ·
      refine ⟨4201460941477958654610571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 89631166751529784631692181 4201460941477958654610571)
      ·
        refine ⟨6302191412216937981915857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4201460941477958654610571 6302191412216937981915857)
        ·
          refine ⟨4726643559162703486436893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6302191412216937981915857 4726643559162703486436893)
          ·
            refine ⟨1772491334686013807413835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4726643559162703486436893 1772491334686013807413835)
            ·
              refine ⟨2658737002029020711120753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1772491334686013807413835 2658737002029020711120753)
              ·
                refine ⟨1994052751521765533340565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2658737002029020711120753 1994052751521765533340565)
                ·
                  refine ⟨93471222727582759375339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1994052751521765533340565 93471222727582759375339)
                  ·
                    rfl

theorem cell23_1638311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 3, 1, 2, 6].length) (baseStart_1638311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1638311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1638311 prefixEnd_1638311 := by exact prefixLift 1638311
  have htrace : WordTrace (prefixWord ++ tailWord_1638311) baseStart_1638311 baseEnd_1638311 := by
    simpa [prefixWord, tailWord_1638311, baseEnd_1638311] using wordTrace_append hprefix tailTrace_1638311
  have hstable : (prefixWord ++ tailWord_1638311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1638311).length < 2 ^ (prefixWord ++ tailWord_1638311).sum := by decide
  have hdescent : baseEnd_1638311 < baseStart_1638311 := by decide
  rcases family_descends (prefixWord ++ tailWord_1638311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1638321 : List Nat := [1, 2, 2, 4, 2, 1, 1, 3, 3, 1, 3]
def baseStart_1638321 : Nat := 118140960795 + 1638321 * 2 ^ 59
def prefixEnd_1638321 : Nat := 4983230072969 + 3 ^ 40 * 1638321 * 2
def baseEnd_1638321 : Nat := 841246139354789795253005

theorem tailTrace_1638321 : CollatzResearch.WordTrace tailWord_1638321 prefixEnd_1638321 841246139354789795253005 := by
  unfold tailWord_1638321
  simp only [CollatzResearch.WordTrace]
  refine ⟨59754475897650294795658817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39836317265100196530439211 59754475897650294795658817)
  ·
    refine ⟨44815856923237721096744113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59754475897650294795658817 44815856923237721096744113)
    ·
      refine ⟨33611892692428290822558085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44815856923237721096744113 33611892692428290822558085)
      ·
        refine ⟨6302229879830304529229641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33611892692428290822558085 6302229879830304529229641)
        ·
          refine ⟨4726672409872728396922231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6302229879830304529229641 4726672409872728396922231)
          ·
            refine ⟨7090008614809092595383347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4726672409872728396922231 7090008614809092595383347)
            ·
              refine ⟨10635012922213638893075021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7090008614809092595383347 10635012922213638893075021)
              ·
                refine ⟨3988129845830114584903133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10635012922213638893075021 3988129845830114584903133)
                ·
                  refine ⟨1495548692186292969338675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3988129845830114584903133 1495548692186292969338675)
                  ·
                    refine ⟨2243323038279439454008013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1495548692186292969338675 2243323038279439454008013)
                    ·
                      refine ⟨841246139354789795253005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2243323038279439454008013 841246139354789795253005)
                      ·
                        rfl

theorem cell23_1638321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 3, 3, 1, 3].length) (baseStart_1638321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1638321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1638321 prefixEnd_1638321 := by exact prefixLift 1638321
  have htrace : WordTrace (prefixWord ++ tailWord_1638321) baseStart_1638321 baseEnd_1638321 := by
    simpa [prefixWord, tailWord_1638321, baseEnd_1638321] using wordTrace_append hprefix tailTrace_1638321
  have hstable : (prefixWord ++ tailWord_1638321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1638321).length < 2 ^ (prefixWord ++ tailWord_1638321).sum := by decide
  have hdescent : baseEnd_1638321 < baseStart_1638321 := by decide
  rcases family_descends (prefixWord ++ tailWord_1638321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1638347 : List Nat := [1, 1, 1, 1, 3, 4, 1, 2, 3, 1, 5]
def baseStart_1638347 : Nat := 118140960795 + 1638347 * 2 ^ 59
def prefixEnd_1638347 : Nat := 4983230072969 + 3 ^ 40 * 1638347 * 2
def baseEnd_1638347 : Nat := 841259489851806693527885

theorem tailTrace_1638347 : CollatzResearch.WordTrace tailWord_1638347 prefixEnd_1638347 841259489851806693527885 := by
  unfold tailWord_1638347
  simp only [CollatzResearch.WordTrace]
  refine ⟨59755424195556101236105295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39836949463704067490736863 59755424195556101236105295)
  ·
    refine ⟨89633136293334151854157943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59755424195556101236105295 89633136293334151854157943)
    ·
      refine ⟨134449704440001227781236915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89633136293334151854157943 134449704440001227781236915)
      ·
        refine ⟨201674556660001841671855373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134449704440001227781236915 201674556660001841671855373)
        ·
          refine ⟨75627958747500690626945765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 201674556660001841671855373 75627958747500690626945765)
          ·
            refine ⟨14180242265156379492552331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 75627958747500690626945765 14180242265156379492552331)
            ·
              refine ⟨21270363397734569238828497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14180242265156379492552331 21270363397734569238828497)
              ·
                refine ⟨15952772548300926929121373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21270363397734569238828497 15952772548300926929121373)
                ·
                  refine ⟨5982289705612847598420515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15952772548300926929121373 5982289705612847598420515)
                  ·
                    refine ⟨8973434558419271397630773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5982289705612847598420515 8973434558419271397630773)
                    ·
                      refine ⟨841259489851806693527885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8973434558419271397630773 841259489851806693527885)
                      ·
                        rfl

theorem cell23_1638347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 2, 3, 1, 5].length) (baseStart_1638347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1638347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1638347 prefixEnd_1638347 := by exact prefixLift 1638347
  have htrace : WordTrace (prefixWord ++ tailWord_1638347) baseStart_1638347 baseEnd_1638347 := by
    simpa [prefixWord, tailWord_1638347, baseEnd_1638347] using wordTrace_append hprefix tailTrace_1638347
  have hstable : (prefixWord ++ tailWord_1638347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1638347).length < 2 ^ (prefixWord ++ tailWord_1638347).sum := by decide
  have hdescent : baseEnd_1638347 < baseStart_1638347 := by decide
  rcases family_descends (prefixWord ++ tailWord_1638347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
