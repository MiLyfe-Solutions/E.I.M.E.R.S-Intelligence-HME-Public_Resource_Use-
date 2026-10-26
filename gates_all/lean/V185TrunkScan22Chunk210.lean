import V185TrunkScan22Chunk209

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_1872341 : List Nat := [1, 3, 2, 3, 1, 3, 1, 1, 4, 3]
def baseStart_1872341 : Nat := 118140960795 + 1872341 * 2 ^ 59
def prefixEnd_1872341 : Nat := 4983230072969 + 3 ^ 40 * 1872341 * 2
def baseEnd_1872341 : Nat := 640940588079976127284511

theorem tailTrace_1872341 : CollatzResearch.WordTrace tailWord_1872341 prefixEnd_1872341 640940588079976127284511 := by
  unfold tailWord_1872341
  simp only [CollatzResearch.WordTrace]
  refine ⟨68289886509835802229688877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45526591006557201486459251 68289886509835802229688877)
  ·
    refine ⟨25608707441188425836133329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68289886509835802229688877 25608707441188425836133329)
    ·
      refine ⟨19206530580891319377099997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25608707441188425836133329 19206530580891319377099997)
      ·
        refine ⟨7202448967834244766412499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19206530580891319377099997 7202448967834244766412499)
        ·
          refine ⟨10803673451751367149618749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7202448967834244766412499 10803673451751367149618749)
          ·
            refine ⟨4051377544406762681107031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10803673451751367149618749 4051377544406762681107031)
            ·
              refine ⟨6077066316610144021660547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4051377544406762681107031 6077066316610144021660547)
              ·
                refine ⟨9115599474915216032490821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6077066316610144021660547 9115599474915216032490821)
                ·
                  refine ⟨1709174901546603006092029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9115599474915216032490821 1709174901546603006092029)
                  ·
                    refine ⟨640940588079976127284511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1709174901546603006092029 640940588079976127284511)
                    ·
                      rfl

theorem cell22_1872341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 1, 1, 4, 3].length) (baseStart_1872341 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1872341 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1872341 prefixEnd_1872341 := by exact prefixLift 1872341
  have htrace : WordTrace (prefixWord ++ tailWord_1872341) baseStart_1872341 baseEnd_1872341 := by
    simpa [prefixWord, tailWord_1872341, baseEnd_1872341] using wordTrace_append hprefix tailTrace_1872341
  have hstable : (prefixWord ++ tailWord_1872341).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1872341).length < 2 ^ (prefixWord ++ tailWord_1872341).sum := by decide
  have hdescent : baseEnd_1872341 < baseStart_1872341 := by decide
  rcases family_descends (prefixWord ++ tailWord_1872341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1872390 : List Nat := [6, 2, 1, 1, 1, 1, 1, 1, 4, 4]
def baseStart_1872390 : Nat := 118140960795 + 1872390 * 2 ^ 59
def prefixEnd_1872390 : Nat := 4983230072969 + 3 ^ 40 * 1872390 * 2
def baseEnd_1872390 : Nat := 640957361781356332809361

theorem tailTrace_1872390 : CollatzResearch.WordTrace tailWord_1872390 prefixEnd_1872390 640957361781356332809361 := by
  unfold tailWord_1872390
  simp only [CollatzResearch.WordTrace]
  refine ⟨2134114802708071362444457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 45527782457772189065481749 2134114802708071362444457)
  ·
    refine ⟨1600586102031053521833343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2134114802708071362444457 1600586102031053521833343)
    ·
      refine ⟨2400879153046580282750015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1600586102031053521833343 2400879153046580282750015)
      ·
        refine ⟨3601318729569870424125023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2400879153046580282750015 3601318729569870424125023)
        ·
          refine ⟨5401978094354805636187535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3601318729569870424125023 5401978094354805636187535)
          ·
            refine ⟨8102967141532208454281303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5401978094354805636187535 8102967141532208454281303)
            ·
              refine ⟨12154450712298312681421955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8102967141532208454281303 12154450712298312681421955)
              ·
                refine ⟨18231676068447469022132933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12154450712298312681421955 18231676068447469022132933)
                ·
                  refine ⟨3418439262833900441649925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18231676068447469022132933 3418439262833900441649925)
                  ·
                    refine ⟨640957361781356332809361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3418439262833900441649925 640957361781356332809361)
                    ·
                      rfl

theorem cell22_1872390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 1, 4, 4].length) (baseStart_1872390 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1872390 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1872390 prefixEnd_1872390 := by exact prefixLift 1872390
  have htrace : WordTrace (prefixWord ++ tailWord_1872390) baseStart_1872390 baseEnd_1872390 := by
    simpa [prefixWord, tailWord_1872390, baseEnd_1872390] using wordTrace_append hprefix tailTrace_1872390
  have hstable : (prefixWord ++ tailWord_1872390).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1872390).length < 2 ^ (prefixWord ++ tailWord_1872390).sum := by decide
  have hdescent : baseEnd_1872390 < baseStart_1872390 := by decide
  rcases family_descends (prefixWord ++ tailWord_1872390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1872454 : List Nat := [6, 1, 1, 1, 2, 1, 4, 2, 1, 3]
def baseStart_1872454 : Nat := 118140960795 + 1872454 * 2 ^ 59
def prefixEnd_1872454 : Nat := 4983230072969 + 3 ^ 40 * 1872454 * 2
def baseEnd_1872454 : Nat := 640979270289281499209165

theorem tailTrace_1872454 : CollatzResearch.WordTrace tailWord_1872454 prefixEnd_1872454 640979270289281499209165 := by
  unfold tailWord_1872454
  simp only [CollatzResearch.WordTrace]
  refine ⟨2134187748700825704017263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 45529338638950948352368277 2134187748700825704017263)
  ·
    refine ⟨3201281623051238556025895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2134187748700825704017263 3201281623051238556025895)
    ·
      refine ⟨4801922434576857834038843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3201281623051238556025895 4801922434576857834038843)
      ·
        refine ⟨7202883651865286751058265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4801922434576857834038843 7202883651865286751058265)
        ·
          refine ⟨5402162738898965063293699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7202883651865286751058265 5402162738898965063293699)
          ·
            refine ⟨8103244108348447594940549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5402162738898965063293699 8103244108348447594940549)
            ·
              refine ⟨1519358270315333924051353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8103244108348447594940549 1519358270315333924051353)
              ·
                refine ⟨1139518702736500443038515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1519358270315333924051353 1139518702736500443038515)
                ·
                  refine ⟨1709278054104750664557773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1139518702736500443038515 1709278054104750664557773)
                  ·
                    refine ⟨640979270289281499209165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1709278054104750664557773 640979270289281499209165)
                    ·
                      rfl

theorem cell22_1872454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 4, 2, 1, 3].length) (baseStart_1872454 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1872454 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1872454 prefixEnd_1872454 := by exact prefixLift 1872454
  have htrace : WordTrace (prefixWord ++ tailWord_1872454) baseStart_1872454 baseEnd_1872454 := by
    simpa [prefixWord, tailWord_1872454, baseEnd_1872454] using wordTrace_append hprefix tailTrace_1872454
  have hstable : (prefixWord ++ tailWord_1872454).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1872454).length < 2 ^ (prefixWord ++ tailWord_1872454).sum := by decide
  have hdescent : baseEnd_1872454 < baseStart_1872454 := by decide
  rcases family_descends (prefixWord ++ tailWord_1872454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1872572 : List Nat := [2, 2, 2, 3, 1, 1, 5, 2, 1, 3]
def baseStart_1872572 : Nat := 118140960795 + 1872572 * 2 ^ 59
def prefixEnd_1872572 : Nat := 4983230072969 + 3 ^ 40 * 1872572 * 2
def baseEnd_1872572 : Nat := 641019664100768524758803

theorem tailTrace_1872572 : CollatzResearch.WordTrace tailWord_1872572 prefixEnd_1872572 641019664100768524758803 := by
  unfold tailWord_1872572
  simp only [CollatzResearch.WordTrace]
  refine ⟨34149155885999464340673985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45532207847999285787565313 34149155885999464340673985)
  ·
    refine ⟨25611866914499598255505489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34149155885999464340673985 25611866914499598255505489)
    ·
      refine ⟨19208900185874698691629117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25611866914499598255505489 19208900185874698691629117)
      ·
        refine ⟨7203337569703012009360919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19208900185874698691629117 7203337569703012009360919)
        ·
          refine ⟨10805006354554518014041379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7203337569703012009360919 10805006354554518014041379)
          ·
            refine ⟨16207509531831777021062069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10805006354554518014041379 16207509531831777021062069)
            ·
              refine ⟨1519454018609229095724569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16207509531831777021062069 1519454018609229095724569)
              ·
                refine ⟨1139590513956921821793427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1519454018609229095724569 1139590513956921821793427)
                ·
                  refine ⟨1709385770935382732690141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1139590513956921821793427 1709385770935382732690141)
                  ·
                    refine ⟨641019664100768524758803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1709385770935382732690141 641019664100768524758803)
                    ·
                      rfl

theorem cell22_1872572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 5, 2, 1, 3].length) (baseStart_1872572 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1872572 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1872572 prefixEnd_1872572 := by exact prefixLift 1872572
  have htrace : WordTrace (prefixWord ++ tailWord_1872572) baseStart_1872572 baseEnd_1872572 := by
    simpa [prefixWord, tailWord_1872572, baseEnd_1872572] using wordTrace_append hprefix tailTrace_1872572
  have hstable : (prefixWord ++ tailWord_1872572).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1872572).length < 2 ^ (prefixWord ++ tailWord_1872572).sum := by decide
  have hdescent : baseEnd_1872572 < baseStart_1872572 := by decide
  rcases family_descends (prefixWord ++ tailWord_1872572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1872630 : List Nat := [5, 1, 1, 1, 1, 2, 3, 4, 4]
def baseStart_1872630 : Nat := 118140960795 + 1872630 * 2 ^ 59
def prefixEnd_1872630 : Nat := 4983230072969 + 3 ^ 40 * 1872630 * 2
def baseEnd_1872630 : Nat := 213679839562025235602875

theorem tailTrace_1872630 : CollatzResearch.WordTrace tailWord_1872630 prefixEnd_1872630 213679839562025235602875 := by
  unfold tailWord_1872630
  simp only [CollatzResearch.WordTrace]
  refine ⟨4268776700361800286684959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 45533618137192536391306229 4268776700361800286684959)
  ·
    refine ⟨6403165050542700430027439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4268776700361800286684959 6403165050542700430027439)
    ·
      refine ⟨9604747575814050645041159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6403165050542700430027439 9604747575814050645041159)
      ·
        refine ⟨14407121363721075967561739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9604747575814050645041159 14407121363721075967561739)
        ·
          refine ⟨21610682045581613951342609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14407121363721075967561739 21610682045581613951342609)
          ·
            refine ⟨16208011534186210463506957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21610682045581613951342609 16208011534186210463506957)
            ·
              refine ⟨6078004325319828923815109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16208011534186210463506957 6078004325319828923815109)
              ·
                refine ⟨1139625810997467923215333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6078004325319828923815109 1139625810997467923215333)
                ·
                  refine ⟨213679839562025235602875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1139625810997467923215333 213679839562025235602875)
                  ·
                    rfl

theorem cell22_1872630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 3, 4, 4].length) (baseStart_1872630 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1872630 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1872630 prefixEnd_1872630 := by exact prefixLift 1872630
  have htrace : WordTrace (prefixWord ++ tailWord_1872630) baseStart_1872630 baseEnd_1872630 := by
    simpa [prefixWord, tailWord_1872630, baseEnd_1872630] using wordTrace_append hprefix tailTrace_1872630
  have hstable : (prefixWord ++ tailWord_1872630).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1872630).length < 2 ^ (prefixWord ++ tailWord_1872630).sum := by decide
  have hdescent : baseEnd_1872630 < baseStart_1872630 := by decide
  rcases family_descends (prefixWord ++ tailWord_1872630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1872673 : List Nat := [1, 2, 3, 2, 1, 2, 1, 2, 5, 3]
def baseStart_1872673 : Nat := 118140960795 + 1872673 * 2 ^ 59
def prefixEnd_1872673 : Nat := 4983230072969 + 3 ^ 40 * 1872673 * 2
def baseEnd_1872673 : Nat := 641054238464837927983493

theorem tailTrace_1872673 : CollatzResearch.WordTrace tailWord_1872673 prefixEnd_1872673 641054238464837927983493 := by
  unfold tailWord_1872673
  simp only [CollatzResearch.WordTrace]
  refine ⟨68301995544633022930774673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45534663696422015287183115 68301995544633022930774673)
  ·
    refine ⟨51226496658474767198081005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68301995544633022930774673 51226496658474767198081005)
    ·
      refine ⟨19209936246928037699280377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51226496658474767198081005 19209936246928037699280377)
      ·
        refine ⟨14407452185196028274460283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19209936246928037699280377 14407452185196028274460283)
        ·
          refine ⟨21611178277794042411690425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14407452185196028274460283 21611178277794042411690425)
          ·
            refine ⟨16208383708345531808767819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21611178277794042411690425 16208383708345531808767819)
            ·
              refine ⟨24312575562518297713151729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16208383708345531808767819 24312575562518297713151729)
              ·
                refine ⟨18234431671888723284863797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24312575562518297713151729 18234431671888723284863797)
                ·
                  refine ⟨1709477969239567807955981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 18234431671888723284863797 1709477969239567807955981)
                  ·
                    refine ⟨641054238464837927983493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1709477969239567807955981 641054238464837927983493)
                    ·
                      rfl

theorem cell22_1872673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 2, 5, 3].length) (baseStart_1872673 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1872673 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1872673 prefixEnd_1872673 := by exact prefixLift 1872673
  have htrace : WordTrace (prefixWord ++ tailWord_1872673) baseStart_1872673 baseEnd_1872673 := by
    simpa [prefixWord, tailWord_1872673, baseEnd_1872673] using wordTrace_append hprefix tailTrace_1872673
  have hstable : (prefixWord ++ tailWord_1872673).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1872673).length < 2 ^ (prefixWord ++ tailWord_1872673).sum := by decide
  have hdescent : baseEnd_1872673 < baseStart_1872673 := by decide
  rcases family_descends (prefixWord ++ tailWord_1872673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1872690 : List Nat := [3, 2, 1, 1, 3, 1, 4, 1, 3, 3]
def baseStart_1872690 : Nat := 118140960795 + 1872690 * 2 ^ 59
def prefixEnd_1872690 : Nat := 4983230072969 + 3 ^ 40 * 1872690 * 2
def baseEnd_1872690 : Nat := 641060057912255550308441

theorem tailTrace_1872690 : CollatzResearch.WordTrace tailWord_1872690 prefixEnd_1872690 641060057912255550308441 := by
  unfold tailWord_1872690
  simp only [CollatzResearch.WordTrace]
  refine ⟨17075653896392858708535881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45535077057047623222762349 17075653896392858708535881)
  ·
    refine ⟨12806740422294644031401911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17075653896392858708535881 12806740422294644031401911)
    ·
      refine ⟨19210110633441966047102867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12806740422294644031401911 19210110633441966047102867)
      ·
        refine ⟨28815165950162949070654301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19210110633441966047102867 28815165950162949070654301)
        ·
          refine ⟨10805687231311105901495363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28815165950162949070654301 10805687231311105901495363)
          ·
            refine ⟨16208530846966658852243045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10805687231311105901495363 16208530846966658852243045)
            ·
              refine ⟨3039099533806248534795571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16208530846966658852243045 3039099533806248534795571)
              ·
                refine ⟨4558649300709372802193357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3039099533806248534795571 4558649300709372802193357)
                ·
                  refine ⟨1709493487766014800822509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4558649300709372802193357 1709493487766014800822509)
                  ·
                    refine ⟨641060057912255550308441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1709493487766014800822509 641060057912255550308441)
                    ·
                      rfl

theorem cell22_1872690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 4, 1, 3, 3].length) (baseStart_1872690 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1872690 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1872690 prefixEnd_1872690 := by exact prefixLift 1872690
  have htrace : WordTrace (prefixWord ++ tailWord_1872690) baseStart_1872690 baseEnd_1872690 := by
    simpa [prefixWord, tailWord_1872690, baseEnd_1872690] using wordTrace_append hprefix tailTrace_1872690
  have hstable : (prefixWord ++ tailWord_1872690).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1872690).length < 2 ^ (prefixWord ++ tailWord_1872690).sum := by decide
  have hdescent : baseEnd_1872690 < baseStart_1872690 := by decide
  rcases family_descends (prefixWord ++ tailWord_1872690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1872797 : List Nat := [1, 4, 2, 1, 2, 1, 4, 2, 2, 3]
def baseStart_1872797 : Nat := 118140960795 + 1872797 * 2 ^ 59
def prefixEnd_1872797 : Nat := 4983230072969 + 3 ^ 40 * 1872797 * 2
def baseEnd_1872797 : Nat := 641096686198942937883113

theorem tailTrace_1872797 : CollatzResearch.WordTrace tailWord_1872797 prefixEnd_1872797 641096686198942937883113 := by
  unfold tailWord_1872797
  simp only [CollatzResearch.WordTrace]
  refine ⟨68306518196183792108288645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45537678797455861405525763 68306518196183792108288645)
  ·
    refine ⟨12807472161784461020304121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 68306518196183792108288645 12807472161784461020304121)
    ·
      refine ⟨9605604121338345765228091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12807472161784461020304121 9605604121338345765228091)
      ·
        refine ⟨14408406182007518647842137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9605604121338345765228091 14408406182007518647842137)
        ·
          refine ⟨10806304636505638985881603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14408406182007518647842137 10806304636505638985881603)
          ·
            refine ⟨16209456954758458478822405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10806304636505638985881603 16209456954758458478822405)
            ·
              refine ⟨3039273179017210964779201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16209456954758458478822405 3039273179017210964779201)
              ·
                refine ⟨2279454884262908223584401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3039273179017210964779201 2279454884262908223584401)
                ·
                  refine ⟨1709591163197181167688301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2279454884262908223584401 1709591163197181167688301)
                  ·
                    refine ⟨641096686198942937883113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1709591163197181167688301 641096686198942937883113)
                    ·
                      rfl

theorem cell22_1872797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 4, 2, 2, 3].length) (baseStart_1872797 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1872797 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1872797 prefixEnd_1872797 := by exact prefixLift 1872797
  have htrace : WordTrace (prefixWord ++ tailWord_1872797) baseStart_1872797 baseEnd_1872797 := by
    simpa [prefixWord, tailWord_1872797, baseEnd_1872797] using wordTrace_append hprefix tailTrace_1872797
  have hstable : (prefixWord ++ tailWord_1872797).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1872797).length < 2 ^ (prefixWord ++ tailWord_1872797).sum := by decide
  have hdescent : baseEnd_1872797 < baseStart_1872797 := by decide
  rcases family_descends (prefixWord ++ tailWord_1872797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1872799 : List Nat := [1, 1, 2, 5, 2, 3, 2, 2, 4]
def baseStart_1872799 : Nat := 118140960795 + 1872799 * 2 ^ 59
def prefixEnd_1872799 : Nat := 4983230072969 + 3 ^ 40 * 1872799 * 2
def baseEnd_1872799 : Nat := 213699123613271866444369

theorem tailTrace_1872799 : CollatzResearch.WordTrace tailWord_1872799 prefixEnd_1872799 213699123613271866444369 := by
  unfold tailWord_1872799
  simp only [CollatzResearch.WordTrace]
  refine ⟨68306591142176546449861451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45537727428117697633240967 68306591142176546449861451)
  ·
    refine ⟨102459886713264819674792177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68306591142176546449861451 102459886713264819674792177)
    ·
      refine ⟨76844915034948614756094133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102459886713264819674792177 76844915034948614756094133)
      ·
        refine ⟨7204210784526432633383825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 76844915034948614756094133 7204210784526432633383825)
        ·
          refine ⟨5403158088394824475037869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7204210784526432633383825 5403158088394824475037869)
          ·
            refine ⟨2026184283148059178139201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5403158088394824475037869 2026184283148059178139201)
            ·
              refine ⟨1519638212361044383604401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2026184283148059178139201 1519638212361044383604401)
              ·
                refine ⟨1139728659270783287703301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1519638212361044383604401 1139728659270783287703301)
                ·
                  refine ⟨213699123613271866444369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1139728659270783287703301 213699123613271866444369)
                  ·
                    rfl

theorem cell22_1872799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 3, 2, 2, 4].length) (baseStart_1872799 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1872799 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1872799 prefixEnd_1872799 := by exact prefixLift 1872799
  have htrace : WordTrace (prefixWord ++ tailWord_1872799) baseStart_1872799 baseEnd_1872799 := by
    simpa [prefixWord, tailWord_1872799, baseEnd_1872799] using wordTrace_append hprefix tailTrace_1872799
  have hstable : (prefixWord ++ tailWord_1872799).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1872799).length < 2 ^ (prefixWord ++ tailWord_1872799).sum := by decide
  have hdescent : baseEnd_1872799 < baseStart_1872799 := by decide
  rcases family_descends (prefixWord ++ tailWord_1872799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1872825 : List Nat := [1, 2, 1, 4, 2, 2, 1, 1, 5, 3]
def baseStart_1872825 : Nat := 118140960795 + 1872825 * 2 ^ 59
def prefixEnd_1872825 : Nat := 4983230072969 + 3 ^ 40 * 1872825 * 2
def baseEnd_1872825 : Nat := 641106271171160198183027

theorem tailTrace_1872825 : CollatzResearch.WordTrace tailWord_1872825 prefixEnd_1872825 641106271171160198183027 := by
  unfold tailWord_1872825
  simp only [CollatzResearch.WordTrace]
  refine ⟨68307539440082352890307929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45538359626721568593538619 68307539440082352890307929)
  ·
    refine ⟨51230654580061764667730947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68307539440082352890307929 51230654580061764667730947)
    ·
      refine ⟨76845981870092647001596421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51230654580061764667730947 76845981870092647001596421)
      ·
        refine ⟨14408621600642371312799329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 76845981870092647001596421 14408621600642371312799329)
        ·
          refine ⟨10806466200481778484599497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14408621600642371312799329 10806466200481778484599497)
          ·
            refine ⟨8104849650361333863449623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10806466200481778484599497 8104849650361333863449623)
            ·
              refine ⟨12157274475542000795174435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8104849650361333863449623 12157274475542000795174435)
              ·
                refine ⟨18235911713313001192761653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12157274475542000795174435 18235911713313001192761653)
                ·
                  refine ⟨1709616723123093861821405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 18235911713313001192761653 1709616723123093861821405)
                  ·
                    refine ⟨641106271171160198183027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1709616723123093861821405 641106271171160198183027)
                    ·
                      rfl

theorem cell22_1872825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 1, 5, 3].length) (baseStart_1872825 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1872825 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1872825 prefixEnd_1872825 := by exact prefixLift 1872825
  have htrace : WordTrace (prefixWord ++ tailWord_1872825) baseStart_1872825 baseEnd_1872825 := by
    simpa [prefixWord, tailWord_1872825, baseEnd_1872825] using wordTrace_append hprefix tailTrace_1872825
  have hstable : (prefixWord ++ tailWord_1872825).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1872825).length < 2 ^ (prefixWord ++ tailWord_1872825).sum := by decide
  have hdescent : baseEnd_1872825 < baseStart_1872825 := by decide
  rcases family_descends (prefixWord ++ tailWord_1872825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1872829 : List Nat := [1, 4, 1, 2, 5, 1, 1, 1, 2, 4]
def baseStart_1872829 : Nat := 118140960795 + 1872829 * 2 ^ 59
def prefixEnd_1872829 : Nat := 4983230072969 + 3 ^ 40 * 1872829 * 2
def baseEnd_1872829 : Nat := 641107640452905521083015

theorem tailTrace_1872829 : CollatzResearch.WordTrace tailWord_1872829 prefixEnd_1872829 641107640452905521083015 := by
  unfold tailWord_1872829
  simp only [CollatzResearch.WordTrace]
  refine ⟨68307685332067861573453541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45538456888045241048969027 68307685332067861573453541)
  ·
    refine ⟨12807690999762724045022539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 68307685332067861573453541 12807690999762724045022539)
    ·
      refine ⟨19211536499644086067533809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12807690999762724045022539 19211536499644086067533809)
      ·
        refine ⟨14408652374733064550650357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19211536499644086067533809 14408652374733064550650357)
        ·
          refine ⟨1350811160131224801623471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14408652374733064550650357 1350811160131224801623471)
          ·
            refine ⟨2026216740196837202435207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1350811160131224801623471 2026216740196837202435207)
            ·
              refine ⟨3039325110295255803652811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2026216740196837202435207 3039325110295255803652811)
              ·
                refine ⟨4558987665442883705479217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3039325110295255803652811 4558987665442883705479217)
                ·
                  refine ⟨3419240749082162779109413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4558987665442883705479217 3419240749082162779109413)
                  ·
                    refine ⟨641107640452905521083015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3419240749082162779109413 641107640452905521083015)
                    ·
                      rfl

theorem cell22_1872829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 5, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 5, 1, 1, 1, 2, 4].length) (baseStart_1872829 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1872829 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1872829 prefixEnd_1872829 := by exact prefixLift 1872829
  have htrace : WordTrace (prefixWord ++ tailWord_1872829) baseStart_1872829 baseEnd_1872829 := by
    simpa [prefixWord, tailWord_1872829, baseEnd_1872829] using wordTrace_append hprefix tailTrace_1872829
  have hstable : (prefixWord ++ tailWord_1872829).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1872829).length < 2 ^ (prefixWord ++ tailWord_1872829).sum := by decide
  have hdescent : baseEnd_1872829 < baseStart_1872829 := by decide
  rcases family_descends (prefixWord ++ tailWord_1872829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1872868 : List Nat := [2, 3, 1, 1, 1, 1, 2, 1, 2, 8]
def baseStart_1872868 : Nat := 118140960795 + 1872868 * 2 ^ 59
def prefixEnd_1872868 : Nat := 4983230072969 + 3 ^ 40 * 1872868 * 2
def baseEnd_1872868 : Nat := 641120990949922419357895

theorem tailTrace_1872868 : CollatzResearch.WordTrace tailWord_1872868 prefixEnd_1872868 641120990949922419357895 := by
  unfold tailWord_1872868
  simp only [CollatzResearch.WordTrace]
  refine ⟨34154553889463285617061629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45539405185951047489415505 34154553889463285617061629)
  ·
    refine ⟨12807957708548732106398111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34154553889463285617061629 12807957708548732106398111)
    ·
      refine ⟨19211936562823098159597167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12807957708548732106398111 19211936562823098159597167)
      ·
        refine ⟨28817904844234647239395751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19211936562823098159597167 28817904844234647239395751)
        ·
          refine ⟨43226857266351970859093627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28817904844234647239395751 43226857266351970859093627)
          ·
            refine ⟨64840285899527956288640441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43226857266351970859093627 64840285899527956288640441)
            ·
              refine ⟨48630214424645967216480331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64840285899527956288640441 48630214424645967216480331)
              ·
                refine ⟨72945321636968950824720497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48630214424645967216480331 72945321636968950824720497)
                ·
                  refine ⟨54708991227726713118540373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72945321636968950824720497 54708991227726713118540373)
                  ·
                    refine ⟨641120990949922419357895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 54708991227726713118540373 641120990949922419357895)
                    ·
                      rfl

theorem cell22_1872868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 1, 2, 8].length) (baseStart_1872868 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1872868 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1872868 prefixEnd_1872868 := by exact prefixLift 1872868
  have htrace : WordTrace (prefixWord ++ tailWord_1872868) baseStart_1872868 baseEnd_1872868 := by
    simpa [prefixWord, tailWord_1872868, baseEnd_1872868] using wordTrace_append hprefix tailTrace_1872868
  have hstable : (prefixWord ++ tailWord_1872868).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1872868).length < 2 ^ (prefixWord ++ tailWord_1872868).sum := by decide
  have hdescent : baseEnd_1872868 < baseStart_1872868 := by decide
  rcases family_descends (prefixWord ++ tailWord_1872868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1872917 : List Nat := [1, 3, 2, 1, 4, 3, 1, 1, 6]
def baseStart_1872917 : Nat := 118140960795 + 1872917 * 2 ^ 59
def prefixEnd_1872917 : Nat := 4983230072969 + 3 ^ 40 * 1872917 * 2
def baseEnd_1872917 : Nat := 213712588217100874960915

theorem tailTrace_1872917 : CollatzResearch.WordTrace tailWord_1872917 prefixEnd_1872917 213712588217100874960915 := by
  unfold tailWord_1872917
  simp only [CollatzResearch.WordTrace]
  refine ⟨68310894955749052602657005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45540596637166035068438003 68310894955749052602657005)
  ·
    refine ⟨25616585608405894725996377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68310894955749052602657005 25616585608405894725996377)
    ·
      refine ⟨19212439206304421044497283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25616585608405894725996377 19212439206304421044497283)
      ·
        refine ⟨28818658809456631566745925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19212439206304421044497283 28818658809456631566745925)
        ·
          refine ⟨5403498526773118418764861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28818658809456631566745925 5403498526773118418764861)
          ·
            refine ⟨2026311947539919407036823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5403498526773118418764861 2026311947539919407036823)
            ·
              refine ⟨3039467921309879110555235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2026311947539919407036823 3039467921309879110555235)
              ·
                refine ⟨4559201881964818665832853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3039467921309879110555235 4559201881964818665832853)
                ·
                  refine ⟨213712588217100874960915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4559201881964818665832853 213712588217100874960915)
                  ·
                    rfl

theorem cell22_1872917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 3, 1, 1, 6].length) (baseStart_1872917 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1872917 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1872917 prefixEnd_1872917 := by exact prefixLift 1872917
  have htrace : WordTrace (prefixWord ++ tailWord_1872917) baseStart_1872917 baseEnd_1872917 := by
    simpa [prefixWord, tailWord_1872917, baseEnd_1872917] using wordTrace_append hprefix tailTrace_1872917
  have hstable : (prefixWord ++ tailWord_1872917).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1872917).length < 2 ^ (prefixWord ++ tailWord_1872917).sum := by decide
  have hdescent : baseEnd_1872917 < baseStart_1872917 := by decide
  rcases family_descends (prefixWord ++ tailWord_1872917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1872966 : List Nat := [6, 1, 1, 1, 1, 2, 1, 4, 2, 3]
def baseStart_1872966 : Nat := 118140960795 + 1872966 * 2 ^ 59
def prefixEnd_1872966 : Nat := 4983230072969 + 3 ^ 40 * 1872966 * 2
def baseEnd_1872966 : Nat := 641154538352682830407595

theorem tailTrace_1872966 : CollatzResearch.WordTrace tailWord_1872966 prefixEnd_1872966 641154538352682830407595 := by
  unfold tailWord_1872966
  simp only [CollatzResearch.WordTrace]
  refine ⟨2134771316642860436599711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 45541788088381022647460501 2134771316642860436599711)
  ·
    refine ⟨3202156974964290654899567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2134771316642860436599711 3202156974964290654899567)
    ·
      refine ⟨4803235462446435982349351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3202156974964290654899567 4803235462446435982349351)
      ·
        refine ⟨7204853193669653973524027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4803235462446435982349351 7204853193669653973524027)
        ·
          refine ⟨10807279790504480960286041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7204853193669653973524027 10807279790504480960286041)
          ·
            refine ⟨8105459842878360720214531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10807279790504480960286041 8105459842878360720214531)
            ·
              refine ⟨12158189764317541080321797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8105459842878360720214531 12158189764317541080321797)
              ·
                refine ⟨2279660580809538952560337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12158189764317541080321797 2279660580809538952560337)
                ·
                  refine ⟨1709745435607154214420253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2279660580809538952560337 1709745435607154214420253)
                  ·
                    refine ⟨641154538352682830407595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1709745435607154214420253 641154538352682830407595)
                    ·
                      rfl

theorem cell22_1872966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 4, 2, 3].length) (baseStart_1872966 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1872966 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1872966 prefixEnd_1872966 := by exact prefixLift 1872966
  have htrace : WordTrace (prefixWord ++ tailWord_1872966) baseStart_1872966 baseEnd_1872966 := by
    simpa [prefixWord, tailWord_1872966, baseEnd_1872966] using wordTrace_append hprefix tailTrace_1872966
  have hstable : (prefixWord ++ tailWord_1872966).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1872966).length < 2 ^ (prefixWord ++ tailWord_1872966).sum := by decide
  have hdescent : baseEnd_1872966 < baseStart_1872966 := by decide
  rcases family_descends (prefixWord ++ tailWord_1872966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1872994 : List Nat := [3, 3, 2, 2, 1, 1, 1, 1, 5, 3]
def baseStart_1872994 : Nat := 118140960795 + 1872994 * 2 ^ 59
def prefixEnd_1872994 : Nat := 4983230072969 + 3 ^ 40 * 1872994 * 2
def baseEnd_1872994 : Nat := 641164123324900090707509

theorem tailTrace_1872994 : CollatzResearch.WordTrace tailWord_1872994 prefixEnd_1872994 641164123324900090707509 := by
  unfold tailWord_1872994
  simp only [CollatzResearch.WordTrace]
  refine ⟨17078425844117523688302509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45542468917646729835473357 17078425844117523688302509)
  ·
    refine ⟨6404409691544071383113441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17078425844117523688302509 6404409691544071383113441)
    ·
      refine ⟨4803307268658053537335081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6404409691544071383113441 4803307268658053537335081)
      ·
        refine ⟨3602480451493540153001311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4803307268658053537335081 3602480451493540153001311)
        ·
          refine ⟨5403720677240310229501967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3602480451493540153001311 5403720677240310229501967)
          ·
            refine ⟨8105581015860465344252951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5403720677240310229501967 8105581015860465344252951)
            ·
              refine ⟨12158371523790698016379427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8105581015860465344252951 12158371523790698016379427)
              ·
                refine ⟨18237557285686047024569141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12158371523790698016379427 18237557285686047024569141)
                ·
                  refine ⟨1709770995533066908553357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 18237557285686047024569141 1709770995533066908553357)
                  ·
                    refine ⟨641164123324900090707509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1709770995533066908553357 641164123324900090707509)
                    ·
                      rfl

theorem cell22_1872994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 1, 5, 3].length) (baseStart_1872994 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1872994 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1872994 prefixEnd_1872994 := by exact prefixLift 1872994
  have htrace : WordTrace (prefixWord ++ tailWord_1872994) baseStart_1872994 baseEnd_1872994 := by
    simpa [prefixWord, tailWord_1872994, baseEnd_1872994] using wordTrace_append hprefix tailTrace_1872994
  have hstable : (prefixWord ++ tailWord_1872994).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1872994).length < 2 ^ (prefixWord ++ tailWord_1872994).sum := by decide
  have hdescent : baseEnd_1872994 < baseStart_1872994 := by decide
  rcases family_descends (prefixWord ++ tailWord_1872994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1873052 : List Nat := [2, 2, 3, 2, 1, 2, 2, 2, 6]
def baseStart_1873052 : Nat := 118140960795 + 1873052 * 2 ^ 59
def prefixEnd_1873052 : Nat := 4983230072969 + 3 ^ 40 * 1873052 * 2
def baseEnd_1873052 : Nat := 213727992636735757585777

theorem tailTrace_1873052 : CollatzResearch.WordTrace tailWord_1873052 prefixEnd_1873052 213727992636735757585777 := by
  unfold tailWord_1873052
  simp only [CollatzResearch.WordTrace]
  refine ⟨34157909405129985329410705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45543879206839980439214273 34157909405129985329410705)
  ·
    refine ⟨25618432053847488997058029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34157909405129985329410705 25618432053847488997058029)
    ·
      refine ⟨9606912020192808373896761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25618432053847488997058029 9606912020192808373896761)
      ·
        refine ⟨7205184015144606280422571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9606912020192808373896761 7205184015144606280422571)
        ·
          refine ⟨10807776022716909420633857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7205184015144606280422571 10807776022716909420633857)
          ·
            refine ⟨8105832017037682065475393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10807776022716909420633857 8105832017037682065475393)
            ·
              refine ⟨6079374012778261549106545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8105832017037682065475393 6079374012778261549106545)
              ·
                refine ⟨4559530509583696161829909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6079374012778261549106545 4559530509583696161829909)
                ·
                  refine ⟨213727992636735757585777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4559530509583696161829909 213727992636735757585777)
                  ·
                    rfl

theorem cell22_1873052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 2, 2, 6].length) (baseStart_1873052 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1873052 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1873052 prefixEnd_1873052 := by exact prefixLift 1873052
  have htrace : WordTrace (prefixWord ++ tailWord_1873052) baseStart_1873052 baseEnd_1873052 := by
    simpa [prefixWord, tailWord_1873052, baseEnd_1873052] using wordTrace_append hprefix tailTrace_1873052
  have hstable : (prefixWord ++ tailWord_1873052).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1873052).length < 2 ^ (prefixWord ++ tailWord_1873052).sum := by decide
  have hdescent : baseEnd_1873052 < baseStart_1873052 := by decide
  rcases family_descends (prefixWord ++ tailWord_1873052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1873084 : List Nat := [2, 2, 2, 3, 2, 1, 2, 1, 4, 3]
def baseStart_1873084 : Nat := 118140960795 + 1873084 * 2 ^ 59
def prefixEnd_1873084 : Nat := 4983230072969 + 3 ^ 40 * 1873084 * 2
def baseEnd_1873084 : Nat := 641194932164169855957233

theorem tailTrace_1873084 : CollatzResearch.WordTrace tailWord_1873084 prefixEnd_1873084 641194932164169855957233 := by
  unfold tailWord_1873084
  simp only [CollatzResearch.WordTrace]
  refine ⟨34158492973072020061993153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45544657297429360082657537 34158492973072020061993153)
  ·
    refine ⟨25618869729804015046494865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34158492973072020061993153 25618869729804015046494865)
    ·
      refine ⟨19214152297353011284871149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25618869729804015046494865 19214152297353011284871149)
      ·
        refine ⟨7205307111507379231826681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19214152297353011284871149 7205307111507379231826681)
        ·
          refine ⟨5403980333630534423870011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7205307111507379231826681 5403980333630534423870011)
          ·
            refine ⟨8105970500445801635805017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5403980333630534423870011 8105970500445801635805017)
            ·
              refine ⟨6079477875334351226853763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8105970500445801635805017 6079477875334351226853763)
              ·
                refine ⟨9119216813001526840280645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6079477875334351226853763 9119216813001526840280645)
                ·
                  refine ⟨1709853152437786282552621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9119216813001526840280645 1709853152437786282552621)
                  ·
                    refine ⟨641194932164169855957233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1709853152437786282552621 641194932164169855957233)
                    ·
                      rfl

theorem cell22_1873084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 2, 1, 4, 3].length) (baseStart_1873084 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1873084 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1873084 prefixEnd_1873084 := by exact prefixLift 1873084
  have htrace : WordTrace (prefixWord ++ tailWord_1873084) baseStart_1873084 baseEnd_1873084 := by
    simpa [prefixWord, tailWord_1873084, baseEnd_1873084] using wordTrace_append hprefix tailTrace_1873084
  have hstable : (prefixWord ++ tailWord_1873084).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1873084).length < 2 ^ (prefixWord ++ tailWord_1873084).sum := by decide
  have hdescent : baseEnd_1873084 < baseStart_1873084 := by decide
  rcases family_descends (prefixWord ++ tailWord_1873084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1873146 : List Nat := [3, 1, 1, 1, 1, 4, 3, 4, 1, 3]
def baseStart_1873146 : Nat := 118140960795 + 1873146 * 2 ^ 59
def prefixEnd_1873146 : Nat := 4983230072969 + 3 ^ 40 * 1873146 * 2
def baseEnd_1873146 : Nat := 641216156031222360907043

theorem tailTrace_1873146 : CollatzResearch.WordTrace tailWord_1873146 prefixEnd_1873146 641216156031222360907043 := by
  unfold tailWord_1873146
  simp only [CollatzResearch.WordTrace]
  refine ⟨17079811817979856178185823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45546164847946283141828861 17079811817979856178185823)
  ·
    refine ⟨25619717726969784267278735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17079811817979856178185823 25619717726969784267278735)
    ·
      refine ⟨38429576590454676400918103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25619717726969784267278735 38429576590454676400918103)
      ·
        refine ⟨57644364885682014601377155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38429576590454676400918103 57644364885682014601377155)
        ·
          refine ⟨86466547328523021902065733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57644364885682014601377155 86466547328523021902065733)
          ·
            refine ⟨16212477624098066606637325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 86466547328523021902065733 16212477624098066606637325)
            ·
              refine ⟨6079679109036774977488997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16212477624098066606637325 6079679109036774977488997)
              ·
                refine ⟨1139939832944395308279187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6079679109036774977488997 1139939832944395308279187)
                ·
                  refine ⟨1709909749416592962418781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1139939832944395308279187 1709909749416592962418781)
                  ·
                    refine ⟨641216156031222360907043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1709909749416592962418781 641216156031222360907043)
                    ·
                      rfl

theorem cell22_1873146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 3, 4, 1, 3].length) (baseStart_1873146 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1873146 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1873146 prefixEnd_1873146 := by exact prefixLift 1873146
  have htrace : WordTrace (prefixWord ++ tailWord_1873146) baseStart_1873146 baseEnd_1873146 := by
    simpa [prefixWord, tailWord_1873146, baseEnd_1873146] using wordTrace_append hprefix tailTrace_1873146
  have hstable : (prefixWord ++ tailWord_1873146).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1873146).length < 2 ^ (prefixWord ++ tailWord_1873146).sum := by decide
  have hdescent : baseEnd_1873146 < baseStart_1873146 := by decide
  rcases family_descends (prefixWord ++ tailWord_1873146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1873157 : List Nat := [1, 3, 1, 1, 2, 1, 5, 1, 2, 5]
def baseStart_1873157 : Nat := 118140960795 + 1873157 * 2 ^ 59
def prefixEnd_1873157 : Nat := 4983230072969 + 3 ^ 40 * 1873157 * 2
def baseEnd_1873157 : Nat := 641219921556021998882009

theorem tailTrace_1873157 : CollatzResearch.WordTrace tailWord_1873157 prefixEnd_1873157 641219921556021998882009 := by
  unfold tailWord_1873157
  simp only [CollatzResearch.WordTrace]
  refine ⟨68319648474879573591393725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45546432316586382394262483 68319648474879573591393725)
  ·
    refine ⟨25619868178079840096772647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68319648474879573591393725 25619868178079840096772647)
    ·
      refine ⟨38429802267119760145158971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25619868178079840096772647 38429802267119760145158971)
      ·
        refine ⟨57644703400679640217738457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38429802267119760145158971 57644703400679640217738457)
        ·
          refine ⟨43233527550509730163303843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57644703400679640217738457 43233527550509730163303843)
          ·
            refine ⟨64850291325764595244955765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43233527550509730163303843 64850291325764595244955765)
            ·
              refine ⟨6079714811790430804214603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 64850291325764595244955765 6079714811790430804214603)
              ·
                refine ⟨9119572217685646206321905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6079714811790430804214603 9119572217685646206321905)
                ·
                  refine ⟨6839679163264234654741429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9119572217685646206321905 6839679163264234654741429)
                  ·
                    refine ⟨641219921556021998882009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6839679163264234654741429 641219921556021998882009)
                    ·
                      rfl

theorem cell22_1873157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 5, 1, 2, 5].length) (baseStart_1873157 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1873157 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1873157 prefixEnd_1873157 := by exact prefixLift 1873157
  have htrace : WordTrace (prefixWord ++ tailWord_1873157) baseStart_1873157 baseEnd_1873157 := by
    simpa [prefixWord, tailWord_1873157, baseEnd_1873157] using wordTrace_append hprefix tailTrace_1873157
  have hstable : (prefixWord ++ tailWord_1873157).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1873157).length < 2 ^ (prefixWord ++ tailWord_1873157).sum := by decide
  have hdescent : baseEnd_1873157 < baseStart_1873157 := by decide
  rcases family_descends (prefixWord ++ tailWord_1873157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1873232 : List Nat := [2, 1, 1, 1, 1, 5, 3, 8]
def baseStart_1873232 : Nat := 118140960795 + 1873232 * 2 ^ 59
def prefixEnd_1873232 : Nat := 4983230072969 + 3 ^ 40 * 1873232 * 2
def baseEnd_1873232 : Nat := 71249510620971867028531

theorem tailTrace_1873232 : CollatzResearch.WordTrace tailWord_1873232 prefixEnd_1873232 71249510620971867028531 := by
  unfold tailWord_1873232
  simp only [CollatzResearch.WordTrace]
  refine ⟨34161191974803930700186975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45548255966405240933582633 34161191974803930700186975)
  ·
    refine ⟨51241787962205896050280463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34161191974803930700186975 51241787962205896050280463)
    ·
      refine ⟨76862681943308844075420695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51241787962205896050280463 76862681943308844075420695)
      ·
        refine ⟨115294022914963266113131043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76862681943308844075420695 115294022914963266113131043)
        ·
          refine ⟨172941034372444899169696565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115294022914963266113131043 172941034372444899169696565)
          ·
            refine ⟨16213221972416709297159053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 172941034372444899169696565 16213221972416709297159053)
            ·
              refine ⟨6079958239656265986434645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16213221972416709297159053 6079958239656265986434645)
              ·
                refine ⟨71249510620971867028531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6079958239656265986434645 71249510620971867028531)
                ·
                  rfl

theorem cell22_1873232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 3, 8].length) (baseStart_1873232 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1873232 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1873232 prefixEnd_1873232 := by exact prefixLift 1873232
  have htrace : WordTrace (prefixWord ++ tailWord_1873232) baseStart_1873232 baseEnd_1873232 := by
    simpa [prefixWord, tailWord_1873232, baseEnd_1873232] using wordTrace_append hprefix tailTrace_1873232
  have hstable : (prefixWord ++ tailWord_1873232).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1873232).length < 2 ^ (prefixWord ++ tailWord_1873232).sum := by decide
  have hdescent : baseEnd_1873232 < baseStart_1873232 := by decide
  rcases family_descends (prefixWord ++ tailWord_1873232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1873234 : List Nat := [3, 2, 2, 1, 1, 1, 1, 5, 2, 4]
def baseStart_1873234 : Nat := 118140960795 + 1873234 * 2 ^ 59
def prefixEnd_1873234 : Nat := 4983230072969 + 3 ^ 40 * 1873234 * 2
def baseEnd_1873234 : Nat := 641246280229619464706773

theorem tailTrace_1873234 : CollatzResearch.WordTrace tailWord_1873234 prefixEnd_1873234 641246280229619464706773 := by
  unfold tailWord_1873234
  simp only [CollatzResearch.WordTrace]
  refine ⟨17080614223900153935486689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45548304597067077161297837 17080614223900153935486689)
  ·
    refine ⟨12810460667925115451615017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17080614223900153935486689 12810460667925115451615017)
    ·
      refine ⟨9607845500943836588711263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12810460667925115451615017 9607845500943836588711263)
      ·
        refine ⟨14411768251415754883066895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9607845500943836588711263 14411768251415754883066895)
        ·
          refine ⟨21617652377123632324600343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14411768251415754883066895 21617652377123632324600343)
          ·
            refine ⟨32426478565685448486900515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21617652377123632324600343 32426478565685448486900515)
            ·
              refine ⟨48639717848528172730350773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32426478565685448486900515 48639717848528172730350773)
              ·
                refine ⟨4559973548299516193470385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 48639717848528172730350773 4559973548299516193470385)
                ·
                  refine ⟨3419980161224637145102789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4559973548299516193470385 3419980161224637145102789)
                  ·
                    refine ⟨641246280229619464706773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3419980161224637145102789 641246280229619464706773)
                    ·
                      rfl

theorem cell22_1873234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 5, 2, 4].length) (baseStart_1873234 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1873234 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1873234 prefixEnd_1873234 := by exact prefixLift 1873234
  have htrace : WordTrace (prefixWord ++ tailWord_1873234) baseStart_1873234 baseEnd_1873234 := by
    simpa [prefixWord, tailWord_1873234, baseEnd_1873234] using wordTrace_append hprefix tailTrace_1873234
  have hstable : (prefixWord ++ tailWord_1873234).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1873234).length < 2 ^ (prefixWord ++ tailWord_1873234).sum := by decide
  have hdescent : baseEnd_1873234 < baseStart_1873234 := by decide
  rcases family_descends (prefixWord ++ tailWord_1873234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1873307 : List Nat := [1, 1, 1, 1, 1, 1, 2, 1, 3, 10]
def baseStart_1873307 : Nat := 118140960795 + 1873307 * 2 ^ 59
def prefixEnd_1873307 : Nat := 4983230072969 + 3 ^ 40 * 1873307 * 2
def baseEnd_1873307 : Nat := 641271269621471607631549

theorem tailTrace_1873307 : CollatzResearch.WordTrace tailWord_1873307 prefixEnd_1873307 641271269621471607631549 := by
  unfold tailWord_1873307
  simp only [CollatzResearch.WordTrace]
  refine ⟨68325119424336149209354175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45550079616224099472902783 68325119424336149209354175)
  ·
    refine ⟨102487679136504223814031263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68325119424336149209354175 102487679136504223814031263)
    ·
      refine ⟨153731518704756335721046895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102487679136504223814031263 153731518704756335721046895)
      ·
        refine ⟨230597278057134503581570343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153731518704756335721046895 230597278057134503581570343)
        ·
          refine ⟨345895917085701755372355515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 230597278057134503581570343 345895917085701755372355515)
          ·
            refine ⟨518843875628552633058533273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 345895917085701755372355515 518843875628552633058533273)
            ·
              refine ⟨389132906721414474793899955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 518843875628552633058533273 389132906721414474793899955)
              ·
                refine ⟨583699360082121712190849933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 389132906721414474793899955 583699360082121712190849933)
                ·
                  refine ⟨218887260030795642071568725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 583699360082121712190849933 218887260030795642071568725)
                  ·
                    refine ⟨641271269621471607631549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 218887260030795642071568725 641271269621471607631549)
                    ·
                      rfl

theorem cell22_1873307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 3, 10].length) (baseStart_1873307 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1873307 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1873307 prefixEnd_1873307 := by exact prefixLift 1873307
  have htrace : WordTrace (prefixWord ++ tailWord_1873307) baseStart_1873307 baseEnd_1873307 := by
    simpa [prefixWord, tailWord_1873307, baseEnd_1873307] using wordTrace_append hprefix tailTrace_1873307
  have hstable : (prefixWord ++ tailWord_1873307).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1873307).length < 2 ^ (prefixWord ++ tailWord_1873307).sum := by decide
  have hdescent : baseEnd_1873307 < baseStart_1873307 := by decide
  rcases family_descends (prefixWord ++ tailWord_1873307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1873311 : List Nat := [1, 1, 2, 5, 1, 3, 2, 2, 5]
def baseStart_1873311 : Nat := 118140960795 + 1873311 * 2 ^ 59
def prefixEnd_1873311 : Nat := 4983230072969 + 3 ^ 40 * 1873311 * 2
def baseEnd_1873311 : Nat := 213757546301072310177179

theorem tailTrace_1873311 : CollatzResearch.WordTrace tailWord_1873311 prefixEnd_1873311 213757546301072310177179 := by
  unfold tailWord_1873311
  simp only [CollatzResearch.WordTrace]
  refine ⟨68325265316321657892499787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45550176877547771928333191 68325265316321657892499787)
  ·
    refine ⟨102487897974482486838749681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68325265316321657892499787 102487897974482486838749681)
    ·
      refine ⟨76865923480861865129062261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102487897974482486838749681 76865923480861865129062261)
      ·
        refine ⟨7206180326330799855849587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 76865923480861865129062261 7206180326330799855849587)
        ·
          refine ⟨10809270489496199783774381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7206180326330799855849587 10809270489496199783774381)
          ·
            refine ⟨4053476433561074918915393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10809270489496199783774381 4053476433561074918915393)
            ·
              refine ⟨3040107325170806189186545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4053476433561074918915393 3040107325170806189186545)
              ·
                refine ⟨2280080493878104641889909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3040107325170806189186545 2280080493878104641889909)
                ·
                  refine ⟨213757546301072310177179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2280080493878104641889909 213757546301072310177179)
                  ·
                    rfl

theorem cell22_1873311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 2, 2, 5].length) (baseStart_1873311 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1873311 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1873311 prefixEnd_1873311 := by exact prefixLift 1873311
  have htrace : WordTrace (prefixWord ++ tailWord_1873311) baseStart_1873311 baseEnd_1873311 := by
    simpa [prefixWord, tailWord_1873311, baseEnd_1873311] using wordTrace_append hprefix tailTrace_1873311
  have hstable : (prefixWord ++ tailWord_1873311).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1873311).length < 2 ^ (prefixWord ++ tailWord_1873311).sum := by decide
  have hdescent : baseEnd_1873311 < baseStart_1873311 := by decide
  rcases family_descends (prefixWord ++ tailWord_1873311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1873324 : List Nat := [2, 2, 1, 1, 1, 1, 5, 2, 3, 4]
def baseStart_1873324 : Nat := 118140960795 + 1873324 * 2 ^ 59
def prefixEnd_1873324 : Nat := 4983230072969 + 3 ^ 40 * 1873324 * 2
def baseEnd_1873324 : Nat := 641277089068889229956497

theorem tailTrace_1873324 : CollatzResearch.WordTrace tailWord_1873324 prefixEnd_1873324 641277089068889229956497 := by
  unfold tailWord_1873324
  simp only [CollatzResearch.WordTrace]
  refine ⟨34162869732637280556361513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45550492976849707408482017 34162869732637280556361513)
  ·
    refine ⟨25622152299477960417271135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34162869732637280556361513 25622152299477960417271135)
    ·
      refine ⟨38433228449216940625906703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25622152299477960417271135 38433228449216940625906703)
      ·
        refine ⟨57649842673825410938860055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38433228449216940625906703 57649842673825410938860055)
        ·
          refine ⟨86474764010738116408290083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57649842673825410938860055 86474764010738116408290083)
          ·
            refine ⟨129712146016107174612435125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86474764010738116408290083 129712146016107174612435125)
            ·
              refine ⟨12160513689010047619915793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 129712146016107174612435125 12160513689010047619915793)
              ·
                refine ⟨9120385266757535714936845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12160513689010047619915793 9120385266757535714936845)
                ·
                  refine ⟨3420144475034075893101317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9120385266757535714936845 3420144475034075893101317)
                  ·
                    refine ⟨641277089068889229956497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3420144475034075893101317 641277089068889229956497)
                    ·
                      rfl

theorem cell22_1873324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 4].length) (baseStart_1873324 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1873324 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1873324 prefixEnd_1873324 := by exact prefixLift 1873324
  have htrace : WordTrace (prefixWord ++ tailWord_1873324) baseStart_1873324 baseEnd_1873324 := by
    simpa [prefixWord, tailWord_1873324, baseEnd_1873324] using wordTrace_append hprefix tailTrace_1873324
  have hstable : (prefixWord ++ tailWord_1873324).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1873324).length < 2 ^ (prefixWord ++ tailWord_1873324).sum := by decide
  have hdescent : baseEnd_1873324 < baseStart_1873324 := by decide
  rcases family_descends (prefixWord ++ tailWord_1873324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1873341 : List Nat := [1, 4, 1, 2, 2, 1, 2, 4, 1, 4]
def baseStart_1873341 : Nat := 118140960795 + 1873341 * 2 ^ 59
def prefixEnd_1873341 : Nat := 4983230072969 + 3 ^ 40 * 1873341 * 2
def baseEnd_1873341 : Nat := 641282908516306852281445

theorem tailTrace_1873341 : CollatzResearch.WordTrace tailWord_1873341 prefixEnd_1873341 641282908516306852281445 := by
  unfold tailWord_1873341
  simp only [CollatzResearch.WordTrace]
  refine ⟨68326359506212973016091877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45550906337475315344061251 68326359506212973016091877)
  ·
    refine ⟨12811192407414932440517227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 68326359506212973016091877 12811192407414932440517227)
    ·
      refine ⟨19216788611122398660775841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12811192407414932440517227 19216788611122398660775841)
      ·
        refine ⟨14412591458341798995581881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19216788611122398660775841 14412591458341798995581881)
        ·
          refine ⟨10809443593756349246686411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14412591458341798995581881 10809443593756349246686411)
          ·
            refine ⟨16214165390634523870029617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10809443593756349246686411 16214165390634523870029617)
            ·
              refine ⟨12160624042975892902522213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16214165390634523870029617 12160624042975892902522213)
              ·
                refine ⟨2280117008057979919222915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12160624042975892902522213 2280117008057979919222915)
                ·
                  refine ⟨3420175512086969878834373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2280117008057979919222915 3420175512086969878834373)
                  ·
                    refine ⟨641282908516306852281445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3420175512086969878834373 641282908516306852281445)
                    ·
                      rfl

theorem cell22_1873341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 4, 1, 4].length) (baseStart_1873341 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1873341 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1873341 prefixEnd_1873341 := by exact prefixLift 1873341
  have htrace : WordTrace (prefixWord ++ tailWord_1873341) baseStart_1873341 baseEnd_1873341 := by
    simpa [prefixWord, tailWord_1873341, baseEnd_1873341] using wordTrace_append hprefix tailTrace_1873341
  have hstable : (prefixWord ++ tailWord_1873341).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1873341).length < 2 ^ (prefixWord ++ tailWord_1873341).sum := by decide
  have hdescent : baseEnd_1873341 < baseStart_1873341 := by decide
  rcases family_descends (prefixWord ++ tailWord_1873341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1873358 : List Nat := [4, 1, 1, 1, 2, 1, 6, 1, 1, 4]
def baseStart_1873358 : Nat := 118140960795 + 1873358 * 2 ^ 59
def prefixEnd_1873358 : Nat := 4983230072969 + 3 ^ 40 * 1873358 * 2
def baseEnd_1873358 : Nat := 641288727963724474606393

theorem tailTrace_1873358 : CollatzResearch.WordTrace tailWord_1873358 prefixEnd_1873358 641288727963724474606393 := by
  unfold tailWord_1873358
  simp only [CollatzResearch.WordTrace]
  refine ⟨8540872443393923114932591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45551319698100923279640485 8540872443393923114932591)
  ·
    refine ⟨12811308665090884672398887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8540872443393923114932591 12811308665090884672398887)
    ·
      refine ⟨19216962997636327008598331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12811308665090884672398887 19216962997636327008598331)
      ·
        refine ⟨28825444496454490512897497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19216962997636327008598331 28825444496454490512897497)
        ·
          refine ⟨21619083372340867884673123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28825444496454490512897497 21619083372340867884673123)
          ·
            refine ⟨32428625058511301827009685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21619083372340867884673123 32428625058511301827009685)
            ·
              refine ⟨1520091799617717273141079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 32428625058511301827009685 1520091799617717273141079)
              ·
                refine ⟨2280137699426575909711619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1520091799617717273141079 2280137699426575909711619)
                ·
                  refine ⟨3420206549139863864567429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2280137699426575909711619 3420206549139863864567429)
                  ·
                    refine ⟨641288727963724474606393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3420206549139863864567429 641288727963724474606393)
                    ·
                      rfl

theorem cell22_1873358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 6, 1, 1, 4].length) (baseStart_1873358 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1873358 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1873358 prefixEnd_1873358 := by exact prefixLift 1873358
  have htrace : WordTrace (prefixWord ++ tailWord_1873358) baseStart_1873358 baseEnd_1873358 := by
    simpa [prefixWord, tailWord_1873358, baseEnd_1873358] using wordTrace_append hprefix tailTrace_1873358
  have hstable : (prefixWord ++ tailWord_1873358).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1873358).length < 2 ^ (prefixWord ++ tailWord_1873358).sum := by decide
  have hdescent : baseEnd_1873358 < baseStart_1873358 := by decide
  rcases family_descends (prefixWord ++ tailWord_1873358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1873373 : List Nat := [1, 4, 3, 1, 1, 2, 2, 4, 4]
def baseStart_1873373 : Nat := 118140960795 + 1873373 * 2 ^ 59
def prefixEnd_1873373 : Nat := 4983230072969 + 3 ^ 40 * 1873373 * 2
def baseEnd_1873373 : Nat := 213764620923423145160449

theorem tailTrace_1873373 : CollatzResearch.WordTrace tailWord_1873373 prefixEnd_1873373 213764620923423145160449 := by
  unfold tailWord_1873373
  simp only [CollatzResearch.WordTrace]
  refine ⟨68327526642097042481256773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45551684428064694987504515 68327526642097042481256773)
  ·
    refine ⟨12811411245393195465235645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 68327526642097042481256773 12811411245393195465235645)
    ·
      refine ⟨4804279217022448299463367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12811411245393195465235645 4804279217022448299463367)
      ·
        refine ⟨7206418825533672449195051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4804279217022448299463367 7206418825533672449195051)
        ·
          refine ⟨10809628238300508673792577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7206418825533672449195051 10809628238300508673792577)
          ·
            refine ⟨8107221178725381505344433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10809628238300508673792577 8107221178725381505344433)
            ·
              refine ⟨6080415884044036129008325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8107221178725381505344433 6080415884044036129008325)
              ·
                refine ⟨1140077978258256774189061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6080415884044036129008325 1140077978258256774189061)
                ·
                  refine ⟨213764620923423145160449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1140077978258256774189061 213764620923423145160449)
                  ·
                    rfl

theorem cell22_1873373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 2, 4, 4].length) (baseStart_1873373 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1873373 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1873373 prefixEnd_1873373 := by exact prefixLift 1873373
  have htrace : WordTrace (prefixWord ++ tailWord_1873373) baseStart_1873373 baseEnd_1873373 := by
    simpa [prefixWord, tailWord_1873373, baseEnd_1873373] using wordTrace_append hprefix tailTrace_1873373
  have hstable : (prefixWord ++ tailWord_1873373).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1873373).length < 2 ^ (prefixWord ++ tailWord_1873373).sum := by decide
  have hdescent : baseEnd_1873373 < baseStart_1873373 := by decide
  rcases family_descends (prefixWord ++ tailWord_1873373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1873384 : List Nat := [2, 1, 4, 1, 1, 2, 2, 9]
def baseStart_1873384 : Nat := 118140960795 + 1873384 * 2 ^ 59
def prefixEnd_1873384 : Nat := 4983230072969 + 3 ^ 40 * 1873384 * 2
def baseEnd_1873384 : Nat := 71255292032785452606257

theorem tailTrace_1873384 : CollatzResearch.WordTrace tailWord_1873384 prefixEnd_1873384 71255292032785452606257 := by
  unfold tailWord_1873384
  simp only [CollatzResearch.WordTrace]
  refine ⟨34163963922528595679953603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45551951896704794239938137 34163963922528595679953603)
  ·
    refine ⟨51245945883792893519930405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34163963922528595679953603 51245945883792893519930405)
    ·
      refine ⟨9608614853211167534986951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51245945883792893519930405 9608614853211167534986951)
      ·
        refine ⟨14412922279816751302480427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9608614853211167534986951 14412922279816751302480427)
        ·
          refine ⟨21619383419725126953720641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14412922279816751302480427 21619383419725126953720641)
          ·
            refine ⟨16214537564793845215290481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21619383419725126953720641 16214537564793845215290481)
            ·
              refine ⟨12160903173595383911467861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16214537564793845215290481 12160903173595383911467861)
              ·
                refine ⟨71255292032785452606257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 12160903173595383911467861 71255292032785452606257)
                ·
                  rfl

theorem cell22_1873384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 9].length) (baseStart_1873384 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1873384 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1873384 prefixEnd_1873384 := by exact prefixLift 1873384
  have htrace : WordTrace (prefixWord ++ tailWord_1873384) baseStart_1873384 baseEnd_1873384 := by
    simpa [prefixWord, tailWord_1873384, baseEnd_1873384] using wordTrace_append hprefix tailTrace_1873384
  have hstable : (prefixWord ++ tailWord_1873384).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1873384).length < 2 ^ (prefixWord ++ tailWord_1873384).sum := by decide
  have hdescent : baseEnd_1873384 < baseStart_1873384 := by decide
  rcases family_descends (prefixWord ++ tailWord_1873384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1873416 : List Nat := [2, 1, 3, 2, 1, 1, 2, 2, 5, 3]
def baseStart_1873416 : Nat := 118140960795 + 1873416 * 2 ^ 59
def prefixEnd_1873416 : Nat := 4983230072969 + 3 ^ 40 * 1873416 * 2
def baseEnd_1873416 : Nat := 641308582549031656656215

theorem tailTrace_1873416 : CollatzResearch.WordTrace tailWord_1873416 prefixEnd_1873416 641308582549031656656215 := by
  unfold tailWord_1873416
  simp only [CollatzResearch.WordTrace]
  refine ⟨34164547490470630412536051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45552729987294173883381401 34164547490470630412536051)
  ·
    refine ⟨51246821235705945618804077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34164547490470630412536051 51246821235705945618804077)
    ·
      refine ⟨19217557963389729607051529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51246821235705945618804077 19217557963389729607051529)
      ·
        refine ⟨14413168472542297205288647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19217557963389729607051529 14413168472542297205288647)
        ·
          refine ⟨21619752708813445807932971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14413168472542297205288647 21619752708813445807932971)
          ·
            refine ⟨32429629063220168711899457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21619752708813445807932971 32429629063220168711899457)
            ·
              refine ⟨24322221797415126533924593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32429629063220168711899457 24322221797415126533924593)
              ·
                refine ⟨18241666348061344900443445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24322221797415126533924593 18241666348061344900443445)
                ·
                  refine ⟨1710156220130751084416573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 18241666348061344900443445 1710156220130751084416573)
                  ·
                    refine ⟨641308582549031656656215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1710156220130751084416573 641308582549031656656215)
                    ·
                      rfl

theorem cell22_1873416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 2, 5, 3].length) (baseStart_1873416 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1873416 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1873416 prefixEnd_1873416 := by exact prefixLift 1873416
  have htrace : WordTrace (prefixWord ++ tailWord_1873416) baseStart_1873416 baseEnd_1873416 := by
    simpa [prefixWord, tailWord_1873416, baseEnd_1873416] using wordTrace_append hprefix tailTrace_1873416
  have hstable : (prefixWord ++ tailWord_1873416).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1873416).length < 2 ^ (prefixWord ++ tailWord_1873416).sum := by decide
  have hdescent : baseEnd_1873416 < baseStart_1873416 := by decide
  rcases family_descends (prefixWord ++ tailWord_1873416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1873525 : List Nat := [1, 3, 4, 2, 1, 1, 1, 5, 4]
def baseStart_1873525 : Nat := 118140960795 + 1873525 * 2 ^ 59
def prefixEnd_1873525 : Nat := 4983230072969 + 3 ^ 40 * 1873525 * 2
def baseEnd_1873525 : Nat := 213781965158863901893627

theorem tailTrace_1873525 : CollatzResearch.WordTrace tailWord_1873525 prefixEnd_1873525 213781965158863901893627 := by
  unfold tailWord_1873525
  simp only [CollatzResearch.WordTrace]
  refine ⟨68333070537546372440790029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45555380358364248293860019 68333070537546372440790029)
  ·
    refine ⟨25624901451579889665296261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68333070537546372440790029 25624901451579889665296261)
    ·
      refine ⟨4804669022171229312243049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25624901451579889665296261 4804669022171229312243049)
      ·
        refine ⟨3603501766628421984182287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4804669022171229312243049 3603501766628421984182287)
        ·
          refine ⟨5405252649942632976273431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3603501766628421984182287 5405252649942632976273431)
          ·
            refine ⟨8107878974913949464410147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5405252649942632976273431 8107878974913949464410147)
            ·
              refine ⟨12161818462370924196615221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8107878974913949464410147 12161818462370924196615221)
              ·
                refine ⟨1140170480847274143432677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12161818462370924196615221 1140170480847274143432677)
                ·
                  refine ⟨213781965158863901893627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1140170480847274143432677 213781965158863901893627)
                  ·
                    rfl

theorem cell22_1873525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 5, 4].length) (baseStart_1873525 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1873525 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1873525 prefixEnd_1873525 := by exact prefixLift 1873525
  have htrace : WordTrace (prefixWord ++ tailWord_1873525) baseStart_1873525 baseEnd_1873525 := by
    simpa [prefixWord, tailWord_1873525, baseEnd_1873525] using wordTrace_append hprefix tailTrace_1873525
  have hstable : (prefixWord ++ tailWord_1873525).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1873525).length < 2 ^ (prefixWord ++ tailWord_1873525).sum := by decide
  have hdescent : baseEnd_1873525 < baseStart_1873525 := by decide
  rcases family_descends (prefixWord ++ tailWord_1873525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1873540 : List Nat := [2, 3, 2, 1, 4, 1, 1, 1, 4, 3]
def baseStart_1873540 : Nat := 118140960795 + 1873540 * 2 ^ 59
def prefixEnd_1873540 : Nat := 4983230072969 + 3 ^ 40 * 1873540 * 2
def baseEnd_1873540 : Nat := 641351030283136666555835

theorem tailTrace_1873540 : CollatzResearch.WordTrace tailWord_1873540 prefixEnd_1873540 641351030283136666555835 := by
  unfold tailWord_1873540
  simp only [CollatzResearch.WordTrace]
  refine ⟨34166808816246015001293037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45555745088328020001724049 34166808816246015001293037)
  ·
    refine ⟨12812553306092255625484889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34166808816246015001293037 12812553306092255625484889)
    ·
      refine ⟨9609414979569191719113667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12812553306092255625484889 9609414979569191719113667)
      ·
        refine ⟨14414122469353787578670501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9609414979569191719113667 14414122469353787578670501)
        ·
          refine ⟨2702647963003835171000719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14414122469353787578670501 2702647963003835171000719)
          ·
            refine ⟨4053971944505752756501079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2702647963003835171000719 4053971944505752756501079)
            ·
              refine ⟨6080957916758629134751619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4053971944505752756501079 6080957916758629134751619)
              ·
                refine ⟨9121436875137943702127429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6080957916758629134751619 9121436875137943702127429)
                ·
                  refine ⟨1710269414088364444148893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9121436875137943702127429 1710269414088364444148893)
                  ·
                    refine ⟨641351030283136666555835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1710269414088364444148893 641351030283136666555835)
                    ·
                      rfl

theorem cell22_1873540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 1, 1, 4, 3].length) (baseStart_1873540 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1873540 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1873540 prefixEnd_1873540 := by exact prefixLift 1873540
  have htrace : WordTrace (prefixWord ++ tailWord_1873540) baseStart_1873540 baseEnd_1873540 := by
    simpa [prefixWord, tailWord_1873540, baseEnd_1873540] using wordTrace_append hprefix tailTrace_1873540
  have hstable : (prefixWord ++ tailWord_1873540).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1873540).length < 2 ^ (prefixWord ++ tailWord_1873540).sum := by decide
  have hdescent : baseEnd_1873540 < baseStart_1873540 := by decide
  rcases family_descends (prefixWord ++ tailWord_1873540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1873570 : List Nat := [3, 3, 1, 4, 1, 1, 1, 8]
def baseStart_1873570 : Nat := 118140960795 + 1873570 * 2 ^ 59
def prefixEnd_1873570 : Nat := 4983230072969 + 3 ^ 40 * 1873570 * 2
def baseEnd_1873570 : Nat := 71262366655136287589527

theorem tailTrace_1873570 : CollatzResearch.WordTrace tailWord_1873570 prefixEnd_1873570 71262366655136287589527 := by
  unfold tailWord_1873570
  simp only [CollatzResearch.WordTrace]
  refine ⟨17083677955595836281544541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45556474548255563417452109 17083677955595836281544541)
  ·
    refine ⟨6406379233348438605579203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17083677955595836281544541 6406379233348438605579203)
    ·
      refine ⟨9609568850022657908368805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6406379233348438605579203 9609568850022657908368805)
      ·
        refine ⟨1801794159379248357819151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9609568850022657908368805 1801794159379248357819151)
        ·
          refine ⟨2702691239068872536728727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1801794159379248357819151 2702691239068872536728727)
          ·
            refine ⟨4054036858603308805093091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2702691239068872536728727 4054036858603308805093091)
            ·
              refine ⟨6081055287904963207639637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4054036858603308805093091 6081055287904963207639637)
              ·
                refine ⟨71262366655136287589527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6081055287904963207639637 71262366655136287589527)
                ·
                  rfl

theorem cell22_1873570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 1, 8].length) (baseStart_1873570 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1873570 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1873570 prefixEnd_1873570 := by exact prefixLift 1873570
  have htrace : WordTrace (prefixWord ++ tailWord_1873570) baseStart_1873570 baseEnd_1873570 := by
    simpa [prefixWord, tailWord_1873570, baseEnd_1873570] using wordTrace_append hprefix tailTrace_1873570
  have hstable : (prefixWord ++ tailWord_1873570).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1873570).length < 2 ^ (prefixWord ++ tailWord_1873570).sum := by decide
  have hdescent : baseEnd_1873570 < baseStart_1873570 := by decide
  rcases family_descends (prefixWord ++ tailWord_1873570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1873576 : List Nat := [2, 1, 7, 1, 1, 2, 1, 3, 4]
def baseStart_1873576 : Nat := 118140960795 + 1873576 * 2 ^ 59
def prefixEnd_1873576 : Nat := 4983230072969 + 3 ^ 40 * 1873576 * 2
def baseEnd_1873576 : Nat := 213787784606281524218575

theorem tailTrace_1873576 : CollatzResearch.WordTrace tailWord_1873576 prefixEnd_1873576 213787784606281524218575 := by
  unfold tailWord_1873576
  simp only [CollatzResearch.WordTrace]
  refine ⟨34167465330180804075448291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45556620440241072100597721 34167465330180804075448291)
  ·
    refine ⟨51251197995271206113172437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34167465330180804075448291 51251197995271206113172437)
    ·
      refine ⟨1201199953014168893277479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 51251197995271206113172437 1201199953014168893277479)
      ·
        refine ⟨1801799929521253339916219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1201199953014168893277479 1801799929521253339916219)
        ·
          refine ⟨2702699894281880009874329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1801799929521253339916219 2702699894281880009874329)
          ·
            refine ⟨2027024920711410007405747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2702699894281880009874329 2027024920711410007405747)
            ·
              refine ⟨3040537381067115011108621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2027024920711410007405747 3040537381067115011108621)
              ·
                refine ⟨1140201517900168129165733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3040537381067115011108621 1140201517900168129165733)
                ·
                  refine ⟨213787784606281524218575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1140201517900168129165733 213787784606281524218575)
                  ·
                    rfl

theorem cell22_1873576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 2, 1, 3, 4].length) (baseStart_1873576 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1873576 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1873576 prefixEnd_1873576 := by exact prefixLift 1873576
  have htrace : WordTrace (prefixWord ++ tailWord_1873576) baseStart_1873576 baseEnd_1873576 := by
    simpa [prefixWord, tailWord_1873576, baseEnd_1873576] using wordTrace_append hprefix tailTrace_1873576
  have hstable : (prefixWord ++ tailWord_1873576).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1873576).length < 2 ^ (prefixWord ++ tailWord_1873576).sum := by decide
  have hdescent : baseEnd_1873576 < baseStart_1873576 := by decide
  rcases family_descends (prefixWord ++ tailWord_1873576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1873598 : List Nat := [4, 2, 1, 1, 2, 2, 2, 1, 7]
def baseStart_1873598 : Nat := 118140960795 + 1873598 * 2 ^ 59
def prefixEnd_1873598 : Nat := 4983230072969 + 3 ^ 40 * 1873598 * 2
def baseEnd_1873598 : Nat := 213790294956147949535219

theorem tailTrace_1873598 : CollatzResearch.WordTrace tailWord_1873598 prefixEnd_1873598 213790294956147949535219 := by
  unfold tailWord_1873598
  simp only [CollatzResearch.WordTrace]
  refine ⟨8541966633285238238524681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45557155377521270605464965 8541966633285238238524681)
  ·
    refine ⟨6406474974963928678893511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8541966633285238238524681 6406474974963928678893511)
    ·
      refine ⟨9609712462445893018340267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6406474974963928678893511 9609712462445893018340267)
      ·
        refine ⟨14414568693668839527510401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9609712462445893018340267 14414568693668839527510401)
        ·
          refine ⟨10810926520251629645632801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14414568693668839527510401 10810926520251629645632801)
          ·
            refine ⟨8108194890188722234224601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10810926520251629645632801 8108194890188722234224601)
            ·
              refine ⟨6081146167641541675668451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8108194890188722234224601 6081146167641541675668451)
              ·
                refine ⟨9121719251462312513502677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6081146167641541675668451 9121719251462312513502677)
                ·
                  refine ⟨213790294956147949535219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9121719251462312513502677 213790294956147949535219)
                  ·
                    rfl

theorem cell22_1873598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 2, 1, 7].length) (baseStart_1873598 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1873598 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1873598 prefixEnd_1873598 := by exact prefixLift 1873598
  have htrace : WordTrace (prefixWord ++ tailWord_1873598) baseStart_1873598 baseEnd_1873598 := by
    simpa [prefixWord, tailWord_1873598, baseEnd_1873598] using wordTrace_append hprefix tailTrace_1873598
  have hstable : (prefixWord ++ tailWord_1873598).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1873598).length < 2 ^ (prefixWord ++ tailWord_1873598).sum := by decide
  have hdescent : baseEnd_1873598 < baseStart_1873598 := by decide
  rcases family_descends (prefixWord ++ tailWord_1873598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1873660 : List Nat := [2, 2, 2, 1, 3, 1, 3, 4, 4]
def baseStart_1873660 : Nat := 118140960795 + 1873660 * 2 ^ 59
def prefixEnd_1873660 : Nat := 4983230072969 + 3 ^ 40 * 1873660 * 2
def baseEnd_1873660 : Nat := 213797369578498784518489

theorem tailTrace_1873660 : CollatzResearch.WordTrace tailWord_1873660 prefixEnd_1873660 213797369578498784518489 := by
  unfold tailWord_1873660
  simp only [CollatzResearch.WordTrace]
  refine ⟨34168997196028645248477217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45558662928038193664636289 34168997196028645248477217)
  ·
    refine ⟨25626747897021483936357913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34168997196028645248477217 25626747897021483936357913)
    ·
      refine ⟨19220060922766112952268435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25626747897021483936357913 19220060922766112952268435)
      ·
        refine ⟨28830091384149169428402653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19220060922766112952268435 28830091384149169428402653)
        ·
          refine ⟨10811284269055938535650995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28830091384149169428402653 10811284269055938535650995)
          ·
            refine ⟨16216926403583907803476493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10811284269055938535650995 16216926403583907803476493)
            ·
              refine ⟨6081347401343965426303685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16216926403583907803476493 6081347401343965426303685)
              ·
                refine ⟨1140252637751993517431941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6081347401343965426303685 1140252637751993517431941)
                ·
                  refine ⟨213797369578498784518489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1140252637751993517431941 213797369578498784518489)
                  ·
                    rfl

theorem cell22_1873660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 3, 4, 4].length) (baseStart_1873660 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1873660 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1873660 prefixEnd_1873660 := by exact prefixLift 1873660
  have htrace : WordTrace (prefixWord ++ tailWord_1873660) baseStart_1873660 baseEnd_1873660 := by
    simpa [prefixWord, tailWord_1873660, baseEnd_1873660] using wordTrace_append hprefix tailTrace_1873660
  have hstable : (prefixWord ++ tailWord_1873660).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1873660).length < 2 ^ (prefixWord ++ tailWord_1873660).sum := by decide
  have hdescent : baseEnd_1873660 < baseStart_1873660 := by decide
  rcases family_descends (prefixWord ++ tailWord_1873660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1873675 : List Nat := [1, 1, 1, 1, 5, 1, 4, 3, 2, 3]
def baseStart_1873675 : Nat := 118140960795 + 1873675 * 2 ^ 59
def prefixEnd_1873675 : Nat := 4983230072969 + 3 ^ 40 * 1873675 * 2
def baseEnd_1873675 : Nat := 641397243542041314430421

theorem tailTrace_1873675 : CollatzResearch.WordTrace tailWord_1873675 prefixEnd_1873675 641397243542041314430421 := by
  unfold tailWord_1873675
  simp only [CollatzResearch.WordTrace]
  refine ⟨68338541487002948058750479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45559027658001965372500319 68338541487002948058750479)
  ·
    refine ⟨102507812230504422088125719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68338541487002948058750479 102507812230504422088125719)
    ·
      refine ⟨153761718345756633132188579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102507812230504422088125719 153761718345756633132188579)
      ·
        refine ⟨230642577518634949698282869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153761718345756633132188579 230642577518634949698282869)
        ·
          refine ⟨21622741642372026534214019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 230642577518634949698282869 21622741642372026534214019)
          ·
            refine ⟨32434112463558039801321029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21622741642372026534214019 32434112463558039801321029)
            ·
              refine ⟨6081396086917132462747693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32434112463558039801321029 6081396086917132462747693)
              ·
                refine ⟨2280523532593924673530385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6081396086917132462747693 2280523532593924673530385)
                ·
                  refine ⟨1710392649445443505147789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2280523532593924673530385 1710392649445443505147789)
                  ·
                    refine ⟨641397243542041314430421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1710392649445443505147789 641397243542041314430421)
                    ·
                      rfl

theorem cell22_1873675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 4, 3, 2, 3].length) (baseStart_1873675 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1873675 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1873675 prefixEnd_1873675 := by exact prefixLift 1873675
  have htrace : WordTrace (prefixWord ++ tailWord_1873675) baseStart_1873675 baseEnd_1873675 := by
    simpa [prefixWord, tailWord_1873675, baseEnd_1873675] using wordTrace_append hprefix tailTrace_1873675
  have hstable : (prefixWord ++ tailWord_1873675).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1873675).length < 2 ^ (prefixWord ++ tailWord_1873675).sum := by decide
  have hdescent : baseEnd_1873675 < baseStart_1873675 := by decide
  rcases family_descends (prefixWord ++ tailWord_1873675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1873690 : List Nat := [3, 1, 1, 3, 2, 2, 3, 1, 2, 4]
def baseStart_1873690 : Nat := 118140960795 + 1873690 * 2 ^ 59
def prefixEnd_1873690 : Nat := 4983230072969 + 3 ^ 40 * 1873690 * 2
def baseEnd_1873690 : Nat := 641402378348586275305375

theorem tailTrace_1873690 : CollatzResearch.WordTrace tailWord_1873690 prefixEnd_1873690 641402378348586275305375 := by
  unfold tailWord_1873690
  simp only [CollatzResearch.WordTrace]
  refine ⟨17084772145487151405136631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45559392387965737080364349 17084772145487151405136631)
  ·
    refine ⟨25627158218230727107704947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17084772145487151405136631 25627158218230727107704947)
    ·
      refine ⟨38440737327346090661557421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25627158218230727107704947 38440737327346090661557421)
      ·
        refine ⟨14415276497754783998084033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38440737327346090661557421 14415276497754783998084033)
        ·
          refine ⟨10811457373316087998563025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14415276497754783998084033 10811457373316087998563025)
          ·
            refine ⟨8108593029987065998922269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10811457373316087998563025 8108593029987065998922269)
            ·
              refine ⟨3040722386245149749595851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8108593029987065998922269 3040722386245149749595851)
              ·
                refine ⟨4561083579367724624393777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3040722386245149749595851 4561083579367724624393777)
                ·
                  refine ⟨3420812684525793468295333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4561083579367724624393777 3420812684525793468295333)
                  ·
                    refine ⟨641402378348586275305375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3420812684525793468295333 641402378348586275305375)
                    ·
                      rfl

theorem cell22_1873690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 3, 1, 2, 4].length) (baseStart_1873690 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1873690 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1873690 prefixEnd_1873690 := by exact prefixLift 1873690
  have htrace : WordTrace (prefixWord ++ tailWord_1873690) baseStart_1873690 baseEnd_1873690 := by
    simpa [prefixWord, tailWord_1873690, baseEnd_1873690] using wordTrace_append hprefix tailTrace_1873690
  have hstable : (prefixWord ++ tailWord_1873690).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1873690).length < 2 ^ (prefixWord ++ tailWord_1873690).sum := by decide
  have hdescent : baseEnd_1873690 < baseStart_1873690 := by decide
  rcases family_descends (prefixWord ++ tailWord_1873690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1873720 : List Nat := [2, 1, 2, 1, 3, 3, 1, 3, 3, 3]
def baseStart_1873720 : Nat := 118140960795 + 1873720 * 2 ^ 59
def prefixEnd_1873720 : Nat := 4983230072969 + 3 ^ 40 * 1873720 * 2
def baseEnd_1873720 : Nat := 641412647961676197055283

theorem tailTrace_1873720 : CollatzResearch.WordTrace tailWord_1873720 prefixEnd_1873720 641412647961676197055283 := by
  unfold tailWord_1873720
  simp only [CollatzResearch.WordTrace]
  refine ⟨34170091385919960372069307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45560121847893280496092409 34170091385919960372069307)
  ·
    refine ⟨51255137078879940558103961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34170091385919960372069307 51255137078879940558103961)
    ·
      refine ⟨38441352809159955418577971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51255137078879940558103961 38441352809159955418577971)
      ·
        refine ⟨57662029213739933127866957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38441352809159955418577971 57662029213739933127866957)
        ·
          refine ⟨21623260955152474922950109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57662029213739933127866957 21623260955152474922950109)
          ·
            refine ⟨8108722858182178096106291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21623260955152474922950109 8108722858182178096106291)
            ·
              refine ⟨12163084287273267144159437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8108722858182178096106291 12163084287273267144159437)
              ·
                refine ⟨4561156607727475179059789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12163084287273267144159437 4561156607727475179059789)
                ·
                  refine ⟨1710433727897803192147421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4561156607727475179059789 1710433727897803192147421)
                  ·
                    refine ⟨641412647961676197055283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1710433727897803192147421 641412647961676197055283)
                    ·
                      rfl

theorem cell22_1873720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 3, 3, 3].length) (baseStart_1873720 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1873720 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1873720 prefixEnd_1873720 := by exact prefixLift 1873720
  have htrace : WordTrace (prefixWord ++ tailWord_1873720) baseStart_1873720 baseEnd_1873720 := by
    simpa [prefixWord, tailWord_1873720, baseEnd_1873720] using wordTrace_append hprefix tailTrace_1873720
  have hstable : (prefixWord ++ tailWord_1873720).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1873720).length < 2 ^ (prefixWord ++ tailWord_1873720).sum := by decide
  have hdescent : baseEnd_1873720 < baseStart_1873720 := by decide
  rcases family_descends (prefixWord ++ tailWord_1873720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1873822 : List Nat := [4, 3, 1, 3, 2, 1, 2, 2, 1, 3]
def baseStart_1873822 : Nat := 118140960795 + 1873822 * 2 ^ 59
def prefixEnd_1873822 : Nat := 4983230072969 + 3 ^ 40 * 1873822 * 2
def baseEnd_1873822 : Nat := 641447564646181931004971

theorem tailTrace_1873822 : CollatzResearch.WordTrace tailWord_1873822 prefixEnd_1873822 641447564646181931004971 := by
  unfold tailWord_1873822
  simp only [CollatzResearch.WordTrace]
  refine ⟨8542987877183799020543965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45562602011646928109567813 8542987877183799020543965)
  ·
    refine ⟨3203620453943924632703987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8542987877183799020543965 3203620453943924632703987)
    ·
      refine ⟨4805430680915886949055981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3203620453943924632703987 4805430680915886949055981)
      ·
        refine ⟨1802036505343457605895993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4805430680915886949055981 1802036505343457605895993)
        ·
          refine ⟨1351527379007593204421995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1802036505343457605895993 1351527379007593204421995)
          ·
            refine ⟨2027291068511389806632993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1351527379007593204421995 2027291068511389806632993)
            ·
              refine ⟨1520468301383542354974745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2027291068511389806632993 1520468301383542354974745)
              ·
                refine ⟨1140351226037656766231059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1520468301383542354974745 1140351226037656766231059)
                ·
                  refine ⟨1710526839056485149346589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1140351226037656766231059 1710526839056485149346589)
                  ·
                    refine ⟨641447564646181931004971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1710526839056485149346589 641447564646181931004971)
                    ·
                      rfl

theorem cell22_1873822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 2, 1, 2, 2, 1, 3].length) (baseStart_1873822 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1873822 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1873822 prefixEnd_1873822 := by exact prefixLift 1873822
  have htrace : WordTrace (prefixWord ++ tailWord_1873822) baseStart_1873822 baseEnd_1873822 := by
    simpa [prefixWord, tailWord_1873822, baseEnd_1873822] using wordTrace_append hprefix tailTrace_1873822
  have hstable : (prefixWord ++ tailWord_1873822).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1873822).length < 2 ^ (prefixWord ++ tailWord_1873822).sum := by decide
  have hdescent : baseEnd_1873822 < baseStart_1873822 := by decide
  rcases family_descends (prefixWord ++ tailWord_1873822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1873823 : List Nat := [1, 1, 2, 5, 13]
def baseStart_1873823 : Nat := 118140960795 + 1873823 * 2 ^ 59
def prefixEnd_1873823 : Nat := 4983230072969 + 3 ^ 40 * 1873823 * 2
def baseEnd_1873823 : Nat := 2639703320850280912469

theorem tailTrace_1873823 : CollatzResearch.WordTrace tailWord_1873823 prefixEnd_1873823 2639703320850280912469 := by
  unfold tailWord_1873823
  simp only [CollatzResearch.WordTrace]
  refine ⟨68343939490466769335138123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45562626326977846223425415 68343939490466769335138123)
  ·
    refine ⟨102515909235700154002707185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68343939490466769335138123 102515909235700154002707185)
    ·
      refine ⟨76886931926775115502030389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102515909235700154002707185 76886931926775115502030389)
      ·
        refine ⟨7208149868135167078315349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 76886931926775115502030389 7208149868135167078315349)
        ·
          refine ⟨2639703320850280912469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 7208149868135167078315349 2639703320850280912469)
          ·
            rfl

theorem cell22_1873823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 13].length) (baseStart_1873823 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1873823 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1873823 prefixEnd_1873823 := by exact prefixLift 1873823
  have htrace : WordTrace (prefixWord ++ tailWord_1873823) baseStart_1873823 baseEnd_1873823 := by
    simpa [prefixWord, tailWord_1873823, baseEnd_1873823] using wordTrace_append hprefix tailTrace_1873823
  have hstable : (prefixWord ++ tailWord_1873823).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1873823).length < 2 ^ (prefixWord ++ tailWord_1873823).sum := by decide
  have hdescent : baseEnd_1873823 < baseStart_1873823 := by decide
  rcases family_descends (prefixWord ++ tailWord_1873823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1873878 : List Nat := [5, 2, 1, 1, 3, 2, 1, 2, 2, 3]
def baseStart_1873878 : Nat := 118140960795 + 1873878 * 2 ^ 59
def prefixEnd_1873878 : Nat := 4983230072969 + 3 ^ 40 * 1873878 * 2
def baseEnd_1873878 : Nat := 641466734590616451604799

theorem tailTrace_1873878 : CollatzResearch.WordTrace tailWord_1873878 prefixEnd_1873878 641466734590616451604799 := by
  unfold tailWord_1873878
  simp only [CollatzResearch.WordTrace]
  refine ⟨4271621594079219608024393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 45563963670178342485593525 4271621594079219608024393)
  ·
    refine ⟨3203716195559414706018295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4271621594079219608024393 3203716195559414706018295)
    ·
      refine ⟨4805574293339122059027443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3203716195559414706018295 4805574293339122059027443)
      ·
        refine ⟨7208361440008683088541165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4805574293339122059027443 7208361440008683088541165)
        ·
          refine ⟨2703135540003256158202937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7208361440008683088541165 2703135540003256158202937)
          ·
            refine ⟨2027351655002442118652203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2703135540003256158202937 2027351655002442118652203)
            ·
              refine ⟨3041027482503663177978305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2027351655002442118652203 3041027482503663177978305)
              ·
                refine ⟨2280770611877747383483729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3041027482503663177978305 2280770611877747383483729)
                ·
                  refine ⟨1710577958908310537612797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2280770611877747383483729 1710577958908310537612797)
                  ·
                    refine ⟨641466734590616451604799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1710577958908310537612797 641466734590616451604799)
                    ·
                      rfl

theorem cell22_1873878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 2, 1, 2, 2, 3].length) (baseStart_1873878 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1873878 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1873878 prefixEnd_1873878 := by exact prefixLift 1873878
  have htrace : WordTrace (prefixWord ++ tailWord_1873878) baseStart_1873878 baseEnd_1873878 := by
    simpa [prefixWord, tailWord_1873878, baseEnd_1873878] using wordTrace_append hprefix tailTrace_1873878
  have hstable : (prefixWord ++ tailWord_1873878).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1873878).length < 2 ^ (prefixWord ++ tailWord_1873878).sum := by decide
  have hdescent : baseEnd_1873878 < baseStart_1873878 := by decide
  rcases family_descends (prefixWord ++ tailWord_1873878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1873889 : List Nat := [1, 2, 3, 1, 2, 1, 4, 4, 1, 3]
def baseStart_1873889 : Nat := 118140960795 + 1873889 * 2 ^ 59
def prefixEnd_1873889 : Nat := 4983230072969 + 3 ^ 40 * 1873889 * 2
def baseEnd_1873889 : Nat := 641470500115416089579765

theorem tailTrace_1873889 : CollatzResearch.WordTrace tailWord_1873889 prefixEnd_1873889 641470500115416089579765 := by
  unfold tailWord_1873889
  simp only [CollatzResearch.WordTrace]
  refine ⟨68346346708227662607040721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45564231138818441738027147 68346346708227662607040721)
  ·
    refine ⟨51259760031170746955280541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68346346708227662607040721 51259760031170746955280541)
    ·
      refine ⟨19222410011689030108230203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51259760031170746955280541 19222410011689030108230203)
      ·
        refine ⟨28833615017533545162345305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19222410011689030108230203 28833615017533545162345305)
        ·
          refine ⟨21625211263150158871758979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28833615017533545162345305 21625211263150158871758979)
          ·
            refine ⟨32437816894725238307638469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21625211263150158871758979 32437816894725238307638469)
            ·
              refine ⟨6082090667760982182682213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32437816894725238307638469 6082090667760982182682213)
              ·
                refine ⟨1140392000205184159252915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6082090667760982182682213 1140392000205184159252915)
                ·
                  refine ⟨1710588000307776238879373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1140392000205184159252915 1710588000307776238879373)
                  ·
                    refine ⟨641470500115416089579765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1710588000307776238879373 641470500115416089579765)
                    ·
                      rfl

theorem cell22_1873889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 4, 4, 1, 3].length) (baseStart_1873889 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1873889 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1873889 prefixEnd_1873889 := by exact prefixLift 1873889
  have htrace : WordTrace (prefixWord ++ tailWord_1873889) baseStart_1873889 baseEnd_1873889 := by
    simpa [prefixWord, tailWord_1873889, baseEnd_1873889] using wordTrace_append hprefix tailTrace_1873889
  have hstable : (prefixWord ++ tailWord_1873889).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1873889).length < 2 ^ (prefixWord ++ tailWord_1873889).sum := by decide
  have hdescent : baseEnd_1873889 < baseStart_1873889 := by decide
  rcases family_descends (prefixWord ++ tailWord_1873889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1873915 : List Nat := [1, 1, 1, 1, 1, 3, 4, 3, 3, 4]
def baseStart_1873915 : Nat := 118140960795 + 1873915 * 2 ^ 59
def prefixEnd_1873915 : Nat := 4983230072969 + 3 ^ 40 * 1873915 * 2
def baseEnd_1873915 : Nat := 641479400446760688429685

theorem tailTrace_1873915 : CollatzResearch.WordTrace tailWord_1873915 prefixEnd_1873915 641479400446760688429685 := by
  unfold tailWord_1873915
  simp only [CollatzResearch.WordTrace]
  refine ⟨68347295006133469047487199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45564863337422312698324799 68347295006133469047487199)
  ·
    refine ⟨102520942509200203571230799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68347295006133469047487199 102520942509200203571230799)
    ·
      refine ⟨153781413763800305356846199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102520942509200203571230799 153781413763800305356846199)
      ·
        refine ⟨230672120645700458035269299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153781413763800305356846199 230672120645700458035269299)
        ·
          refine ⟨346008180968550687052903949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 230672120645700458035269299 346008180968550687052903949)
          ·
            refine ⟨129753067863206507644838981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 346008180968550687052903949 129753067863206507644838981)
            ·
              refine ⟨24328700224351220183407309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 129753067863206507644838981 24328700224351220183407309)
              ·
                refine ⟨9123262584131707568777741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24328700224351220183407309 9123262584131707568777741)
                ·
                  refine ⟨3421223469049390338291653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9123262584131707568777741 3421223469049390338291653)
                  ·
                    refine ⟨641479400446760688429685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3421223469049390338291653 641479400446760688429685)
                    ·
                      rfl

theorem cell22_1873915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 3, 3, 4].length) (baseStart_1873915 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1873915 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1873915 prefixEnd_1873915 := by exact prefixLift 1873915
  have htrace : WordTrace (prefixWord ++ tailWord_1873915) baseStart_1873915 baseEnd_1873915 := by
    simpa [prefixWord, tailWord_1873915, baseEnd_1873915] using wordTrace_append hprefix tailTrace_1873915
  have hstable : (prefixWord ++ tailWord_1873915).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1873915).length < 2 ^ (prefixWord ++ tailWord_1873915).sum := by decide
  have hdescent : baseEnd_1873915 < baseStart_1873915 := by decide
  rcases family_descends (prefixWord ++ tailWord_1873915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1873932 : List Nat := [2, 2, 1, 2, 3, 1, 1, 5, 1, 4]
def baseStart_1873932 : Nat := 118140960795 + 1873932 * 2 ^ 59
def prefixEnd_1873932 : Nat := 4983230072969 + 3 ^ 40 * 1873932 * 2
def baseEnd_1873932 : Nat := 641485219894178310754633

theorem tailTrace_1873932 : CollatzResearch.WordTrace tailWord_1873932 prefixEnd_1873932 641485219894178310754633 := by
  unfold tailWord_1873932
  simp only [CollatzResearch.WordTrace]
  refine ⟨34173957523535940475428025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45565276698047920633904033 34173957523535940475428025)
  ·
    refine ⟨25630468142651955356571019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34173957523535940475428025 25630468142651955356571019)
    ·
      refine ⟨38445702213977933034856529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25630468142651955356571019 38445702213977933034856529)
      ·
        refine ⟨28834276660483449776142397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38445702213977933034856529 28834276660483449776142397)
        ·
          refine ⟨10812853747681293666053399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28834276660483449776142397 10812853747681293666053399)
          ·
            refine ⟨16219280621521940499080099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10812853747681293666053399 16219280621521940499080099)
            ·
              refine ⟨24328920932282910748620149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16219280621521940499080099 24328920932282910748620149)
              ·
                refine ⟨2280836337401522882683139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24328920932282910748620149 2280836337401522882683139)
                ·
                  refine ⟨3421254506102284324024709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2280836337401522882683139 3421254506102284324024709)
                  ·
                    refine ⟨641485219894178310754633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3421254506102284324024709 641485219894178310754633)
                    ·
                      rfl

theorem cell22_1873932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 5, 1, 4].length) (baseStart_1873932 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1873932 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1873932 prefixEnd_1873932 := by exact prefixLift 1873932
  have htrace : WordTrace (prefixWord ++ tailWord_1873932) baseStart_1873932 baseEnd_1873932 := by
    simpa [prefixWord, tailWord_1873932, baseEnd_1873932] using wordTrace_append hprefix tailTrace_1873932
  have hstable : (prefixWord ++ tailWord_1873932).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1873932).length < 2 ^ (prefixWord ++ tailWord_1873932).sum := by decide
  have hdescent : baseEnd_1873932 < baseStart_1873932 := by decide
  rcases family_descends (prefixWord ++ tailWord_1873932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1873940 : List Nat := [2, 4, 3, 2, 2, 1, 1, 1, 3, 3]
def baseStart_1873940 : Nat := 118140960795 + 1873940 * 2 ^ 59
def prefixEnd_1873940 : Nat := 4983230072969 + 3 ^ 40 * 1873940 * 2
def baseEnd_1873940 : Nat := 641487958457668956554609

theorem tailTrace_1873940 : CollatzResearch.WordTrace tailWord_1873940 prefixEnd_1873940 641487958457668956554609 := by
  unfold tailWord_1873940
  simp only [CollatzResearch.WordTrace]
  refine ⟨34174103415521449158573637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45565471220695265544764849 34174103415521449158573637)
  ·
    refine ⟨6407644390410271717232557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34174103415521449158573637 6407644390410271717232557)
    ·
      refine ⟨2402866646403851893962209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6407644390410271717232557 2402866646403851893962209)
      ·
        refine ⟨1802149984802888920471657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2402866646403851893962209 1802149984802888920471657)
        ·
          refine ⟨1351612488602166690353743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1802149984802888920471657 1351612488602166690353743)
          ·
            refine ⟨2027418732903250035530615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1351612488602166690353743 2027418732903250035530615)
            ·
              refine ⟨3041128099354875053295923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2027418732903250035530615 3041128099354875053295923)
              ·
                refine ⟨4561692149032312579943885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3041128099354875053295923 4561692149032312579943885)
                ·
                  refine ⟨1710634555887117217478957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4561692149032312579943885 1710634555887117217478957)
                  ·
                    refine ⟨641487958457668956554609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1710634555887117217478957 641487958457668956554609)
                    ·
                      rfl

theorem cell22_1873940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 2, 1, 1, 1, 3, 3].length) (baseStart_1873940 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1873940 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1873940 prefixEnd_1873940 := by exact prefixLift 1873940
  have htrace : WordTrace (prefixWord ++ tailWord_1873940) baseStart_1873940 baseEnd_1873940 := by
    simpa [prefixWord, tailWord_1873940, baseEnd_1873940] using wordTrace_append hprefix tailTrace_1873940
  have hstable : (prefixWord ++ tailWord_1873940).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1873940).length < 2 ^ (prefixWord ++ tailWord_1873940).sum := by decide
  have hdescent : baseEnd_1873940 < baseStart_1873940 := by decide
  rcases family_descends (prefixWord ++ tailWord_1873940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1873966 : List Nat := [4, 1, 3, 1, 1, 4, 1, 2, 1, 4]
def baseStart_1873966 : Nat := 118140960795 + 1873966 * 2 ^ 59
def prefixEnd_1873966 : Nat := 4983230072969 + 3 ^ 40 * 1873966 * 2
def baseEnd_1873966 : Nat := 641496858789013555404529

theorem tailTrace_1873966 : CollatzResearch.WordTrace tailWord_1873966 prefixEnd_1873966 641496858789013555404529 := by
  unfold tailWord_1873966
  simp only [CollatzResearch.WordTrace]
  refine ⟨8543644391118588094699219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45566103419299136505062501 8543644391118588094699219)
  ·
    refine ⟨12815466586677882142048829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8543644391118588094699219 12815466586677882142048829)
    ·
      refine ⟨4805799970004205803268311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12815466586677882142048829 4805799970004205803268311)
      ·
        refine ⟨7208699955006308704902467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4805799970004205803268311 7208699955006308704902467)
        ·
          refine ⟨10813049932509463057353701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7208699955006308704902467 10813049932509463057353701)
          ·
            refine ⟨2027446862345524323253819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10813049932509463057353701 2027446862345524323253819)
            ·
              refine ⟨3041170293518286484880729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2027446862345524323253819 3041170293518286484880729)
              ·
                refine ⟨2280877720138714863660547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3041170293518286484880729 2280877720138714863660547)
                ·
                  refine ⟨3421316580208072295490821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2280877720138714863660547 3421316580208072295490821)
                  ·
                    refine ⟨641496858789013555404529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3421316580208072295490821 641496858789013555404529)
                    ·
                      rfl

theorem cell22_1873966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 4, 1, 2, 1, 4].length) (baseStart_1873966 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1873966 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1873966 prefixEnd_1873966 := by exact prefixLift 1873966
  have htrace : WordTrace (prefixWord ++ tailWord_1873966) baseStart_1873966 baseEnd_1873966 := by
    simpa [prefixWord, tailWord_1873966, baseEnd_1873966] using wordTrace_append hprefix tailTrace_1873966
  have hstable : (prefixWord ++ tailWord_1873966).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1873966).length < 2 ^ (prefixWord ++ tailWord_1873966).sum := by decide
  have hdescent : baseEnd_1873966 < baseStart_1873966 := by decide
  rcases family_descends (prefixWord ++ tailWord_1873966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1873975 : List Nat := [1, 1, 3, 1, 2, 2, 4, 8]
def baseStart_1873975 : Nat := 118140960795 + 1873975 * 2 ^ 59
def prefixEnd_1873975 : Nat := 4983230072969 + 3 ^ 40 * 1873975 * 2
def baseEnd_1873975 : Nat := 71277771074771170214389

theorem tailTrace_1873975 : CollatzResearch.WordTrace tailWord_1873975 prefixEnd_1873975 71277771074771170214389 := by
  unfold tailWord_1873975
  simp only [CollatzResearch.WordTrace]
  refine ⟨68349483385916099294671379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45566322257277399529780919 68349483385916099294671379)
  ·
    refine ⟨102524225078874148942007069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68349483385916099294671379 102524225078874148942007069)
    ·
      refine ⟨38446584404577805853252651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102524225078874148942007069 38446584404577805853252651)
      ·
        refine ⟨57669876606866708779878977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38446584404577805853252651 57669876606866708779878977)
        ·
          refine ⟨43252407455150031584909233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57669876606866708779878977 43252407455150031584909233)
          ·
            refine ⟨32439305591362523688681925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43252407455150031584909233 32439305591362523688681925)
            ·
              refine ⟨6082369798380473191627861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32439305591362523688681925 6082369798380473191627861)
              ·
                refine ⟨71277771074771170214389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6082369798380473191627861 71277771074771170214389)
                ·
                  rfl

theorem cell22_1873975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 4, 8].length) (baseStart_1873975 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1873975 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1873975 prefixEnd_1873975 := by exact prefixLift 1873975
  have htrace : WordTrace (prefixWord ++ tailWord_1873975) baseStart_1873975 baseEnd_1873975 := by
    simpa [prefixWord, tailWord_1873975, baseEnd_1873975] using wordTrace_append hprefix tailTrace_1873975
  have hstable : (prefixWord ++ tailWord_1873975).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1873975).length < 2 ^ (prefixWord ++ tailWord_1873975).sum := by decide
  have hdescent : baseEnd_1873975 < baseStart_1873975 := by decide
  rcases family_descends (prefixWord ++ tailWord_1873975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1874041 : List Nat := [1, 2, 1, 3, 4, 1, 1, 5, 1, 3]
def baseStart_1874041 : Nat := 118140960795 + 1874041 * 2 ^ 59
def prefixEnd_1874041 : Nat := 4983230072969 + 3 ^ 40 * 1874041 * 2
def baseEnd_1874041 : Nat := 641522532821738359779299

theorem tailTrace_1874041 : CollatzResearch.WordTrace tailWord_1874041 prefixEnd_1874041 641522532821738359779299 := by
  unfold tailWord_1874041
  simp only [CollatzResearch.WordTrace]
  refine ⟨68351890603676992566573977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45567927069117995044382651 68351890603676992566573977)
  ·
    refine ⟨51263917952757744424930483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68351890603676992566573977 51263917952757744424930483)
    ·
      refine ⟨76895876929136616637395725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51263917952757744424930483 76895876929136616637395725)
      ·
        refine ⟨28835953848426231239023397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76895876929136616637395725 28835953848426231239023397)
        ·
          refine ⟨5406741346579918357316887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28835953848426231239023397 5406741346579918357316887)
          ·
            refine ⟨8110112019869877535975331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5406741346579918357316887 8110112019869877535975331)
            ·
              refine ⟨12165168029804816303962997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8110112019869877535975331 12165168029804816303962997)
              ·
                refine ⟨1140484502794201528496531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12165168029804816303962997 1140484502794201528496531)
                ·
                  refine ⟨1710726754191302292744797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1140484502794201528496531 1710726754191302292744797)
                  ·
                    refine ⟨641522532821738359779299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1710726754191302292744797 641522532821738359779299)
                    ·
                      rfl

theorem cell22_1874041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 5, 1, 3].length) (baseStart_1874041 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1874041 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1874041 prefixEnd_1874041 := by exact prefixLift 1874041
  have htrace : WordTrace (prefixWord ++ tailWord_1874041) baseStart_1874041 baseEnd_1874041 := by
    simpa [prefixWord, tailWord_1874041, baseEnd_1874041] using wordTrace_append hprefix tailTrace_1874041
  have hstable : (prefixWord ++ tailWord_1874041).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1874041).length < 2 ^ (prefixWord ++ tailWord_1874041).sum := by decide
  have hdescent : baseEnd_1874041 < baseStart_1874041 := by decide
  rcases family_descends (prefixWord ++ tailWord_1874041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1874052 : List Nat := [2, 3, 2, 1, 2, 1, 1, 1, 4, 5]
def baseStart_1874052 : Nat := 118140960795 + 1874052 * 2 ^ 59
def prefixEnd_1874052 : Nat := 4983230072969 + 3 ^ 40 * 1874052 * 2
def baseEnd_1874052 : Nat := 641526298346537997754265

theorem tailTrace_1874052 : CollatzResearch.WordTrace tailWord_1874052 prefixEnd_1874052 641526298346537997754265 := by
  unfold tailWord_1874052
  simp only [CollatzResearch.WordTrace]
  refine ⟨34176145903318570722612205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45568194537758094296816273 34176145903318570722612205)
  ·
    refine ⟨12816054713744464020979577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34176145903318570722612205 12816054713744464020979577)
    ·
      refine ⟨9612041035308348015734683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12816054713744464020979577 9612041035308348015734683)
      ·
        refine ⟨14418061552962522023602025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9612041035308348015734683 14418061552962522023602025)
        ·
          refine ⟨10813546164721891517701519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14418061552962522023602025 10813546164721891517701519)
          ·
            refine ⟨16220319247082837276552279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10813546164721891517701519 16220319247082837276552279)
            ·
              refine ⟨24330478870624255914828419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16220319247082837276552279 24330478870624255914828419)
              ·
                refine ⟨36495718305936383872242629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24330478870624255914828419 36495718305936383872242629)
                ·
                  refine ⟨6842947182363071976045493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36495718305936383872242629 6842947182363071976045493)
                  ·
                    refine ⟨641526298346537997754265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6842947182363071976045493 641526298346537997754265)
                    ·
                      rfl

theorem cell22_1874052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 1, 4, 5].length) (baseStart_1874052 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1874052 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1874052 prefixEnd_1874052 := by exact prefixLift 1874052
  have htrace : WordTrace (prefixWord ++ tailWord_1874052) baseStart_1874052 baseEnd_1874052 := by
    simpa [prefixWord, tailWord_1874052, baseEnd_1874052] using wordTrace_append hprefix tailTrace_1874052
  have hstable : (prefixWord ++ tailWord_1874052).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1874052).length < 2 ^ (prefixWord ++ tailWord_1874052).sum := by decide
  have hdescent : baseEnd_1874052 < baseStart_1874052 := by decide
  rcases family_descends (prefixWord ++ tailWord_1874052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1874071 : List Nat := [1, 1, 3, 3, 4, 1, 3, 1, 5]
def baseStart_1874071 : Nat := 118140960795 + 1874071 * 2 ^ 59
def prefixEnd_1874071 : Nat := 4983230072969 + 3 ^ 40 * 1874071 * 2
def baseEnd_1874071 : Nat := 213844267478276093843069

theorem tailTrace_1874071 : CollatzResearch.WordTrace tailWord_1874071 prefixEnd_1874071 213844267478276093843069 := by
  unfold tailWord_1874071
  simp only [CollatzResearch.WordTrace]
  refine ⟨68352984793568307690166067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45568656529045538460110711 68352984793568307690166067)
  ·
    refine ⟨102529477190352461535249101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68352984793568307690166067 102529477190352461535249101)
    ·
      refine ⟨38448553946382173075718413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102529477190352461535249101 38448553946382173075718413)
      ·
        refine ⟨14418207729893314903394405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38448553946382173075718413 14418207729893314903394405)
        ·
          refine ⟨2703413949354996544386451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14418207729893314903394405 2703413949354996544386451)
          ·
            refine ⟨4055120924032494816579677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2703413949354996544386451 4055120924032494816579677)
            ·
              refine ⟨1520670346512185556217379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4055120924032494816579677 1520670346512185556217379)
              ·
                refine ⟨2281005519768278334326069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1520670346512185556217379 2281005519768278334326069)
                ·
                  refine ⟨213844267478276093843069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2281005519768278334326069 213844267478276093843069)
                  ·
                    rfl

theorem cell22_1874071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 3, 1, 5].length) (baseStart_1874071 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1874071 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1874071 prefixEnd_1874071 := by exact prefixLift 1874071
  have htrace : WordTrace (prefixWord ++ tailWord_1874071) baseStart_1874071 baseEnd_1874071 := by
    simpa [prefixWord, tailWord_1874071, baseEnd_1874071] using wordTrace_append hprefix tailTrace_1874071
  have hstable : (prefixWord ++ tailWord_1874071).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1874071).length < 2 ^ (prefixWord ++ tailWord_1874071).sum := by decide
  have hdescent : baseEnd_1874071 < baseStart_1874071 := by decide
  rcases family_descends (prefixWord ++ tailWord_1874071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1874116 : List Nat := [2, 3, 3, 1, 2, 3, 1, 1, 6]
def baseStart_1874116 : Nat := 118140960795 + 1874116 * 2 ^ 59
def prefixEnd_1874116 : Nat := 4983230072969 + 3 ^ 40 * 1874116 * 2
def baseEnd_1874116 : Nat := 213849402284821054718023

theorem tailTrace_1874116 : CollatzResearch.WordTrace tailWord_1874116 prefixEnd_1874116 213849402284821054718023 := by
  unfold tailWord_1874116
  simp only [CollatzResearch.WordTrace]
  refine ⟨34177313039202640187777101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45569750718936853583702801 34177313039202640187777101)
  ·
    refine ⟨12816492389700990070416413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34177313039202640187777101 12816492389700990070416413)
    ·
      refine ⟨4806184646137871276406155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12816492389700990070416413 4806184646137871276406155)
      ·
        refine ⟨7209276969206806914609233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4806184646137871276406155 7209276969206806914609233)
        ·
          refine ⟨5406957726905105185956925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7209276969206806914609233 5406957726905105185956925)
          ·
            refine ⟨2027609147589414444733847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5406957726905105185956925 2027609147589414444733847)
            ·
              refine ⟨3041413721384121667100771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2027609147589414444733847 3041413721384121667100771)
              ·
                refine ⟨4562120582076182500651157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3041413721384121667100771 4562120582076182500651157)
                ·
                  refine ⟨213849402284821054718023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4562120582076182500651157 213849402284821054718023)
                  ·
                    rfl

theorem cell22_1874116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 3, 1, 1, 6].length) (baseStart_1874116 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1874116 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1874116 prefixEnd_1874116 := by exact prefixLift 1874116
  have htrace : WordTrace (prefixWord ++ tailWord_1874116) baseStart_1874116 baseEnd_1874116 := by
    simpa [prefixWord, tailWord_1874116, baseEnd_1874116] using wordTrace_append hprefix tailTrace_1874116
  have hstable : (prefixWord ++ tailWord_1874116).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1874116).length < 2 ^ (prefixWord ++ tailWord_1874116).sum := by decide
  have hdescent : baseEnd_1874116 < baseStart_1874116 := by decide
  rcases family_descends (prefixWord ++ tailWord_1874116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1874127 : List Nat := [1, 1, 2, 1, 1, 3, 6, 7]
def baseStart_1874127 : Nat := 118140960795 + 1874127 * 2 ^ 59
def prefixEnd_1874127 : Nat := 4983230072969 + 3 ^ 40 * 1874127 * 2
def baseEnd_1874127 : Nat := 71283552486584755792115

theorem tailTrace_1874127 : CollatzResearch.WordTrace tailWord_1874127 prefixEnd_1874127 71283552486584755792115 := by
  unfold tailWord_1874127
  simp only [CollatzResearch.WordTrace]
  refine ⟨68355027281365429254204635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45570018187576952836136423 68355027281365429254204635)
  ·
    refine ⟨102532540922048143881306953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68355027281365429254204635 102532540922048143881306953)
    ·
      refine ⟨76899405691536107910980215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102532540922048143881306953 76899405691536107910980215)
      ·
        refine ⟨115349108537304161866470323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76899405691536107910980215 115349108537304161866470323)
        ·
          refine ⟨173023662805956242799705485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115349108537304161866470323 173023662805956242799705485)
          ·
            refine ⟨64883873552233591049889557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 173023662805956242799705485 64883873552233591049889557)
            ·
              refine ⟨3041431572760949580463573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 64883873552233591049889557 3041431572760949580463573)
              ·
                refine ⟨71283552486584755792115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3041431572760949580463573 71283552486584755792115)
                ·
                  rfl

theorem cell22_1874127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 6, 7].length) (baseStart_1874127 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1874127 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1874127 prefixEnd_1874127 := by exact prefixLift 1874127
  have htrace : WordTrace (prefixWord ++ tailWord_1874127) baseStart_1874127 baseEnd_1874127 := by
    simpa [prefixWord, tailWord_1874127, baseEnd_1874127] using wordTrace_append hprefix tailTrace_1874127
  have hstable : (prefixWord ++ tailWord_1874127).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1874127).length < 2 ^ (prefixWord ++ tailWord_1874127).sum := by decide
  have hdescent : baseEnd_1874127 < baseStart_1874127 := by decide
  rcases family_descends (prefixWord ++ tailWord_1874127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1874174 : List Nat := [4, 2, 2, 1, 1, 1, 1, 1, 1, 8]
def baseStart_1874174 : Nat := 118140960795 + 1874174 * 2 ^ 59
def prefixEnd_1874174 : Nat := 4983230072969 + 3 ^ 40 * 1874174 * 2
def baseEnd_1874174 : Nat := 641568061439770346203891

theorem tailTrace_1874174 : CollatzResearch.WordTrace tailWord_1874174 prefixEnd_1874174 641568061439770346203891 := by
  unfold tailWord_1874174
  simp only [CollatzResearch.WordTrace]
  refine ⟨8544592689024394535145697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45571161008130104187443717 8544592689024394535145697)
  ·
    refine ⟨6408444516768295901359273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8544592689024394535145697 6408444516768295901359273)
    ·
      refine ⟨4806333387576221926019455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6408444516768295901359273 4806333387576221926019455)
      ·
        refine ⟨7209500081364332889029183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4806333387576221926019455 7209500081364332889029183)
        ·
          refine ⟨10814250122046499333543775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7209500081364332889029183 10814250122046499333543775)
          ·
            refine ⟨16221375183069749000315663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10814250122046499333543775 16221375183069749000315663)
            ·
              refine ⟨24332062774604623500473495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16221375183069749000315663 24332062774604623500473495)
              ·
                refine ⟨36498094161906935250710243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24332062774604623500473495 36498094161906935250710243)
                ·
                  refine ⟨54747141242860402876065365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36498094161906935250710243 54747141242860402876065365)
                  ·
                    refine ⟨641568061439770346203891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 54747141242860402876065365 641568061439770346203891)
                    ·
                      rfl

theorem cell22_1874174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 1, 1, 8].length) (baseStart_1874174 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1874174 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1874174 prefixEnd_1874174 := by exact prefixLift 1874174
  have htrace : WordTrace (prefixWord ++ tailWord_1874174) baseStart_1874174 baseEnd_1874174 := by
    simpa [prefixWord, tailWord_1874174, baseEnd_1874174] using wordTrace_append hprefix tailTrace_1874174
  have hstable : (prefixWord ++ tailWord_1874174).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1874174).length < 2 ^ (prefixWord ++ tailWord_1874174).sum := by decide
  have hdescent : baseEnd_1874174 < baseStart_1874174 := by decide
  rcases family_descends (prefixWord ++ tailWord_1874174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1874210 : List Nat := [3, 3, 1, 1, 3, 2, 2, 3, 1, 3]
def baseStart_1874210 : Nat := 118140960795 + 1874210 * 2 ^ 59
def prefixEnd_1874210 : Nat := 4983230072969 + 3 ^ 40 * 1874210 * 2
def baseEnd_1874210 : Nat := 641580384975478252303781

theorem tailTrace_1874210 : CollatzResearch.WordTrace tailWord_1874210 prefixEnd_1874210 641580384975478252303781 := by
  unfold tailWord_1874210
  simp only [CollatzResearch.WordTrace]
  refine ⟨17089513635016183607369021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45572036360043156286317389 17089513635016183607369021)
  ·
    refine ⟨6408567613131068852763383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17089513635016183607369021 6408567613131068852763383)
    ·
      refine ⟨9612851419696603279145075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6408567613131068852763383 9612851419696603279145075)
      ·
        refine ⟨14419277129544904918717613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9612851419696603279145075 14419277129544904918717613)
        ·
          refine ⟨5407228923579339344519105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14419277129544904918717613 5407228923579339344519105)
          ·
            refine ⟨4055421692684504508389329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5407228923579339344519105 4055421692684504508389329)
            ·
              refine ⟨3041566269513378381291997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4055421692684504508389329 3041566269513378381291997)
              ·
                refine ⟨1140587351067516892984499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3041566269513378381291997 1140587351067516892984499)
                ·
                  refine ⟨1710881026601275339476749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1140587351067516892984499 1710881026601275339476749)
                  ·
                    refine ⟨641580384975478252303781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1710881026601275339476749 641580384975478252303781)
                    ·
                      rfl

theorem cell22_1874210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 2, 3, 1, 3].length) (baseStart_1874210 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1874210 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1874210 prefixEnd_1874210 := by exact prefixLift 1874210
  have htrace : WordTrace (prefixWord ++ tailWord_1874210) baseStart_1874210 baseEnd_1874210 := by
    simpa [prefixWord, tailWord_1874210, baseEnd_1874210] using wordTrace_append hprefix tailTrace_1874210
  have hstable : (prefixWord ++ tailWord_1874210).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1874210).length < 2 ^ (prefixWord ++ tailWord_1874210).sum := by decide
  have hdescent : baseEnd_1874210 < baseStart_1874210 := by decide
  rcases family_descends (prefixWord ++ tailWord_1874210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1874234 : List Nat := [3, 1, 1, 1, 4, 2, 1, 3, 6]
def baseStart_1874234 : Nat := 118140960795 + 1874234 * 2 ^ 59
def prefixEnd_1874234 : Nat := 4983230072969 + 3 ^ 40 * 1874234 * 2
def baseEnd_1874234 : Nat := 213862866888650063234569

theorem tailTrace_1874234 : CollatzResearch.WordTrace tailWord_1874234 prefixEnd_1874234 213862866888650063234569 := by
  unfold tailWord_1874234
  simp only [CollatzResearch.WordTrace]
  refine ⟨17089732472994446632087439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45572619927985191018899837 17089732472994446632087439)
  ·
    refine ⟨25634598709491669948131159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17089732472994446632087439 25634598709491669948131159)
    ·
      refine ⟨38451898064237504922196739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25634598709491669948131159 38451898064237504922196739)
      ·
        refine ⟨57677847096356257383295109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38451898064237504922196739 57677847096356257383295109)
        ·
          refine ⟨10814596330566798259367833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57677847096356257383295109 10814596330566798259367833)
          ·
            refine ⟨8110947247925098694525875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10814596330566798259367833 8110947247925098694525875)
            ·
              refine ⟨12166420871887648041788813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8110947247925098694525875 12166420871887648041788813)
              ·
                refine ⟨4562407826957868015670805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12166420871887648041788813 4562407826957868015670805)
                ·
                  refine ⟨213862866888650063234569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4562407826957868015670805 213862866888650063234569)
                  ·
                    rfl

theorem cell22_1874234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 3, 6].length) (baseStart_1874234 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1874234 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1874234 prefixEnd_1874234 := by exact prefixLift 1874234
  have htrace : WordTrace (prefixWord ++ tailWord_1874234) baseStart_1874234 baseEnd_1874234 := by
    simpa [prefixWord, tailWord_1874234, baseEnd_1874234] using wordTrace_append hprefix tailTrace_1874234
  have hstable : (prefixWord ++ tailWord_1874234).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1874234).length < 2 ^ (prefixWord ++ tailWord_1874234).sum := by decide
  have hdescent : baseEnd_1874234 < baseStart_1874234 := by decide
  rcases family_descends (prefixWord ++ tailWord_1874234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1874279 : List Nat := [1, 1, 5, 1, 3, 1, 10]
def baseStart_1874279 : Nat := 118140960795 + 1874279 * 2 ^ 59
def prefixEnd_1874279 : Nat := 4983230072969 + 3 ^ 40 * 1874279 * 2
def baseEnd_1874279 : Nat := 23763111299466113789947

theorem tailTrace_1874279 : CollatzResearch.WordTrace tailWord_1874279 prefixEnd_1874279 23763111299466113789947 := by
  unfold tailWord_1874279
  simp only [CollatzResearch.WordTrace]
  refine ⟨68360571176814759213737891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45573714117876506142491927 68360571176814759213737891)
  ·
    refine ⟨102540856765222138820606837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68360571176814759213737891 102540856765222138820606837)
    ·
      refine ⟨9613205321739575514431891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 102540856765222138820606837 9613205321739575514431891)
      ·
        refine ⟨14419807982609363271647837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9613205321739575514431891 14419807982609363271647837)
        ·
          refine ⟨5407427993478511226867939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14419807982609363271647837 5407427993478511226867939)
          ·
            refine ⟨8111141990217766840301909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5407427993478511226867939 8111141990217766840301909)
            ·
              refine ⟨23763111299466113789947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 8111141990217766840301909 23763111299466113789947)
              ·
                rfl

theorem cell22_1874279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 10].length) (baseStart_1874279 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1874279 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1874279 prefixEnd_1874279 := by exact prefixLift 1874279
  have htrace : WordTrace (prefixWord ++ tailWord_1874279) baseStart_1874279 baseEnd_1874279 := by
    simpa [prefixWord, tailWord_1874279, baseEnd_1874279] using wordTrace_append hprefix tailTrace_1874279
  have hstable : (prefixWord ++ tailWord_1874279).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1874279).length < 2 ^ (prefixWord ++ tailWord_1874279).sum := by decide
  have hdescent : baseEnd_1874279 < baseStart_1874279 := by decide
  rcases family_descends (prefixWord ++ tailWord_1874279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1874311 : List Nat := [1, 1, 4, 2, 2, 1, 2, 1, 5, 3]
def baseStart_1874311 : Nat := 118140960795 + 1874311 * 2 ^ 59
def prefixEnd_1874311 : Nat := 4983230072969 + 3 ^ 40 * 1874311 * 2
def baseEnd_1874311 : Nat := 641614959339547655528471

theorem tailTrace_1874311 : CollatzResearch.WordTrace tailWord_1874311 prefixEnd_1874311 641614959339547655528471 := by
  unfold tailWord_1874311
  simp only [CollatzResearch.WordTrace]
  refine ⟨68361738312698828678902787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45574492208465885785935191 68361738312698828678902787)
  ·
    refine ⟨102542607469048243018354181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68361738312698828678902787 102542607469048243018354181)
    ·
      refine ⟨19226738900446545565941409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 102542607469048243018354181 19226738900446545565941409)
      ·
        refine ⟨14420054175334909174456057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19226738900446545565941409 14420054175334909174456057)
        ·
          refine ⟨10815040631501181880842043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14420054175334909174456057 10815040631501181880842043)
          ·
            refine ⟨16222560947251772821263065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10815040631501181880842043 16222560947251772821263065)
            ·
              refine ⟨12166920710438829615947299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16222560947251772821263065 12166920710438829615947299)
              ·
                refine ⟨18250381065658244423920949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12166920710438829615947299 18250381065658244423920949)
                ·
                  refine ⟨1710973224905460414742589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 18250381065658244423920949 1710973224905460414742589)
                  ·
                    refine ⟨641614959339547655528471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1710973224905460414742589 641614959339547655528471)
                    ·
                      rfl

theorem cell22_1874311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 1, 5, 3].length) (baseStart_1874311 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1874311 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1874311 prefixEnd_1874311 := by exact prefixLift 1874311
  have htrace : WordTrace (prefixWord ++ tailWord_1874311) baseStart_1874311 baseEnd_1874311 := by
    simpa [prefixWord, tailWord_1874311, baseEnd_1874311] using wordTrace_append hprefix tailTrace_1874311
  have hstable : (prefixWord ++ tailWord_1874311).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1874311).length < 2 ^ (prefixWord ++ tailWord_1874311).sum := by decide
  have hdescent : baseEnd_1874311 < baseStart_1874311 := by decide
  rcases family_descends (prefixWord ++ tailWord_1874311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1874341 : List Nat := [1, 3, 1, 2, 1, 1, 6, 2, 5]
def baseStart_1874341 : Nat := 118140960795 + 1874341 * 2 ^ 59
def prefixEnd_1874341 : Nat := 4983230072969 + 3 ^ 40 * 1874341 * 2
def baseEnd_1874341 : Nat := 213875076317545859092793

theorem tailTrace_1874341 : CollatzResearch.WordTrace tailWord_1874341 prefixEnd_1874341 213875076317545859092793 := by
  unfold tailWord_1874341
  simp only [CollatzResearch.WordTrace]
  refine ⟨68362832502590143802494877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45575221668393429201663251 68362832502590143802494877)
  ·
    refine ⟨25636062188471303925935579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68362832502590143802494877 25636062188471303925935579)
    ·
      refine ⟨38454093282706955888903369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25636062188471303925935579 38454093282706955888903369)
      ·
        refine ⟨28840569962030216916677527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38454093282706955888903369 28840569962030216916677527)
        ·
          refine ⟨43260854943045325375016291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28840569962030216916677527 43260854943045325375016291)
          ·
            refine ⟨64891282414567988062524437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43260854943045325375016291 64891282414567988062524437)
            ·
              refine ⟨3041778863182874440430833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 64891282414567988062524437 3041778863182874440430833)
              ·
                refine ⟨2281334147387155830323125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3041778863182874440430833 2281334147387155830323125)
                ·
                  refine ⟨213875076317545859092793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2281334147387155830323125 213875076317545859092793)
                  ·
                    rfl

theorem cell22_1874341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 6, 2, 5].length) (baseStart_1874341 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1874341 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1874341 prefixEnd_1874341 := by exact prefixLift 1874341
  have htrace : WordTrace (prefixWord ++ tailWord_1874341) baseStart_1874341 baseEnd_1874341 := by
    simpa [prefixWord, tailWord_1874341, baseEnd_1874341] using wordTrace_append hprefix tailTrace_1874341
  have hstable : (prefixWord ++ tailWord_1874341).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1874341).length < 2 ^ (prefixWord ++ tailWord_1874341).sum := by decide
  have hdescent : baseEnd_1874341 < baseStart_1874341 := by decide
  rcases family_descends (prefixWord ++ tailWord_1874341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1874371 : List Nat := [1, 1, 1, 3, 1, 1, 3, 6, 1, 4]
def baseStart_1874371 : Nat := 118140960795 + 1874371 * 2 ^ 59
def prefixEnd_1874371 : Nat := 4983230072969 + 3 ^ 40 * 1874371 * 2
def baseEnd_1874371 : Nat := 641635498565727499028287

theorem tailTrace_1874371 : CollatzResearch.WordTrace tailWord_1874371 prefixEnd_1874371 641635498565727499028287 := by
  unfold tailWord_1874371
  simp only [CollatzResearch.WordTrace]
  refine ⟨68363926692481458926086967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45575951128320972617391311 68363926692481458926086967)
  ·
    refine ⟨102545890038722188389130451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68363926692481458926086967 102545890038722188389130451)
    ·
      refine ⟨153818835058083282583695677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102545890038722188389130451 153818835058083282583695677)
      ·
        refine ⟨57682063146781230968885879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 153818835058083282583695677 57682063146781230968885879)
        ·
          refine ⟨86523094720171846453328819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57682063146781230968885879 86523094720171846453328819)
          ·
            refine ⟨129784642080257769679993229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86523094720171846453328819 129784642080257769679993229)
            ·
              refine ⟨48669240780096663629997461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 129784642080257769679993229 48669240780096663629997461)
              ·
                refine ⟨2281370661567031107656131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 48669240780096663629997461 2281370661567031107656131)
                ·
                  refine ⟨3422055992350546661484197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2281370661567031107656131 3422055992350546661484197)
                  ·
                    refine ⟨641635498565727499028287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3422055992350546661484197 641635498565727499028287)
                    ·
                      rfl

theorem cell22_1874371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 6, 1, 4].length) (baseStart_1874371 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1874371 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1874371 prefixEnd_1874371 := by exact prefixLift 1874371
  have htrace : WordTrace (prefixWord ++ tailWord_1874371) baseStart_1874371 baseEnd_1874371 := by
    simpa [prefixWord, tailWord_1874371, baseEnd_1874371] using wordTrace_append hprefix tailTrace_1874371
  have hstable : (prefixWord ++ tailWord_1874371).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1874371).length < 2 ^ (prefixWord ++ tailWord_1874371).sum := by decide
  have hdescent : baseEnd_1874371 < baseStart_1874371 := by decide
  rcases family_descends (prefixWord ++ tailWord_1874371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1874403 : List Nat := [1, 1, 1, 6, 3, 1, 2, 1, 6]
def baseStart_1874403 : Nat := 118140960795 + 1874403 * 2 ^ 59
def prefixEnd_1874403 : Nat := 4983230072969 + 3 ^ 40 * 1874403 * 2
def baseEnd_1874403 : Nat := 213882150939896694076063

theorem tailTrace_1874403 : CollatzResearch.WordTrace tailWord_1874403 prefixEnd_1874403 213882150939896694076063 := by
  unfold tailWord_1874403
  simp only [CollatzResearch.WordTrace]
  refine ⟨68365093828365528391251863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45576729218910352260834575 68365093828365528391251863)
  ·
    refine ⟨102547640742548292586877795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68365093828365528391251863 102547640742548292586877795)
    ·
      refine ⟨153821461113822438880316693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102547640742548292586877795 153821461113822438880316693)
      ·
        refine ⟨7210380989710426822514845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 153821461113822438880316693 7210380989710426822514845)
        ·
          refine ⟨2703892871141410058443067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7210380989710426822514845 2703892871141410058443067)
          ·
            refine ⟨4055839306712115087664601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2703892871141410058443067 4055839306712115087664601)
            ·
              refine ⟨3041879480034086315748451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4055839306712115087664601 3041879480034086315748451)
              ·
                refine ⟨4562819220051129473622677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3041879480034086315748451 4562819220051129473622677)
                ·
                  refine ⟨213882150939896694076063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4562819220051129473622677 213882150939896694076063)
                  ·
                    rfl

theorem cell22_1874403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 2, 1, 6].length) (baseStart_1874403 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1874403 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1874403 prefixEnd_1874403 := by exact prefixLift 1874403
  have htrace : WordTrace (prefixWord ++ tailWord_1874403) baseStart_1874403 baseEnd_1874403 := by
    simpa [prefixWord, tailWord_1874403, baseEnd_1874403] using wordTrace_append hprefix tailTrace_1874403
  have hstable : (prefixWord ++ tailWord_1874403).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1874403).length < 2 ^ (prefixWord ++ tailWord_1874403).sum := by decide
  have hdescent : baseEnd_1874403 < baseStart_1874403 := by decide
  rcases family_descends (prefixWord ++ tailWord_1874403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1874538 : List Nat := [3, 1, 3, 2, 1, 1, 3, 2, 6]
def baseStart_1874538 : Nat := 118140960795 + 1874538 * 2 ^ 59
def prefixEnd_1874538 : Nat := 4983230072969 + 3 ^ 40 * 1874538 * 2
def baseEnd_1874538 : Nat := 213897555359531576700925

theorem tailTrace_1874538 : CollatzResearch.WordTrace tailWord_1874538 prefixEnd_1874538 213897555359531576700925 := by
  unfold tailWord_1874538
  simp only [CollatzResearch.WordTrace]
  refine ⟨17092504420719111611854067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45580011788584297631610845 17092504420719111611854067)
  ·
    refine ⟨25638756631078667417781101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17092504420719111611854067 25638756631078667417781101)
    ·
      refine ⟨9614533736654500281667913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25638756631078667417781101 9614533736654500281667913)
      ·
        refine ⟨7210900302490875211250935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9614533736654500281667913 7210900302490875211250935)
        ·
          refine ⟨10816350453736312816876403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7210900302490875211250935 10816350453736312816876403)
          ·
            refine ⟨16224525680604469225314605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10816350453736312816876403 16224525680604469225314605)
            ·
              refine ⟨6084197130226675959492977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16224525680604469225314605 6084197130226675959492977)
              ·
                refine ⟨4563147847670006969619733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6084197130226675959492977 4563147847670006969619733)
                ·
                  refine ⟨213897555359531576700925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4563147847670006969619733 213897555359531576700925)
                  ·
                    rfl

theorem cell22_1874538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 3, 2, 6].length) (baseStart_1874538 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1874538 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1874538 prefixEnd_1874538 := by exact prefixLift 1874538
  have htrace : WordTrace (prefixWord ++ tailWord_1874538) baseStart_1874538 baseEnd_1874538 := by
    simpa [prefixWord, tailWord_1874538, baseEnd_1874538] using wordTrace_append hprefix tailTrace_1874538
  have hstable : (prefixWord ++ tailWord_1874538).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1874538).length < 2 ^ (prefixWord ++ tailWord_1874538).sum := by decide
  have hdescent : baseEnd_1874538 < baseStart_1874538 := by decide
  rcases family_descends (prefixWord ++ tailWord_1874538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1874553 : List Nat := [1, 2, 1, 3, 3, 2, 2, 2, 1, 5]
def baseStart_1874553 : Nat := 118140960795 + 1874553 * 2 ^ 59
def prefixEnd_1874553 : Nat := 4983230072969 + 3 ^ 40 * 1874553 * 2
def baseEnd_1874553 : Nat := 641697800885139690977729

theorem tailTrace_1874553 : CollatzResearch.WordTrace tailWord_1874553 prefixEnd_1874553 641697800885139690977729 := by
  unfold tailWord_1874553
  simp only [CollatzResearch.WordTrace]
  refine ⟨68370564777822104009212313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45580376518548069339474875 68370564777822104009212313)
  ·
    refine ⟨51277923583366578006909235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68370564777822104009212313 51277923583366578006909235)
    ·
      refine ⟨76916885375049867010363853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51277923583366578006909235 76916885375049867010363853)
      ·
        refine ⟨28843832015643700128886445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76916885375049867010363853 28843832015643700128886445)
        ·
          refine ⟨10816437005866387548332417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28843832015643700128886445 10816437005866387548332417)
          ·
            refine ⟨8112327754399790661249313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10816437005866387548332417 8112327754399790661249313)
            ·
              refine ⟨6084245815799842995936985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8112327754399790661249313 6084245815799842995936985)
              ·
                refine ⟨4563184361849882246952739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6084245815799842995936985 4563184361849882246952739)
                ·
                  refine ⟨6844776542774823370429109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4563184361849882246952739 6844776542774823370429109)
                  ·
                    refine ⟨641697800885139690977729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6844776542774823370429109 641697800885139690977729)
                    ·
                      rfl

theorem cell22_1874553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 2, 2, 1, 5].length) (baseStart_1874553 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1874553 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1874553 prefixEnd_1874553 := by exact prefixLift 1874553
  have htrace : WordTrace (prefixWord ++ tailWord_1874553) baseStart_1874553 baseEnd_1874553 := by
    simpa [prefixWord, tailWord_1874553, baseEnd_1874553] using wordTrace_append hprefix tailTrace_1874553
  have hstable : (prefixWord ++ tailWord_1874553).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1874553).length < 2 ^ (prefixWord ++ tailWord_1874553).sum := by decide
  have hdescent : baseEnd_1874553 < baseStart_1874553 := by decide
  rcases family_descends (prefixWord ++ tailWord_1874553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1874632 : List Nat := [2, 1, 3, 1, 2, 5, 1, 1, 3, 3]
def baseStart_1874632 : Nat := 118140960795 + 1874632 * 2 ^ 59
def prefixEnd_1874632 : Nat := 4983230072969 + 3 ^ 40 * 1874632 * 2
def baseEnd_1874632 : Nat := 641724844199609818252487

theorem tailTrace_1874632 : CollatzResearch.WordTrace tailWord_1874632 prefixEnd_1874632 641724844199609818252487 := by
  unfold tailWord_1874632
  simp only [CollatzResearch.WordTrace]
  refine ⟨34186723072267950250669075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45582297429690600334225433 34186723072267950250669075)
  ·
    refine ⟨51280084608401925376003613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34186723072267950250669075 51280084608401925376003613)
    ·
      refine ⟨19230031728150722016001355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51280084608401925376003613 19230031728150722016001355)
      ·
        refine ⟨28845047592226083024002033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19230031728150722016001355 28845047592226083024002033)
        ·
          refine ⟨21633785694169562268001525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28845047592226083024002033 21633785694169562268001525)
          ·
            refine ⟨2028167408828396462625143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 21633785694169562268001525 2028167408828396462625143)
            ·
              refine ⟨3042251113242594693937715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2028167408828396462625143 3042251113242594693937715)
              ·
                refine ⟨4563376669863892040906573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3042251113242594693937715 4563376669863892040906573)
                ·
                  refine ⟨1711266251198959515339965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4563376669863892040906573 1711266251198959515339965)
                  ·
                    refine ⟨641724844199609818252487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1711266251198959515339965 641724844199609818252487)
                    ·
                      rfl

theorem cell22_1874632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 5, 1, 1, 3, 3].length) (baseStart_1874632 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1874632 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1874632 prefixEnd_1874632 := by exact prefixLift 1874632
  have htrace : WordTrace (prefixWord ++ tailWord_1874632) baseStart_1874632 baseEnd_1874632 := by
    simpa [prefixWord, tailWord_1874632, baseEnd_1874632] using wordTrace_append hprefix tailTrace_1874632
  have hstable : (prefixWord ++ tailWord_1874632).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1874632).length < 2 ^ (prefixWord ++ tailWord_1874632).sum := by decide
  have hdescent : baseEnd_1874632 < baseStart_1874632 := by decide
  rcases family_descends (prefixWord ++ tailWord_1874632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1874703 : List Nat := [1, 1, 2, 1, 1, 1, 6, 2, 1, 6]
def baseStart_1874703 : Nat := 118140960795 + 1874703 * 2 ^ 59
def prefixEnd_1874703 : Nat := 4983230072969 + 3 ^ 40 * 1874703 * 2
def baseEnd_1874703 : Nat := 641749148950589299727269

theorem tailTrace_1874703 : CollatzResearch.WordTrace tailWord_1874703 prefixEnd_1874703 641749148950589299727269 := by
  unfold tailWord_1874703
  simp only [CollatzResearch.WordTrace]
  refine ⟨68376035727278679627172763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45584023818185786418115175 68376035727278679627172763)
  ·
    refine ⟨102564053590918019440759145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68376035727278679627172763 102564053590918019440759145)
    ·
      refine ⟨76923040193188514580569359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102564053590918019440759145 76923040193188514580569359)
      ·
        refine ⟨115384560289782771870854039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76923040193188514580569359 115384560289782771870854039)
        ·
          refine ⟨173076840434674157806281059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115384560289782771870854039 173076840434674157806281059)
          ·
            refine ⟨259615260652011236709421589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173076840434674157806281059 259615260652011236709421589)
            ·
              refine ⟨12169465343063026720754137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 259615260652011236709421589 12169465343063026720754137)
              ·
                refine ⟨9127099007297270040565603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12169465343063026720754137 9127099007297270040565603)
                ·
                  refine ⟨13690648510945905060848405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9127099007297270040565603 13690648510945905060848405)
                  ·
                    refine ⟨641749148950589299727269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13690648510945905060848405 641749148950589299727269)
                    ·
                      rfl

theorem cell22_1874703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 2, 1, 6].length) (baseStart_1874703 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1874703 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1874703 prefixEnd_1874703 := by exact prefixLift 1874703
  have htrace : WordTrace (prefixWord ++ tailWord_1874703) baseStart_1874703 baseEnd_1874703 := by
    simpa [prefixWord, tailWord_1874703, baseEnd_1874703] using wordTrace_append hprefix tailTrace_1874703
  have hstable : (prefixWord ++ tailWord_1874703).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1874703).length < 2 ^ (prefixWord ++ tailWord_1874703).sum := by decide
  have hdescent : baseEnd_1874703 < baseStart_1874703 := by decide
  rcases family_descends (prefixWord ++ tailWord_1874703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1874720 : List Nat := [2, 1, 1, 5, 1, 3, 1, 1, 1, 6]
def baseStart_1874720 : Nat := 118140960795 + 1874720 * 2 ^ 59
def prefixEnd_1874720 : Nat := 4983230072969 + 3 ^ 40 * 1874720 * 2
def baseEnd_1874720 : Nat := 641754968398006922052217

theorem tailTrace_1874720 : CollatzResearch.WordTrace tailWord_1874720 prefixEnd_1874720 641754968398006922052217 := by
  unfold tailWord_1874720
  simp only [CollatzResearch.WordTrace]
  refine ⟨34188327884108545765270807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45584437178811394353694409 34188327884108545765270807)
  ·
    refine ⟨51282491826162818647906211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34188327884108545765270807 51282491826162818647906211)
    ·
      refine ⟨76923737739244227971859317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51282491826162818647906211 76923737739244227971859317)
      ·
        refine ⟨7211600413054146372361811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 76923737739244227971859317 7211600413054146372361811)
        ·
          refine ⟨10817400619581219558542717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7211600413054146372361811 10817400619581219558542717)
          ·
            refine ⟨4056525232342957334453519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10817400619581219558542717 4056525232342957334453519)
            ·
              refine ⟨6084787848514436001680279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4056525232342957334453519 6084787848514436001680279)
              ·
                refine ⟨9127181772771654002520419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6084787848514436001680279 9127181772771654002520419)
                ·
                  refine ⟨13690772659157481003780629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9127181772771654002520419 13690772659157481003780629)
                  ·
                    refine ⟨641754968398006922052217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13690772659157481003780629 641754968398006922052217)
                    ·
                      rfl

theorem cell22_1874720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 1, 1, 1, 6].length) (baseStart_1874720 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1874720 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1874720 prefixEnd_1874720 := by exact prefixLift 1874720
  have htrace : WordTrace (prefixWord ++ tailWord_1874720) baseStart_1874720 baseEnd_1874720 := by
    simpa [prefixWord, tailWord_1874720, baseEnd_1874720] using wordTrace_append hprefix tailTrace_1874720
  have hstable : (prefixWord ++ tailWord_1874720).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1874720).length < 2 ^ (prefixWord ++ tailWord_1874720).sum := by decide
  have hdescent : baseEnd_1874720 < baseStart_1874720 := by decide
  rcases family_descends (prefixWord ++ tailWord_1874720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1874724 : List Nat := [2, 3, 1, 3, 3, 1, 2, 3, 4]
def baseStart_1874724 : Nat := 118140960795 + 1874724 * 2 ^ 59
def prefixEnd_1874724 : Nat := 4983230072969 + 3 ^ 40 * 1874724 * 2
def baseEnd_1874724 : Nat := 213918779226584081650735

theorem tailTrace_1874724 : CollatzResearch.WordTrace tailWord_1874724 prefixEnd_1874724 213918779226584081650735 := by
  unfold tailWord_1874724
  simp only [CollatzResearch.WordTrace]
  refine ⟨34188400830101300106843613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45584534440135066809124817 34188400830101300106843613)
  ·
    refine ⟨12820650311287987540066355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34188400830101300106843613 12820650311287987540066355)
    ·
      refine ⟨19230975466931981310099533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12820650311287987540066355 19230975466931981310099533)
      ·
        refine ⟨7211615800099492991287325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19230975466931981310099533 7211615800099492991287325)
        ·
          refine ⟨2704355925037309871732747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7211615800099492991287325 2704355925037309871732747)
          ·
            refine ⟨4056533887555964807599121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2704355925037309871732747 4056533887555964807599121)
            ·
              refine ⟨3042400415666973605699341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4056533887555964807599121 3042400415666973605699341)
              ·
                refine ⟨1140900155875115102137253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3042400415666973605699341 1140900155875115102137253)
                ·
                  refine ⟨213918779226584081650735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1140900155875115102137253 213918779226584081650735)
                  ·
                    rfl

theorem cell22_1874724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 2, 3, 4].length) (baseStart_1874724 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1874724 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1874724 prefixEnd_1874724 := by exact prefixLift 1874724
  have htrace : WordTrace (prefixWord ++ tailWord_1874724) baseStart_1874724 baseEnd_1874724 := by
    simpa [prefixWord, tailWord_1874724, baseEnd_1874724] using wordTrace_append hprefix tailTrace_1874724
  have hstable : (prefixWord ++ tailWord_1874724).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1874724).length < 2 ^ (prefixWord ++ tailWord_1874724).sum := by decide
  have hdescent : baseEnd_1874724 < baseStart_1874724 := by decide
  rcases family_descends (prefixWord ++ tailWord_1874724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1874739 : List Nat := [1, 1, 1, 2, 6, 3, 1, 2, 2, 3]
def baseStart_1874739 : Nat := 118140960795 + 1874739 * 2 ^ 59
def prefixEnd_1874739 : Nat := 4983230072969 + 3 ^ 40 * 1874739 * 2
def baseEnd_1874739 : Nat := 641761472486297205827159

theorem tailTrace_1874739 : CollatzResearch.WordTrace tailWord_1874739 prefixEnd_1874739 641761472486297205827159 := by
  unfold tailWord_1874739
  simp only [CollatzResearch.WordTrace]
  refine ⟨68377348755148257775483271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45584899170098838516988847 68377348755148257775483271)
  ·
    refine ⟨102566023132722386663224907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68377348755148257775483271 102566023132722386663224907)
    ·
      refine ⟨153849034699083579994837361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102566023132722386663224907 153849034699083579994837361)
      ·
        refine ⟨115386776024312684996128021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153849034699083579994837361 115386776024312684996128021)
        ·
          refine ⟨5408755126139657109193501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 115386776024312684996128021 5408755126139657109193501)
          ·
            refine ⟨2028283172302371415947563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5408755126139657109193501 2028283172302371415947563)
            ·
              refine ⟨3042424758453557123921345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2028283172302371415947563 3042424758453557123921345)
              ·
                refine ⟨2281818568840167842941009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3042424758453557123921345 2281818568840167842941009)
                ·
                  refine ⟨1711363926630125882205757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2281818568840167842941009 1711363926630125882205757)
                  ·
                    refine ⟨641761472486297205827159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1711363926630125882205757 641761472486297205827159)
                    ·
                      rfl

theorem cell22_1874739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 3, 1, 2, 2, 3].length) (baseStart_1874739 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1874739 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1874739 prefixEnd_1874739 := by exact prefixLift 1874739
  have htrace : WordTrace (prefixWord ++ tailWord_1874739) baseStart_1874739 baseEnd_1874739 := by
    simpa [prefixWord, tailWord_1874739, baseEnd_1874739] using wordTrace_append hprefix tailTrace_1874739
  have hstable : (prefixWord ++ tailWord_1874739).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1874739).length < 2 ^ (prefixWord ++ tailWord_1874739).sum := by decide
  have hdescent : baseEnd_1874739 < baseStart_1874739 := by decide
  rcases family_descends (prefixWord ++ tailWord_1874739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1874756 : List Nat := [2, 3, 4, 2, 1, 2, 1, 1, 1, 5]
def baseStart_1874756 : Nat := 118140960795 + 1874756 * 2 ^ 59
def prefixEnd_1874756 : Nat := 4983230072969 + 3 ^ 40 * 1874756 * 2
def baseEnd_1874756 : Nat := 641767291933714828152107

theorem tailTrace_1874756 : CollatzResearch.WordTrace tailWord_1874756 prefixEnd_1874756 641767291933714828152107 := by
  unfold tailWord_1874756
  simp only [CollatzResearch.WordTrace]
  refine ⟨34188984398043334839426061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45585312530724446452568081 34188984398043334839426061)
  ·
    refine ⟨12820869149266250564784773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34188984398043334839426061 12820869149266250564784773)
    ·
      refine ⟨2403912965487421980897145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12820869149266250564784773 2403912965487421980897145)
      ·
        refine ⟨1802934724115566485672859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2403912965487421980897145 1802934724115566485672859)
        ·
          refine ⟨2704402086173349728509289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1802934724115566485672859 2704402086173349728509289)
          ·
            refine ⟨2028301564630012296381967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2704402086173349728509289 2028301564630012296381967)
            ·
              refine ⟨3042452346945018444572951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2028301564630012296381967 3042452346945018444572951)
              ·
                refine ⟨4563678520417527666859427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3042452346945018444572951 4563678520417527666859427)
                ·
                  refine ⟨6845517780626291500289141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4563678520417527666859427 6845517780626291500289141)
                  ·
                    refine ⟨641767291933714828152107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6845517780626291500289141 641767291933714828152107)
                    ·
                      rfl

theorem cell22_1874756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 2, 1, 1, 1, 5].length) (baseStart_1874756 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1874756 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1874756 prefixEnd_1874756 := by exact prefixLift 1874756
  have htrace : WordTrace (prefixWord ++ tailWord_1874756) baseStart_1874756 baseEnd_1874756 := by
    simpa [prefixWord, tailWord_1874756, baseEnd_1874756] using wordTrace_append hprefix tailTrace_1874756
  have hstable : (prefixWord ++ tailWord_1874756).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1874756).length < 2 ^ (prefixWord ++ tailWord_1874756).sum := by decide
  have hdescent : baseEnd_1874756 < baseStart_1874756 := by decide
  rcases family_descends (prefixWord ++ tailWord_1874756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1874769 : List Nat := [1, 2, 2, 1, 7, 1, 2, 6]
def baseStart_1874769 : Nat := 118140960795 + 1874769 * 2 ^ 59
def prefixEnd_1874769 : Nat := 4983230072969 + 3 ^ 40 * 1874769 * 2
def baseEnd_1874769 : Nat := 71307971344376347508563

theorem tailTrace_1874769 : CollatzResearch.WordTrace tailWord_1874769 prefixEnd_1874769 71307971344376347508563 := by
  unfold tailWord_1874769
  simp only [CollatzResearch.WordTrace]
  refine ⟨68378442945039572899075361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45585628630026381932716907 68378442945039572899075361)
  ·
    refine ⟨51283832208779679674306521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68378442945039572899075361 51283832208779679674306521)
    ·
      refine ⟨38462874156584759755729891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51283832208779679674306521 38462874156584759755729891)
      ·
        refine ⟨57694311234877139633594837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38462874156584759755729891 57694311234877139633594837)
        ·
          refine ⟨1352210419567432960162379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 57694311234877139633594837 1352210419567432960162379)
          ·
            refine ⟨2028315629351149440243569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1352210419567432960162379 2028315629351149440243569)
            ·
              refine ⟨1521236722013362080182677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2028315629351149440243569 1521236722013362080182677)
              ·
                refine ⟨71307971344376347508563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1521236722013362080182677 71307971344376347508563)
                ·
                  rfl

theorem cell22_1874769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 7, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 7, 1, 2, 6].length) (baseStart_1874769 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1874769 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1874769 prefixEnd_1874769 := by exact prefixLift 1874769
  have htrace : WordTrace (prefixWord ++ tailWord_1874769) baseStart_1874769 baseEnd_1874769 := by
    simpa [prefixWord, tailWord_1874769, baseEnd_1874769] using wordTrace_append hprefix tailTrace_1874769
  have hstable : (prefixWord ++ tailWord_1874769).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1874769).length < 2 ^ (prefixWord ++ tailWord_1874769).sum := by decide
  have hdescent : baseEnd_1874769 < baseStart_1874769 := by decide
  rcases family_descends (prefixWord ++ tailWord_1874769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1874801 : List Nat := [1, 2, 2, 2, 1, 5, 3, 2, 1, 3]
def baseStart_1874801 : Nat := 118140960795 + 1874801 * 2 ^ 59
def prefixEnd_1874801 : Nat := 4983230072969 + 3 ^ 40 * 1874801 * 2
def baseEnd_1874801 : Nat := 641782696353349710776969

theorem tailTrace_1874801 : CollatzResearch.WordTrace tailWord_1874801 prefixEnd_1874801 641782696353349710776969 := by
  unfold tailWord_1874801
  simp only [CollatzResearch.WordTrace]
  refine ⟨68379610080923642364240257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45586406720615761576160171 68379610080923642364240257)
  ·
    refine ⟨51284707560692731773180193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68379610080923642364240257 51284707560692731773180193)
    ·
      refine ⟨38463530670519548829885145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51284707560692731773180193 38463530670519548829885145)
      ·
        refine ⟨28847648002889661622413859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38463530670519548829885145 28847648002889661622413859)
        ·
          refine ⟨43271472004334492433620789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28847648002889661622413859 43271472004334492433620789)
          ·
            refine ⟨4056700500406358665651949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 43271472004334492433620789 4056700500406358665651949)
            ·
              refine ⟨1521262687652384499619481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4056700500406358665651949 1521262687652384499619481)
              ·
                refine ⟨1140947015739288374714611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1521262687652384499619481 1140947015739288374714611)
                ·
                  refine ⟨1711420523608932562071917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1140947015739288374714611 1711420523608932562071917)
                  ·
                    refine ⟨641782696353349710776969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1711420523608932562071917 641782696353349710776969)
                    ·
                      rfl

theorem cell22_1874801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 3, 2, 1, 3].length) (baseStart_1874801 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1874801 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1874801 prefixEnd_1874801 := by exact prefixLift 1874801
  have htrace : WordTrace (prefixWord ++ tailWord_1874801) baseStart_1874801 baseEnd_1874801 := by
    simpa [prefixWord, tailWord_1874801, baseEnd_1874801] using wordTrace_append hprefix tailTrace_1874801
  have hstable : (prefixWord ++ tailWord_1874801).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1874801).length < 2 ^ (prefixWord ++ tailWord_1874801).sum := by decide
  have hdescent : baseEnd_1874801 < baseStart_1874801 := by decide
  rcases family_descends (prefixWord ++ tailWord_1874801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1874810 : List Nat := [3, 1, 1, 1, 1, 1, 3, 4, 3, 4]
def baseStart_1874810 : Nat := 118140960795 + 1874810 * 2 ^ 59
def prefixEnd_1874810 : Nat := 4983230072969 + 3 ^ 40 * 1874810 * 2
def baseEnd_1874810 : Nat := 641785777237276687301941

theorem tailTrace_1874810 : CollatzResearch.WordTrace tailWord_1874810 prefixEnd_1874810 641785777237276687301941 := by
  unfold tailWord_1874810
  simp only [CollatzResearch.WordTrace]
  refine ⟨17094984584472759225329471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45586625558594024600878589 17094984584472759225329471)
  ·
    refine ⟨25642476876709138837994207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17094984584472759225329471 25642476876709138837994207)
    ·
      refine ⟨38463715315063708256991311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25642476876709138837994207 38463715315063708256991311)
      ·
        refine ⟨57695572972595562385486967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38463715315063708256991311 57695572972595562385486967)
        ·
          refine ⟨86543359458893343578230451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57695572972595562385486967 86543359458893343578230451)
          ·
            refine ⟨129815039188340015367345677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86543359458893343578230451 129815039188340015367345677)
            ·
              refine ⟨48680639695627505762754629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 129815039188340015367345677 48680639695627505762754629)
              ·
                refine ⟨9127619942930157330516493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48680639695627505762754629 9127619942930157330516493)
                ·
                  refine ⟨3422857478598808998943685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9127619942930157330516493 3422857478598808998943685)
                  ·
                    refine ⟨641785777237276687301941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3422857478598808998943685 641785777237276687301941)
                    ·
                      rfl

theorem cell22_1874810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 4, 3, 4].length) (baseStart_1874810 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1874810 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1874810 prefixEnd_1874810 := by exact prefixLift 1874810
  have htrace : WordTrace (prefixWord ++ tailWord_1874810) baseStart_1874810 baseEnd_1874810 := by
    simpa [prefixWord, tailWord_1874810, baseEnd_1874810] using wordTrace_append hprefix tailTrace_1874810
  have hstable : (prefixWord ++ tailWord_1874810).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1874810).length < 2 ^ (prefixWord ++ tailWord_1874810).sum := by decide
  have hdescent : baseEnd_1874810 < baseStart_1874810 := by decide
  rcases family_descends (prefixWord ++ tailWord_1874810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1874827 : List Nat := [1, 1, 1, 1, 4, 2, 5, 2, 1, 4]
def baseStart_1874827 : Nat := 118140960795 + 1874827 * 2 ^ 59
def prefixEnd_1874827 : Nat := 4983230072969 + 3 ^ 40 * 1874827 * 2
def baseEnd_1874827 : Nat := 641791596684694309626889

theorem tailTrace_1874827 : CollatzResearch.WordTrace tailWord_1874827 prefixEnd_1874827 641791596684694309626889 := by
  unfold tailWord_1874827
  simp only [CollatzResearch.WordTrace]
  refine ⟨68380558378829448804686735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45587038919219632536457823 68380558378829448804686735)
  ·
    refine ⟨102570837568244173207030103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68380558378829448804686735 102570837568244173207030103)
    ·
      refine ⟨153856256352366259810545155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102570837568244173207030103 153856256352366259810545155)
      ·
        refine ⟨230784384528549389715817733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153856256352366259810545155 230784384528549389715817733)
        ·
          refine ⟨43272072099103010571715825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 230784384528549389715817733 43272072099103010571715825)
          ·
            refine ⟨32454054074327257928786869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43272072099103010571715825 32454054074327257928786869)
            ·
              refine ⟨3042567569468180430823769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 32454054074327257928786869 3042567569468180430823769)
              ·
                refine ⟨2281925677101135323117827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3042567569468180430823769 2281925677101135323117827)
                ·
                  refine ⟨3422888515651702984676741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2281925677101135323117827 3422888515651702984676741)
                  ·
                    refine ⟨641791596684694309626889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3422888515651702984676741 641791596684694309626889)
                    ·
                      rfl

theorem cell22_1874827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 5, 2, 1, 4].length) (baseStart_1874827 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1874827 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1874827 prefixEnd_1874827 := by exact prefixLift 1874827
  have htrace : WordTrace (prefixWord ++ tailWord_1874827) baseStart_1874827 baseEnd_1874827 := by
    simpa [prefixWord, tailWord_1874827, baseEnd_1874827] using wordTrace_append hprefix tailTrace_1874827
  have hstable : (prefixWord ++ tailWord_1874827).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1874827).length < 2 ^ (prefixWord ++ tailWord_1874827).sum := by decide
  have hdescent : baseEnd_1874827 < baseStart_1874827 := by decide
  rcases family_descends (prefixWord ++ tailWord_1874827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1874919 : List Nat := [1, 1, 5, 2, 2, 1, 1, 3, 3, 3]
def baseStart_1874919 : Nat := 118140960795 + 1874919 * 2 ^ 59
def prefixEnd_1874919 : Nat := 4983230072969 + 3 ^ 40 * 1874919 * 2
def baseEnd_1874919 : Nat := 641823090164836736326607

theorem tailTrace_1874919 : CollatzResearch.WordTrace tailWord_1874919 prefixEnd_1874919 641823090164836736326607 := by
  unfold tailWord_1874919
  simp only [CollatzResearch.WordTrace]
  refine ⟨68383913894496148517035811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45589275929664099011357207 68383913894496148517035811)
  ·
    refine ⟨102575870841744222775553717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68383913894496148517035811 102575870841744222775553717)
    ·
      refine ⟨9616487891413520885208161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 102575870841744222775553717 9616487891413520885208161)
      ·
        refine ⟨7212365918560140663906121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9616487891413520885208161 7212365918560140663906121)
        ·
          refine ⟨5409274438920105497929591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7212365918560140663906121 5409274438920105497929591)
          ·
            refine ⟨8113911658380158246894387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5409274438920105497929591 8113911658380158246894387)
            ·
              refine ⟨12170867487570237370341581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8113911658380158246894387 12170867487570237370341581)
              ·
                refine ⟨4564075307838839013878093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12170867487570237370341581 4564075307838839013878093)
                ·
                  refine ⟨1711528240439564630204285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4564075307838839013878093 1711528240439564630204285)
                  ·
                    refine ⟨641823090164836736326607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1711528240439564630204285 641823090164836736326607)
                    ·
                      rfl

theorem cell22_1874919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 3, 3, 3].length) (baseStart_1874919 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1874919 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1874919 prefixEnd_1874919 := by exact prefixLift 1874919
  have htrace : WordTrace (prefixWord ++ tailWord_1874919) baseStart_1874919 baseEnd_1874919 := by
    simpa [prefixWord, tailWord_1874919, baseEnd_1874919] using wordTrace_append hprefix tailTrace_1874919
  have hstable : (prefixWord ++ tailWord_1874919).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1874919).length < 2 ^ (prefixWord ++ tailWord_1874919).sum := by decide
  have hdescent : baseEnd_1874919 < baseStart_1874919 := by decide
  rcases family_descends (prefixWord ++ tailWord_1874919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1874983 : List Nat := [1, 1, 7, 1, 1, 3, 2, 1, 5]
def baseStart_1874983 : Nat := 118140960795 + 1874983 * 2 ^ 59
def prefixEnd_1874983 : Nat := 4983230072969 + 3 ^ 40 * 1874983 * 2
def baseEnd_1874983 : Nat := 213948332890920634242137

theorem tailTrace_1874983 : CollatzResearch.WordTrace tailWord_1874983 prefixEnd_1874983 213948332890920634242137 := by
  unfold tailWord_1874983
  simp only [CollatzResearch.WordTrace]
  refine ⟨68386248166264287447365603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45590832110842858298243735 68386248166264287447365603)
  ·
    refine ⟨102579372249396431171048405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68386248166264287447365603 102579372249396431171048405)
    ·
      refine ⟨2404204037095228855571447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 102579372249396431171048405 2404204037095228855571447)
      ·
        refine ⟨3606306055642843283357171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2404204037095228855571447 3606306055642843283357171)
        ·
          refine ⟨5409459083464264925035757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3606306055642843283357171 5409459083464264925035757)
          ·
            refine ⟨2028547156299099346888409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5409459083464264925035757 2028547156299099346888409)
            ·
              refine ⟨1521410367224324510166307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2028547156299099346888409 1521410367224324510166307)
              ·
                refine ⟨2282115550836486765249461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1521410367224324510166307 2282115550836486765249461)
                ·
                  refine ⟨213948332890920634242137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2282115550836486765249461 213948332890920634242137)
                  ·
                    rfl

theorem cell22_1874983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 3, 2, 1, 5].length) (baseStart_1874983 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1874983 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1874983 prefixEnd_1874983 := by exact prefixLift 1874983
  have htrace : WordTrace (prefixWord ++ tailWord_1874983) baseStart_1874983 baseEnd_1874983 := by
    simpa [prefixWord, tailWord_1874983, baseEnd_1874983] using wordTrace_append hprefix tailTrace_1874983
  have hstable : (prefixWord ++ tailWord_1874983).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1874983).length < 2 ^ (prefixWord ++ tailWord_1874983).sum := by decide
  have hdescent : baseEnd_1874983 < baseStart_1874983 := by decide
  rcases family_descends (prefixWord ++ tailWord_1874983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1874992 : List Nat := [2, 1, 1, 1, 2, 4, 2, 3, 1, 5]
def baseStart_1874992 : Nat := 118140960795 + 1874992 * 2 ^ 59
def prefixEnd_1874992 : Nat := 4983230072969 + 3 ^ 40 * 1874992 * 2
def baseEnd_1874992 : Nat := 641848079556688879251383

theorem tailTrace_1874992 : CollatzResearch.WordTrace tailWord_1874992 prefixEnd_1874992 641848079556688879251383 := by
  unfold tailWord_1874992
  simp only [CollatzResearch.WordTrace]
  refine ⟨34193288211615840992221615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45591050948821121322962153 34193288211615840992221615)
  ·
    refine ⟨51289932317423761488332423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34193288211615840992221615 51289932317423761488332423)
    ·
      refine ⟨76934898476135642232498635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51289932317423761488332423 76934898476135642232498635)
      ·
        refine ⟨115402347714203463348747953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76934898476135642232498635 115402347714203463348747953)
        ·
          refine ⟨86551760785652597511560965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115402347714203463348747953 86551760785652597511560965)
          ·
            refine ⟨16228455147309862033417681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 86551760785652597511560965 16228455147309862033417681)
            ·
              refine ⟨12171341360482396525063261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16228455147309862033417681 12171341360482396525063261)
              ·
                refine ⟨4564253010180898696898723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12171341360482396525063261 4564253010180898696898723)
                ·
                  refine ⟨6846379515271348045348085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4564253010180898696898723 6846379515271348045348085)
                  ·
                    refine ⟨641848079556688879251383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6846379515271348045348085 641848079556688879251383)
                    ·
                      rfl

theorem cell22_1874992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 3, 1, 5].length) (baseStart_1874992 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1874992 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1874992 prefixEnd_1874992 := by exact prefixLift 1874992
  have htrace : WordTrace (prefixWord ++ tailWord_1874992) baseStart_1874992 baseEnd_1874992 := by
    simpa [prefixWord, tailWord_1874992, baseEnd_1874992] using wordTrace_append hprefix tailTrace_1874992
  have hstable : (prefixWord ++ tailWord_1874992).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1874992).length < 2 ^ (prefixWord ++ tailWord_1874992).sum := by decide
  have hdescent : baseEnd_1874992 < baseStart_1874992 := by decide
  rcases family_descends (prefixWord ++ tailWord_1874992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1874996 : List Nat := [2, 5, 1, 2, 1, 2, 1, 1, 3, 4]
def baseStart_1874996 : Nat := 118140960795 + 1874996 * 2 ^ 59
def prefixEnd_1874996 : Nat := 4983230072969 + 3 ^ 40 * 1874996 * 2
def baseEnd_1874996 : Nat := 641849448838434202151371

theorem tailTrace_1874996 : CollatzResearch.WordTrace tailWord_1874996 prefixEnd_1874996 641849448838434202151371 := by
  unfold tailWord_1874996
  simp only [CollatzResearch.WordTrace]
  refine ⟨34193361157608595333794421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45591148210144793778392561 34193361157608595333794421)
  ·
    refine ⟨3205627608525805812543227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 34193361157608595333794421 3205627608525805812543227)
    ·
      refine ⟨4808441412788708718814841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3205627608525805812543227 4808441412788708718814841)
      ·
        refine ⟨3606331059591531539111131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4808441412788708718814841 3606331059591531539111131)
        ·
          refine ⟨5409496589387297308666697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3606331059591531539111131 5409496589387297308666697)
          ·
            refine ⟨4057122442040472981500023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5409496589387297308666697 4057122442040472981500023)
            ·
              refine ⟨6085683663060709472250035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4057122442040472981500023 6085683663060709472250035)
              ·
                refine ⟨9128525494591064208375053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6085683663060709472250035 9128525494591064208375053)
                ·
                  refine ⟨3423197060471649078140645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9128525494591064208375053 3423197060471649078140645)
                  ·
                    refine ⟨641849448838434202151371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3423197060471649078140645 641849448838434202151371)
                    ·
                      rfl

theorem cell22_1874996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 1, 1, 3, 4].length) (baseStart_1874996 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1874996 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1874996 prefixEnd_1874996 := by exact prefixLift 1874996
  have htrace : WordTrace (prefixWord ++ tailWord_1874996) baseStart_1874996 baseEnd_1874996 := by
    simpa [prefixWord, tailWord_1874996, baseEnd_1874996] using wordTrace_append hprefix tailTrace_1874996
  have hstable : (prefixWord ++ tailWord_1874996).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1874996).length < 2 ^ (prefixWord ++ tailWord_1874996).sum := by decide
  have hdescent : baseEnd_1874996 < baseStart_1874996 := by decide
  rcases family_descends (prefixWord ++ tailWord_1874996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1875026 : List Nat := [3, 2, 2, 1, 3, 1, 1, 4, 2, 3]
def baseStart_1875026 : Nat := 118140960795 + 1875026 * 2 ^ 59
def prefixEnd_1875026 : Nat := 4983230072969 + 3 ^ 40 * 1875026 * 2
def baseEnd_1875026 : Nat := 641859718451524123901279

theorem tailTrace_1875026 : CollatzResearch.WordTrace tailWord_1875026 prefixEnd_1875026 641859718451524123901279 := by
  unfold tailWord_1875026
  simp only [CollatzResearch.WordTrace]
  refine ⟨17096954126277126447795233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45591877670072337194120621 17096954126277126447795233)
  ·
    refine ⟨12822715594707844835846425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17096954126277126447795233 12822715594707844835846425)
    ·
      refine ⟨9617036696030883626884819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12822715594707844835846425 9617036696030883626884819)
      ·
        refine ⟨14425555044046325440327229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9617036696030883626884819 14425555044046325440327229)
        ·
          refine ⟨5409583141517372040122711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14425555044046325440327229 5409583141517372040122711)
          ·
            refine ⟨8114374712276058060184067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5409583141517372040122711 8114374712276058060184067)
            ·
              refine ⟨12171562068414087090276101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8114374712276058060184067 12171562068414087090276101)
              ·
                refine ⟨2282167887827641329426769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12171562068414087090276101 2282167887827641329426769)
                ·
                  refine ⟨1711625915870730997070077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2282167887827641329426769 1711625915870730997070077)
                  ·
                    refine ⟨641859718451524123901279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1711625915870730997070077 641859718451524123901279)
                    ·
                      rfl

theorem cell22_1875026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 4, 2, 3].length) (baseStart_1875026 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1875026 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1875026 prefixEnd_1875026 := by exact prefixLift 1875026
  have htrace : WordTrace (prefixWord ++ tailWord_1875026) baseStart_1875026 baseEnd_1875026 := by
    simpa [prefixWord, tailWord_1875026, baseEnd_1875026] using wordTrace_append hprefix tailTrace_1875026
  have hstable : (prefixWord ++ tailWord_1875026).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1875026).length < 2 ^ (prefixWord ++ tailWord_1875026).sum := by decide
  have hdescent : baseEnd_1875026 < baseStart_1875026 := by decide
  rcases family_descends (prefixWord ++ tailWord_1875026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1875052 : List Nat := [2, 2, 1, 1, 3, 2, 1, 2, 2, 6]
def baseStart_1875052 : Nat := 118140960795 + 1875052 * 2 ^ 59
def prefixEnd_1875052 : Nat := 4983230072969 + 3 ^ 40 * 1875052 * 2
def baseEnd_1875052 : Nat := 641868618782868722751199

theorem tailTrace_1875052 : CollatzResearch.WordTrace tailWord_1875052 prefixEnd_1875052 641868618782868722751199 := by
  unfold tailWord_1875052
  simp only [CollatzResearch.WordTrace]
  refine ⟨34194382401507156115813705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45592509868676208154418273 34194382401507156115813705)
  ·
    refine ⟨25645786801130367086860279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34194382401507156115813705 25645786801130367086860279)
    ·
      refine ⟨38468680201695550630290419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25645786801130367086860279 38468680201695550630290419)
      ·
        refine ⟨57703020302543325945435629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38468680201695550630290419 57703020302543325945435629)
        ·
          refine ⟨21638632613453747229538361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57703020302543325945435629 21638632613453747229538361)
          ·
            refine ⟨16228974460090310422153771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21638632613453747229538361 16228974460090310422153771)
            ·
              refine ⟨24343461690135465633230657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16228974460090310422153771 24343461690135465633230657)
              ·
                refine ⟨18257596267601599224922993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24343461690135465633230657 18257596267601599224922993)
                ·
                  refine ⟨13693197200701199418692245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18257596267601599224922993 13693197200701199418692245)
                  ·
                    refine ⟨641868618782868722751199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13693197200701199418692245 641868618782868722751199)
                    ·
                      rfl

theorem cell22_1875052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 6].length) (baseStart_1875052 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1875052 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1875052 prefixEnd_1875052 := by exact prefixLift 1875052
  have htrace : WordTrace (prefixWord ++ tailWord_1875052) baseStart_1875052 baseEnd_1875052 := by
    simpa [prefixWord, tailWord_1875052, baseEnd_1875052] using wordTrace_append hprefix tailTrace_1875052
  have hstable : (prefixWord ++ tailWord_1875052).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1875052).length < 2 ^ (prefixWord ++ tailWord_1875052).sum := by decide
  have hdescent : baseEnd_1875052 < baseStart_1875052 := by decide
  rcases family_descends (prefixWord ++ tailWord_1875052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1875101 : List Nat := [1, 4, 2, 1, 1, 2, 5, 1, 5]
def baseStart_1875101 : Nat := 118140960795 + 1875101 * 2 ^ 59
def prefixEnd_1875101 : Nat := 4983230072969 + 3 ^ 40 * 1875101 * 2
def baseEnd_1875101 : Nat := 213961797494749642758683

theorem tailTrace_1875101 : CollatzResearch.WordTrace tailWord_1875101 prefixEnd_1875101 213961797494749642758683 := by
  unfold tailWord_1875101
  simp only [CollatzResearch.WordTrace]
  refine ⟨68390551979836793600161157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45593701319891195733440771 68390551979836793600161157)
  ·
    refine ⟨12823228496219398800030217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 68390551979836793600161157 12823228496219398800030217)
    ·
      refine ⟨9617421372164549100022663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12823228496219398800030217 9617421372164549100022663)
      ·
        refine ⟨14426132058246823650033995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9617421372164549100022663 14426132058246823650033995)
        ·
          refine ⟨21639198087370235475050993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14426132058246823650033995 21639198087370235475050993)
          ·
            refine ⟨16229398565527676606288245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21639198087370235475050993 16229398565527676606288245)
            ·
              refine ⟨1521506115518219681839523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16229398565527676606288245 1521506115518219681839523)
              ·
                refine ⟨2282259173277329522759285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1521506115518219681839523 2282259173277329522759285)
                ·
                  refine ⟨213961797494749642758683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2282259173277329522759285 213961797494749642758683)
                  ·
                    rfl

theorem cell22_1875101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 5, 1, 5].length) (baseStart_1875101 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1875101 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1875101 prefixEnd_1875101 := by exact prefixLift 1875101
  have htrace : WordTrace (prefixWord ++ tailWord_1875101) baseStart_1875101 baseEnd_1875101 := by
    simpa [prefixWord, tailWord_1875101, baseEnd_1875101] using wordTrace_append hprefix tailTrace_1875101
  have hstable : (prefixWord ++ tailWord_1875101).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1875101).length < 2 ^ (prefixWord ++ tailWord_1875101).sum := by decide
  have hdescent : baseEnd_1875101 < baseStart_1875101 := by decide
  rcases family_descends (prefixWord ++ tailWord_1875101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1875146 : List Nat := [3, 1, 2, 1, 3, 4, 1, 1, 6]
def baseStart_1875146 : Nat := 118140960795 + 1875146 * 2 ^ 59
def prefixEnd_1875146 : Nat := 4983230072969 + 3 ^ 40 * 1875146 * 2
def baseEnd_1875146 : Nat := 213966932301294603633637

theorem tailTrace_1875146 : CollatzResearch.WordTrace tailWord_1875146 prefixEnd_1875146 213966932301294603633637 := by
  unfold tailWord_1875146
  simp only [CollatzResearch.WordTrace]
  refine ⟨17098048316168441571387323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45594795509782510857032861 17098048316168441571387323)
  ·
    refine ⟨25647072474252662357080985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17098048316168441571387323 25647072474252662357080985)
    ·
      refine ⟨19235304355689496767810739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25647072474252662357080985 19235304355689496767810739)
      ·
        refine ⟨28852956533534245151716109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19235304355689496767810739 28852956533534245151716109)
        ·
          refine ⟨10819858700075341931893541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28852956533534245151716109 10819858700075341931893541)
          ·
            refine ⟨2028723506264126612230039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10819858700075341931893541 2028723506264126612230039)
            ·
              refine ⟨3043085259396189918345059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2028723506264126612230039 3043085259396189918345059)
              ·
                refine ⟨4564627889094284877517589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3043085259396189918345059 4564627889094284877517589)
                ·
                  refine ⟨213966932301294603633637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4564627889094284877517589 213966932301294603633637)
                  ·
                    rfl

theorem cell22_1875146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 4, 1, 1, 6].length) (baseStart_1875146 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1875146 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1875146 prefixEnd_1875146 := by exact prefixLift 1875146
  have htrace : WordTrace (prefixWord ++ tailWord_1875146) baseStart_1875146 baseEnd_1875146 := by
    simpa [prefixWord, tailWord_1875146, baseEnd_1875146] using wordTrace_append hprefix tailTrace_1875146
  have hstable : (prefixWord ++ tailWord_1875146).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1875146).length < 2 ^ (prefixWord ++ tailWord_1875146).sum := by decide
  have hdescent : baseEnd_1875146 < baseStart_1875146 := by decide
  rcases family_descends (prefixWord ++ tailWord_1875146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1875165 : List Nat := [1, 4, 3, 2, 2, 2, 1, 2, 1, 4]
def baseStart_1875165 : Nat := 118140960795 + 1875165 * 2 ^ 59
def prefixEnd_1875165 : Nat := 4983230072969 + 3 ^ 40 * 1875165 * 2
def baseEnd_1875165 : Nat := 641907300992174094675853

theorem tailTrace_1875165 : CollatzResearch.WordTrace tailWord_1875165 prefixEnd_1875165 641907300992174094675853 := by
  unfold tailWord_1875165
  simp only [CollatzResearch.WordTrace]
  refine ⟨68392886251604932530490949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45595257501069955020327299 68392886251604932530490949)
  ·
    refine ⟨12823666172175924849467053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 68392886251604932530490949 12823666172175924849467053)
    ·
      refine ⟨4808874814565971818550145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12823666172175924849467053 4808874814565971818550145)
      ·
        refine ⟨3606656110924478863912609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4808874814565971818550145 3606656110924478863912609)
        ·
          refine ⟨2704992083193359147934457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3606656110924478863912609 2704992083193359147934457)
          ·
            refine ⟨2028744062395019360950843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2704992083193359147934457 2028744062395019360950843)
            ·
              refine ⟨3043116093592529041426265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2028744062395019360950843 3043116093592529041426265)
              ·
                refine ⟨2282337070194396781069699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3043116093592529041426265 2282337070194396781069699)
                ·
                  refine ⟨3423505605291595171604549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2282337070194396781069699 3423505605291595171604549)
                  ·
                    refine ⟨641907300992174094675853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3423505605291595171604549 641907300992174094675853)
                    ·
                      rfl

theorem cell22_1875165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 2, 1, 2, 1, 4].length) (baseStart_1875165 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1875165 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1875165 prefixEnd_1875165 := by exact prefixLift 1875165
  have htrace : WordTrace (prefixWord ++ tailWord_1875165) baseStart_1875165 baseEnd_1875165 := by
    simpa [prefixWord, tailWord_1875165, baseEnd_1875165] using wordTrace_append hprefix tailTrace_1875165
  have hstable : (prefixWord ++ tailWord_1875165).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1875165).length < 2 ^ (prefixWord ++ tailWord_1875165).sum := by decide
  have hdescent : baseEnd_1875165 < baseStart_1875165 := by decide
  rcases family_descends (prefixWord ++ tailWord_1875165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1875176 : List Nat := [2, 1, 4, 1, 2, 1, 4, 1, 2, 4]
def baseStart_1875176 : Nat := 118140960795 + 1875176 * 2 ^ 59
def prefixEnd_1875176 : Nat := 4983230072969 + 3 ^ 40 * 1875176 * 2
def baseEnd_1875176 : Nat := 641911066516973732650819

theorem tailTrace_1875176 : CollatzResearch.WordTrace tailWord_1875176 prefixEnd_1875176 641911066516973732650819 := by
  unfold tailWord_1875176
  simp only [CollatzResearch.WordTrace]
  refine ⟨34196643727282540704570691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45595524969710054272760921 34196643727282540704570691)
  ·
    refine ⟨51294965590923811056856037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34196643727282540704570691 51294965590923811056856037)
    ·
      refine ⟨9617806048298214573160507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51294965590923811056856037 9617806048298214573160507)
      ·
        refine ⟨14426709072447321859740761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9617806048298214573160507 14426709072447321859740761)
        ·
          refine ⟨10820031804335491394805571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14426709072447321859740761 10820031804335491394805571)
          ·
            refine ⟨16230047706503237092208357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10820031804335491394805571 16230047706503237092208357)
            ·
              refine ⟨3043133944969356954789067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16230047706503237092208357 3043133944969356954789067)
              ·
                refine ⟨4564700917454035432183601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3043133944969356954789067 4564700917454035432183601)
                ·
                  refine ⟨3423525688090526574137701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4564700917454035432183601 3423525688090526574137701)
                  ·
                    refine ⟨641911066516973732650819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3423525688090526574137701 641911066516973732650819)
                    ·
                      rfl

theorem cell22_1875176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 4, 1, 2, 4].length) (baseStart_1875176 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1875176 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1875176 prefixEnd_1875176 := by exact prefixLift 1875176
  have htrace : WordTrace (prefixWord ++ tailWord_1875176) baseStart_1875176 baseEnd_1875176 := by
    simpa [prefixWord, tailWord_1875176, baseEnd_1875176] using wordTrace_append hprefix tailTrace_1875176
  have hstable : (prefixWord ++ tailWord_1875176).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1875176).length < 2 ^ (prefixWord ++ tailWord_1875176).sum := by decide
  have hdescent : baseEnd_1875176 < baseStart_1875176 := by decide
  rcases family_descends (prefixWord ++ tailWord_1875176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1875208 : List Nat := [2, 1, 3, 2, 5, 1, 1, 7]
def baseStart_1875208 : Nat := 118140960795 + 1875208 * 2 ^ 59
def prefixEnd_1875208 : Nat := 4983230072969 + 3 ^ 40 * 1875208 * 2
def baseEnd_1875208 : Nat := 71324668974548479538969

theorem tailTrace_1875208 : CollatzResearch.WordTrace tailWord_1875208 prefixEnd_1875208 71324668974548479538969 := by
  unfold tailWord_1875208
  simp only [CollatzResearch.WordTrace]
  refine ⟨34197227295224575437153139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45596303060299433916204185 34197227295224575437153139)
  ·
    refine ⟨51295840942836863155729709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34197227295224575437153139 51295840942836863155729709)
    ·
      refine ⟨19235940353563823683398641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51295840942836863155729709 19235940353563823683398641)
      ·
        refine ⟨14426955265172867762548981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19235940353563823683398641 14426955265172867762548981)
        ·
          refine ⟨1352527056109956352738967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14426955265172867762548981 1352527056109956352738967)
          ·
            refine ⟨2028790584164934529108451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1352527056109956352738967 2028790584164934529108451)
            ·
              refine ⟨3043185876247401793662677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2028790584164934529108451 3043185876247401793662677)
              ·
                refine ⟨71324668974548479538969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3043185876247401793662677 71324668974548479538969)
                ·
                  rfl

theorem cell22_1875208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 5, 1, 1, 7].length) (baseStart_1875208 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1875208 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1875208 prefixEnd_1875208 := by exact prefixLift 1875208
  have htrace : WordTrace (prefixWord ++ tailWord_1875208) baseStart_1875208 baseEnd_1875208 := by
    simpa [prefixWord, tailWord_1875208, baseEnd_1875208] using wordTrace_append hprefix tailTrace_1875208
  have hstable : (prefixWord ++ tailWord_1875208).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1875208).length < 2 ^ (prefixWord ++ tailWord_1875208).sum := by decide
  have hdescent : baseEnd_1875208 < baseStart_1875208 := by decide
  rcases family_descends (prefixWord ++ tailWord_1875208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1875240 : List Nat := [2, 1, 5, 1, 2, 1, 1, 5, 1, 3]
def baseStart_1875240 : Nat := 118140960795 + 1875240 * 2 ^ 59
def prefixEnd_1875240 : Nat := 4983230072969 + 3 ^ 40 * 1875240 * 2
def baseEnd_1875240 : Nat := 641932975024898899050623

theorem tailTrace_1875240 : CollatzResearch.WordTrace tailWord_1875240 prefixEnd_1875240 641932975024898899050623 := by
  unfold tailWord_1875240
  simp only [CollatzResearch.WordTrace]
  refine ⟨34197810863166610169735587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45597081150888813559647449 34197810863166610169735587)
  ·
    refine ⟨51296716294749915254603381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34197810863166610169735587 51296716294749915254603381)
    ·
      refine ⟨4809067152632804555119067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 51296716294749915254603381 4809067152632804555119067)
      ·
        refine ⟨7213600728949206832678601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4809067152632804555119067 7213600728949206832678601)
        ·
          refine ⟨5410200546711905124508951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7213600728949206832678601 5410200546711905124508951)
          ·
            refine ⟨8115300820067857686763427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5410200546711905124508951 8115300820067857686763427)
            ·
              refine ⟨12172951230101786530145141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8115300820067857686763427 12172951230101786530145141)
              ·
                refine ⟨1141214177822042487201107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12172951230101786530145141 1141214177822042487201107)
                ·
                  refine ⟨1711821266733063730801661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1141214177822042487201107 1711821266733063730801661)
                  ·
                    refine ⟨641932975024898899050623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1711821266733063730801661 641932975024898899050623)
                    ·
                      rfl

theorem cell22_1875240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 5, 1, 3].length) (baseStart_1875240 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1875240 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1875240 prefixEnd_1875240 := by exact prefixLift 1875240
  have htrace : WordTrace (prefixWord ++ tailWord_1875240) baseStart_1875240 baseEnd_1875240 := by
    simpa [prefixWord, tailWord_1875240, baseEnd_1875240] using wordTrace_append hprefix tailTrace_1875240
  have hstable : (prefixWord ++ tailWord_1875240).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1875240).length < 2 ^ (prefixWord ++ tailWord_1875240).sum := by decide
  have hdescent : baseEnd_1875240 < baseStart_1875240 := by decide
  rcases family_descends (prefixWord ++ tailWord_1875240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1875253 : List Nat := [1, 3, 3, 1, 2, 4, 1, 2, 5]
def baseStart_1875253 : Nat := 118140960795 + 1875253 * 2 ^ 59
def prefixEnd_1875253 : Nat := 4983230072969 + 3 ^ 40 * 1875253 * 2
def baseEnd_1875253 : Nat := 213979141730190399491861

theorem tailTrace_1875253 : CollatzResearch.WordTrace tailWord_1875253 prefixEnd_1875253 213979141730190399491861 := by
  unfold tailWord_1875253
  simp only [CollatzResearch.WordTrace]
  refine ⟨68396095875286123559694413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45597397250190749039796275 68396095875286123559694413)
  ·
    refine ⟨25648535953232296334885405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68396095875286123559694413 25648535953232296334885405)
    ·
      refine ⟨9618200982462111125582027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25648535953232296334885405 9618200982462111125582027)
      ·
        refine ⟨14427301473693166688373041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9618200982462111125582027 14427301473693166688373041)
        ·
          refine ⟨10820476105269875016279781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14427301473693166688373041 10820476105269875016279781)
          ·
            refine ⟨2028839269738101565552459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10820476105269875016279781 2028839269738101565552459)
            ·
              refine ⟨3043258904607152348328689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2028839269738101565552459 3043258904607152348328689)
              ·
                refine ⟨2282444178455364261246517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3043258904607152348328689 2282444178455364261246517)
                ·
                  refine ⟨213979141730190399491861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2282444178455364261246517 213979141730190399491861)
                  ·
                    rfl

theorem cell22_1875253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 4, 1, 2, 5].length) (baseStart_1875253 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1875253 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1875253 prefixEnd_1875253 := by exact prefixLift 1875253
  have htrace : WordTrace (prefixWord ++ tailWord_1875253) baseStart_1875253 baseEnd_1875253 := by
    simpa [prefixWord, tailWord_1875253, baseEnd_1875253] using wordTrace_append hprefix tailTrace_1875253
  have hstable : (prefixWord ++ tailWord_1875253).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1875253).length < 2 ^ (prefixWord ++ tailWord_1875253).sum := by decide
  have hdescent : baseEnd_1875253 < baseStart_1875253 := by decide
  rcases family_descends (prefixWord ++ tailWord_1875253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1875268 : List Nat := [2, 3, 4, 1, 1, 1, 2, 1, 2, 5]
def baseStart_1875268 : Nat := 118140960795 + 1875268 * 2 ^ 59
def prefixEnd_1875268 : Nat := 4983230072969 + 3 ^ 40 * 1875268 * 2
def baseEnd_1875268 : Nat := 641942559997116159350537

theorem tailTrace_1875268 : CollatzResearch.WordTrace tailWord_1875268 prefixEnd_1875268 641942559997116159350537 := by
  unfold tailWord_1875268
  simp only [CollatzResearch.WordTrace]
  refine ⟨34198321485115890560745229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45597761980154520747660305 34198321485115890560745229)
  ·
    refine ⟨12824370556918458960279461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34198321485115890560745229 12824370556918458960279461)
    ·
      refine ⟨2404569479422211055052399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12824370556918458960279461 2404569479422211055052399)
      ·
        refine ⟨3606854219133316582578599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2404569479422211055052399 3606854219133316582578599)
        ·
          refine ⟨5410281328699974873867899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3606854219133316582578599 5410281328699974873867899)
          ·
            refine ⟨8115421993049962310801849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5410281328699974873867899 8115421993049962310801849)
            ·
              refine ⟨6086566494787471733101387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8115421993049962310801849 6086566494787471733101387)
              ·
                refine ⟨9129849742181207599652081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6086566494787471733101387 9129849742181207599652081)
                ·
                  refine ⟨6847387306635905699739061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9129849742181207599652081 6847387306635905699739061)
                  ·
                    refine ⟨641942559997116159350537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6847387306635905699739061 641942559997116159350537)
                    ·
                      rfl

theorem cell22_1875268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 2, 1, 2, 5].length) (baseStart_1875268 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1875268 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1875268 prefixEnd_1875268 := by exact prefixLift 1875268
  have htrace : WordTrace (prefixWord ++ tailWord_1875268) baseStart_1875268 baseEnd_1875268 := by
    simpa [prefixWord, tailWord_1875268, baseEnd_1875268] using wordTrace_append hprefix tailTrace_1875268
  have hstable : (prefixWord ++ tailWord_1875268).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1875268).length < 2 ^ (prefixWord ++ tailWord_1875268).sum := by decide
  have hdescent : baseEnd_1875268 < baseStart_1875268 := by decide
  rcases family_descends (prefixWord ++ tailWord_1875268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1875311 : List Nat := [1, 1, 2, 1, 3, 1, 5, 2, 2, 4]
def baseStart_1875311 : Nat := 118140960795 + 1875311 * 2 ^ 59
def prefixEnd_1875311 : Nat := 4983230072969 + 3 ^ 40 * 1875311 * 2
def baseEnd_1875311 : Nat := 641957279775878380525405

theorem tailTrace_1875311 : CollatzResearch.WordTrace tailWord_1875311 prefixEnd_1875311 641957279775878380525405 := by
  unfold tailWord_1875311
  simp only [CollatzResearch.WordTrace]
  refine ⟨68398211309075999465305787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45598807539383999643537191 68398211309075999465305787)
  ·
    refine ⟨102597316963613999197958681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68398211309075999465305787 102597316963613999197958681)
    ·
      refine ⟨76947987722710499398469011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102597316963613999197958681 76947987722710499398469011)
      ·
        refine ⟨115421981584065749097703517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76947987722710499398469011 115421981584065749097703517)
        ·
          refine ⟨43283243094024655911638819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 115421981584065749097703517 43283243094024655911638819)
          ·
            refine ⟨64924864641036983867458229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43283243094024655911638819 64924864641036983867458229)
            ·
              refine ⟨6086706060097217237574209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 64924864641036983867458229 6086706060097217237574209)
              ·
                refine ⟨4565029545072912928180657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6086706060097217237574209 4565029545072912928180657)
                ·
                  refine ⟨3423772158804684696135493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4565029545072912928180657 3423772158804684696135493)
                  ·
                    refine ⟨641957279775878380525405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3423772158804684696135493 641957279775878380525405)
                    ·
                      rfl

theorem cell22_1875311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 5, 2, 2, 4].length) (baseStart_1875311 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1875311 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1875311 prefixEnd_1875311 := by exact prefixLift 1875311
  have htrace : WordTrace (prefixWord ++ tailWord_1875311) baseStart_1875311 baseEnd_1875311 := by
    simpa [prefixWord, tailWord_1875311, baseEnd_1875311] using wordTrace_append hprefix tailTrace_1875311
  have hstable : (prefixWord ++ tailWord_1875311).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1875311).length < 2 ^ (prefixWord ++ tailWord_1875311).sum := by decide
  have hdescent : baseEnd_1875311 < baseStart_1875311 := by decide
  rcases family_descends (prefixWord ++ tailWord_1875311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1875373 : List Nat := [1, 5, 2, 2, 1, 1, 1, 1, 2, 6]
def baseStart_1875373 : Nat := 118140960795 + 1875373 * 2 ^ 59
def prefixEnd_1875373 : Nat := 4983230072969 + 3 ^ 40 * 1875373 * 2
def baseEnd_1875373 : Nat := 641978503642930885475215

theorem tailTrace_1875373 : CollatzResearch.WordTrace tailWord_1875373 prefixEnd_1875373 641978503642930885475215 := by
  unfold tailWord_1875373
  simp only [CollatzResearch.WordTrace]
  refine ⟨68400472634851384054062773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45600315089900922702708515 68400472634851384054062773)
  ·
    refine ⟨6412544309517317255068385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 68400472634851384054062773 6412544309517317255068385)
    ·
      refine ⟨4809408232137987941301289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6412544309517317255068385 4809408232137987941301289)
      ·
        refine ⟨3607056174103490955975967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4809408232137987941301289 3607056174103490955975967)
        ·
          refine ⟨5410584261155236433963951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3607056174103490955975967 5410584261155236433963951)
          ·
            refine ⟨8115876391732854650945927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5410584261155236433963951 8115876391732854650945927)
            ·
              refine ⟨12173814587599281976418891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8115876391732854650945927 12173814587599281976418891)
              ·
                refine ⟨18260721881398922964628337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12173814587599281976418891 18260721881398922964628337)
                ·
                  refine ⟨13695541411049192223471253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18260721881398922964628337 13695541411049192223471253)
                  ·
                    refine ⟨641978503642930885475215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13695541411049192223471253 641978503642930885475215)
                    ·
                      rfl

theorem cell22_1875373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 1, 2, 6].length) (baseStart_1875373 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1875373 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1875373 prefixEnd_1875373 := by exact prefixLift 1875373
  have htrace : WordTrace (prefixWord ++ tailWord_1875373) baseStart_1875373 baseEnd_1875373 := by
    simpa [prefixWord, tailWord_1875373, baseEnd_1875373] using wordTrace_append hprefix tailTrace_1875373
  have hstable : (prefixWord ++ tailWord_1875373).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1875373).length < 2 ^ (prefixWord ++ tailWord_1875373).sum := by decide
  have hdescent : baseEnd_1875373 < baseStart_1875373 := by decide
  rcases family_descends (prefixWord ++ tailWord_1875373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1875448 : List Nat := [2, 1, 2, 1, 1, 5, 3, 1, 1, 5]
def baseStart_1875448 : Nat := 118140960795 + 1875448 * 2 ^ 59
def prefixEnd_1875448 : Nat := 4983230072969 + 3 ^ 40 * 1875448 * 2
def baseEnd_1875448 : Nat := 642004177675655689849985

theorem tailTrace_1875448 : CollatzResearch.WordTrace tailWord_1875448 prefixEnd_1875448 642004177675655689849985 := by
  unfold tailWord_1875448
  simp only [CollatzResearch.WordTrace]
  refine ⟨34201604054789835931521499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45602138739719781242028665 34201604054789835931521499)
  ·
    refine ⟨51302406082184753897282249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34201604054789835931521499 51302406082184753897282249)
    ·
      refine ⟨38476804561638565422961687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51302406082184753897282249 38476804561638565422961687)
      ·
        refine ⟨57715206842457848134442531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38476804561638565422961687 57715206842457848134442531)
        ·
          refine ⟨86572810263686772201663797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57715206842457848134442531 86572810263686772201663797)
          ·
            refine ⟨8116200962220634893905981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 86572810263686772201663797 8116200962220634893905981)
            ·
              refine ⟨3043575360832738085214743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8116200962220634893905981 3043575360832738085214743)
              ·
                refine ⟨4565363041249107127822115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3043575360832738085214743 4565363041249107127822115)
                ·
                  refine ⟨6848044561873660691733173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4565363041249107127822115 6848044561873660691733173)
                  ·
                    refine ⟨642004177675655689849985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6848044561873660691733173 642004177675655689849985)
                    ·
                      rfl

theorem cell22_1875448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 3, 1, 1, 5].length) (baseStart_1875448 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1875448 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1875448 prefixEnd_1875448 := by exact prefixLift 1875448
  have htrace : WordTrace (prefixWord ++ tailWord_1875448) baseStart_1875448 baseEnd_1875448 := by
    simpa [prefixWord, tailWord_1875448, baseEnd_1875448] using wordTrace_append hprefix tailTrace_1875448
  have hstable : (prefixWord ++ tailWord_1875448).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1875448).length < 2 ^ (prefixWord ++ tailWord_1875448).sum := by decide
  have hdescent : baseEnd_1875448 < baseStart_1875448 := by decide
  rcases family_descends (prefixWord ++ tailWord_1875448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1875463 : List Nat := [1, 1, 4, 3, 2, 1, 2, 1, 1, 6]
def baseStart_1875463 : Nat := 118140960795 + 1875463 * 2 ^ 59
def prefixEnd_1875463 : Nat := 4983230072969 + 3 ^ 40 * 1875463 * 2
def baseEnd_1875463 : Nat := 642009312482200650724939

theorem tailTrace_1875463 : CollatzResearch.WordTrace tailWord_1875463 prefixEnd_1875463 642009312482200650724939 := by
  unfold tailWord_1875463
  simp only [CollatzResearch.WordTrace]
  refine ⟨68403755204525329424839043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45602503469683552949892695 68403755204525329424839043)
  ·
    refine ⟨102605632806787994137258565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68403755204525329424839043 102605632806787994137258565)
    ·
      refine ⟨19238556151272748900735981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 102605632806787994137258565 19238556151272748900735981)
      ·
        refine ⟨7214458556727280837775993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19238556151272748900735981 7214458556727280837775993)
        ·
          refine ⟨5410843917545460628331995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7214458556727280837775993 5410843917545460628331995)
          ·
            refine ⟨8116265876318190942497993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5410843917545460628331995 8116265876318190942497993)
            ·
              refine ⟨6087199407238643206873495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8116265876318190942497993 6087199407238643206873495)
              ·
                refine ⟨9130799110857964810310243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6087199407238643206873495 9130799110857964810310243)
                ·
                  refine ⟨13696198666286947215465365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9130799110857964810310243 13696198666286947215465365)
                  ·
                    refine ⟨642009312482200650724939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13696198666286947215465365 642009312482200650724939)
                    ·
                      rfl

theorem cell22_1875463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 2, 1, 1, 6].length) (baseStart_1875463 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1875463 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1875463 prefixEnd_1875463 := by exact prefixLift 1875463
  have htrace : WordTrace (prefixWord ++ tailWord_1875463) baseStart_1875463 baseEnd_1875463 := by
    simpa [prefixWord, tailWord_1875463, baseEnd_1875463] using wordTrace_append hprefix tailTrace_1875463
  have hstable : (prefixWord ++ tailWord_1875463).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1875463).length < 2 ^ (prefixWord ++ tailWord_1875463).sum := by decide
  have hdescent : baseEnd_1875463 < baseStart_1875463 := by decide
  rcases family_descends (prefixWord ++ tailWord_1875463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1875467 : List Nat := [1, 1, 1, 1, 8, 2, 1, 3, 4]
def baseStart_1875467 : Nat := 118140960795 + 1875467 * 2 ^ 59
def prefixEnd_1875467 : Nat := 4983230072969 + 3 ^ 40 * 1875467 * 2
def baseEnd_1875467 : Nat := 214003560587981991208309

theorem tailTrace_1875467 : CollatzResearch.WordTrace tailWord_1875467 prefixEnd_1875467 214003560587981991208309 := by
  unfold tailWord_1875467
  simp only [CollatzResearch.WordTrace]
  refine ⟨68403901096510838107984655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45602600731007225405323103 68403901096510838107984655)
  ·
    refine ⟨102605851644766257161976983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68403901096510838107984655 102605851644766257161976983)
    ·
      refine ⟨153908777467149385742965475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102605851644766257161976983 153908777467149385742965475)
      ·
        refine ⟨230863166200724078614448213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153908777467149385742965475 230863166200724078614448213)
        ·
          refine ⟨2705427728914735296263065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 230863166200724078614448213 2705427728914735296263065)
          ·
            refine ⟨2029070796686051472197299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2705427728914735296263065 2029070796686051472197299)
            ·
              refine ⟨3043606195029077208295949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2029070796686051472197299 3043606195029077208295949)
              ·
                refine ⟨1141352323135903953110981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3043606195029077208295949 1141352323135903953110981)
                ·
                  refine ⟨214003560587981991208309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1141352323135903953110981 214003560587981991208309)
                  ·
                    rfl

theorem cell22_1875467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 2, 1, 3, 4].length) (baseStart_1875467 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1875467 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1875467 prefixEnd_1875467 := by exact prefixLift 1875467
  have htrace : WordTrace (prefixWord ++ tailWord_1875467) baseStart_1875467 baseEnd_1875467 := by
    simpa [prefixWord, tailWord_1875467, baseEnd_1875467] using wordTrace_append hprefix tailTrace_1875467
  have hstable : (prefixWord ++ tailWord_1875467).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1875467).length < 2 ^ (prefixWord ++ tailWord_1875467).sum := by decide
  have hdescent : baseEnd_1875467 < baseStart_1875467 := by decide
  rcases family_descends (prefixWord ++ tailWord_1875467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1875480 : List Nat := [2, 1, 2, 3, 4, 1, 1, 2, 2, 4]
def baseStart_1875480 : Nat := 118140960795 + 1875480 * 2 ^ 59
def prefixEnd_1875480 : Nat := 4983230072969 + 3 ^ 40 * 1875480 * 2
def baseEnd_1875480 : Nat := 642015131929618273049887

theorem tailTrace_1875480 : CollatzResearch.WordTrace tailWord_1875480 prefixEnd_1875480 642015131929618273049887 := by
  unfold tailWord_1875480
  simp only [CollatzResearch.WordTrace]
  refine ⟨34202187622731870664103947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45602916830309160885471929 34202187622731870664103947)
  ·
    refine ⟨51303281434097805996155921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34202187622731870664103947 51303281434097805996155921)
    ·
      refine ⟨38477461075573354497116941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51303281434097805996155921 38477461075573354497116941)
      ·
        refine ⟨14429047903340007936418853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38477461075573354497116941 14429047903340007936418853)
        ·
          refine ⟨2705446481876251488078535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14429047903340007936418853 2705446481876251488078535)
          ·
            refine ⟨4058169722814377232117803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2705446481876251488078535 4058169722814377232117803)
            ·
              refine ⟨6087254584221565848176705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4058169722814377232117803 6087254584221565848176705)
              ·
                refine ⟨4565440938166174386132529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6087254584221565848176705 4565440938166174386132529)
                ·
                  refine ⟨3424080703624630789599397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4565440938166174386132529 3424080703624630789599397)
                  ·
                    refine ⟨642015131929618273049887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3424080703624630789599397 642015131929618273049887)
                    ·
                      rfl

theorem cell22_1875480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 1, 2, 2, 4].length) (baseStart_1875480 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1875480 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1875480 prefixEnd_1875480 := by exact prefixLift 1875480
  have htrace : WordTrace (prefixWord ++ tailWord_1875480) baseStart_1875480 baseEnd_1875480 := by
    simpa [prefixWord, tailWord_1875480, baseEnd_1875480] using wordTrace_append hprefix tailTrace_1875480
  have hstable : (prefixWord ++ tailWord_1875480).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1875480).length < 2 ^ (prefixWord ++ tailWord_1875480).sum := by decide
  have hdescent : baseEnd_1875480 < baseStart_1875480 := by decide
  rcases family_descends (prefixWord ++ tailWord_1875480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1875540 : List Nat := [2, 4, 1, 1, 1, 2, 4, 2, 5]
def baseStart_1875540 : Nat := 118140960795 + 1875540 * 2 ^ 59
def prefixEnd_1875540 : Nat := 4983230072969 + 3 ^ 40 * 1875540 * 2
def baseEnd_1875540 : Nat := 214011890385266038849901

theorem tailTrace_1875540 : CollatzResearch.WordTrace tailWord_1875540 prefixEnd_1875540 214011890385266038849901 := by
  unfold tailWord_1875540
  simp only [CollatzResearch.WordTrace]
  refine ⟨34203281812623185787696037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45604375750164247716928049 34203281812623185787696037)
  ·
    refine ⟨6413115339866847335193007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34203281812623185787696037 6413115339866847335193007)
    ·
      refine ⟨9619673009800271002789511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6413115339866847335193007 9619673009800271002789511)
      ·
        refine ⟨14429509514700406504184267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9619673009800271002789511 14429509514700406504184267)
        ·
          refine ⟨21644264272050609756276401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14429509514700406504184267 21644264272050609756276401)
          ·
            refine ⟨16233198204037957317207301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21644264272050609756276401 16233198204037957317207301)
            ·
              refine ⟨3043724663257116996976369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16233198204037957317207301 3043724663257116996976369)
              ·
                refine ⟨2282793497442837747732277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3043724663257116996976369 2282793497442837747732277)
                ·
                  refine ⟨214011890385266038849901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2282793497442837747732277 214011890385266038849901)
                  ·
                    rfl

theorem cell22_1875540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 4, 2, 5].length) (baseStart_1875540 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1875540 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1875540 prefixEnd_1875540 := by exact prefixLift 1875540
  have htrace : WordTrace (prefixWord ++ tailWord_1875540) baseStart_1875540 baseEnd_1875540 := by
    simpa [prefixWord, tailWord_1875540, baseEnd_1875540] using wordTrace_append hprefix tailTrace_1875540
  have hstable : (prefixWord ++ tailWord_1875540).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1875540).length < 2 ^ (prefixWord ++ tailWord_1875540).sum := by decide
  have hdescent : baseEnd_1875540 < baseStart_1875540 := by decide
  rcases family_descends (prefixWord ++ tailWord_1875540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1875553 : List Nat := [1, 2, 3, 1, 1, 3, 1, 1, 5, 4]
def baseStart_1875553 : Nat := 118140960795 + 1875553 * 2 ^ 59
def prefixEnd_1875553 : Nat := 4983230072969 + 3 ^ 40 * 1875553 * 2
def baseEnd_1875553 : Nat := 642040121321470415974663

theorem tailTrace_1875553 : CollatzResearch.WordTrace tailWord_1875553 prefixEnd_1875553 642040121321470415974663 := by
  unfold tailWord_1875553
  simp only [CollatzResearch.WordTrace]
  refine ⟨68407037774199274795615313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45604691849466183197076875 68407037774199274795615313)
  ·
    refine ⟨51305278330649456096711485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68407037774199274795615313 51305278330649456096711485)
    ·
      refine ⟨19239479373993546036266807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51305278330649456096711485 19239479373993546036266807)
      ·
        refine ⟨28859219060990319054400211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19239479373993546036266807 28859219060990319054400211)
        ·
          refine ⟨43288828591485478581600317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28859219060990319054400211 43288828591485478581600317)
          ·
            refine ⟨16233310721807054468100119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43288828591485478581600317 16233310721807054468100119)
            ·
              refine ⟨24349966082710581702150179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16233310721807054468100119 24349966082710581702150179)
              ·
                refine ⟨36524949124065872553225269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24349966082710581702150179 36524949124065872553225269)
                ·
                  refine ⟨3424213980381175551864869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 36524949124065872553225269 3424213980381175551864869)
                  ·
                    refine ⟨642040121321470415974663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3424213980381175551864869 642040121321470415974663)
                    ·
                      rfl

theorem cell22_1875553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 1, 5, 4].length) (baseStart_1875553 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1875553 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1875553 prefixEnd_1875553 := by exact prefixLift 1875553
  have htrace : WordTrace (prefixWord ++ tailWord_1875553) baseStart_1875553 baseEnd_1875553 := by
    simpa [prefixWord, tailWord_1875553, baseEnd_1875553] using wordTrace_append hprefix tailTrace_1875553
  have hstable : (prefixWord ++ tailWord_1875553).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1875553).length < 2 ^ (prefixWord ++ tailWord_1875553).sum := by decide
  have hdescent : baseEnd_1875553 < baseStart_1875553 := by decide
  rcases family_descends (prefixWord ++ tailWord_1875553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1875568 : List Nat := [2, 1, 1, 1, 6, 1, 1, 1, 8]
def baseStart_1875568 : Nat := 118140960795 + 1875568 * 2 ^ 59
def prefixEnd_1875568 : Nat := 4983230072969 + 3 ^ 40 * 1875568 * 2
def baseEnd_1875568 : Nat := 214015085376005125616539

theorem tailTrace_1875568 : CollatzResearch.WordTrace tailWord_1875568 prefixEnd_1875568 214015085376005125616539 := by
  unfold tailWord_1875568
  simp only [CollatzResearch.WordTrace]
  refine ⟨34203792434572466178705679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45605056579429954904940905 34203792434572466178705679)
  ·
    refine ⟨51305688651858699268058519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34203792434572466178705679 51305688651858699268058519)
    ·
      refine ⟨76958532977788048902087779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51305688651858699268058519 76958532977788048902087779)
      ·
        refine ⟨115437799466682073353131669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76958532977788048902087779 115437799466682073353131669)
        ·
          refine ⟨5411146850000722188428047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 115437799466682073353131669 5411146850000722188428047)
          ·
            refine ⟨8116720275001083282642071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5411146850000722188428047 8116720275001083282642071)
            ·
              refine ⟨12175080412501624923963107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8116720275001083282642071 12175080412501624923963107)
              ·
                refine ⟨18262620618752437385944661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12175080412501624923963107 18262620618752437385944661)
                ·
                  refine ⟨214015085376005125616539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 18262620618752437385944661 214015085376005125616539)
                  ·
                    rfl

theorem cell22_1875568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 1, 8].length) (baseStart_1875568 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1875568 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1875568 prefixEnd_1875568 := by exact prefixLift 1875568
  have htrace : WordTrace (prefixWord ++ tailWord_1875568) baseStart_1875568 baseEnd_1875568 := by
    simpa [prefixWord, tailWord_1875568, baseEnd_1875568] using wordTrace_append hprefix tailTrace_1875568
  have hstable : (prefixWord ++ tailWord_1875568).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1875568).length < 2 ^ (prefixWord ++ tailWord_1875568).sum := by decide
  have hdescent : baseEnd_1875568 < baseStart_1875568 := by decide
  rcases family_descends (prefixWord ++ tailWord_1875568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1875570 : List Nat := [3, 2, 1, 2, 3, 1, 2, 1, 3, 4]
def baseStart_1875570 : Nat := 118140960795 + 1875570 * 2 ^ 59
def prefixEnd_1875570 : Nat := 4983230072969 + 3 ^ 40 * 1875570 * 2
def baseEnd_1875570 : Nat := 642045940768888038299611

theorem tailTrace_1875570 : CollatzResearch.WordTrace tailWord_1875570 prefixEnd_1875570 642045940768888038299611 := by
  unfold tailWord_1875570
  simp only [CollatzResearch.WordTrace]
  refine ⟨17101914453784421674746041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45605105210091791132656109 17101914453784421674746041)
  ·
    refine ⟨12826435840338316256059531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17101914453784421674746041 12826435840338316256059531)
    ·
      refine ⟨19239653760507474384089297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12826435840338316256059531 19239653760507474384089297)
      ·
        refine ⟨14429740320380605788066973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19239653760507474384089297 14429740320380605788066973)
        ·
          refine ⟨5411152620142727170525115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14429740320380605788066973 5411152620142727170525115)
          ·
            refine ⟨8116728930214090755787673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5411152620142727170525115 8116728930214090755787673)
            ·
              refine ⟨6087546697660568066840755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8116728930214090755787673 6087546697660568066840755)
              ·
                refine ⟨9131320046490852100261133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6087546697660568066840755 9131320046490852100261133)
                ·
                  refine ⟨3424245017434069537597925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9131320046490852100261133 3424245017434069537597925)
                  ·
                    refine ⟨642045940768888038299611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3424245017434069537597925 642045940768888038299611)
                    ·
                      rfl

theorem cell22_1875570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 2, 1, 3, 4].length) (baseStart_1875570 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1875570 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1875570 prefixEnd_1875570 := by exact prefixLift 1875570
  have htrace : WordTrace (prefixWord ++ tailWord_1875570) baseStart_1875570 baseEnd_1875570 := by
    simpa [prefixWord, tailWord_1875570, baseEnd_1875570] using wordTrace_append hprefix tailTrace_1875570
  have hstable : (prefixWord ++ tailWord_1875570).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1875570).length < 2 ^ (prefixWord ++ tailWord_1875570).sum := by decide
  have hdescent : baseEnd_1875570 < baseStart_1875570 := by decide
  rcases family_descends (prefixWord ++ tailWord_1875570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1875602 : List Nat := [3, 2, 3, 1, 3, 1, 2, 1, 6]
def baseStart_1875602 : Nat := 118140960795 + 1875602 * 2 ^ 59
def prefixEnd_1875602 : Nat := 4983230072969 + 3 ^ 40 * 1875602 * 2
def baseEnd_1875602 : Nat := 214018965007616873833171

theorem tailTrace_1875602 : CollatzResearch.WordTrace tailWord_1875602 prefixEnd_1875602 214018965007616873833171 := by
  unfold tailWord_1875602
  simp only [CollatzResearch.WordTrace]
  refine ⟨17102206237755439041037265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45605883300681170776099373 17102206237755439041037265)
  ·
    refine ⟨12826654678316579280777949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17102206237755439041037265 12826654678316579280777949)
    ·
      refine ⟨4809995504368717230291731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12826654678316579280777949 4809995504368717230291731)
      ·
        refine ⟨7214993256553075845437597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4809995504368717230291731 7214993256553075845437597)
        ·
          refine ⟨2705622471207403442039099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7214993256553075845437597 2705622471207403442039099)
          ·
            refine ⟨4058433706811105163058649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2705622471207403442039099 4058433706811105163058649)
            ·
              refine ⟨3043825280108328872293987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4058433706811105163058649 3043825280108328872293987)
              ·
                refine ⟨4565737920162493308440981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3043825280108328872293987 4565737920162493308440981)
                ·
                  refine ⟨214018965007616873833171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4565737920162493308440981 214018965007616873833171)
                  ·
                    rfl

theorem cell22_1875602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 2, 1, 6].length) (baseStart_1875602 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1875602 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1875602 prefixEnd_1875602 := by exact prefixLift 1875602
  have htrace : WordTrace (prefixWord ++ tailWord_1875602) baseStart_1875602 baseEnd_1875602 := by
    simpa [prefixWord, tailWord_1875602, baseEnd_1875602] using wordTrace_append hprefix tailTrace_1875602
  have hstable : (prefixWord ++ tailWord_1875602).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1875602).length < 2 ^ (prefixWord ++ tailWord_1875602).sum := by decide
  have hdescent : baseEnd_1875602 < baseStart_1875602 := by decide
  rcases family_descends (prefixWord ++ tailWord_1875602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1875613 : List Nat := [1, 4, 2, 1, 1, 1, 1, 11]
def baseStart_1875613 : Nat := 118140960795 + 1875613 * 2 ^ 59
def prefixEnd_1875613 : Nat := 4983230072969 + 3 ^ 40 * 1875613 * 2
def baseEnd_1875613 : Nat := 71340073394183362163831

theorem tailTrace_1875613 : CollatzResearch.WordTrace tailWord_1875613 prefixEnd_1875613 71340073394183362163831 := by
  unfold tailWord_1875613
  simp only [CollatzResearch.WordTrace]
  refine ⟨68409226153981905042799493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45606150769321270028532995 68409226153981905042799493)
  ·
    refine ⟨12826729903871607195524905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 68409226153981905042799493 12826729903871607195524905)
    ·
      refine ⟨9620047427903705396643679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12826729903871607195524905 9620047427903705396643679)
      ·
        refine ⟨14430071141855558094965519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9620047427903705396643679 14430071141855558094965519)
        ·
          refine ⟨21645106712783337142448279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14430071141855558094965519 21645106712783337142448279)
          ·
            refine ⟨32467660069175005713672419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21645106712783337142448279 32467660069175005713672419)
            ·
              refine ⟨48701490103762508570508629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32467660069175005713672419 48701490103762508570508629)
              ·
                refine ⟨71340073394183362163831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 48701490103762508570508629 71340073394183362163831)
                ·
                  rfl

theorem cell22_1875613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 11].length) (baseStart_1875613 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1875613 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1875613 prefixEnd_1875613 := by exact prefixLift 1875613
  have htrace : WordTrace (prefixWord ++ tailWord_1875613) baseStart_1875613 baseEnd_1875613 := by
    simpa [prefixWord, tailWord_1875613, baseEnd_1875613] using wordTrace_append hprefix tailTrace_1875613
  have hstable : (prefixWord ++ tailWord_1875613).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1875613).length < 2 ^ (prefixWord ++ tailWord_1875613).sum := by decide
  have hdescent : baseEnd_1875613 < baseStart_1875613 := by decide
  rcases family_descends (prefixWord ++ tailWord_1875613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1875617 : List Nat := [1, 2, 3, 3, 2, 3, 1, 1, 1, 5]
def baseStart_1875617 : Nat := 118140960795 + 1875617 * 2 ^ 59
def prefixEnd_1875617 : Nat := 4983230072969 + 3 ^ 40 * 1875617 * 2
def baseEnd_1875617 : Nat := 642062029829395582374467

theorem tailTrace_1875617 : CollatzResearch.WordTrace tailWord_1875617 prefixEnd_1875617 642062029829395582374467 := by
  unfold tailWord_1875617
  simp only [CollatzResearch.WordTrace]
  refine ⟨68409372045967413725945105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45606248030644942483963403 68409372045967413725945105)
  ·
    refine ⟨51307029034475560294458829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68409372045967413725945105 51307029034475560294458829)
    ·
      refine ⟨19240135887928335110422061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51307029034475560294458829 19240135887928335110422061)
      ·
        refine ⟨7215050957973125666408273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19240135887928335110422061 7215050957973125666408273)
        ·
          refine ⟨5411288218479844249806205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7215050957973125666408273 5411288218479844249806205)
          ·
            refine ⟨2029233081929941593677327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5411288218479844249806205 2029233081929941593677327)
            ·
              refine ⟨3043849622894912390515991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2029233081929941593677327 3043849622894912390515991)
              ·
                refine ⟨4565774434342368585773987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3043849622894912390515991 4565774434342368585773987)
                ·
                  refine ⟨6848661651513552878660981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4565774434342368585773987 6848661651513552878660981)
                  ·
                    refine ⟨642062029829395582374467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6848661651513552878660981 642062029829395582374467)
                    ·
                      rfl

theorem cell22_1875617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 3, 1, 1, 1, 5].length) (baseStart_1875617 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1875617 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1875617 prefixEnd_1875617 := by exact prefixLift 1875617
  have htrace : WordTrace (prefixWord ++ tailWord_1875617) baseStart_1875617 baseEnd_1875617 := by
    simpa [prefixWord, tailWord_1875617, baseEnd_1875617] using wordTrace_append hprefix tailTrace_1875617
  have hstable : (prefixWord ++ tailWord_1875617).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1875617).length < 2 ^ (prefixWord ++ tailWord_1875617).sum := by decide
  have hdescent : baseEnd_1875617 < baseStart_1875617 := by decide
  rcases family_descends (prefixWord ++ tailWord_1875617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1875720 : List Nat := [2, 1, 3, 2, 2, 1, 2, 3, 6]
def baseStart_1875720 : Nat := 118140960795 + 1875720 * 2 ^ 59
def prefixEnd_1875720 : Nat := 4983230072969 + 3 ^ 40 * 1875720 * 2
def baseEnd_1875720 : Nat := 214032429611445882349717

theorem tailTrace_1875720 : CollatzResearch.WordTrace tailWord_1875720 prefixEnd_1875720 214032429611445882349717 := by
  unfold tailWord_1875720
  simp only [CollatzResearch.WordTrace]
  refine ⟨34206564382297131158472307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45608752509729508211296409 34206564382297131158472307)
  ·
    refine ⟨51309846573445696737708461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34206564382297131158472307 51309846573445696737708461)
    ·
      refine ⟨19241192465042136276640673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51309846573445696737708461 19241192465042136276640673)
      ·
        refine ⟨14430894348781602207480505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19241192465042136276640673 14430894348781602207480505)
        ·
          refine ⟨10823170761586201655610379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14430894348781602207480505 10823170761586201655610379)
          ·
            refine ⟨16234756142379302483415569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10823170761586201655610379 16234756142379302483415569)
            ·
              refine ⟨12176067106784476862561677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16234756142379302483415569 12176067106784476862561677)
              ·
                refine ⟨4566025165044178823460629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12176067106784476862561677 4566025165044178823460629)
                ·
                  refine ⟨214032429611445882349717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4566025165044178823460629 214032429611445882349717)
                  ·
                    rfl

theorem cell22_1875720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 3, 6].length) (baseStart_1875720 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1875720 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1875720 prefixEnd_1875720 := by exact prefixLift 1875720
  have htrace : WordTrace (prefixWord ++ tailWord_1875720) baseStart_1875720 baseEnd_1875720 := by
    simpa [prefixWord, tailWord_1875720, baseEnd_1875720] using wordTrace_append hprefix tailTrace_1875720
  have hstable : (prefixWord ++ tailWord_1875720).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1875720).length < 2 ^ (prefixWord ++ tailWord_1875720).sum := by decide
  have hdescent : baseEnd_1875720 < baseStart_1875720 := by decide
  rcases family_descends (prefixWord ++ tailWord_1875720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1875752 : List Nat := [2, 1, 5, 1, 1, 2, 2, 2, 1, 5]
def baseStart_1875752 : Nat := 118140960795 + 1875752 * 2 ^ 59
def prefixEnd_1875752 : Nat := 4983230072969 + 3 ^ 40 * 1875752 * 2
def baseEnd_1875752 : Nat := 642108243088300230249053

theorem tailTrace_1875752 : CollatzResearch.WordTrace tailWord_1875752 prefixEnd_1875752 642108243088300230249053 := by
  unfold tailWord_1875752
  simp only [CollatzResearch.WordTrace]
  refine ⟨34207147950239165891054755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45609530600318887854739673 34207147950239165891054755)
  ·
    refine ⟨51310721925358748836582133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34207147950239165891054755 51310721925358748836582133)
    ·
      refine ⟨4810380180502382703429575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 51310721925358748836582133 4810380180502382703429575)
      ·
        refine ⟨7215570270753574055144363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4810380180502382703429575 7215570270753574055144363)
        ·
          refine ⟨10823355406130361082716545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7215570270753574055144363 10823355406130361082716545)
          ·
            refine ⟨8117516554597770812037409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10823355406130361082716545 8117516554597770812037409)
            ·
              refine ⟨6088137415948328109028057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8117516554597770812037409 6088137415948328109028057)
              ·
                refine ⟨4566103061961246081771043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6088137415948328109028057 4566103061961246081771043)
                ·
                  refine ⟨6849154592941869122656565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4566103061961246081771043 6849154592941869122656565)
                  ·
                    refine ⟨642108243088300230249053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6849154592941869122656565 642108243088300230249053)
                    ·
                      rfl

theorem cell22_1875752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 2, 2, 1, 5].length) (baseStart_1875752 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1875752 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1875752 prefixEnd_1875752 := by exact prefixLift 1875752
  have htrace : WordTrace (prefixWord ++ tailWord_1875752) baseStart_1875752 baseEnd_1875752 := by
    simpa [prefixWord, tailWord_1875752, baseEnd_1875752] using wordTrace_append hprefix tailTrace_1875752
  have hstable : (prefixWord ++ tailWord_1875752).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1875752).length < 2 ^ (prefixWord ++ tailWord_1875752).sum := by decide
  have hdescent : baseEnd_1875752 < baseStart_1875752 := by decide
  rcases family_descends (prefixWord ++ tailWord_1875752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1875799 : List Nat := [1, 1, 3, 2, 5, 2, 2, 6]
def baseStart_1875799 : Nat := 118140960795 + 1875799 * 2 ^ 59
def prefixEnd_1875799 : Nat := 4983230072969 + 3 ^ 40 * 1875799 * 2
def baseEnd_1875799 : Nat := 71347148016534197147101

theorem tailTrace_1875799 : CollatzResearch.WordTrace tailWord_1875799 prefixEnd_1875799 71347148016534197147101 := by
  unfold tailWord_1875799
  simp only [CollatzResearch.WordTrace]
  refine ⟨68416010131308058809070451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45610673420872039206046967 68416010131308058809070451)
  ·
    refine ⟨102624015196962088213605677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68416010131308058809070451 102624015196962088213605677)
    ·
      refine ⟨38484005698860783080102129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102624015196962088213605677 38484005698860783080102129)
      ·
        refine ⟨28863004274145587310076597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38484005698860783080102129 28863004274145587310076597)
        ·
          refine ⟨2705906650701148810319681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 28863004274145587310076597 2705906650701148810319681)
          ·
            refine ⟨2029429988025861607739761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2705906650701148810319681 2029429988025861607739761)
            ·
              refine ⟨1522072491019396205804821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2029429988025861607739761 1522072491019396205804821)
              ·
                refine ⟨71347148016534197147101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1522072491019396205804821 71347148016534197147101)
                ·
                  rfl

theorem cell22_1875799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 2, 2, 6].length) (baseStart_1875799 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1875799 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1875799 prefixEnd_1875799 := by exact prefixLift 1875799
  have htrace : WordTrace (prefixWord ++ tailWord_1875799) baseStart_1875799 baseEnd_1875799 := by
    simpa [prefixWord, tailWord_1875799, baseEnd_1875799] using wordTrace_append hprefix tailTrace_1875799
  have hstable : (prefixWord ++ tailWord_1875799).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1875799).length < 2 ^ (prefixWord ++ tailWord_1875799).sum := by decide
  have hdescent : baseEnd_1875799 < baseStart_1875799 := by decide
  rcases family_descends (prefixWord ++ tailWord_1875799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1875844 : List Nat := [2, 3, 2, 1, 1, 1, 6, 1, 5]
def baseStart_1875844 : Nat := 118140960795 + 1875844 * 2 ^ 59
def prefixEnd_1875844 : Nat := 4983230072969 + 3 ^ 40 * 1875844 * 2
def baseEnd_1875844 : Nat := 214046578856147552316257

theorem tailTrace_1875844 : CollatzResearch.WordTrace tailWord_1875844 prefixEnd_1875844 214046578856147552316257 := by
  unfold tailWord_1875844
  simp only [CollatzResearch.WordTrace]
  refine ⟨34208825708072515747229293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45611767610763354329639057 34208825708072515747229293)
  ·
    refine ⟨12828309640527193405210985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34208825708072515747229293 12828309640527193405210985)
    ·
      refine ⟨9621232230395395053908239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12828309640527193405210985 9621232230395395053908239)
      ·
        refine ⟨14431848345593092580862359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9621232230395395053908239 14431848345593092580862359)
        ·
          refine ⟨21647772518389638871293539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14431848345593092580862359 21647772518389638871293539)
          ·
            refine ⟨32471658777584458306940309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21647772518389638871293539 32471658777584458306940309)
            ·
              refine ⟨1522109005199271483137827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 32471658777584458306940309 1522109005199271483137827)
              ·
                refine ⟨2283163507798907224706741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1522109005199271483137827 2283163507798907224706741)
                ·
                  refine ⟨214046578856147552316257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2283163507798907224706741 214046578856147552316257)
                  ·
                    rfl

theorem cell22_1875844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 6, 1, 5].length) (baseStart_1875844 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1875844 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1875844 prefixEnd_1875844 := by exact prefixLift 1875844
  have htrace : WordTrace (prefixWord ++ tailWord_1875844) baseStart_1875844 baseEnd_1875844 := by
    simpa [prefixWord, tailWord_1875844, baseEnd_1875844] using wordTrace_append hprefix tailTrace_1875844
  have hstable : (prefixWord ++ tailWord_1875844).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1875844).length < 2 ^ (prefixWord ++ tailWord_1875844).sum := by decide
  have hdescent : baseEnd_1875844 < baseStart_1875844 := by decide
  rcases family_descends (prefixWord ++ tailWord_1875844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1875904 : List Nat := [2, 1, 1, 2, 3, 2, 1, 5, 2, 3]
def baseStart_1875904 : Nat := 118140960795 + 1875904 * 2 ^ 59
def prefixEnd_1875904 : Nat := 4983230072969 + 3 ^ 40 * 1875904 * 2
def baseEnd_1875904 : Nat := 642160275794622500448587

theorem tailTrace_1875904 : CollatzResearch.WordTrace tailWord_1875904 prefixEnd_1875904 642160275794622500448587 := by
  unfold tailWord_1875904
  simp only [CollatzResearch.WordTrace]
  refine ⟨34209919897963830870821383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45613226530618441161095177 34209919897963830870821383)
  ·
    refine ⟨51314879846945746306232075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34209919897963830870821383 51314879846945746306232075)
    ·
      refine ⟨76972319770418619459348113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51314879846945746306232075 76972319770418619459348113)
      ·
        refine ⟨57729239827813964594511085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76972319770418619459348113 57729239827813964594511085)
        ·
          refine ⟨21648464935430236722941657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57729239827813964594511085 21648464935430236722941657)
          ·
            refine ⟨16236348701572677542206243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21648464935430236722941657 16236348701572677542206243)
            ·
              refine ⟨24354523052359016313309365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16236348701572677542206243 24354523052359016313309365)
              ·
                refine ⟨2283236536158657779372753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24354523052359016313309365 2283236536158657779372753)
                ·
                  refine ⟨1712427402118993334529565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2283236536158657779372753 1712427402118993334529565)
                  ·
                    refine ⟨642160275794622500448587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1712427402118993334529565 642160275794622500448587)
                    ·
                      rfl

theorem cell22_1875904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 5, 2, 3].length) (baseStart_1875904 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1875904 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1875904 prefixEnd_1875904 := by exact prefixLift 1875904
  have htrace : WordTrace (prefixWord ++ tailWord_1875904) baseStart_1875904 baseEnd_1875904 := by
    simpa [prefixWord, tailWord_1875904, baseEnd_1875904] using wordTrace_append hprefix tailTrace_1875904
  have hstable : (prefixWord ++ tailWord_1875904).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1875904).length < 2 ^ (prefixWord ++ tailWord_1875904).sum := by decide
  have hdescent : baseEnd_1875904 < baseStart_1875904 := by decide
  rcases family_descends (prefixWord ++ tailWord_1875904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1875938 : List Nat := [3, 3, 3, 1, 2, 1, 1, 1, 4, 3]
def baseStart_1875938 : Nat := 118140960795 + 1875938 * 2 ^ 59
def prefixEnd_1875938 : Nat := 4983230072969 + 3 ^ 40 * 1875938 * 2
def baseEnd_1875938 : Nat := 642171914689457745098483

theorem tailTrace_1875938 : CollatzResearch.WordTrace tailWord_1875938 prefixEnd_1875938 642171914689457745098483 := by
  unfold tailWord_1875938
  simp only [CollatzResearch.WordTrace]
  refine ⟨17105269969451121387095117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45614053251869657032253645 17105269969451121387095117)
  ·
    refine ⟨6414476238544170520160669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17105269969451121387095117 6414476238544170520160669)
    ·
      refine ⟨2405428589454063945060251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6414476238544170520160669 2405428589454063945060251)
      ·
        refine ⟨3608142884181095917590377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2405428589454063945060251 3608142884181095917590377)
        ·
          refine ⟨2706107163135821938192783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3608142884181095917590377 2706107163135821938192783)
          ·
            refine ⟨4059160744703732907289175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2706107163135821938192783 4059160744703732907289175)
            ·
              refine ⟨6088741117055599360933763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4059160744703732907289175 6088741117055599360933763)
              ·
                refine ⟨9133111675583399041400645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6088741117055599360933763 9133111675583399041400645)
                ·
                  refine ⟨1712458439171887320262621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9133111675583399041400645 1712458439171887320262621)
                  ·
                    refine ⟨642171914689457745098483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1712458439171887320262621 642171914689457745098483)
                    ·
                      rfl

theorem cell22_1875938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 1, 1, 4, 3].length) (baseStart_1875938 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1875938 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1875938 prefixEnd_1875938 := by exact prefixLift 1875938
  have htrace : WordTrace (prefixWord ++ tailWord_1875938) baseStart_1875938 baseEnd_1875938 := by
    simpa [prefixWord, tailWord_1875938, baseEnd_1875938] using wordTrace_append hprefix tailTrace_1875938
  have hstable : (prefixWord ++ tailWord_1875938).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1875938).length < 2 ^ (prefixWord ++ tailWord_1875938).sum := by decide
  have hdescent : baseEnd_1875938 < baseStart_1875938 := by decide
  rcases family_descends (prefixWord ++ tailWord_1875938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1875974 : List Nat := [6, 2, 1, 2, 1, 2, 1, 3, 4]
def baseStart_1875974 : Nat := 118140960795 + 1875974 * 2 ^ 59
def prefixEnd_1875974 : Nat := 4983230072969 + 3 ^ 40 * 1875974 * 2
def baseEnd_1875974 : Nat := 214061412741721883732791

theorem tailTrace_1875974 : CollatzResearch.WordTrace tailWord_1875974 prefixEnd_1875974 214061412741721883732791 := by
  unfold tailWord_1875974
  simp only [CollatzResearch.WordTrace]
  refine ⟨2138199778302314490521593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 45614928603782709131127317 2138199778302314490521593)
  ·
    refine ⟨1603649833726735867891195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2138199778302314490521593 1603649833726735867891195)
    ·
      refine ⟨2405474750590103801836793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1603649833726735867891195 2405474750590103801836793)
      ·
        refine ⟨1804106062942577851377595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2405474750590103801836793 1804106062942577851377595)
        ·
          refine ⟨2706159094413866777066393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1804106062942577851377595 2706159094413866777066393)
          ·
            refine ⟨2029619320810400082799795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2706159094413866777066393 2029619320810400082799795)
            ·
              refine ⟨3044428981215600124199693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2029619320810400082799795 3044428981215600124199693)
              ·
                refine ⟨1141660867955850046574885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3044428981215600124199693 1141660867955850046574885)
                ·
                  refine ⟨214061412741721883732791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1141660867955850046574885 214061412741721883732791)
                  ·
                    rfl

theorem cell22_1875974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 2, 1, 3, 4].length) (baseStart_1875974 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1875974 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1875974 prefixEnd_1875974 := by exact prefixLift 1875974
  have htrace : WordTrace (prefixWord ++ tailWord_1875974) baseStart_1875974 baseEnd_1875974 := by
    simpa [prefixWord, tailWord_1875974, baseEnd_1875974] using wordTrace_append hprefix tailTrace_1875974
  have hstable : (prefixWord ++ tailWord_1875974).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1875974).length < 2 ^ (prefixWord ++ tailWord_1875974).sum := by decide
  have hdescent : baseEnd_1875974 < baseStart_1875974 := by decide
  rcases family_descends (prefixWord ++ tailWord_1875974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1876039 : List Nat := [1, 1, 4, 1, 3, 1, 3, 2, 1, 5]
def baseStart_1876039 : Nat := 118140960795 + 1876039 * 2 ^ 59
def prefixEnd_1876039 : Nat := 4983230072969 + 3 ^ 40 * 1876039 * 2
def baseEnd_1876039 : Nat := 642206489053527148323173

theorem tailTrace_1876039 : CollatzResearch.WordTrace tailWord_1876039 prefixEnd_1876039 642206489053527148323173 := by
  unfold tailWord_1876039
  simp only [CollatzResearch.WordTrace]
  refine ⟨68424763650438579797807171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45616509100292386531871447 68424763650438579797807171)
  ·
    refine ⟨102637145475657869696710757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68424763650438579797807171 102637145475657869696710757)
    ·
      refine ⟨19244464776685850568133267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 102637145475657869696710757 19244464776685850568133267)
      ·
        refine ⟨28866697165028775852199901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19244464776685850568133267 28866697165028775852199901)
        ·
          refine ⟨10825011436885790944574963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28866697165028775852199901 10825011436885790944574963)
          ·
            refine ⟨16237517155328686416862445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10825011436885790944574963 16237517155328686416862445)
            ·
              refine ⟨6089068933248257406323417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16237517155328686416862445 6089068933248257406323417)
              ·
                refine ⟨4566801699936193054742563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6089068933248257406323417 4566801699936193054742563)
                ·
                  refine ⟨6850202549904289582113845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4566801699936193054742563 6850202549904289582113845)
                  ·
                    refine ⟨642206489053527148323173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6850202549904289582113845 642206489053527148323173)
                    ·
                      rfl

theorem cell22_1876039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 3, 2, 1, 5].length) (baseStart_1876039 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1876039 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1876039 prefixEnd_1876039 := by exact prefixLift 1876039
  have htrace : WordTrace (prefixWord ++ tailWord_1876039) baseStart_1876039 baseEnd_1876039 := by
    simpa [prefixWord, tailWord_1876039, baseEnd_1876039] using wordTrace_append hprefix tailTrace_1876039
  have hstable : (prefixWord ++ tailWord_1876039).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1876039).length < 2 ^ (prefixWord ++ tailWord_1876039).sum := by decide
  have hdescent : baseEnd_1876039 < baseStart_1876039 := by decide
  rcases family_descends (prefixWord ++ tailWord_1876039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1876056 : List Nat := [2, 1, 2, 2, 1, 4, 1, 4, 2, 3]
def baseStart_1876056 : Nat := 118140960795 + 1876056 * 2 ^ 59
def prefixEnd_1876056 : Nat := 4983230072969 + 3 ^ 40 * 1876056 * 2
def baseEnd_1876056 : Nat := 642212308500944770648121

theorem tailTrace_1876056 : CollatzResearch.WordTrace tailWord_1876056 prefixEnd_1876056 642212308500944770648121 := by
  unfold tailWord_1876056
  simp only [CollatzResearch.WordTrace]
  refine ⟨34212691845688495850588011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45616922460917994467450681 34212691845688495850588011)
  ·
    refine ⟨51319037768532743775882017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34212691845688495850588011 51319037768532743775882017)
    ·
      refine ⟨38489278326399557831911513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51319037768532743775882017 38489278326399557831911513)
      ·
        refine ⟨28866958744799668373933635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38489278326399557831911513 28866958744799668373933635)
        ·
          refine ⟨43300438117199502560900453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28866958744799668373933635 43300438117199502560900453)
          ·
            refine ⟨8118832146974906730168835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43300438117199502560900453 8118832146974906730168835)
            ·
              refine ⟨12178248220462360095253253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8118832146974906730168835 12178248220462360095253253)
              ·
                refine ⟨2283421541336692517859985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12178248220462360095253253 2283421541336692517859985)
                ·
                  refine ⟨1712566156002519388394989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2283421541336692517859985 1712566156002519388394989)
                  ·
                    refine ⟨642212308500944770648121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1712566156002519388394989 642212308500944770648121)
                    ·
                      rfl

theorem cell22_1876056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 4, 2, 3].length) (baseStart_1876056 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1876056 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1876056 prefixEnd_1876056 := by exact prefixLift 1876056
  have htrace : WordTrace (prefixWord ++ tailWord_1876056) baseStart_1876056 baseEnd_1876056 := by
    simpa [prefixWord, tailWord_1876056, baseEnd_1876056] using wordTrace_append hprefix tailTrace_1876056
  have hstable : (prefixWord ++ tailWord_1876056).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1876056).length < 2 ^ (prefixWord ++ tailWord_1876056).sum := by decide
  have hdescent : baseEnd_1876056 < baseStart_1876056 := by decide
  rcases family_descends (prefixWord ++ tailWord_1876056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1876069 : List Nat := [1, 3, 1, 3, 2, 2, 3, 7]
def baseStart_1876069 : Nat := 118140960795 + 1876069 * 2 ^ 59
def prefixEnd_1876069 : Nat := 4983230072969 + 3 ^ 40 * 1876069 * 2
def baseEnd_1876069 : Nat := 71357417629624118897009

theorem tailTrace_1876069 : CollatzResearch.WordTrace tailWord_1876069 prefixEnd_1876069 71357417629624118897009 := by
  unfold tailWord_1876069
  simp only [CollatzResearch.WordTrace]
  refine ⟨68425857840329894921399261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45617238560219929947599507 68425857840329894921399261)
  ·
    refine ⟨25659696690123710595524723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68425857840329894921399261 25659696690123710595524723)
    ·
      refine ⟨38489545035185565893287085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25659696690123710595524723 38489545035185565893287085)
      ·
        refine ⟨14433579388194587209982657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38489545035185565893287085 14433579388194587209982657)
        ·
          refine ⟨10825184541145940407486993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14433579388194587209982657 10825184541145940407486993)
          ·
            refine ⟨8118888405859455305615245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10825184541145940407486993 8118888405859455305615245)
            ·
              refine ⟨3044583152197295739605717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8118888405859455305615245 3044583152197295739605717)
              ·
                refine ⟨71357417629624118897009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3044583152197295739605717 71357417629624118897009)
                ·
                  rfl

theorem cell22_1876069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 3, 7].length) (baseStart_1876069 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1876069 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1876069 prefixEnd_1876069 := by exact prefixLift 1876069
  have htrace : WordTrace (prefixWord ++ tailWord_1876069) baseStart_1876069 baseEnd_1876069 := by
    simpa [prefixWord, tailWord_1876069, baseEnd_1876069] using wordTrace_append hprefix tailTrace_1876069
  have hstable : (prefixWord ++ tailWord_1876069).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1876069).length < 2 ^ (prefixWord ++ tailWord_1876069).sum := by decide
  have hdescent : baseEnd_1876069 < baseStart_1876069 := by decide
  rcases family_descends (prefixWord ++ tailWord_1876069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1876182 : List Nat := [5, 2, 1, 2, 1, 3, 2, 1, 5]
def baseStart_1876182 : Nat := 118140960795 + 1876182 * 2 ^ 59
def prefixEnd_1876182 : Nat := 4983230072969 + 3 ^ 40 * 1876182 * 2
def baseEnd_1876182 : Nat := 214085146958640813999245

theorem tailTrace_1876182 : CollatzResearch.WordTrace tailWord_1876182 prefixEnd_1876182 214085146958640813999245 := by
  unfold tailWord_1876182
  simp only [CollatzResearch.WordTrace]
  refine ⟨4276873705557532201266425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 45619986192613676813508533 4276873705557532201266425)
  ·
    refine ⟨3207655279168149150949819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4276873705557532201266425 3207655279168149150949819)
    ·
      refine ⟨4811482918752223726424729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3207655279168149150949819 4811482918752223726424729)
      ·
        refine ⟨3608612189064167794818547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4811482918752223726424729 3608612189064167794818547)
        ·
          refine ⟨5412918283596251692227821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3608612189064167794818547 5412918283596251692227821)
          ·
            refine ⟨2029844356348594384585433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5412918283596251692227821 2029844356348594384585433)
            ·
              refine ⟨1522383267261445788439075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2029844356348594384585433 1522383267261445788439075)
              ·
                refine ⟨2283574900892168682658613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1522383267261445788439075 2283574900892168682658613)
                ·
                  refine ⟨214085146958640813999245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2283574900892168682658613 214085146958640813999245)
                  ·
                    rfl

theorem cell22_1876182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 3, 2, 1, 5].length) (baseStart_1876182 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1876182 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1876182 prefixEnd_1876182 := by exact prefixLift 1876182
  have htrace : WordTrace (prefixWord ++ tailWord_1876182) baseStart_1876182 baseEnd_1876182 := by
    simpa [prefixWord, tailWord_1876182, baseEnd_1876182] using wordTrace_append hprefix tailTrace_1876182
  have hstable : (prefixWord ++ tailWord_1876182).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1876182).length < 2 ^ (prefixWord ++ tailWord_1876182).sum := by decide
  have hdescent : baseEnd_1876182 < baseStart_1876182 := by decide
  rcases family_descends (prefixWord ++ tailWord_1876182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1876204 : List Nat := [2, 2, 1, 1, 2, 3, 1, 10]
def baseStart_1876204 : Nat := 118140960795 + 1876204 * 2 ^ 59
def prefixEnd_1876204 : Nat := 4983230072969 + 3 ^ 40 * 1876204 * 2
def baseEnd_1876204 : Nat := 71362552436169079771963

theorem tailTrace_1876204 : CollatzResearch.WordTrace tailWord_1876204 prefixEnd_1876204 71362552436169079771963 := by
  unfold tailWord_1876204
  simp only [CollatzResearch.WordTrace]
  refine ⟨34215390847420406488781833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45620521129893875318375777 34215390847420406488781833)
  ·
    refine ⟨25661543135565304866586375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34215390847420406488781833 25661543135565304866586375)
    ·
      refine ⟨38492314703347957299879563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25661543135565304866586375 38492314703347957299879563)
      ·
        refine ⟨57738472055021935949819345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38492314703347957299879563 57738472055021935949819345)
        ·
          refine ⟨43303854041266451962364509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57738472055021935949819345 43303854041266451962364509)
          ·
            refine ⟨16238945265474919485886691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43303854041266451962364509 16238945265474919485886691)
            ·
              refine ⟨24358417898212379228830037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16238945265474919485886691 24358417898212379228830037)
              ·
                refine ⟨71362552436169079771963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 24358417898212379228830037 71362552436169079771963)
                ·
                  rfl

theorem cell22_1876204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 10].length) (baseStart_1876204 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1876204 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1876204 prefixEnd_1876204 := by exact prefixLift 1876204
  have htrace : WordTrace (prefixWord ++ tailWord_1876204) baseStart_1876204 baseEnd_1876204 := by
    simpa [prefixWord, tailWord_1876204, baseEnd_1876204] using wordTrace_append hprefix tailTrace_1876204
  have hstable : (prefixWord ++ tailWord_1876204).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1876204).length < 2 ^ (prefixWord ++ tailWord_1876204).sum := by decide
  have hdescent : baseEnd_1876204 < baseStart_1876204 := by decide
  rcases family_descends (prefixWord ++ tailWord_1876204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1876296 : List Nat := [2, 1, 3, 1, 1, 2, 2, 1, 5, 4]
def baseStart_1876296 : Nat := 118140960795 + 1876296 * 2 ^ 59
def prefixEnd_1876296 : Nat := 4983230072969 + 3 ^ 40 * 1876296 * 2
def baseEnd_1876296 : Nat := 642294465405664144647385

theorem tailTrace_1876296 : CollatzResearch.WordTrace tailWord_1876296 prefixEnd_1876296 642294465405664144647385 := by
  unfold tailWord_1876296
  simp only [CollatzResearch.WordTrace]
  refine ⟨34217068605253756344956371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45622758140338341793275161 34217068605253756344956371)
  ·
    refine ⟨51325602907880634517434557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34217068605253756344956371 51325602907880634517434557)
    ·
      refine ⟨19247101090455237944037959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51325602907880634517434557 19247101090455237944037959)
      ·
        refine ⟨28870651635682856916056939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19247101090455237944037959 28870651635682856916056939)
        ·
          refine ⟨43305977453524285374085409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28870651635682856916056939 43305977453524285374085409)
          ·
            refine ⟨32479483090143214030564057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43305977453524285374085409 32479483090143214030564057)
            ·
              refine ⟨24359612317607410522923043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32479483090143214030564057 24359612317607410522923043)
              ·
                refine ⟨36539418476411115784384565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24359612317607410522923043 36539418476411115784384565)
                ·
                  refine ⟨3425570482163542104786053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 36539418476411115784384565 3425570482163542104786053)
                  ·
                    refine ⟨642294465405664144647385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3425570482163542104786053 642294465405664144647385)
                    ·
                      rfl

theorem cell22_1876296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 1, 5, 4].length) (baseStart_1876296 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1876296 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1876296 prefixEnd_1876296 := by exact prefixLift 1876296
  have htrace : WordTrace (prefixWord ++ tailWord_1876296) baseStart_1876296 baseEnd_1876296 := by
    simpa [prefixWord, tailWord_1876296, baseEnd_1876296] using wordTrace_append hprefix tailTrace_1876296
  have hstable : (prefixWord ++ tailWord_1876296).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1876296).length < 2 ^ (prefixWord ++ tailWord_1876296).sum := by decide
  have hdescent : baseEnd_1876296 < baseStart_1876296 := by decide
  rcases family_descends (prefixWord ++ tailWord_1876296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1876311 : List Nat := [1, 1, 3, 2, 3, 1, 1, 4, 6]
def baseStart_1876311 : Nat := 118140960795 + 1876311 * 2 ^ 59
def prefixEnd_1876311 : Nat := 4983230072969 + 3 ^ 40 * 1876311 * 2
def baseEnd_1876311 : Nat := 214099866737403035174113

theorem tailTrace_1876311 : CollatzResearch.WordTrace tailWord_1876311 prefixEnd_1876311 214099866737403035174113 := by
  unfold tailWord_1876311
  simp only [CollatzResearch.WordTrace]
  refine ⟨68434684305453170251708787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45623122870302113501139191 68434684305453170251708787)
  ·
    refine ⟨102652026458179755377563181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68434684305453170251708787 102652026458179755377563181)
    ·
      refine ⟨38494509921817408266586193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102652026458179755377563181 38494509921817408266586193)
      ·
        refine ⟨28870882441363056199939645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38494509921817408266586193 28870882441363056199939645)
        ·
          refine ⟨10826580915511146074977367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28870882441363056199939645 10826580915511146074977367)
          ·
            refine ⟨16239871373266719112466051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10826580915511146074977367 16239871373266719112466051)
            ·
              refine ⟨24359807059900078668699077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16239871373266719112466051 24359807059900078668699077)
              ·
                refine ⟨4567463823731264750381077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24359807059900078668699077 4567463823731264750381077)
                ·
                  refine ⟨214099866737403035174113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4567463823731264750381077 214099866737403035174113)
                  ·
                    rfl

theorem cell22_1876311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 4, 6].length) (baseStart_1876311 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1876311 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1876311 prefixEnd_1876311 := by exact prefixLift 1876311
  have htrace : WordTrace (prefixWord ++ tailWord_1876311) baseStart_1876311 baseEnd_1876311 := by
    simpa [prefixWord, tailWord_1876311, baseEnd_1876311] using wordTrace_append hprefix tailTrace_1876311
  have hstable : (prefixWord ++ tailWord_1876311).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1876311).length < 2 ^ (prefixWord ++ tailWord_1876311).sum := by decide
  have hdescent : baseEnd_1876311 < baseStart_1876311 := by decide
  rcases family_descends (prefixWord ++ tailWord_1876311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1876330 : List Nat := [3, 1, 3, 3, 1, 1, 2, 3, 1, 4]
def baseStart_1876330 : Nat := 118140960795 + 1876330 * 2 ^ 59
def prefixEnd_1876330 : Nat := 4983230072969 + 3 ^ 40 * 1876330 * 2
def baseEnd_1876330 : Nat := 642306104300499389297281

theorem tailTrace_1876330 : CollatzResearch.WordTrace tailWord_1876330 prefixEnd_1876330 642306104300499389297281 := by
  unfold tailWord_1876330
  simp only [CollatzResearch.WordTrace]
  refine ⟨17108844323096084124162611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45623584861589557664433629 17108844323096084124162611)
  ·
    refine ⟨25663266484644126186243917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17108844323096084124162611 25663266484644126186243917)
    ·
      refine ⟨9623724931741547319841469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25663266484644126186243917 9623724931741547319841469)
      ·
        refine ⟨3608896849403080244940551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9623724931741547319841469 3608896849403080244940551)
        ·
          refine ⟨5413345274104620367410827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3608896849403080244940551 5413345274104620367410827)
          ·
            refine ⟨8120017911156930551116241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5413345274104620367410827 8120017911156930551116241)
            ·
              refine ⟨6090013433367697913337181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8120017911156930551116241 6090013433367697913337181)
              ·
                refine ⟨2283755037512886717501443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6090013433367697913337181 2283755037512886717501443)
                ·
                  refine ⟨3425632556269330076252165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2283755037512886717501443 3425632556269330076252165)
                  ·
                    refine ⟨642306104300499389297281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3425632556269330076252165 642306104300499389297281)
                    ·
                      rfl

theorem cell22_1876330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 2, 3, 1, 4].length) (baseStart_1876330 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1876330 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1876330 prefixEnd_1876330 := by exact prefixLift 1876330
  have htrace : WordTrace (prefixWord ++ tailWord_1876330) baseStart_1876330 baseEnd_1876330 := by
    simpa [prefixWord, tailWord_1876330, baseEnd_1876330] using wordTrace_append hprefix tailTrace_1876330
  have hstable : (prefixWord ++ tailWord_1876330).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1876330).length < 2 ^ (prefixWord ++ tailWord_1876330).sum := by decide
  have hdescent : baseEnd_1876330 < baseStart_1876330 := by decide
  rcases family_descends (prefixWord ++ tailWord_1876330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1876360 : List Nat := [2, 1, 3, 3, 1, 1, 3, 3, 2, 3]
def baseStart_1876360 : Nat := 118140960795 + 1876360 * 2 ^ 59
def prefixEnd_1876360 : Nat := 4983230072969 + 3 ^ 40 * 1876360 * 2
def baseEnd_1876360 : Nat := 642316373913589311047189

theorem tailTrace_1876360 : CollatzResearch.WordTrace tailWord_1876360 prefixEnd_1876360 642316373913589311047189 := by
  unfold tailWord_1876360
  simp only [CollatzResearch.WordTrace]
  refine ⟨34218235741137825810121267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45624314321517101080161689 34218235741137825810121267)
  ·
    refine ⟨51327353611706738715181901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34218235741137825810121267 51327353611706738715181901)
    ·
      refine ⟨19247757604390027018193213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51327353611706738715181901 19247757604390027018193213)
      ·
        refine ⟨7217909101646260131822455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19247757604390027018193213 7217909101646260131822455)
        ·
          refine ⟨10826863652469390197733683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7217909101646260131822455 10826863652469390197733683)
          ·
            refine ⟨16240295478704085296600525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10826863652469390197733683 16240295478704085296600525)
            ·
              refine ⟨6090110804514031986225197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16240295478704085296600525 6090110804514031986225197)
              ·
                refine ⟨2283791551692761994834449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6090110804514031986225197 2283791551692761994834449)
                ·
                  refine ⟨1712843663769571496125837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2283791551692761994834449 1712843663769571496125837)
                  ·
                    refine ⟨642316373913589311047189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1712843663769571496125837 642316373913589311047189)
                    ·
                      rfl

theorem cell22_1876360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 3, 3, 2, 3].length) (baseStart_1876360 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1876360 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1876360 prefixEnd_1876360 := by exact prefixLift 1876360
  have htrace : WordTrace (prefixWord ++ tailWord_1876360) baseStart_1876360 baseEnd_1876360 := by
    simpa [prefixWord, tailWord_1876360, baseEnd_1876360] using wordTrace_append hprefix tailTrace_1876360
  have hstable : (prefixWord ++ tailWord_1876360).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1876360).length < 2 ^ (prefixWord ++ tailWord_1876360).sum := by decide
  have hdescent : baseEnd_1876360 < baseStart_1876360 := by decide
  rcases family_descends (prefixWord ++ tailWord_1876360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1876469 : List Nat := [1, 3, 5, 1, 2, 1, 3, 1, 5]
def baseStart_1876469 : Nat := 118140960795 + 1876469 * 2 ^ 59
def prefixEnd_1876469 : Nat := 4983230072969 + 3 ^ 40 * 1876469 * 2
def baseEnd_1876469 : Nat := 214117895613716453357285

theorem tailTrace_1876469 : CollatzResearch.WordTrace tailWord_1876469 prefixEnd_1876469 214117895613716453357285 := by
  unfold tailWord_1876469
  simp only [CollatzResearch.WordTrace]
  refine ⟨68440447038880763235960461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45626964692587175490640307 68440447038880763235960461)
  ·
    refine ⟨25665167639580286213485173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68440447038880763235960461 25665167639580286213485173)
    ·
      refine ⟨2406109466210651832514235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 25665167639580286213485173 2406109466210651832514235)
      ·
        refine ⟨3609164199315977748771353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2406109466210651832514235 3609164199315977748771353)
        ·
          refine ⟨2706873149486983311578515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3609164199315977748771353 2706873149486983311578515)
          ·
            refine ⟨4060309724230474967367773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2706873149486983311578515 4060309724230474967367773)
            ·
              refine ⟨1522616146586428112762915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4060309724230474967367773 1522616146586428112762915)
              ·
                refine ⟨2283924219879642169144373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1522616146586428112762915 2283924219879642169144373)
                ·
                  refine ⟨214117895613716453357285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2283924219879642169144373 214117895613716453357285)
                  ·
                    rfl

theorem cell22_1876469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 3, 1, 5].length) (baseStart_1876469 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1876469 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1876469 prefixEnd_1876469 := by exact prefixLift 1876469
  have htrace : WordTrace (prefixWord ++ tailWord_1876469) baseStart_1876469 baseEnd_1876469 := by
    simpa [prefixWord, tailWord_1876469, baseEnd_1876469] using wordTrace_append hprefix tailTrace_1876469
  have hstable : (prefixWord ++ tailWord_1876469).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1876469).length < 2 ^ (prefixWord ++ tailWord_1876469).sum := by decide
  have hdescent : baseEnd_1876469 < baseStart_1876469 := by decide
  rcases family_descends (prefixWord ++ tailWord_1876469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1876508 : List Nat := [2, 2, 3, 1, 2, 2, 10]
def baseStart_1876508 : Nat := 118140960795 + 1876508 * 2 ^ 59
def prefixEnd_1876508 : Nat := 4983230072969 + 3 ^ 40 * 1876508 * 2
def baseEnd_1876508 : Nat := 23791371753265416975805

theorem tailTrace_1876508 : CollatzResearch.WordTrace tailWord_1876508 prefixEnd_1876508 23791371753265416975805 := by
  unfold tailWord_1876508
  simp only [CollatzResearch.WordTrace]
  refine ⟨34220934742869736448315089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45627912990492981931086785 34220934742869736448315089)
  ·
    refine ⟨25665701057152302336236317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34220934742869736448315089 25665701057152302336236317)
    ·
      refine ⟨9624637896432113376088619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25665701057152302336236317 9624637896432113376088619)
      ·
        refine ⟨14436956844648170064132929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9624637896432113376088619 14436956844648170064132929)
        ·
          refine ⟨10827717633486127548099697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14436956844648170064132929 10827717633486127548099697)
          ·
            refine ⟨8120788225114595661074773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10827717633486127548099697 8120788225114595661074773)
            ·
              refine ⟨23791371753265416975805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 8120788225114595661074773 23791371753265416975805)
              ·
                rfl

theorem cell22_1876508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 10].length) (baseStart_1876508 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1876508 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1876508 prefixEnd_1876508 := by exact prefixLift 1876508
  have htrace : WordTrace (prefixWord ++ tailWord_1876508) baseStart_1876508 baseEnd_1876508 := by
    simpa [prefixWord, tailWord_1876508, baseEnd_1876508] using wordTrace_append hprefix tailTrace_1876508
  have hstable : (prefixWord ++ tailWord_1876508).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1876508).length < 2 ^ (prefixWord ++ tailWord_1876508).sum := by decide
  have hdescent : baseEnd_1876508 < baseStart_1876508 := by decide
  rcases family_descends (prefixWord ++ tailWord_1876508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1876632 : List Nat := [2, 1, 2, 4, 1, 1, 1, 6, 4]
def baseStart_1876632 : Nat := 118140960795 + 1876632 * 2 ^ 59
def prefixEnd_1876632 : Nat := 4983230072969 + 3 ^ 40 * 1876632 * 2
def baseEnd_1876632 : Nat := 214136495024090422748785

theorem tailTrace_1876632 : CollatzResearch.WordTrace tailWord_1876632 prefixEnd_1876632 214136495024090422748785 := by
  unfold tailWord_1876632
  simp only [CollatzResearch.WordTrace]
  refine ⟨34223196068645121037072075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45630928091526828049429433 34223196068645121037072075)
  ·
    refine ⟨51334794102967681555608113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34223196068645121037072075 51334794102967681555608113)
    ·
      refine ⟨38501095577225761166706085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51334794102967681555608113 38501095577225761166706085)
      ·
        refine ⟨7218955420729830218757391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38501095577225761166706085 7218955420729830218757391)
        ·
          refine ⟨10828433131094745328136087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7218955420729830218757391 10828433131094745328136087)
          ·
            refine ⟨16242649696642117992204131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10828433131094745328136087 16242649696642117992204131)
            ·
              refine ⟨24363974544963176988306197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16242649696642117992204131 24363974544963176988306197)
              ·
                refine ⟨1142061306795148921326853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 24363974544963176988306197 1142061306795148921326853)
                ·
                  refine ⟨214136495024090422748785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1142061306795148921326853 214136495024090422748785)
                  ·
                    rfl

theorem cell22_1876632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 6, 4].length) (baseStart_1876632 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1876632 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1876632 prefixEnd_1876632 := by exact prefixLift 1876632
  have htrace : WordTrace (prefixWord ++ tailWord_1876632) baseStart_1876632 baseEnd_1876632 := by
    simpa [prefixWord, tailWord_1876632, baseEnd_1876632] using wordTrace_append hprefix tailTrace_1876632
  have hstable : (prefixWord ++ tailWord_1876632).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1876632).length < 2 ^ (prefixWord ++ tailWord_1876632).sum := by decide
  have hdescent : baseEnd_1876632 < baseStart_1876632 := by decide
  rcases family_descends (prefixWord ++ tailWord_1876632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1876726 : List Nat := [5, 1, 1, 1, 1, 2, 2, 5, 1, 3]
def baseStart_1876726 : Nat := 118140960795 + 1876726 * 2 ^ 59
def prefixEnd_1876726 : Nat := 4983230072969 + 3 ^ 40 * 1876726 * 2
def baseEnd_1876726 : Nat := 642441663193286356396067

theorem tailTrace_1876726 : CollatzResearch.WordTrace tailWord_1876726 prefixEnd_1876726 642441663193286356396067 := by
  unfold tailWord_1876726
  simp only [CollatzResearch.WordTrace]
  refine ⟨4278113787434356008004127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 45633213732633130752044021 4278113787434356008004127)
  ·
    refine ⟨6417170681151534012006191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4278113787434356008004127 6417170681151534012006191)
    ·
      refine ⟨9625756021727301018009287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6417170681151534012006191 9625756021727301018009287)
      ·
        refine ⟨14438634032590951527013931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9625756021727301018009287 14438634032590951527013931)
        ·
          refine ⟨21657951048886427290520897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14438634032590951527013931 21657951048886427290520897)
          ·
            refine ⟨16243463286664820467890673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21657951048886427290520897 16243463286664820467890673)
            ·
              refine ⟨12182597464998615350918005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16243463286664820467890673 12182597464998615350918005)
              ·
                refine ⟨1142118512343620189148563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12182597464998615350918005 1142118512343620189148563)
                ·
                  refine ⟨1713177768515430283722845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1142118512343620189148563 1713177768515430283722845)
                  ·
                    refine ⟨642441663193286356396067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1713177768515430283722845 642441663193286356396067)
                    ·
                      rfl

theorem cell22_1876726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 5, 1, 3].length) (baseStart_1876726 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1876726 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1876726 prefixEnd_1876726 := by exact prefixLift 1876726
  have htrace : WordTrace (prefixWord ++ tailWord_1876726) baseStart_1876726 baseEnd_1876726 := by
    simpa [prefixWord, tailWord_1876726, baseEnd_1876726] using wordTrace_append hprefix tailTrace_1876726
  have hstable : (prefixWord ++ tailWord_1876726).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1876726).length < 2 ^ (prefixWord ++ tailWord_1876726).sum := by decide
  have hdescent : baseEnd_1876726 < baseStart_1876726 := by decide
  rcases family_descends (prefixWord ++ tailWord_1876726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1876743 : List Nat := [1, 1, 4, 4, 1, 1, 4, 2, 1, 3]
def baseStart_1876743 : Nat := 118140960795 + 1876743 * 2 ^ 59
def prefixEnd_1876743 : Nat := 4983230072969 + 3 ^ 40 * 1876743 * 2
def baseEnd_1876743 : Nat := 642447482640703978721015

theorem tailTrace_1876743 : CollatzResearch.WordTrace tailWord_1876743 prefixEnd_1876743 642447482640703978721015 := by
  unfold tailWord_1876743
  simp only [CollatzResearch.WordTrace]
  refine ⟨68450440639888108031434883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45633627093258738687623255 68450440639888108031434883)
  ·
    refine ⟨102675660959832162047152325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68450440639888108031434883 102675660959832162047152325)
    ·
      refine ⟨19251686429968530383841061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 102675660959832162047152325 19251686429968530383841061)
      ·
        refine ⟨3609691205619099446970199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19251686429968530383841061 3609691205619099446970199)
        ·
          refine ⟨5414536808428649170455299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3609691205619099446970199 5414536808428649170455299)
          ·
            refine ⟨8121805212642973755682949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5414536808428649170455299 8121805212642973755682949)
            ·
              refine ⟨1522838477370557579190553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8121805212642973755682949 1522838477370557579190553)
              ·
                refine ⟨1142128858027918184392915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1522838477370557579190553 1142128858027918184392915)
                ·
                  refine ⟨1713193287041877276589373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1142128858027918184392915 1713193287041877276589373)
                  ·
                    refine ⟨642447482640703978721015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1713193287041877276589373 642447482640703978721015)
                    ·
                      rfl

theorem cell22_1876743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 4, 2, 1, 3].length) (baseStart_1876743 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1876743 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1876743 prefixEnd_1876743 := by exact prefixLift 1876743
  have htrace : WordTrace (prefixWord ++ tailWord_1876743) baseStart_1876743 baseEnd_1876743 := by
    simpa [prefixWord, tailWord_1876743, baseEnd_1876743] using wordTrace_append hprefix tailTrace_1876743
  have hstable : (prefixWord ++ tailWord_1876743).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1876743).length < 2 ^ (prefixWord ++ tailWord_1876743).sum := by decide
  have hdescent : baseEnd_1876743 < baseStart_1876743 := by decide
  rcases family_descends (prefixWord ++ tailWord_1876743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1876767 : List Nat := [1, 1, 2, 4, 2, 3, 1, 2, 6]
def baseStart_1876767 : Nat := 118140960795 + 1876767 * 2 ^ 59
def prefixEnd_1876767 : Nat := 4983230072969 + 3 ^ 40 * 1876767 * 2
def baseEnd_1876767 : Nat := 214151899443725305373647

theorem tailTrace_1876767 : CollatzResearch.WordTrace tailWord_1876767 prefixEnd_1876767 214151899443725305373647 := by
  unfold tailWord_1876767
  simp only [CollatzResearch.WordTrace]
  refine ⟨68451315991801160130308555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45634210661200773420205703 68451315991801160130308555)
  ·
    refine ⟨102676973987701740195462833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68451315991801160130308555 102676973987701740195462833)
    ·
      refine ⟨77007730490776305146597125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102676973987701740195462833 77007730490776305146597125)
      ·
        refine ⟨14438949467020557214986961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 77007730490776305146597125 14438949467020557214986961)
        ·
          refine ⟨10829212100265417911240221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14438949467020557214986961 10829212100265417911240221)
          ·
            refine ⟨4060954537599531716715083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10829212100265417911240221 4060954537599531716715083)
            ·
              refine ⟨6091431806399297575072625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4060954537599531716715083 6091431806399297575072625)
              ·
                refine ⟨4568573854799473181304469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6091431806399297575072625 4568573854799473181304469)
                ·
                  refine ⟨214151899443725305373647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4568573854799473181304469 214151899443725305373647)
                  ·
                    rfl

theorem cell22_1876767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 1, 2, 6].length) (baseStart_1876767 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1876767 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1876767 prefixEnd_1876767 := by exact prefixLift 1876767
  have htrace : WordTrace (prefixWord ++ tailWord_1876767) baseStart_1876767 baseEnd_1876767 := by
    simpa [prefixWord, tailWord_1876767, baseEnd_1876767] using wordTrace_append hprefix tailTrace_1876767
  have hstable : (prefixWord ++ tailWord_1876767).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1876767).length < 2 ^ (prefixWord ++ tailWord_1876767).sum := by decide
  have hdescent : baseEnd_1876767 < baseStart_1876767 := by decide
  rcases family_descends (prefixWord ++ tailWord_1876767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1876799 : List Nat := [1, 1, 2, 2, 5, 2, 1, 1, 4, 3]
def baseStart_1876799 : Nat := 118140960795 + 1876799 * 2 ^ 59
def prefixEnd_1876799 : Nat := 4983230072969 + 3 ^ 40 * 1876799 * 2
def baseEnd_1876799 : Nat := 642466652585138499320843

theorem tailTrace_1876799 : CollatzResearch.WordTrace tailWord_1876799 prefixEnd_1876799 642466652585138499320843 := by
  unfold tailWord_1876799
  simp only [CollatzResearch.WordTrace]
  refine ⟨68452483127685229595473451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45634988751790153063648967 68452483127685229595473451)
  ·
    refine ⟨102678724691527844393210177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68452483127685229595473451 102678724691527844393210177)
    ·
      refine ⟨77009043518645883294907633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102678724691527844393210177 77009043518645883294907633)
      ·
        refine ⟨57756782638984412471180725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77009043518645883294907633 57756782638984412471180725)
        ·
          refine ⟨5414698372404788669173193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 57756782638984412471180725 5414698372404788669173193)
          ·
            refine ⟨4061023779303591501879895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5414698372404788669173193 4061023779303591501879895)
            ·
              refine ⟨6091535668955387252819843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4061023779303591501879895 6091535668955387252819843)
              ·
                refine ⟨9137303503433080879229765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6091535668955387252819843 9137303503433080879229765)
                ·
                  refine ⟨1713244406893702664855581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9137303503433080879229765 1713244406893702664855581)
                  ·
                    refine ⟨642466652585138499320843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1713244406893702664855581 642466652585138499320843)
                    ·
                      rfl

theorem cell22_1876799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 1, 1, 4, 3].length) (baseStart_1876799 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1876799 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1876799 prefixEnd_1876799 := by exact prefixLift 1876799
  have htrace : WordTrace (prefixWord ++ tailWord_1876799) baseStart_1876799 baseEnd_1876799 := by
    simpa [prefixWord, tailWord_1876799, baseEnd_1876799] using wordTrace_append hprefix tailTrace_1876799
  have hstable : (prefixWord ++ tailWord_1876799).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1876799).length < 2 ^ (prefixWord ++ tailWord_1876799).sum := by decide
  have hdescent : baseEnd_1876799 < baseStart_1876799 := by decide
  rcases family_descends (prefixWord ++ tailWord_1876799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1876801 : List Nat := [1, 2, 5, 3, 1, 1, 2, 1, 6]
def baseStart_1876801 : Nat := 118140960795 + 1876801 * 2 ^ 59
def prefixEnd_1876801 : Nat := 4983230072969 + 3 ^ 40 * 1876801 * 2
def baseEnd_1876801 : Nat := 214155779075337053590279

theorem tailTrace_1876801 : CollatzResearch.WordTrace tailWord_1876801 prefixEnd_1876801 214155779075337053590279 := by
  unfold tailWord_1876801
  simp only [CollatzResearch.WordTrace]
  refine ⟨68452556073677983937046257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45635037382451989291364171 68452556073677983937046257)
  ·
    refine ⟨51339417055258487952784693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68452556073677983937046257 51339417055258487952784693)
    ·
      refine ⟨4813070348930483245573565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 51339417055258487952784693 4813070348930483245573565)
      ·
        refine ⟨1804901380848931217090087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4813070348930483245573565 1804901380848931217090087)
        ·
          refine ⟨2707352071273396825635131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1804901380848931217090087 2707352071273396825635131)
          ·
            refine ⟨4061028106910095238452697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2707352071273396825635131 4061028106910095238452697)
            ·
              refine ⟨3045771080182571428839523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4061028106910095238452697 3045771080182571428839523)
              ·
                refine ⟨4568656620273857143259285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3045771080182571428839523 4568656620273857143259285)
                ·
                  refine ⟨214155779075337053590279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4568656620273857143259285 214155779075337053590279)
                  ·
                    rfl

theorem cell22_1876801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 2, 1, 6].length) (baseStart_1876801 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1876801 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1876801 prefixEnd_1876801 := by exact prefixLift 1876801
  have htrace : WordTrace (prefixWord ++ tailWord_1876801) baseStart_1876801 baseEnd_1876801 := by
    simpa [prefixWord, tailWord_1876801, baseEnd_1876801] using wordTrace_append hprefix tailTrace_1876801
  have hstable : (prefixWord ++ tailWord_1876801).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1876801).length < 2 ^ (prefixWord ++ tailWord_1876801).sum := by decide
  have hdescent : baseEnd_1876801 < baseStart_1876801 := by decide
  rcases family_descends (prefixWord ++ tailWord_1876801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1876827 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 11, 3]
def baseStart_1876827 : Nat := 118140960795 + 1876827 * 2 ^ 59
def prefixEnd_1876827 : Nat := 4983230072969 + 3 ^ 40 * 1876827 * 2
def baseEnd_1876827 : Nat := 642476237557355759620757

theorem tailTrace_1876827 : CollatzResearch.WordTrace tailWord_1876827 prefixEnd_1876827 642476237557355759620757 := by
  unfold tailWord_1876827
  simp only [CollatzResearch.WordTrace]
  refine ⟨68453504371583790377492735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45635669581055860251661823 68453504371583790377492735)
  ·
    refine ⟨102680256557375685566239103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68453504371583790377492735 102680256557375685566239103)
    ·
      refine ⟨154020384836063528349358655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102680256557375685566239103 154020384836063528349358655)
      ·
        refine ⟨231030577254095292524037983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154020384836063528349358655 231030577254095292524037983)
        ·
          refine ⟨346545865881142938786056975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 231030577254095292524037983 346545865881142938786056975)
          ·
            refine ⟨519818798821714408179085463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 346545865881142938786056975 519818798821714408179085463)
            ·
              refine ⟨779728198232571612268628195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 519818798821714408179085463 779728198232571612268628195)
              ·
                refine ⟨1169592297348857418402942293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 779728198232571612268628195 1169592297348857418402942293)
                ·
                  refine ⟨1713269966819615358988685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 1169592297348857418402942293 1713269966819615358988685)
                  ·
                    refine ⟨642476237557355759620757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1713269966819615358988685 642476237557355759620757)
                    ·
                      rfl

theorem cell22_1876827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 11, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 11, 3].length) (baseStart_1876827 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1876827 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1876827 prefixEnd_1876827 := by exact prefixLift 1876827
  have htrace : WordTrace (prefixWord ++ tailWord_1876827) baseStart_1876827 baseEnd_1876827 := by
    simpa [prefixWord, tailWord_1876827, baseEnd_1876827] using wordTrace_append hprefix tailTrace_1876827
  have hstable : (prefixWord ++ tailWord_1876827).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1876827).length < 2 ^ (prefixWord ++ tailWord_1876827).sum := by decide
  have hdescent : baseEnd_1876827 < baseStart_1876827 := by decide
  rcases family_descends (prefixWord ++ tailWord_1876827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1876846 : List Nat := [4, 1, 2, 3, 3, 1, 8]
def baseStart_1876846 : Nat := 118140960795 + 1876846 * 2 ^ 59
def prefixEnd_1876846 : Nat := 4983230072969 + 3 ^ 40 * 1876846 * 2
def baseEnd_1876846 : Nat := 23795657097986890496137

theorem tailTrace_1876846 : CollatzResearch.WordTrace tailWord_1876846 prefixEnd_1876846 23795657097986890496137 := by
  unfold tailWord_1876846
  simp only [CollatzResearch.WordTrace]
  refine ⟨8556774669814369577804299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45636131572343304414956261 8556774669814369577804299)
  ·
    refine ⟨12835162004721554366706449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8556774669814369577804299 12835162004721554366706449)
    ·
      refine ⟨9626371503541165775029837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12835162004721554366706449 9626371503541165775029837)
      ·
        refine ⟨3609889313827937165636189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9626371503541165775029837 3609889313827937165636189)
        ·
          refine ⟨1353708492685476437113571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3609889313827937165636189 1353708492685476437113571)
          ·
            refine ⟨2030562739028214655670357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1353708492685476437113571 2030562739028214655670357)
            ·
              refine ⟨23795657097986890496137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2030562739028214655670357 23795657097986890496137)
              ·
                rfl

theorem cell22_1876846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 3, 1, 8].length) (baseStart_1876846 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1876846 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1876846 prefixEnd_1876846 := by exact prefixLift 1876846
  have htrace : WordTrace (prefixWord ++ tailWord_1876846) baseStart_1876846 baseEnd_1876846 := by
    simpa [prefixWord, tailWord_1876846, baseEnd_1876846] using wordTrace_append hprefix tailTrace_1876846
  have hstable : (prefixWord ++ tailWord_1876846).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1876846).length < 2 ^ (prefixWord ++ tailWord_1876846).sum := by decide
  have hdescent : baseEnd_1876846 < baseStart_1876846 := by decide
  rcases family_descends (prefixWord ++ tailWord_1876846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1876857 : List Nat := [1, 2, 1, 3, 2, 3, 2, 1, 7]
def baseStart_1876857 : Nat := 118140960795 + 1876857 * 2 ^ 59
def prefixEnd_1876857 : Nat := 4983230072969 + 3 ^ 40 * 1876857 * 2
def baseEnd_1876857 : Nat := 214162169056815227123555

theorem tailTrace_1876857 : CollatzResearch.WordTrace tailWord_1876857 prefixEnd_1876857 214162169056815227123555 := by
  unfold tailWord_1876857
  simp only [CollatzResearch.WordTrace]
  refine ⟨68454598561475105501084825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45636399040983403667389883 68454598561475105501084825)
  ·
    refine ⟨51340948921106329125813619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68454598561475105501084825 51340948921106329125813619)
    ·
      refine ⟨77011423381659493688720429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51340948921106329125813619 77011423381659493688720429)
      ·
        refine ⟨28879283768122310133270161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77011423381659493688720429 28879283768122310133270161)
        ·
          refine ⟨21659462826091732599952621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28879283768122310133270161 21659462826091732599952621)
          ·
            refine ⟨8122298559784399724982233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21659462826091732599952621 8122298559784399724982233)
            ·
              refine ⟨6091723919838299793736675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8122298559784399724982233 6091723919838299793736675)
              ·
                refine ⟨9137585879757449690605013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6091723919838299793736675 9137585879757449690605013)
                ·
                  refine ⟨214162169056815227123555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9137585879757449690605013 214162169056815227123555)
                  ·
                    rfl

theorem cell22_1876857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 2, 1, 7].length) (baseStart_1876857 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1876857 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1876857 prefixEnd_1876857 := by exact prefixLift 1876857
  have htrace : WordTrace (prefixWord ++ tailWord_1876857) baseStart_1876857 baseEnd_1876857 := by
    simpa [prefixWord, tailWord_1876857, baseEnd_1876857] using wordTrace_append hprefix tailTrace_1876857
  have hstable : (prefixWord ++ tailWord_1876857).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1876857).length < 2 ^ (prefixWord ++ tailWord_1876857).sum := by decide
  have hdescent : baseEnd_1876857 < baseStart_1876857 := by decide
  rcases family_descends (prefixWord ++ tailWord_1876857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1876861 : List Nat := [1, 4, 1, 1, 2, 1, 2, 6, 1, 3]
def baseStart_1876861 : Nat := 118140960795 + 1876861 * 2 ^ 59
def prefixEnd_1876861 : Nat := 4983230072969 + 3 ^ 40 * 1876861 * 2
def baseEnd_1876861 : Nat := 642487876452191004270653

theorem tailTrace_1876861 : CollatzResearch.WordTrace tailWord_1876861 prefixEnd_1876861 642487876452191004270653 := by
  unfold tailWord_1876861
  simp only [CollatzResearch.WordTrace]
  refine ⟨68454744453460614184230437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45636496302307076122820291 68454744453460614184230437)
  ·
    refine ⟨12835264585023865159543207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 68454744453460614184230437 12835264585023865159543207)
    ·
      refine ⟨19252896877535797739314811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12835264585023865159543207 19252896877535797739314811)
      ·
        refine ⟨28879345316303696608972217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19252896877535797739314811 28879345316303696608972217)
        ·
          refine ⟨21659508987227772456729163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28879345316303696608972217 21659508987227772456729163)
          ·
            refine ⟨32489263480841658685093745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21659508987227772456729163 32489263480841658685093745)
            ·
              refine ⟨24366947610631244013820309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32489263480841658685093745 24366947610631244013820309)
              ·
                refine ⟨1142200669248339563147827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 24366947610631244013820309 1142200669248339563147827)
                ·
                  refine ⟨1713301003872509344721741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1142200669248339563147827 1713301003872509344721741)
                  ·
                    refine ⟨642487876452191004270653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1713301003872509344721741 642487876452191004270653)
                    ·
                      rfl

theorem cell22_1876861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 6, 1, 3].length) (baseStart_1876861 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1876861 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1876861 prefixEnd_1876861 := by exact prefixLift 1876861
  have htrace : WordTrace (prefixWord ++ tailWord_1876861) baseStart_1876861 baseEnd_1876861 := by
    simpa [prefixWord, tailWord_1876861, baseEnd_1876861] using wordTrace_append hprefix tailTrace_1876861
  have hstable : (prefixWord ++ tailWord_1876861).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1876861).length < 2 ^ (prefixWord ++ tailWord_1876861).sum := by decide
  have hdescent : baseEnd_1876861 < baseStart_1876861 := by decide
  rcases family_descends (prefixWord ++ tailWord_1876861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1877116 : List Nat := [2, 2, 2, 1, 1, 3, 5, 6]
def baseStart_1877116 : Nat := 118140960795 + 1877116 * 2 ^ 59
def prefixEnd_1877116 : Nat := 4983230072969 + 3 ^ 40 * 1877116 * 2
def baseEnd_1877116 : Nat := 71397240907050593238319

theorem tailTrace_1877116 : CollatzResearch.WordTrace tailWord_1877116 prefixEnd_1877116 71397240907050593238319 := by
  unfold tailWord_1877116
  simp only [CollatzResearch.WordTrace]
  refine ⟨34232022533768396367381601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45642696711691195156508801 34232022533768396367381601)
  ·
    refine ⟨25674016900326297275536201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34232022533768396367381601 25674016900326297275536201)
    ·
      refine ⟨19255512675244722956652151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25674016900326297275536201 19255512675244722956652151)
      ·
        refine ⟨28883269012867084434978227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19255512675244722956652151 28883269012867084434978227)
        ·
          refine ⟨43324903519300626652467341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28883269012867084434978227 43324903519300626652467341)
          ·
            refine ⟨16246838819737734994675253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43324903519300626652467341 16246838819737734994675253)
            ·
              refine ⟨1523141139350412655750805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16246838819737734994675253 1523141139350412655750805)
              ·
                refine ⟨71397240907050593238319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1523141139350412655750805 71397240907050593238319)
                ·
                  rfl

theorem cell22_1877116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 5, 6].length) (baseStart_1877116 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1877116 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1877116 prefixEnd_1877116 := by exact prefixLift 1877116
  have htrace : WordTrace (prefixWord ++ tailWord_1877116) baseStart_1877116 baseEnd_1877116 := by
    simpa [prefixWord, tailWord_1877116, baseEnd_1877116] using wordTrace_append hprefix tailTrace_1877116
  have hstable : (prefixWord ++ tailWord_1877116).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1877116).length < 2 ^ (prefixWord ++ tailWord_1877116).sum := by decide
  have hdescent : baseEnd_1877116 < baseStart_1877116 := by decide
  rcases family_descends (prefixWord ++ tailWord_1877116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1877148 : List Nat := [2, 2, 3, 2, 1, 2, 1, 3, 3, 3]
def baseStart_1877148 : Nat := 118140960795 + 1877148 * 2 ^ 59
def prefixEnd_1877148 : Nat := 4983230072969 + 3 ^ 40 * 1877148 * 2
def baseEnd_1877148 : Nat := 642586122417417922344773

theorem tailTrace_1877148 : CollatzResearch.WordTrace tailWord_1877148 prefixEnd_1877148 642586122417417922344773 := by
  unfold tailWord_1877148
  simp only [CollatzResearch.WordTrace]
  refine ⟨34232606101710431099964049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45643474802280574799952065 34232606101710431099964049)
  ·
    refine ⟨25674454576282823324973037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34232606101710431099964049 25674454576282823324973037)
    ·
      refine ⟨9627920466106058746864889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25674454576282823324973037 9627920466106058746864889)
      ·
        refine ⟨7220940349579544060148667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9627920466106058746864889 7220940349579544060148667)
        ·
          refine ⟨10831410524369316090223001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7220940349579544060148667 10831410524369316090223001)
          ·
            refine ⟨8123557893276987067667251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10831410524369316090223001 8123557893276987067667251)
            ·
              refine ⟨12185336839915480601500877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8123557893276987067667251 12185336839915480601500877)
              ·
                refine ⟨4569501314968305225562829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12185336839915480601500877 4569501314968305225562829)
                ·
                  refine ⟨1713562993113114459586061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4569501314968305225562829 1713562993113114459586061)
                  ·
                    refine ⟨642586122417417922344773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1713562993113114459586061 642586122417417922344773)
                    ·
                      rfl

theorem cell22_1877148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 3, 3, 3].length) (baseStart_1877148 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1877148 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1877148 prefixEnd_1877148 := by exact prefixLift 1877148
  have htrace : WordTrace (prefixWord ++ tailWord_1877148) baseStart_1877148 baseEnd_1877148 := by
    simpa [prefixWord, tailWord_1877148, baseEnd_1877148] using wordTrace_append hprefix tailTrace_1877148
  have hstable : (prefixWord ++ tailWord_1877148).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1877148).length < 2 ^ (prefixWord ++ tailWord_1877148).sum := by decide
  have hdescent : baseEnd_1877148 < baseStart_1877148 := by decide
  rcases family_descends (prefixWord ++ tailWord_1877148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1877182 : List Nat := [4, 2, 1, 1, 3, 1, 3, 3, 1, 3]
def baseStart_1877182 : Nat := 118140960795 + 1877182 * 2 ^ 59
def prefixEnd_1877182 : Nat := 4983230072969 + 3 ^ 40 * 1877182 * 2
def baseEnd_1877182 : Nat := 642597761312253166994669

theorem tailTrace_1877182 : CollatzResearch.WordTrace tailWord_1877182 prefixEnd_1877182 642597761312253166994669 := by
  unfold tailWord_1877182
  simp only [CollatzResearch.WordTrace]
  refine ⟨8558306535662210750833225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45644301523531790671110533 8558306535662210750833225)
  ·
    refine ⟨6418729901746658063124919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8558306535662210750833225 6418729901746658063124919)
    ·
      refine ⟨9628094852619987094687379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6418729901746658063124919 9628094852619987094687379)
      ·
        refine ⟨14442142278929980642031069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9628094852619987094687379 14442142278929980642031069)
        ·
          refine ⟨5415803354598742740761651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14442142278929980642031069 5415803354598742740761651)
          ·
            refine ⟨8123705031898114111142477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5415803354598742740761651 8123705031898114111142477)
            ·
              refine ⟨3046389386961792791678429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8123705031898114111142477 3046389386961792791678429)
              ·
                refine ⟨1142396020110672296879411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3046389386961792791678429 1142396020110672296879411)
                ·
                  refine ⟨1713594030166008445319117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1142396020110672296879411 1713594030166008445319117)
                  ·
                    refine ⟨642597761312253166994669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1713594030166008445319117 642597761312253166994669)
                    ·
                      rfl

theorem cell22_1877182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 3, 3, 1, 3].length) (baseStart_1877182 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1877182 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1877182 prefixEnd_1877182 := by exact prefixLift 1877182
  have htrace : WordTrace (prefixWord ++ tailWord_1877182) baseStart_1877182 baseEnd_1877182 := by
    simpa [prefixWord, tailWord_1877182, baseEnd_1877182] using wordTrace_append hprefix tailTrace_1877182
  have hstable : (prefixWord ++ tailWord_1877182).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1877182).length < 2 ^ (prefixWord ++ tailWord_1877182).sum := by decide
  have hdescent : baseEnd_1877182 < baseStart_1877182 := by decide
  rcases family_descends (prefixWord ++ tailWord_1877182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1877281 : List Nat := [1, 2, 3, 2, 1, 1, 1, 1, 4, 6]
def baseStart_1877281 : Nat := 118140960795 + 1877281 * 2 ^ 59
def prefixEnd_1877281 : Nat := 4983230072969 + 3 ^ 40 * 1877281 * 2
def baseEnd_1877281 : Nat := 642631651035449908769365

theorem tailTrace_1877281 : CollatzResearch.WordTrace tailWord_1877281 prefixEnd_1877281 642631651035449908769365 := by
  unfold tailWord_1877281
  simp only [CollatzResearch.WordTrace]
  refine ⟨68470063111939025914519697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45646708741292683943013131 68470063111939025914519697)
  ·
    refine ⟨51352547333954269435889773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68470063111939025914519697 51352547333954269435889773)
    ·
      refine ⟨19257205250232851038458665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51352547333954269435889773 19257205250232851038458665)
      ·
        refine ⟨14442903937674638278843999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19257205250232851038458665 14442903937674638278843999)
        ·
          refine ⟨21664355906511957418265999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14442903937674638278843999 21664355906511957418265999)
          ·
            refine ⟨32496533859767936127398999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21664355906511957418265999 32496533859767936127398999)
            ·
              refine ⟨48744800789651904191098499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32496533859767936127398999 48744800789651904191098499)
              ·
                refine ⟨73117201184477856286647749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48744800789651904191098499 73117201184477856286647749)
                ·
                  refine ⟨13709475222089598053746453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 73117201184477856286647749 13709475222089598053746453)
                  ·
                    refine ⟨642631651035449908769365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13709475222089598053746453 642631651035449908769365)
                    ·
                      rfl

theorem cell22_1877281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 1, 4, 6].length) (baseStart_1877281 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1877281 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1877281 prefixEnd_1877281 := by exact prefixLift 1877281
  have htrace : WordTrace (prefixWord ++ tailWord_1877281) baseStart_1877281 baseEnd_1877281 := by
    simpa [prefixWord, tailWord_1877281, baseEnd_1877281] using wordTrace_append hprefix tailTrace_1877281
  have hstable : (prefixWord ++ tailWord_1877281).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1877281).length < 2 ^ (prefixWord ++ tailWord_1877281).sum := by decide
  have hdescent : baseEnd_1877281 < baseStart_1877281 := by decide
  rcases family_descends (prefixWord ++ tailWord_1877281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1877283 : List Nat := [1, 1, 1, 4, 2, 3, 1, 1, 5, 3]
def baseStart_1877283 : Nat := 118140960795 + 1877283 * 2 ^ 59
def prefixEnd_1877283 : Nat := 4983230072969 + 3 ^ 40 * 1877283 * 2
def baseEnd_1877283 : Nat := 642632335676322570219359

theorem tailTrace_1877283 : CollatzResearch.WordTrace tailWord_1877283 prefixEnd_1877283 642632335676322570219359 := by
  unfold tailWord_1877283
  simp only [CollatzResearch.WordTrace]
  refine ⟨68470136057931780256092503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45646757371954520170728335 68470136057931780256092503)
  ·
    refine ⟨102705204086897670384138755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68470136057931780256092503 102705204086897670384138755)
    ·
      refine ⟨154057806130346505576208133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102705204086897670384138755 154057806130346505576208133)
      ·
        refine ⟨28885838649439969795539025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 154057806130346505576208133 28885838649439969795539025)
        ·
          refine ⟨21664378987079977346654269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28885838649439969795539025 21664378987079977346654269)
          ·
            refine ⟨8124142120154991504995351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21664378987079977346654269 8124142120154991504995351)
            ·
              refine ⟨12186213180232487257493027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8124142120154991504995351 12186213180232487257493027)
              ·
                refine ⟨18279319770348730886239541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12186213180232487257493027 18279319770348730886239541)
                ·
                  refine ⟨1713686228470193520584957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 18279319770348730886239541 1713686228470193520584957)
                  ·
                    refine ⟨642632335676322570219359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1713686228470193520584957 642632335676322570219359)
                    ·
                      rfl

theorem cell22_1877283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 1, 5, 3].length) (baseStart_1877283 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1877283 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1877283 prefixEnd_1877283 := by exact prefixLift 1877283
  have htrace : WordTrace (prefixWord ++ tailWord_1877283) baseStart_1877283 baseEnd_1877283 := by
    simpa [prefixWord, tailWord_1877283, baseEnd_1877283] using wordTrace_append hprefix tailTrace_1877283
  have hstable : (prefixWord ++ tailWord_1877283).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1877283).length < 2 ^ (prefixWord ++ tailWord_1877283).sum := by decide
  have hdescent : baseEnd_1877283 < baseStart_1877283 := by decide
  rcases family_descends (prefixWord ++ tailWord_1877283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1877296 : List Nat := [2, 1, 1, 1, 2, 2, 4, 2, 7]
def baseStart_1877296 : Nat := 118140960795 + 1877296 * 2 ^ 59
def prefixEnd_1877296 : Nat := 4983230072969 + 3 ^ 40 * 1877296 * 2
def baseEnd_1877296 : Nat := 214212261947331623214773

theorem tailTrace_1877296 : CollatzResearch.WordTrace tailWord_1877296 prefixEnd_1877296 214212261947331623214773 := by
  unfold tailWord_1877296
  simp only [CollatzResearch.WordTrace]
  refine ⟨34235305103442341738157871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45647073471256455650877161 34235305103442341738157871)
  ·
    refine ⟨51352957655163512607236807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34235305103442341738157871 51352957655163512607236807)
    ·
      refine ⟨77029436482745268910855211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51352957655163512607236807 77029436482745268910855211)
      ·
        refine ⟨115544154724117903366282817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77029436482745268910855211 115544154724117903366282817)
        ·
          refine ⟨86658116043088427524712113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115544154724117903366282817 86658116043088427524712113)
          ·
            refine ⟨64993587032316320643534085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86658116043088427524712113 64993587032316320643534085)
            ·
              refine ⟨12186297568559310120662641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64993587032316320643534085 12186297568559310120662641)
              ·
                refine ⟨9139723176419482590496981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12186297568559310120662641 9139723176419482590496981)
                ·
                  refine ⟨214212261947331623214773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9139723176419482590496981 214212261947331623214773)
                  ·
                    rfl

theorem cell22_1877296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 2, 7].length) (baseStart_1877296 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1877296 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1877296 prefixEnd_1877296 := by exact prefixLift 1877296
  have htrace : WordTrace (prefixWord ++ tailWord_1877296) baseStart_1877296 baseEnd_1877296 := by
    simpa [prefixWord, tailWord_1877296, baseEnd_1877296] using wordTrace_append hprefix tailTrace_1877296
  have hstable : (prefixWord ++ tailWord_1877296).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1877296).length < 2 ^ (prefixWord ++ tailWord_1877296).sum := by decide
  have hdescent : baseEnd_1877296 < baseStart_1877296 := by decide
  rcases family_descends (prefixWord ++ tailWord_1877296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1877300 : List Nat := [2, 5, 1, 1, 1, 1, 1, 2, 5, 3]
def baseStart_1877300 : Nat := 118140960795 + 1877300 * 2 ^ 59
def prefixEnd_1877300 : Nat := 4983230072969 + 3 ^ 40 * 1877300 * 2
def baseEnd_1877300 : Nat := 642638155123740192544307

theorem tailTrace_1877300 : CollatzResearch.WordTrace tailWord_1877300 prefixEnd_1877300 642638155123740192544307 := by
  unfold tailWord_1877300
  simp only [CollatzResearch.WordTrace]
  refine ⟨34235378049435096079730677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45647170732580128106307569 34235378049435096079730677)
  ·
    refine ⟨3209566692134540257474751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 34235378049435096079730677 3209566692134540257474751)
    ·
      refine ⟨4814350038201810386212127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3209566692134540257474751 4814350038201810386212127)
      ·
        refine ⟨7221525057302715579318191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4814350038201810386212127 7221525057302715579318191)
        ·
          refine ⟨10832287585954073368977287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7221525057302715579318191 10832287585954073368977287)
          ·
            refine ⟨16248431378931110053465931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10832287585954073368977287 16248431378931110053465931)
            ·
              refine ⟨24372647068396665080198897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16248431378931110053465931 24372647068396665080198897)
              ·
                refine ⟨18279485301297498810149173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24372647068396665080198897 18279485301297498810149173)
                ·
                  refine ⟨1713701746996640513451485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 18279485301297498810149173 1713701746996640513451485)
                  ·
                    refine ⟨642638155123740192544307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1713701746996640513451485 642638155123740192544307)
                    ·
                      rfl

theorem cell22_1877300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 2, 5, 3].length) (baseStart_1877300 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1877300 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1877300 prefixEnd_1877300 := by exact prefixLift 1877300
  have htrace : WordTrace (prefixWord ++ tailWord_1877300) baseStart_1877300 baseEnd_1877300 := by
    simpa [prefixWord, tailWord_1877300, baseEnd_1877300] using wordTrace_append hprefix tailTrace_1877300
  have hstable : (prefixWord ++ tailWord_1877300).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1877300).length < 2 ^ (prefixWord ++ tailWord_1877300).sum := by decide
  have hdescent : baseEnd_1877300 < baseStart_1877300 := by decide
  rcases family_descends (prefixWord ++ tailWord_1877300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1877351 : List Nat := [1, 1, 5, 1, 5, 1, 1, 3, 1, 3]
def baseStart_1877351 : Nat := 118140960795 + 1877351 * 2 ^ 59
def prefixEnd_1877351 : Nat := 4983230072969 + 3 ^ 40 * 1877351 * 2
def baseEnd_1877351 : Nat := 642655613465993059519151

theorem tailTrace_1877351 : CollatzResearch.WordTrace tailWord_1877351 prefixEnd_1877351 642655613465993059519151 := by
  unfold tailWord_1877351
  simp only [CollatzResearch.WordTrace]
  refine ⟨68472616221685427869567907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45648410814456951913045271 68472616221685427869567907)
  ·
    refine ⟨102708924332528141804351861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68472616221685427869567907 102708924332528141804351861)
    ·
      refine ⟨9628961656174513294157987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 102708924332528141804351861 9628961656174513294157987)
      ·
        refine ⟨14443442484261769941236981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9628961656174513294157987 14443442484261769941236981)
        ·
          refine ⟨1354072732899540931990967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14443442484261769941236981 1354072732899540931990967)
          ·
            refine ⟨2031109099349311397986451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1354072732899540931990967 2031109099349311397986451)
            ·
              refine ⟨3046663649023967096979677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2031109099349311397986451 3046663649023967096979677)
              ·
                refine ⟨1142498868383987661367379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3046663649023967096979677 1142498868383987661367379)
                ·
                  refine ⟨1713748302575981492051069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1142498868383987661367379 1713748302575981492051069)
                  ·
                    refine ⟨642655613465993059519151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1713748302575981492051069 642655613465993059519151)
                    ·
                      rfl

theorem cell22_1877351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 5, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 5, 1, 1, 3, 1, 3].length) (baseStart_1877351 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1877351 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1877351 prefixEnd_1877351 := by exact prefixLift 1877351
  have htrace : WordTrace (prefixWord ++ tailWord_1877351) baseStart_1877351 baseEnd_1877351 := by
    simpa [prefixWord, tailWord_1877351, baseEnd_1877351] using wordTrace_append hprefix tailTrace_1877351
  have hstable : (prefixWord ++ tailWord_1877351).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1877351).length < 2 ^ (prefixWord ++ tailWord_1877351).sum := by decide
  have hdescent : baseEnd_1877351 < baseStart_1877351 := by decide
  rcases family_descends (prefixWord ++ tailWord_1877351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1877388 : List Nat := [2, 2, 1, 2, 1, 3, 1, 2, 4, 4]
def baseStart_1877388 : Nat := 118140960795 + 1877388 * 2 ^ 59
def prefixEnd_1877388 : Nat := 4983230072969 + 3 ^ 40 * 1877388 * 2
def baseEnd_1877388 : Nat := 642668279322137296344037

theorem tailTrace_1877388 : CollatzResearch.WordTrace tailWord_1877388 prefixEnd_1877388 642668279322137296344037 := by
  unfold tailWord_1877388
  simp only [CollatzResearch.WordTrace]
  refine ⟨34236982861275691594332409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45649310481700922125776545 34236982861275691594332409)
  ·
    refine ⟨25677737145956768695749307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34236982861275691594332409 25677737145956768695749307)
    ·
      refine ⟨38516605718935153043623961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25677737145956768695749307 38516605718935153043623961)
      ·
        refine ⟨28887454289201364782717971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38516605718935153043623961 28887454289201364782717971)
        ·
          refine ⟨43331181433802047174076957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28887454289201364782717971 43331181433802047174076957)
          ·
            refine ⟨16249193037675767690278859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43331181433802047174076957 16249193037675767690278859)
            ·
              refine ⟨24373789556513651535418289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16249193037675767690278859 24373789556513651535418289)
              ·
                refine ⟨18280342167385238651563717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24373789556513651535418289 18280342167385238651563717)
                ·
                  refine ⟨3427564156384732247168197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18280342167385238651563717 3427564156384732247168197)
                  ·
                    refine ⟨642668279322137296344037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3427564156384732247168197 642668279322137296344037)
                    ·
                      rfl

theorem cell22_1877388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 2, 4, 4].length) (baseStart_1877388 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1877388 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1877388 prefixEnd_1877388 := by exact prefixLift 1877388
  have htrace : WordTrace (prefixWord ++ tailWord_1877388) baseStart_1877388 baseEnd_1877388 := by
    simpa [prefixWord, tailWord_1877388, baseEnd_1877388] using wordTrace_append hprefix tailTrace_1877388
  have hstable : (prefixWord ++ tailWord_1877388).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1877388).length < 2 ^ (prefixWord ++ tailWord_1877388).sum := by decide
  have hdescent : baseEnd_1877388 < baseStart_1877388 := by decide
  rcases family_descends (prefixWord ++ tailWord_1877388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1877405 : List Nat := [1, 4, 2, 1, 3, 1, 1, 3, 2, 4]
def baseStart_1877405 : Nat := 118140960795 + 1877405 * 2 ^ 59
def prefixEnd_1877405 : Nat := 4983230072969 + 3 ^ 40 * 1877405 * 2
def baseEnd_1877405 : Nat := 642674098769554918668985

theorem tailTrace_1877405 : CollatzResearch.WordTrace tailWord_1877405 prefixEnd_1877405 642674098769554918668985 := by
  unfold tailWord_1877405
  simp only [CollatzResearch.WordTrace]
  refine ⟨68474585763489795092033669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45649723842326530061355779 68474585763489795092033669)
  ·
    refine ⟨12838984830654336579756313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 68474585763489795092033669 12838984830654336579756313)
    ·
      refine ⟨9629238622990752434817235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12838984830654336579756313 9629238622990752434817235)
      ·
        refine ⟨14443857934486128652225853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9629238622990752434817235 14443857934486128652225853)
        ·
          refine ⟨5416446725432298244584695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14443857934486128652225853 5416446725432298244584695)
          ·
            refine ⟨8124670088148447366877043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5416446725432298244584695 8124670088148447366877043)
            ·
              refine ⟨12187005132222671050315565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8124670088148447366877043 12187005132222671050315565)
              ·
                refine ⟨4570126924583501643868337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12187005132222671050315565 4570126924583501643868337)
                ·
                  refine ⟨3427595193437626232901253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4570126924583501643868337 3427595193437626232901253)
                  ·
                    refine ⟨642674098769554918668985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3427595193437626232901253 642674098769554918668985)
                    ·
                      rfl

theorem cell22_1877405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 3, 2, 4].length) (baseStart_1877405 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1877405 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1877405 prefixEnd_1877405 := by exact prefixLift 1877405
  have htrace : WordTrace (prefixWord ++ tailWord_1877405) baseStart_1877405 baseEnd_1877405 := by
    simpa [prefixWord, tailWord_1877405, baseEnd_1877405] using wordTrace_append hprefix tailTrace_1877405
  have hstable : (prefixWord ++ tailWord_1877405).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1877405).length < 2 ^ (prefixWord ++ tailWord_1877405).sum := by decide
  have hdescent : baseEnd_1877405 < baseStart_1877405 := by decide
  rcases family_descends (prefixWord ++ tailWord_1877405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1877452 : List Nat := [2, 2, 1, 4, 2, 2, 1, 2, 3, 3]
def baseStart_1877452 : Nat := 118140960795 + 1877452 * 2 ^ 59
def prefixEnd_1877452 : Nat := 4983230072969 + 3 ^ 40 * 1877452 * 2
def baseEnd_1877452 : Nat := 642690187830062462743841

theorem tailTrace_1877452 : CollatzResearch.WordTrace tailWord_1877452 prefixEnd_1877452 642690187830062462743841 := by
  unfold tailWord_1877452
  simp only [CollatzResearch.WordTrace]
  refine ⟨34238149997159761059497305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45650866662879681412663073 34238149997159761059497305)
  ·
    refine ⟨25678612497869820794622979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34238149997159761059497305 25678612497869820794622979)
    ·
      refine ⟨38517918746804731191934469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25678612497869820794622979 38517918746804731191934469)
      ·
        refine ⟨7222109765025887098487713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38517918746804731191934469 7222109765025887098487713)
        ·
          refine ⟨5416582323769415323865785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7222109765025887098487713 5416582323769415323865785)
          ·
            refine ⟨4062436742827061492899339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5416582323769415323865785 4062436742827061492899339)
            ·
              refine ⟨6093655114240592239349009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4062436742827061492899339 6093655114240592239349009)
              ·
                refine ⟨4570241335680444179511757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6093655114240592239349009 4570241335680444179511757)
                ·
                  refine ⟨1713840500880166567316909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4570241335680444179511757 1713840500880166567316909)
                  ·
                    refine ⟨642690187830062462743841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1713840500880166567316909 642690187830062462743841)
                    ·
                      rfl

theorem cell22_1877452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 1, 2, 3, 3].length) (baseStart_1877452 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1877452 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1877452 prefixEnd_1877452 := by exact prefixLift 1877452
  have htrace : WordTrace (prefixWord ++ tailWord_1877452) baseStart_1877452 baseEnd_1877452 := by
    simpa [prefixWord, tailWord_1877452, baseEnd_1877452] using wordTrace_append hprefix tailTrace_1877452
  have hstable : (prefixWord ++ tailWord_1877452).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1877452).length < 2 ^ (prefixWord ++ tailWord_1877452).sum := by decide
  have hdescent : baseEnd_1877452 < baseStart_1877452 := by decide
  rcases family_descends (prefixWord ++ tailWord_1877452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1877469 : List Nat := [1, 4, 3, 1, 1, 2, 1, 5, 1, 3]
def baseStart_1877469 : Nat := 118140960795 + 1877469 * 2 ^ 59
def prefixEnd_1877469 : Nat := 4983230072969 + 3 ^ 40 * 1877469 * 2
def baseEnd_1877469 : Nat := 642696007277480085068789

theorem tailTrace_1877469 : CollatzResearch.WordTrace tailWord_1877469 prefixEnd_1877469 642696007277480085068789 := by
  unfold tailWord_1877469
  simp only [CollatzResearch.WordTrace]
  refine ⟨68476920035257934022363461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45651280023505289348242307 68476920035257934022363461)
  ·
    refine ⟨12839422506610862629193149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 68476920035257934022363461 12839422506610862629193149)
    ·
      refine ⟨4814783439979073485947431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12839422506610862629193149 4814783439979073485947431)
      ·
        refine ⟨7222175159968610228921147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4814783439979073485947431 7222175159968610228921147)
        ·
          refine ⟨10833262739952915343381721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7222175159968610228921147 10833262739952915343381721)
          ·
            refine ⟨8124947054964686507536291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10833262739952915343381721 8124947054964686507536291)
            ·
              refine ⟨12187420582447029761304437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8124947054964686507536291 12187420582447029761304437)
              ·
                refine ⟨1142570679604409040122291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12187420582447029761304437 1142570679604409040122291)
                ·
                  refine ⟨1713856019406613560183437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1142570679604409040122291 1713856019406613560183437)
                  ·
                    refine ⟨642696007277480085068789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1713856019406613560183437 642696007277480085068789)
                    ·
                      rfl

theorem cell22_1877469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 5, 1, 3].length) (baseStart_1877469 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1877469 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1877469 prefixEnd_1877469 := by exact prefixLift 1877469
  have htrace : WordTrace (prefixWord ++ tailWord_1877469) baseStart_1877469 baseEnd_1877469 := by
    simpa [prefixWord, tailWord_1877469, baseEnd_1877469] using wordTrace_append hprefix tailTrace_1877469
  have hstable : (prefixWord ++ tailWord_1877469).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1877469).length < 2 ^ (prefixWord ++ tailWord_1877469).sum := by decide
  have hdescent : baseEnd_1877469 < baseStart_1877469 := by decide
  rcases family_descends (prefixWord ++ tailWord_1877469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1877544 : List Nat := [2, 1, 5, 2, 2, 2, 1, 1, 6]
def baseStart_1877544 : Nat := 118140960795 + 1877544 * 2 ^ 59
def prefixEnd_1877544 : Nat := 4983230072969 + 3 ^ 40 * 1877544 * 2
def baseEnd_1877544 : Nat := 214240560436734963147853

theorem tailTrace_1877544 : CollatzResearch.WordTrace tailWord_1877544 prefixEnd_1877544 214240560436734963147853 := by
  unfold tailWord_1877544
  simp only [CollatzResearch.WordTrace]
  refine ⟨34239827754993110915671843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45653103673324147887562457 34239827754993110915671843)
  ·
    refine ⟨51359741632489666373507765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34239827754993110915671843 51359741632489666373507765)
    ·
      refine ⟨4814975778045906222516353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 51359741632489666373507765 4814975778045906222516353)
      ·
        refine ⟨3611231833534429666887265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4814975778045906222516353 3611231833534429666887265)
        ·
          refine ⟨2708423875150822250165449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3611231833534429666887265 2708423875150822250165449)
          ·
            refine ⟨2031317906363116687624087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2708423875150822250165449 2031317906363116687624087)
            ·
              refine ⟨3046976859544675031436131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2031317906363116687624087 3046976859544675031436131)
              ·
                refine ⟨4570465289317012547154197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3046976859544675031436131 4570465289317012547154197)
                ·
                  refine ⟨214240560436734963147853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4570465289317012547154197 214240560436734963147853)
                  ·
                    rfl

theorem cell22_1877544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 2, 1, 1, 6].length) (baseStart_1877544 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1877544 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1877544 prefixEnd_1877544 := by exact prefixLift 1877544
  have htrace : WordTrace (prefixWord ++ tailWord_1877544) baseStart_1877544 baseEnd_1877544 := by
    simpa [prefixWord, tailWord_1877544, baseEnd_1877544] using wordTrace_append hprefix tailTrace_1877544
  have hstable : (prefixWord ++ tailWord_1877544).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1877544).length < 2 ^ (prefixWord ++ tailWord_1877544).sum := by decide
  have hdescent : baseEnd_1877544 < baseStart_1877544 := by decide
  rcases family_descends (prefixWord ++ tailWord_1877544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1877555 : List Nat := [1, 1, 1, 2, 4, 4, 2, 7]
def baseStart_1877555 : Nat := 118140960795 + 1877555 * 2 ^ 59
def prefixEnd_1877555 : Nat := 4983230072969 + 3 ^ 40 * 1877555 * 2
def baseEnd_1877555 : Nat := 71413938537222725268725

theorem tailTrace_1877555 : CollatzResearch.WordTrace tailWord_1877555 prefixEnd_1877555 71413938537222725268725 := by
  unfold tailWord_1877555
  simp only [CollatzResearch.WordTrace]
  refine ⟨68480056712946370709994119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45653371141964247139996079 68480056712946370709994119)
  ·
    refine ⟨102720085069419556064991179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68480056712946370709994119 102720085069419556064991179)
    ·
      refine ⟨154080127604129334097486769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102720085069419556064991179 154080127604129334097486769)
      ·
        refine ⟨115560095703097000573115077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154080127604129334097486769 115560095703097000573115077)
        ·
          refine ⟨21667517944330687607459077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 115560095703097000573115077 21667517944330687607459077)
          ·
            refine ⟨4062659614562003926398577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21667517944330687607459077 4062659614562003926398577)
            ·
              refine ⟨3046994710921502944798933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4062659614562003926398577 3046994710921502944798933)
              ·
                refine ⟨71413938537222725268725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3046994710921502944798933 71413938537222725268725)
                ·
                  rfl

theorem cell22_1877555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 2, 7].length) (baseStart_1877555 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1877555 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1877555 prefixEnd_1877555 := by exact prefixLift 1877555
  have htrace : WordTrace (prefixWord ++ tailWord_1877555) baseStart_1877555 baseEnd_1877555 := by
    simpa [prefixWord, tailWord_1877555, baseEnd_1877555] using wordTrace_append hprefix tailTrace_1877555
  have hstable : (prefixWord ++ tailWord_1877555).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1877555).length < 2 ^ (prefixWord ++ tailWord_1877555).sum := by decide
  have hdescent : baseEnd_1877555 < baseStart_1877555 := by decide
  rcases family_descends (prefixWord ++ tailWord_1877555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1877559 : List Nat := [1, 1, 3, 1, 2, 4, 4, 1, 2, 3]
def baseStart_1877559 : Nat := 118140960795 + 1877559 * 2 ^ 59
def prefixEnd_1877559 : Nat := 4983230072969 + 3 ^ 40 * 1877559 * 2
def baseEnd_1877559 : Nat := 642726816116749850318513

theorem tailTrace_1877559 : CollatzResearch.WordTrace tailWord_1877559 prefixEnd_1877559 642726816116749850318513 := by
  unfold tailWord_1877559
  simp only [CollatzResearch.WordTrace]
  refine ⟨68480202604931879393139731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45653468403287919595426487 68480202604931879393139731)
  ·
    refine ⟨102720303907397819089709597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68480202604931879393139731 102720303907397819089709597)
    ·
      refine ⟨38520113965274182158641099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102720303907397819089709597 38520113965274182158641099)
      ·
        refine ⟨57780170947911273237961649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38520113965274182158641099 57780170947911273237961649)
        ·
          refine ⟨43335128210933454928471237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57780170947911273237961649 43335128210933454928471237)
          ·
            refine ⟨8125336539550022799088357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43335128210933454928471237 8125336539550022799088357)
            ·
              refine ⟨1523500601165629274829067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8125336539550022799088357 1523500601165629274829067)
              ·
                refine ⟨2285250901748443912243601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1523500601165629274829067 2285250901748443912243601)
                ·
                  refine ⟨1713938176311332934182701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2285250901748443912243601 1713938176311332934182701)
                  ·
                    refine ⟨642726816116749850318513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1713938176311332934182701 642726816116749850318513)
                    ·
                      rfl

theorem cell22_1877559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 4, 1, 2, 3].length) (baseStart_1877559 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1877559 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1877559 prefixEnd_1877559 := by exact prefixLift 1877559
  have htrace : WordTrace (prefixWord ++ tailWord_1877559) baseStart_1877559 baseEnd_1877559 := by
    simpa [prefixWord, tailWord_1877559, baseEnd_1877559] using wordTrace_append hprefix tailTrace_1877559
  have hstable : (prefixWord ++ tailWord_1877559).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1877559).length < 2 ^ (prefixWord ++ tailWord_1877559).sum := by decide
  have hdescent : baseEnd_1877559 < baseStart_1877559 := by decide
  rcases family_descends (prefixWord ++ tailWord_1877559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1877692 : List Nat := [2, 2, 2, 3, 1, 2, 2, 1, 1, 6]
def baseStart_1877692 : Nat := 118140960795 + 1877692 * 2 ^ 59
def prefixEnd_1877692 : Nat := 4983230072969 + 3 ^ 40 * 1877692 * 2
def baseEnd_1877692 : Nat := 642772344734781836743105

theorem tailTrace_1877692 : CollatzResearch.WordTrace tailWord_1877692 prefixEnd_1877692 642772344734781836743105 := by
  unfold tailWord_1877692
  simp only [CollatzResearch.WordTrace]
  refine ⟨34242526756725021553865665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45656702342300028738487553 34242526756725021553865665)
  ·
    refine ⟨25681895067543766165399249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34242526756725021553865665 25681895067543766165399249)
    ·
      refine ⟨19261421300657824624049437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25681895067543766165399249 19261421300657824624049437)
      ·
        refine ⟨7223032987746684234018539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19261421300657824624049437 7223032987746684234018539)
        ·
          refine ⟨10834549481620026351027809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7223032987746684234018539 10834549481620026351027809)
          ·
            refine ⟨8125912111215019763270857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10834549481620026351027809 8125912111215019763270857)
            ·
              refine ⟨6094434083411264822453143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8125912111215019763270857 6094434083411264822453143)
              ·
                refine ⟨9141651125116897233679715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6094434083411264822453143 9141651125116897233679715)
                ·
                  refine ⟨13712476687675345850519573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9141651125116897233679715 13712476687675345850519573)
                  ·
                    refine ⟨642772344734781836743105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13712476687675345850519573 642772344734781836743105)
                    ·
                      rfl

theorem cell22_1877692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 2, 1, 1, 6].length) (baseStart_1877692 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1877692 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1877692 prefixEnd_1877692 := by exact prefixLift 1877692
  have htrace : WordTrace (prefixWord ++ tailWord_1877692) baseStart_1877692 baseEnd_1877692 := by
    simpa [prefixWord, tailWord_1877692, baseEnd_1877692] using wordTrace_append hprefix tailTrace_1877692
  have hstable : (prefixWord ++ tailWord_1877692).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1877692).length < 2 ^ (prefixWord ++ tailWord_1877692).sum := by decide
  have hdescent : baseEnd_1877692 < baseStart_1877692 := by decide
  rcases family_descends (prefixWord ++ tailWord_1877692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1877694 : List Nat := [4, 2, 1, 1, 2, 2, 1, 2, 4, 3]
def baseStart_1877694 : Nat := 118140960795 + 1877694 * 2 ^ 59
def prefixEnd_1877694 : Nat := 4983230072969 + 3 ^ 40 * 1877694 * 2
def baseEnd_1877694 : Nat := 642773029375654498193099

theorem tailTrace_1877694 : CollatzResearch.WordTrace tailWord_1877694 prefixEnd_1877694 642773029375654498193099 := by
  unfold tailWord_1877694
  simp only [CollatzResearch.WordTrace]
  refine ⟨8560640807430349681163017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45656750972961864966202757 8560640807430349681163017)
  ·
    refine ⟨6420480605572762260872263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8560640807430349681163017 6420480605572762260872263)
    ·
      refine ⟨9630720908359143391308395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6420480605572762260872263 9630720908359143391308395)
      ·
        refine ⟨14446081362538715086962593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9630720908359143391308395 14446081362538715086962593)
        ·
          refine ⟨10834561021904036315221945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14446081362538715086962593 10834561021904036315221945)
          ·
            refine ⟨8125920766428027236416459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10834561021904036315221945 8125920766428027236416459)
            ·
              refine ⟨12188881149642040854624689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8125920766428027236416459 12188881149642040854624689)
              ·
                refine ⟨9141660862231530640968517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12188881149642040854624689 9141660862231530640968517)
                ·
                  refine ⟨1714061411668411995181597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9141660862231530640968517 1714061411668411995181597)
                  ·
                    refine ⟨642773029375654498193099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1714061411668411995181597 642773029375654498193099)
                    ·
                      rfl

theorem cell22_1877694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 2, 4, 3].length) (baseStart_1877694 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1877694 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1877694 prefixEnd_1877694 := by exact prefixLift 1877694
  have htrace : WordTrace (prefixWord ++ tailWord_1877694) baseStart_1877694 baseEnd_1877694 := by
    simpa [prefixWord, tailWord_1877694, baseEnd_1877694] using wordTrace_append hprefix tailTrace_1877694
  have hstable : (prefixWord ++ tailWord_1877694).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1877694).length < 2 ^ (prefixWord ++ tailWord_1877694).sum := by decide
  have hdescent : baseEnd_1877694 < baseStart_1877694 := by decide
  rcases family_descends (prefixWord ++ tailWord_1877694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1877756 : List Nat := [2, 2, 2, 1, 3, 1, 2, 5, 1, 3]
def baseStart_1877756 : Nat := 118140960795 + 1877756 * 2 ^ 59
def prefixEnd_1877756 : Nat := 4983230072969 + 3 ^ 40 * 1877756 * 2
def baseEnd_1877756 : Nat := 642794253242707003142909

theorem tailTrace_1877756 : CollatzResearch.WordTrace tailWord_1877756 prefixEnd_1877756 642794253242707003142909 := by
  unfold tailWord_1877756
  simp only [CollatzResearch.WordTrace]
  refine ⟨34243693892609091019030561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45658258523478788025374081 34243693892609091019030561)
  ·
    refine ⟨25682770419456818264272921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34243693892609091019030561 25682770419456818264272921)
    ·
      refine ⟨19262077814592613698204691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25682770419456818264272921 19262077814592613698204691)
      ·
        refine ⟨28893116721888920547307037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19262077814592613698204691 28893116721888920547307037)
        ·
          refine ⟨10834918770708345205240139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28893116721888920547307037 10834918770708345205240139)
          ·
            refine ⟨16252378156062517807860209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10834918770708345205240139 16252378156062517807860209)
            ·
              refine ⟨12189283617046888355895157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16252378156062517807860209 12189283617046888355895157)
              ·
                refine ⟨1142745339098145783365171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12189283617046888355895157 1142745339098145783365171)
                ·
                  refine ⟨1714118008647218675047757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1142745339098145783365171 1714118008647218675047757)
                  ·
                    refine ⟨642794253242707003142909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1714118008647218675047757 642794253242707003142909)
                    ·
                      rfl

theorem cell22_1877756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 5, 1, 3].length) (baseStart_1877756 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1877756 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1877756 prefixEnd_1877756 := by exact prefixLift 1877756
  have htrace : WordTrace (prefixWord ++ tailWord_1877756) baseStart_1877756 baseEnd_1877756 := by
    simpa [prefixWord, tailWord_1877756, baseEnd_1877756] using wordTrace_append hprefix tailTrace_1877756
  have hstable : (prefixWord ++ tailWord_1877756).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1877756).length < 2 ^ (prefixWord ++ tailWord_1877756).sum := by decide
  have hdescent : baseEnd_1877756 < baseStart_1877756 := by decide
  rcases family_descends (prefixWord ++ tailWord_1877756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1877790 : List Nat := [4, 3, 2, 2, 1, 1, 1, 2, 3, 3]
def baseStart_1877790 : Nat := 118140960795 + 1877790 * 2 ^ 59
def prefixEnd_1877790 : Nat := 4983230072969 + 3 ^ 40 * 1877790 * 2
def baseEnd_1877790 : Nat := 642805892137542247792805

theorem tailTrace_1877790 : CollatzResearch.WordTrace tailWord_1877790 prefixEnd_1877790 642805892137542247792805 := by
  unfold tailWord_1877790
  simp only [CollatzResearch.WordTrace]
  refine ⟨8561078483386875730599853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45659085244730003896532549 8561078483386875730599853)
  ·
    refine ⟨3210404431270078398974945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8561078483386875730599853 3210404431270078398974945)
    ·
      refine ⟨2407803323452558799231209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3210404431270078398974945 2407803323452558799231209)
      ·
        refine ⟨1805852492589419099423407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2407803323452558799231209 1805852492589419099423407)
        ·
          refine ⟨2708778738884128649135111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1805852492589419099423407 2708778738884128649135111)
          ·
            refine ⟨4063168108326192973702667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2708778738884128649135111 4063168108326192973702667)
            ·
              refine ⟨6094752162489289460554001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4063168108326192973702667 6094752162489289460554001)
              ·
                refine ⟨4571064121866967095415501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6094752162489289460554001 4571064121866967095415501)
                ·
                  refine ⟨1714149045700112660780813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4571064121866967095415501 1714149045700112660780813)
                  ·
                    refine ⟨642805892137542247792805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1714149045700112660780813 642805892137542247792805)
                    ·
                      rfl

theorem cell22_1877790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 1, 2, 3, 3].length) (baseStart_1877790 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1877790 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1877790 prefixEnd_1877790 := by exact prefixLift 1877790
  have htrace : WordTrace (prefixWord ++ tailWord_1877790) baseStart_1877790 baseEnd_1877790 := by
    simpa [prefixWord, tailWord_1877790, baseEnd_1877790] using wordTrace_append hprefix tailTrace_1877790
  have hstable : (prefixWord ++ tailWord_1877790).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1877790).length < 2 ^ (prefixWord ++ tailWord_1877790).sum := by decide
  have hdescent : baseEnd_1877790 < baseStart_1877790 := by decide
  rcases family_descends (prefixWord ++ tailWord_1877790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1877797 : List Nat := [1, 3, 1, 2, 3, 2, 1, 1, 8]
def baseStart_1877797 : Nat := 118140960795 + 1877797 * 2 ^ 59
def prefixEnd_1877797 : Nat := 4983230072969 + 3 ^ 40 * 1877797 * 2
def baseEnd_1877797 : Nat := 214269429460198854289261

theorem tailTrace_1877797 : CollatzResearch.WordTrace tailWord_1877797 prefixEnd_1877797 214269429460198854289261 := by
  unfold tailWord_1877797
  simp only [CollatzResearch.WordTrace]
  refine ⟨68488883178069646040303645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45659255452046430693535763 68488883178069646040303645)
  ·
    refine ⟨25683331191776117265113867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68488883178069646040303645 25683331191776117265113867)
    ·
      refine ⟨38524996787664175897670801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25683331191776117265113867 38524996787664175897670801)
      ·
        refine ⟨28893747590748131923253101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38524996787664175897670801 28893747590748131923253101)
        ·
          refine ⟨10835155346530549471219913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28893747590748131923253101 10835155346530549471219913)
          ·
            refine ⟨8126366509897912103414935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10835155346530549471219913 8126366509897912103414935)
            ·
              refine ⟨12189549764846868155122403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8126366509897912103414935 12189549764846868155122403)
              ·
                refine ⟨18284324647270302232683605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12189549764846868155122403 18284324647270302232683605)
                ·
                  refine ⟨214269429460198854289261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 18284324647270302232683605 214269429460198854289261)
                  ·
                    rfl

theorem cell22_1877797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 1, 8].length) (baseStart_1877797 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1877797 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1877797 prefixEnd_1877797 := by exact prefixLift 1877797
  have htrace : WordTrace (prefixWord ++ tailWord_1877797) baseStart_1877797 baseEnd_1877797 := by
    simpa [prefixWord, tailWord_1877797, baseEnd_1877797] using wordTrace_append hprefix tailTrace_1877797
  have hstable : (prefixWord ++ tailWord_1877797).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1877797).length < 2 ^ (prefixWord ++ tailWord_1877797).sum := by decide
  have hdescent : baseEnd_1877797 < baseStart_1877797 := by decide
  rcases family_descends (prefixWord ++ tailWord_1877797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1877816 : List Nat := [2, 1, 2, 1, 3, 3, 4, 1, 1, 4]
def baseStart_1877816 : Nat := 118140960795 + 1877816 * 2 ^ 59
def prefixEnd_1877816 : Nat := 4983230072969 + 3 ^ 40 * 1877816 * 2
def baseEnd_1877816 : Nat := 642814792468886846642725

theorem tailTrace_1877816 : CollatzResearch.WordTrace tailWord_1877816 prefixEnd_1877816 642814792468886846642725 := by
  unfold tailWord_1877816
  simp only [CollatzResearch.WordTrace]
  refine ⟨34244788082500406142622651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45659717443333874856830201 34244788082500406142622651)
  ·
    refine ⟨51367182123750609213933977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34244788082500406142622651 51367182123750609213933977)
    ·
      refine ⟨38525386592812956910450483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51367182123750609213933977 38525386592812956910450483)
      ·
        refine ⟨57788079889219435365675725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38525386592812956910450483 57788079889219435365675725)
        ·
          refine ⟨21670529958457288262128397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57788079889219435365675725 21670529958457288262128397)
          ·
            refine ⟨8126448734421483098298149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21670529958457288262128397 8126448734421483098298149)
            ·
              refine ⟨1523709137704028080930903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8126448734421483098298149 1523709137704028080930903)
              ·
                refine ⟨2285563706556042121396355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1523709137704028080930903 2285563706556042121396355)
                ·
                  refine ⟨3428345559834063182094533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2285563706556042121396355 3428345559834063182094533)
                  ·
                    refine ⟨642814792468886846642725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3428345559834063182094533 642814792468886846642725)
                    ·
                      rfl

theorem cell22_1877816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 4, 1, 1, 4].length) (baseStart_1877816 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1877816 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1877816 prefixEnd_1877816 := by exact prefixLift 1877816
  have htrace : WordTrace (prefixWord ++ tailWord_1877816) baseStart_1877816 baseEnd_1877816 := by
    simpa [prefixWord, tailWord_1877816, baseEnd_1877816] using wordTrace_append hprefix tailTrace_1877816
  have hstable : (prefixWord ++ tailWord_1877816).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1877816).length < 2 ^ (prefixWord ++ tailWord_1877816).sum := by decide
  have hdescent : baseEnd_1877816 < baseStart_1877816 := by decide
  rcases family_descends (prefixWord ++ tailWord_1877816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1877829 : List Nat := [1, 3, 1, 1, 1, 2, 5, 1, 4, 3]
def baseStart_1877829 : Nat := 118140960795 + 1877829 * 2 ^ 59
def prefixEnd_1877829 : Nat := 4983230072969 + 3 ^ 40 * 1877829 * 2
def baseEnd_1877829 : Nat := 642819242634559146067685

theorem tailTrace_1877829 : CollatzResearch.WordTrace tailWord_1877829 prefixEnd_1877829 642819242634559146067685 := by
  unfold tailWord_1877829
  simp only [CollatzResearch.WordTrace]
  refine ⟨68490050313953715505468541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45660033542635810336979027 68490050313953715505468541)
  ·
    refine ⟨25683768867732643314550703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68490050313953715505468541 25683768867732643314550703)
    ·
      refine ⟨38525653301598964971826055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25683768867732643314550703 38525653301598964971826055)
      ·
        refine ⟨57788479952398447457739083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38525653301598964971826055 57788479952398447457739083)
        ·
          refine ⟨86682719928597671186608625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57788479952398447457739083 86682719928597671186608625)
          ·
            refine ⟨65012039946448253389956469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86682719928597671186608625 65012039946448253389956469)
            ·
              refine ⟨6094878744979523755308419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 65012039946448253389956469 6094878744979523755308419)
              ·
                refine ⟨9142318117469285632962629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6094878744979523755308419 9142318117469285632962629)
                ·
                  refine ⟨1714184647025491056180493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9142318117469285632962629 1714184647025491056180493)
                  ·
                    refine ⟨642819242634559146067685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1714184647025491056180493 642819242634559146067685)
                    ·
                      rfl

theorem cell22_1877829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 5, 1, 4, 3].length) (baseStart_1877829 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1877829 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1877829 prefixEnd_1877829 := by exact prefixLift 1877829
  have htrace : WordTrace (prefixWord ++ tailWord_1877829) baseStart_1877829 baseEnd_1877829 := by
    simpa [prefixWord, tailWord_1877829, baseEnd_1877829] using wordTrace_append hprefix tailTrace_1877829
  have hstable : (prefixWord ++ tailWord_1877829).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1877829).length < 2 ^ (prefixWord ++ tailWord_1877829).sum := by decide
  have hdescent : baseEnd_1877829 < baseStart_1877829 := by decide
  rcases family_descends (prefixWord ++ tailWord_1877829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1877844 : List Nat := [2, 4, 1, 1, 3, 1, 1, 2, 1, 6]
def baseStart_1877844 : Nat := 118140960795 + 1877844 * 2 ^ 59
def prefixEnd_1877844 : Nat := 4983230072969 + 3 ^ 40 * 1877844 * 2
def baseEnd_1877844 : Nat := 642824377441104106942639

theorem tailTrace_1877844 : CollatzResearch.WordTrace tailWord_1877844 prefixEnd_1877844 642824377441104106942639 := by
  unfold tailWord_1877844
  simp only [CollatzResearch.WordTrace]
  refine ⟨34245298704449686533632293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45660398272599582044843057 34245298704449686533632293)
  ·
    refine ⟨6420993507084316225056055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34245298704449686533632293 6420993507084316225056055)
    ·
      refine ⟨9631490260626474337584083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6420993507084316225056055 9631490260626474337584083)
      ·
        refine ⟨14447235390939711506376125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9631490260626474337584083 14447235390939711506376125)
        ·
          refine ⟨5417713271602391814891047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14447235390939711506376125 5417713271602391814891047)
          ·
            refine ⟨8126569907403587722336571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5417713271602391814891047 8126569907403587722336571)
            ·
              refine ⟨12189854861105381583504857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8126569907403587722336571 12189854861105381583504857)
              ·
                refine ⟨9142391145829036187628643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12189854861105381583504857 9142391145829036187628643)
                ·
                  refine ⟨13713586718743554281442965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9142391145829036187628643 13713586718743554281442965)
                  ·
                    refine ⟨642824377441104106942639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13713586718743554281442965 642824377441104106942639)
                    ·
                      rfl

theorem cell22_1877844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 2, 1, 6].length) (baseStart_1877844 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1877844 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1877844 prefixEnd_1877844 := by exact prefixLift 1877844
  have htrace : WordTrace (prefixWord ++ tailWord_1877844) baseStart_1877844 baseEnd_1877844 := by
    simpa [prefixWord, tailWord_1877844, baseEnd_1877844] using wordTrace_append hprefix tailTrace_1877844
  have hstable : (prefixWord ++ tailWord_1877844).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1877844).length < 2 ^ (prefixWord ++ tailWord_1877844).sum := by decide
  have hdescent : baseEnd_1877844 < baseStart_1877844 := by decide
  rcases family_descends (prefixWord ++ tailWord_1877844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1877857 : List Nat := [1, 2, 3, 1, 1, 1, 3, 1, 2, 7]
def baseStart_1877857 : Nat := 118140960795 + 1877857 * 2 ^ 59
def prefixEnd_1877857 : Nat := 4983230072969 + 3 ^ 40 * 1877857 * 2
def baseEnd_1877857 : Nat := 642828827606776406367599

theorem tailTrace_1877857 : CollatzResearch.WordTrace tailWord_1877857 prefixEnd_1877857 642828827606776406367599 := by
  unfold tailWord_1877857
  simp only [CollatzResearch.WordTrace]
  refine ⟨68491071557852276287487825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45660714371901517524991883 68491071557852276287487825)
  ·
    refine ⟨51368303668389207215615869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68491071557852276287487825 51368303668389207215615869)
    ·
      refine ⟨19263113875645952705855951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51368303668389207215615869 19263113875645952705855951)
      ·
        refine ⟨28894670813468929058783927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19263113875645952705855951 28894670813468929058783927)
        ·
          refine ⟨43342006220203393588175891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28894670813468929058783927 43342006220203393588175891)
          ·
            refine ⟨65013009330305090382263837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43342006220203393588175891 65013009330305090382263837)
            ·
              refine ⟨24379878498864408893348939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65013009330305090382263837 24379878498864408893348939)
              ·
                refine ⟨36569817748296613340023409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24379878498864408893348939 36569817748296613340023409)
                ·
                  refine ⟨27427363311222460005017557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36569817748296613340023409 27427363311222460005017557)
                  ·
                    refine ⟨642828827606776406367599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 27427363311222460005017557 642828827606776406367599)
                    ·
                      rfl

theorem cell22_1877857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 1, 2, 7].length) (baseStart_1877857 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1877857 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1877857 prefixEnd_1877857 := by exact prefixLift 1877857
  have htrace : WordTrace (prefixWord ++ tailWord_1877857) baseStart_1877857 baseEnd_1877857 := by
    simpa [prefixWord, tailWord_1877857, baseEnd_1877857] using wordTrace_append hprefix tailTrace_1877857
  have hstable : (prefixWord ++ tailWord_1877857).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1877857).length < 2 ^ (prefixWord ++ tailWord_1877857).sum := by decide
  have hdescent : baseEnd_1877857 < baseStart_1877857 := by decide
  rcases family_descends (prefixWord ++ tailWord_1877857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1877859 : List Nat := [1, 1, 1, 5, 4, 1, 1, 8]
def baseStart_1877859 : Nat := 118140960795 + 1877859 * 2 ^ 59
def prefixEnd_1877859 : Nat := 4983230072969 + 3 ^ 40 * 1877859 * 2
def baseEnd_1877859 : Nat := 71425501360849896424177

theorem tailTrace_1877859 : CollatzResearch.WordTrace tailWord_1877859 prefixEnd_1877859 71425501360849896424177 := by
  unfold tailWord_1877859
  simp only [CollatzResearch.WordTrace]
  refine ⟨68491144503845030629060631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45660763002563353752707087 68491144503845030629060631)
  ·
    refine ⟨102736716755767545943590947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68491144503845030629060631 102736716755767545943590947)
    ·
      refine ⟨154105075133651318915386421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102736716755767545943590947 154105075133651318915386421)
      ·
        refine ⟨14447350793779811148317477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 154105075133651318915386421 14447350793779811148317477)
        ·
          refine ⟨2708878273833714590309527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14447350793779811148317477 2708878273833714590309527)
          ·
            refine ⟨4063317410750571885464291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2708878273833714590309527 4063317410750571885464291)
            ·
              refine ⟨6094976116125857828196437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4063317410750571885464291 6094976116125857828196437)
              ·
                refine ⟨71425501360849896424177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6094976116125857828196437 71425501360849896424177)
                ·
                  rfl

theorem cell22_1877859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 1, 8].length) (baseStart_1877859 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1877859 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1877859 prefixEnd_1877859 := by exact prefixLift 1877859
  have htrace : WordTrace (prefixWord ++ tailWord_1877859) baseStart_1877859 baseEnd_1877859 := by
    simpa [prefixWord, tailWord_1877859, baseEnd_1877859] using wordTrace_append hprefix tailTrace_1877859
  have hstable : (prefixWord ++ tailWord_1877859).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1877859).length < 2 ^ (prefixWord ++ tailWord_1877859).sum := by decide
  have hdescent : baseEnd_1877859 < baseStart_1877859 := by decide
  rcases family_descends (prefixWord ++ tailWord_1877859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1877872 : List Nat := [2, 1, 1, 1, 4, 1, 1, 2, 1, 8]
def baseStart_1877872 : Nat := 118140960795 + 1877872 * 2 ^ 59
def prefixEnd_1877872 : Nat := 4983230072969 + 3 ^ 40 * 1877872 * 2
def baseEnd_1877872 : Nat := 642833962413321367242553

theorem tailTrace_1877872 : CollatzResearch.WordTrace tailWord_1877872 prefixEnd_1877872 642833962413321367242553 := by
  unfold tailWord_1877872
  simp only [CollatzResearch.WordTrace]
  refine ⟨34245809326398966924641935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45661079101865289232855913 34245809326398966924641935)
  ·
    refine ⟨51368713989598450386962903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34245809326398966924641935 51368713989598450386962903)
    ·
      refine ⟨77053070984397675580444355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51368713989598450386962903 77053070984397675580444355)
      ·
        refine ⟨115579606476596513370666533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77053070984397675580444355 115579606476596513370666533)
        ·
          refine ⟨21671176214361846256999975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 115579606476596513370666533 21671176214361846256999975)
          ·
            refine ⟨32506764321542769385499963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21671176214361846256999975 32506764321542769385499963)
            ·
              refine ⟨48760146482314154078249945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32506764321542769385499963 48760146482314154078249945)
              ·
                refine ⟨36570109861735615558687459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48760146482314154078249945 36570109861735615558687459)
                ·
                  refine ⟨54855164792603423338031189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36570109861735615558687459 54855164792603423338031189)
                  ·
                    refine ⟨642833962413321367242553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 54855164792603423338031189 642833962413321367242553)
                    ·
                      rfl

theorem cell22_1877872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 2, 1, 8].length) (baseStart_1877872 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1877872 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1877872 prefixEnd_1877872 := by exact prefixLift 1877872
  have htrace : WordTrace (prefixWord ++ tailWord_1877872) baseStart_1877872 baseEnd_1877872 := by
    simpa [prefixWord, tailWord_1877872, baseEnd_1877872] using wordTrace_append hprefix tailTrace_1877872
  have hstable : (prefixWord ++ tailWord_1877872).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1877872).length < 2 ^ (prefixWord ++ tailWord_1877872).sum := by decide
  have hdescent : baseEnd_1877872 < baseStart_1877872 := by decide
  rcases family_descends (prefixWord ++ tailWord_1877872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1877878 : List Nat := [5, 1, 1, 3, 2, 1, 1, 2, 2, 4]
def baseStart_1877878 : Nat := 118140960795 + 1877878 * 2 ^ 59
def prefixEnd_1877878 : Nat := 4983230072969 + 3 ^ 40 * 1877878 * 2
def baseEnd_1877878 : Nat := 642836016335939351592535

theorem tailTrace_1877878 : CollatzResearch.WordTrace tailWord_1877878 prefixEnd_1877878 642836016335939351592535 := by
  unfold tailWord_1877878
  simp only [CollatzResearch.WordTrace]
  refine ⟨4280739843173512304625143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 45661224993850797916001525 4280739843173512304625143)
  ·
    refine ⟨6421109764760268456937715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4280739843173512304625143 6421109764760268456937715)
    ·
      refine ⟨9631664647140402685406573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6421109764760268456937715 9631664647140402685406573)
      ·
        refine ⟨3611874242677651007027465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9631664647140402685406573 3611874242677651007027465)
        ·
          refine ⟨2708905682008238255270599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3611874242677651007027465 2708905682008238255270599)
          ·
            refine ⟨4063358523012357382905899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2708905682008238255270599 4063358523012357382905899)
            ·
              refine ⟨6095037784518536074358849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4063358523012357382905899 6095037784518536074358849)
              ·
                refine ⟨4571278338388902055769137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6095037784518536074358849 4571278338388902055769137)
                ·
                  refine ⟨3428458753791676541826853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4571278338388902055769137 3428458753791676541826853)
                  ·
                    refine ⟨642836016335939351592535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3428458753791676541826853 642836016335939351592535)
                    ·
                      rfl

theorem cell22_1877878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 1, 2, 2, 4].length) (baseStart_1877878 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1877878 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1877878 prefixEnd_1877878 := by exact prefixLift 1877878
  have htrace : WordTrace (prefixWord ++ tailWord_1877878) baseStart_1877878 baseEnd_1877878 := by
    simpa [prefixWord, tailWord_1877878, baseEnd_1877878] using wordTrace_append hprefix tailTrace_1877878
  have hstable : (prefixWord ++ tailWord_1877878).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1877878).length < 2 ^ (prefixWord ++ tailWord_1877878).sum := by decide
  have hdescent : baseEnd_1877878 < baseStart_1877878 := by decide
  rcases family_descends (prefixWord ++ tailWord_1877878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1877891 : List Nat := [1, 1, 1, 3, 4, 2, 3, 1, 3, 3]
def baseStart_1877891 : Nat := 118140960795 + 1877891 * 2 ^ 59
def prefixEnd_1877891 : Nat := 4983230072969 + 3 ^ 40 * 1877891 * 2
def baseEnd_1877891 : Nat := 642840466501611651017495

theorem tailTrace_1877891 : CollatzResearch.WordTrace tailWord_1877891 prefixEnd_1877891 642840466501611651017495 := by
  unfold tailWord_1877891
  simp only [CollatzResearch.WordTrace]
  refine ⟨68492311639729100094225527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45661541093152733396150351 68492311639729100094225527)
  ·
    refine ⟨102738467459593650141338291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68492311639729100094225527 102738467459593650141338291)
    ·
      refine ⟨154107701189390475212007437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102738467459593650141338291 154107701189390475212007437)
      ·
        refine ⟨57790387946021428204502789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 154107701189390475212007437 57790387946021428204502789)
        ·
          refine ⟨10835697739879017788344273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57790387946021428204502789 10835697739879017788344273)
          ·
            refine ⟨8126773304909263341258205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10835697739879017788344273 8126773304909263341258205)
            ·
              refine ⟨3047539989340973752971827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8126773304909263341258205 3047539989340973752971827)
              ·
                refine ⟨4571309984011460629457741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3047539989340973752971827 4571309984011460629457741)
                ·
                  refine ⟨1714241244004297736046653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4571309984011460629457741 1714241244004297736046653)
                  ·
                    refine ⟨642840466501611651017495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1714241244004297736046653 642840466501611651017495)
                    ·
                      rfl

theorem cell22_1877891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 3, 1, 3, 3].length) (baseStart_1877891 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1877891 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1877891 prefixEnd_1877891 := by exact prefixLift 1877891
  have htrace : WordTrace (prefixWord ++ tailWord_1877891) baseStart_1877891 baseEnd_1877891 := by
    simpa [prefixWord, tailWord_1877891, baseEnd_1877891] using wordTrace_append hprefix tailTrace_1877891
  have hstable : (prefixWord ++ tailWord_1877891).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1877891).length < 2 ^ (prefixWord ++ tailWord_1877891).sum := by decide
  have hdescent : baseEnd_1877891 < baseStart_1877891 := by decide
  rcases family_descends (prefixWord ++ tailWord_1877891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1877983 : List Nat := [1, 1, 2, 3, 4, 2, 2, 3, 4]
def baseStart_1877983 : Nat := 118140960795 + 1877983 * 2 ^ 59
def prefixEnd_1877983 : Nat := 4983230072969 + 3 ^ 40 * 1877983 * 2
def baseEnd_1877983 : Nat := 214290653327251359239071

theorem tailTrace_1877983 : CollatzResearch.WordTrace tailWord_1877983 prefixEnd_1877983 214290653327251359239071 := by
  unfold tailWord_1877983
  simp only [CollatzResearch.WordTrace]
  refine ⟨68495667155395799806574603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45663778103597199871049735 68495667155395799806574603)
  ·
    refine ⟨102743500733093699709861905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68495667155395799806574603 102743500733093699709861905)
    ·
      refine ⟨77057625549820274782396429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102743500733093699709861905 77057625549820274782396429)
      ·
        refine ⟨28896609581182603043398661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77057625549820274782396429 28896609581182603043398661)
        ·
          refine ⟨5418114296471738070637249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28896609581182603043398661 5418114296471738070637249)
          ·
            refine ⟨4063585722353803552977937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5418114296471738070637249 4063585722353803552977937)
            ·
              refine ⟨3047689291765352664733453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4063585722353803552977937 3047689291765352664733453)
              ·
                refine ⟨1142883484412007249275045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3047689291765352664733453 1142883484412007249275045)
                ·
                  refine ⟨214290653327251359239071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1142883484412007249275045 214290653327251359239071)
                  ·
                    rfl

theorem cell22_1877983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 2, 3, 4].length) (baseStart_1877983 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1877983 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1877983 prefixEnd_1877983 := by exact prefixLift 1877983
  have htrace : WordTrace (prefixWord ++ tailWord_1877983) baseStart_1877983 baseEnd_1877983 := by
    simpa [prefixWord, tailWord_1877983, baseEnd_1877983] using wordTrace_append hprefix tailTrace_1877983
  have hstable : (prefixWord ++ tailWord_1877983).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1877983).length < 2 ^ (prefixWord ++ tailWord_1877983).sum := by decide
  have hdescent : baseEnd_1877983 < baseStart_1877983 := by decide
  rcases family_descends (prefixWord ++ tailWord_1877983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1877994 : List Nat := [3, 1, 3, 1, 2, 1, 11]
def baseStart_1877994 : Nat := 118140960795 + 1877994 * 2 ^ 59
def prefixEnd_1877994 : Nat := 4983230072969 + 3 ^ 40 * 1877994 * 2
def baseEnd_1877994 : Nat := 23810212055798285766377

theorem tailTrace_1877994 : CollatzResearch.WordTrace tailWord_1877994 prefixEnd_1877994 23810212055798285766377 := by
  unfold tailWord_1877994
  simp only [CollatzResearch.WordTrace]
  refine ⟨17124017089588987171306259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45664045572237299123483357 17124017089588987171306259)
  ·
    refine ⟨25686025634383480756959389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17124017089588987171306259 25686025634383480756959389)
    ·
      refine ⟨9632259612893805283859771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25686025634383480756959389 9632259612893805283859771)
      ·
        refine ⟨14448389419340707925789657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9632259612893805283859771 14448389419340707925789657)
        ·
          refine ⟨10836292064505530944342243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14448389419340707925789657 10836292064505530944342243)
          ·
            refine ⟨16254438096758296416513365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10836292064505530944342243 16254438096758296416513365)
            ·
              refine ⟨23810212055798285766377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 16254438096758296416513365 23810212055798285766377)
              ·
                rfl

theorem cell22_1877994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 11].length) (baseStart_1877994 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1877994 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1877994 prefixEnd_1877994 := by exact prefixLift 1877994
  have htrace : WordTrace (prefixWord ++ tailWord_1877994) baseStart_1877994 baseEnd_1877994 := by
    simpa [prefixWord, tailWord_1877994, baseEnd_1877994] using wordTrace_append hprefix tailTrace_1877994
  have hstable : (prefixWord ++ tailWord_1877994).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1877994).length < 2 ^ (prefixWord ++ tailWord_1877994).sum := by decide
  have hdescent : baseEnd_1877994 < baseStart_1877994 := by decide
  rcases family_descends (prefixWord ++ tailWord_1877994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1877998 : List Nat := [4, 1, 2, 1, 3, 2, 1, 1, 4, 3]
def baseStart_1877998 : Nat := 118140960795 + 1877998 * 2 ^ 59
def prefixEnd_1877998 : Nat := 4983230072969 + 3 ^ 40 * 1877998 * 2
def baseEnd_1877998 : Nat := 642877094788299038592167

theorem tailTrace_1877998 : CollatzResearch.WordTrace tailWord_1877998 prefixEnd_1877998 642877094788299038592167 := by
  unfold tailWord_1877998
  simp only [CollatzResearch.WordTrace]
  refine ⟨8562026781292682171046331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45664142833560971578913765 8562026781292682171046331)
  ·
    refine ⟨12843040171939023256569497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8562026781292682171046331 12843040171939023256569497)
    ·
      refine ⟨9632280128954267442427123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12843040171939023256569497 9632280128954267442427123)
      ·
        refine ⟨14448420193431401163640685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9632280128954267442427123 14448420193431401163640685)
        ·
          refine ⟨5418157572536775436365257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14448420193431401163640685 5418157572536775436365257)
          ·
            refine ⟨4063618179402581577273943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5418157572536775436365257 4063618179402581577273943)
            ·
              refine ⟨6095427269103872365910915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4063618179402581577273943 6095427269103872365910915)
              ·
                refine ⟨9143140903655808548866373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6095427269103872365910915 9143140903655808548866373)
                ·
                  refine ⟨1714338919435464102912445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9143140903655808548866373 1714338919435464102912445)
                  ·
                    refine ⟨642877094788299038592167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1714338919435464102912445 642877094788299038592167)
                    ·
                      rfl

theorem cell22_1877998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 1, 1, 4, 3].length) (baseStart_1877998 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1877998 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1877998 prefixEnd_1877998 := by exact prefixLift 1877998
  have htrace : WordTrace (prefixWord ++ tailWord_1877998) baseStart_1877998 baseEnd_1877998 := by
    simpa [prefixWord, tailWord_1877998, baseEnd_1877998] using wordTrace_append hprefix tailTrace_1877998
  have hstable : (prefixWord ++ tailWord_1877998).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1877998).length < 2 ^ (prefixWord ++ tailWord_1877998).sum := by decide
  have hdescent : baseEnd_1877998 < baseStart_1877998 := by decide
  rcases family_descends (prefixWord ++ tailWord_1877998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1878043 : List Nat := [1, 1, 1, 1, 1, 1, 3, 9, 1, 3]
def baseStart_1878043 : Nat := 118140960795 + 1878043 * 2 ^ 59
def prefixEnd_1878043 : Nat := 4983230072969 + 3 ^ 40 * 1878043 * 2
def baseEnd_1878043 : Nat := 642892499207933921217029

theorem tailTrace_1878043 : CollatzResearch.WordTrace tailWord_1878043 prefixEnd_1878043 642892499207933921217029 := by
  unfold tailWord_1878043
  simp only [CollatzResearch.WordTrace]
  refine ⟨68497855535178430053758783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45665237023452286702505855 68497855535178430053758783)
  ·
    refine ⟨102746783302767645080638175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68497855535178430053758783 102746783302767645080638175)
    ·
      refine ⟨154120174954151467620957263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102746783302767645080638175 154120174954151467620957263)
      ·
        refine ⟨231180262431227201431435895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154120174954151467620957263 231180262431227201431435895)
        ·
          refine ⟨346770393646840802147153843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 231180262431227201431435895 346770393646840802147153843)
          ·
            refine ⟨520155590470261203220730765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 346770393646840802147153843 520155590470261203220730765)
            ·
              refine ⟨195058346426347951207774037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 520155590470261203220730765 195058346426347951207774037)
              ·
                refine ⟨1142919998591882526608051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 195058346426347951207774037 1142919998591882526608051)
                ·
                  refine ⟨1714379997887823789912077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1142919998591882526608051 1714379997887823789912077)
                  ·
                    refine ⟨642892499207933921217029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1714379997887823789912077 642892499207933921217029)
                    ·
                      rfl

theorem cell22_1878043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 9, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 9, 1, 3].length) (baseStart_1878043 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1878043 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1878043 prefixEnd_1878043 := by exact prefixLift 1878043
  have htrace : WordTrace (prefixWord ++ tailWord_1878043) baseStart_1878043 baseEnd_1878043 := by
    simpa [prefixWord, tailWord_1878043, baseEnd_1878043] using wordTrace_append hprefix tailTrace_1878043
  have hstable : (prefixWord ++ tailWord_1878043).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1878043).length < 2 ^ (prefixWord ++ tailWord_1878043).sum := by decide
  have hdescent : baseEnd_1878043 < baseStart_1878043 := by decide
  rcases family_descends (prefixWord ++ tailWord_1878043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1878073 : List Nat := [1, 2, 1, 5, 3, 1, 1, 3, 5]
def baseStart_1878073 : Nat := 118140960795 + 1878073 * 2 ^ 59
def prefixEnd_1878073 : Nat := 4983230072969 + 3 ^ 40 * 1878073 * 2
def baseEnd_1878073 : Nat := 214300922940341280988979

theorem tailTrace_1878073 : CollatzResearch.WordTrace tailWord_1878073 prefixEnd_1878073 214300922940341280988979 := by
  unfold tailWord_1878073
  simp only [CollatzResearch.WordTrace]
  refine ⟨68498949725069745177350873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45665966483379830118233915 68498949725069745177350873)
  ·
    refine ⟨51374212293802308883013155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68498949725069745177350873 51374212293802308883013155)
    ·
      refine ⟨77061318440703463324519733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51374212293802308883013155 77061318440703463324519733)
      ·
        refine ⟨7224498603815949686673725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 77061318440703463324519733 7224498603815949686673725)
        ·
          refine ⟨2709186976430981132502647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7224498603815949686673725 2709186976430981132502647)
          ·
            refine ⟨4063780464646471698753971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2709186976430981132502647 4063780464646471698753971)
            ·
              refine ⟨6095670696969707548130957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4063780464646471698753971 6095670696969707548130957)
              ·
                refine ⟨2285876511363640330549109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6095670696969707548130957 2285876511363640330549109)
                ·
                  refine ⟨214300922940341280988979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2285876511363640330549109 214300922940341280988979)
                  ·
                    rfl

theorem cell22_1878073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 1, 3, 5].length) (baseStart_1878073 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1878073 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1878073 prefixEnd_1878073 := by exact prefixLift 1878073
  have htrace : WordTrace (prefixWord ++ tailWord_1878073) baseStart_1878073 baseEnd_1878073 := by
    simpa [prefixWord, tailWord_1878073, baseEnd_1878073] using wordTrace_append hprefix tailTrace_1878073
  have hstable : (prefixWord ++ tailWord_1878073).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1878073).length < 2 ^ (prefixWord ++ tailWord_1878073).sum := by decide
  have hdescent : baseEnd_1878073 < baseStart_1878073 := by decide
  rcases family_descends (prefixWord ++ tailWord_1878073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1878099 : List Nat := [1, 1, 1, 2, 1, 1, 2, 2, 2, 9]
def baseStart_1878099 : Nat := 118140960795 + 1878099 * 2 ^ 59
def prefixEnd_1878099 : Nat := 4983230072969 + 3 ^ 40 * 1878099 * 2
def baseEnd_1878099 : Nat := 642911669152368441816857

theorem tailTrace_1878099 : CollatzResearch.WordTrace tailWord_1878099 prefixEnd_1878099 642911669152368441816857 := by
  unfold tailWord_1878099
  simp only [CollatzResearch.WordTrace]
  refine ⟨68499898022975551617797351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45666598681983701078531567 68499898022975551617797351)
  ·
    refine ⟨102749847034463327426696027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68499898022975551617797351 102749847034463327426696027)
    ·
      refine ⟨154124770551694991140044041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102749847034463327426696027 154124770551694991140044041)
      ·
        refine ⟨115593577913771243355033031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154124770551694991140044041 115593577913771243355033031)
        ·
          refine ⟨173390366870656865032549547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115593577913771243355033031 173390366870656865032549547)
          ·
            refine ⟨260085550305985297548824321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173390366870656865032549547 260085550305985297548824321)
            ·
              refine ⟨195064162729488973161618241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 260085550305985297548824321 195064162729488973161618241)
              ·
                refine ⟨146298122047116729871213681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 195064162729488973161618241 146298122047116729871213681)
                ·
                  refine ⟨109723591535337547403410261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 146298122047116729871213681 109723591535337547403410261)
                  ·
                    refine ⟨642911669152368441816857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 109723591535337547403410261 642911669152368441816857)
                    ·
                      rfl

theorem cell22_1878099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 2, 2, 9].length) (baseStart_1878099 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1878099 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1878099 prefixEnd_1878099 := by exact prefixLift 1878099
  have htrace : WordTrace (prefixWord ++ tailWord_1878099) baseStart_1878099 baseEnd_1878099 := by
    simpa [prefixWord, tailWord_1878099, baseEnd_1878099] using wordTrace_append hprefix tailTrace_1878099
  have hstable : (prefixWord ++ tailWord_1878099).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1878099).length < 2 ^ (prefixWord ++ tailWord_1878099).sum := by decide
  have hdescent : baseEnd_1878099 < baseStart_1878099 := by decide
  rcases family_descends (prefixWord ++ tailWord_1878099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1878167 : List Nat := [1, 1, 3, 3, 4, 2, 1, 2, 2, 3]
def baseStart_1878167 : Nat := 118140960795 + 1878167 * 2 ^ 59
def prefixEnd_1878167 : Nat := 4983230072969 + 3 ^ 40 * 1878167 * 2
def baseEnd_1878167 : Nat := 642934946942038931116649

theorem tailTrace_1878167 : CollatzResearch.WordTrace tailWord_1878167 prefixEnd_1878167 642934946942038931116649 := by
  unfold tailWord_1878167
  simp only [CollatzResearch.WordTrace]
  refine ⟨68502378186729199231272755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45668252124486132820848503 68502378186729199231272755)
  ·
    refine ⟨102753567280093798846909133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68502378186729199231272755 102753567280093798846909133)
    ·
      refine ⟨38532587730035174567590925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102753567280093798846909133 38532587730035174567590925)
      ·
        refine ⟨14449720398763190462846597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38532587730035174567590925 14449720398763190462846597)
        ·
          refine ⟨2709322574768098211783737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14449720398763190462846597 2709322574768098211783737)
          ·
            refine ⟨2031991931076073658837803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2709322574768098211783737 2031991931076073658837803)
            ·
              refine ⟨3047987896614110488256705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2031991931076073658837803 3047987896614110488256705)
              ·
                refine ⟨2285990922460582866192529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3047987896614110488256705 2285990922460582866192529)
                ·
                  refine ⟨1714493191845437149644397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2285990922460582866192529 1714493191845437149644397)
                  ·
                    refine ⟨642934946942038931116649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1714493191845437149644397 642934946942038931116649)
                    ·
                      rfl

theorem cell22_1878167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 2, 1, 2, 2, 3].length) (baseStart_1878167 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1878167 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1878167 prefixEnd_1878167 := by exact prefixLift 1878167
  have htrace : WordTrace (prefixWord ++ tailWord_1878167) baseStart_1878167 baseEnd_1878167 := by
    simpa [prefixWord, tailWord_1878167, baseEnd_1878167] using wordTrace_append hprefix tailTrace_1878167
  have hstable : (prefixWord ++ tailWord_1878167).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1878167).length < 2 ^ (prefixWord ++ tailWord_1878167).sum := by decide
  have hdescent : baseEnd_1878167 < baseStart_1878167 := by decide
  rcases family_descends (prefixWord ++ tailWord_1878167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1878197 : List Nat := [1, 3, 3, 4, 1, 2, 2, 6]
def baseStart_1878197 : Nat := 118140960795 + 1878197 * 2 ^ 59
def prefixEnd_1878197 : Nat := 4983230072969 + 3 ^ 40 * 1878197 * 2
def baseEnd_1878197 : Nat := 71438357395014316985173

theorem tailTrace_1878197 : CollatzResearch.WordTrace tailWord_1878197 prefixEnd_1878197 71438357395014316985173 := by
  unfold tailWord_1878197
  simp only [CollatzResearch.WordTrace]
  refine ⟨68503472376620514354864845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45668981584413676236576563 68503472376620514354864845)
  ·
    refine ⟨25688802141232692883074317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68503472376620514354864845 25688802141232692883074317)
    ·
      refine ⟨9633300802962259831152869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25688802141232692883074317 9633300802962259831152869)
      ·
        refine ⟨1806243900555423718341163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9633300802962259831152869 1806243900555423718341163)
        ·
          refine ⟨2709365850833135577511745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1806243900555423718341163 2709365850833135577511745)
          ·
            refine ⟨2032024388124851683133809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2709365850833135577511745 2032024388124851683133809)
            ·
              refine ⟨1524018291093638762350357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2032024388124851683133809 1524018291093638762350357)
              ·
                refine ⟨71438357395014316985173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1524018291093638762350357 71438357395014316985173)
                ·
                  rfl

theorem cell22_1878197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 2, 2, 6].length) (baseStart_1878197 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1878197 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1878197 prefixEnd_1878197 := by exact prefixLift 1878197
  have htrace : WordTrace (prefixWord ++ tailWord_1878197) baseStart_1878197 baseEnd_1878197 := by
    simpa [prefixWord, tailWord_1878197, baseEnd_1878197] using wordTrace_append hprefix tailTrace_1878197
  have hstable : (prefixWord ++ tailWord_1878197).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1878197).length < 2 ^ (prefixWord ++ tailWord_1878197).sum := by decide
  have hdescent : baseEnd_1878197 < baseStart_1878197 := by decide
  rcases family_descends (prefixWord ++ tailWord_1878197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1878229 : List Nat := [1, 3, 2, 4, 3, 1, 1, 1, 3, 3]
def baseStart_1878229 : Nat := 118140960795 + 1878229 * 2 ^ 59
def prefixEnd_1878229 : Nat := 4983230072969 + 3 ^ 40 * 1878229 * 2
def baseEnd_1878229 : Nat := 642956170809091436066459

theorem tailTrace_1878229 : CollatzResearch.WordTrace tailWord_1878229 prefixEnd_1878229 642956170809091436066459 := by
  unfold tailWord_1878229
  simp only [CollatzResearch.WordTrace]
  refine ⟨68504639512504583820029741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45669759675003055880019827 68504639512504583820029741)
  ·
    refine ⟨25689239817189218932511153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68504639512504583820029741 25689239817189218932511153)
    ·
      refine ⟨19266929862891914199383365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25689239817189218932511153 19266929862891914199383365)
      ·
        refine ⟨3612549349292233912384381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19266929862891914199383365 3612549349292233912384381)
        ·
          refine ⟨1354706005984587717144143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3612549349292233912384381 1354706005984587717144143)
          ·
            refine ⟨2032059008976881575716215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1354706005984587717144143 2032059008976881575716215)
            ·
              refine ⟨3048088513465322363574323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2032059008976881575716215 3048088513465322363574323)
              ·
                refine ⟨4572132770197983545361485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3048088513465322363574323 4572132770197983545361485)
                ·
                  refine ⟨1714549788824243829510557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4572132770197983545361485 1714549788824243829510557)
                  ·
                    refine ⟨642956170809091436066459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1714549788824243829510557 642956170809091436066459)
                    ·
                      rfl

theorem cell22_1878229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 3, 1, 1, 1, 3, 3].length) (baseStart_1878229 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1878229 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1878229 prefixEnd_1878229 := by exact prefixLift 1878229
  have htrace : WordTrace (prefixWord ++ tailWord_1878229) baseStart_1878229 baseEnd_1878229 := by
    simpa [prefixWord, tailWord_1878229, baseEnd_1878229] using wordTrace_append hprefix tailTrace_1878229
  have hstable : (prefixWord ++ tailWord_1878229).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1878229).length < 2 ^ (prefixWord ++ tailWord_1878229).sum := by decide
  have hdescent : baseEnd_1878229 < baseStart_1878229 := by decide
  rcases family_descends (prefixWord ++ tailWord_1878229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1878255 : List Nat := [1, 1, 2, 1, 6, 1, 3, 2, 1, 4]
def baseStart_1878255 : Nat := 118140960795 + 1878255 * 2 ^ 59
def prefixEnd_1878255 : Nat := 4983230072969 + 3 ^ 40 * 1878255 * 2
def baseEnd_1878255 : Nat := 642965071140436034916379

theorem tailTrace_1878255 : CollatzResearch.WordTrace tailWord_1878255 prefixEnd_1878255 642965071140436034916379 := by
  unfold tailWord_1878255
  simp only [CollatzResearch.WordTrace]
  refine ⟨68505587810410390260476219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45670391873606926840317479 68505587810410390260476219)
  ·
    refine ⟨102758381715615585390714329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68505587810410390260476219 102758381715615585390714329)
    ·
      refine ⟨77068786286711689043035747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102758381715615585390714329 77068786286711689043035747)
      ·
        refine ⟨115603179430067533564553621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77068786286711689043035747 115603179430067533564553621)
        ·
          refine ⟨5418899035784415635838451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 115603179430067533564553621 5418899035784415635838451)
          ·
            refine ⟨8128348553676623453757677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5418899035784415635838451 8128348553676623453757677)
            ·
              refine ⟨3048130707628733795159129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8128348553676623453757677 3048130707628733795159129)
              ·
                refine ⟨2286098030721550346369347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3048130707628733795159129 2286098030721550346369347)
                ·
                  refine ⟨3429147046082325519554021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2286098030721550346369347 3429147046082325519554021)
                  ·
                    refine ⟨642965071140436034916379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3429147046082325519554021 642965071140436034916379)
                    ·
                      rfl

theorem cell22_1878255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 3, 2, 1, 4].length) (baseStart_1878255 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1878255 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1878255 prefixEnd_1878255 := by exact prefixLift 1878255
  have htrace : WordTrace (prefixWord ++ tailWord_1878255) baseStart_1878255 baseEnd_1878255 := by
    simpa [prefixWord, tailWord_1878255, baseEnd_1878255] using wordTrace_append hprefix tailTrace_1878255
  have hstable : (prefixWord ++ tailWord_1878255).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1878255).length < 2 ^ (prefixWord ++ tailWord_1878255).sum := by decide
  have hdescent : baseEnd_1878255 < baseStart_1878255 := by decide
  rcases family_descends (prefixWord ++ tailWord_1878255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1878268 : List Nat := [2, 2, 2, 1, 4, 1, 1, 1, 3, 5]
def baseStart_1878268 : Nat := 118140960795 + 1878268 * 2 ^ 59
def prefixEnd_1878268 : Nat := 4983230072969 + 3 ^ 40 * 1878268 * 2
def baseEnd_1878268 : Nat := 642969521306108334341339

theorem tailTrace_1878268 : CollatzResearch.WordTrace tailWord_1878268 prefixEnd_1878268 642969521306108334341339 := by
  unfold tailWord_1878268
  simp only [CollatzResearch.WordTrace]
  refine ⟨34253030979681646740349729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45670707972908862320466305 34253030979681646740349729)
  ·
    refine ⟨25689773234761235055262297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34253030979681646740349729 25689773234761235055262297)
    ·
      refine ⟨19267329926070926291446723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25689773234761235055262297 19267329926070926291446723)
      ·
        refine ⟨28900994889106389437170085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19267329926070926291446723 28900994889106389437170085)
        ·
          refine ⟨5418936541707448019469391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28900994889106389437170085 5418936541707448019469391)
          ·
            refine ⟨8128404812561172029204087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5418936541707448019469391 8128404812561172029204087)
            ·
              refine ⟨12192607218841758043806131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8128404812561172029204087 12192607218841758043806131)
              ·
                refine ⟨18288910828262637065709197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12192607218841758043806131 18288910828262637065709197)
                ·
                  refine ⟨6858341560598488899640949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18288910828262637065709197 6858341560598488899640949)
                  ·
                    refine ⟨642969521306108334341339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6858341560598488899640949 642969521306108334341339)
                    ·
                      rfl

theorem cell22_1878268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 1, 3, 5].length) (baseStart_1878268 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1878268 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1878268 prefixEnd_1878268 := by exact prefixLift 1878268
  have htrace : WordTrace (prefixWord ++ tailWord_1878268) baseStart_1878268 baseEnd_1878268 := by
    simpa [prefixWord, tailWord_1878268, baseEnd_1878268] using wordTrace_append hprefix tailTrace_1878268
  have hstable : (prefixWord ++ tailWord_1878268).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1878268).length < 2 ^ (prefixWord ++ tailWord_1878268).sum := by decide
  have hdescent : baseEnd_1878268 < baseStart_1878268 := by decide
  rcases family_descends (prefixWord ++ tailWord_1878268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1878281 : List Nat := [1, 2, 1, 1, 3, 14]
def baseStart_1878281 : Nat := 118140960795 + 1878281 * 2 ^ 59
def prefixEnd_1878281 : Nat := 4983230072969 + 3 ^ 40 * 1878281 * 2
def baseEnd_1878281 : Nat := 7937950265083711527979

theorem tailTrace_1878281 : CollatzResearch.WordTrace tailWord_1878281 prefixEnd_1878281 7937950265083711527979 := by
  unfold tailWord_1878281
  simp only [CollatzResearch.WordTrace]
  refine ⟨68506536108316196700922697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45671024072210797800615131 68506536108316196700922697)
  ·
    refine ⟨51379902081237147525692023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68506536108316196700922697 51379902081237147525692023)
    ·
      refine ⟨77069853121855721288538035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51379902081237147525692023 77069853121855721288538035)
      ·
        refine ⟨115604779682783581932807053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77069853121855721288538035 115604779682783581932807053)
        ·
          refine ⟨43351792381043843224802645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 115604779682783581932807053 43351792381043843224802645)
          ·
            refine ⟨7937950265083711527979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 14 43351792381043843224802645 7937950265083711527979)
            ·
              rfl

theorem cell22_1878281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 14].length) (baseStart_1878281 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1878281 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1878281 prefixEnd_1878281 := by exact prefixLift 1878281
  have htrace : WordTrace (prefixWord ++ tailWord_1878281) baseStart_1878281 baseEnd_1878281 := by
    simpa [prefixWord, tailWord_1878281, baseEnd_1878281] using wordTrace_append hprefix tailTrace_1878281
  have hstable : (prefixWord ++ tailWord_1878281).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1878281).length < 2 ^ (prefixWord ++ tailWord_1878281).sum := by decide
  have hdescent : baseEnd_1878281 < baseStart_1878281 := by decide
  rcases family_descends (prefixWord ++ tailWord_1878281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1878283 : List Nat := [1, 1, 1, 1, 5, 2, 1, 4, 2, 4]
def baseStart_1878283 : Nat := 118140960795 + 1878283 * 2 ^ 59
def prefixEnd_1878283 : Nat := 4983230072969 + 3 ^ 40 * 1878283 * 2
def baseEnd_1878283 : Nat := 642974656112653295216293

theorem tailTrace_1878283 : CollatzResearch.WordTrace tailWord_1878283 prefixEnd_1878283 642974656112653295216293 := by
  unfold tailWord_1878283
  simp only [CollatzResearch.WordTrace]
  refine ⟨68506609054308951042495503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45671072702872634028330335 68506609054308951042495503)
  ·
    refine ⟨102759913581463426563743255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68506609054308951042495503 102759913581463426563743255)
    ·
      refine ⟨154139870372195139845614883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102759913581463426563743255 154139870372195139845614883)
      ·
        refine ⟨231209805558292709768422325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154139870372195139845614883 231209805558292709768422325)
        ·
          refine ⟨21675919271089941540789593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 231209805558292709768422325 21675919271089941540789593)
          ·
            refine ⟨16256939453317456155592195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21675919271089941540789593 16256939453317456155592195)
            ·
              refine ⟨24385409179976184233388293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16256939453317456155592195 24385409179976184233388293)
              ·
                refine ⟨4572264221245534543760305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24385409179976184233388293 4572264221245534543760305)
                ·
                  refine ⟨3429198165934150907820229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4572264221245534543760305 3429198165934150907820229)
                  ·
                    refine ⟨642974656112653295216293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3429198165934150907820229 642974656112653295216293)
                    ·
                      rfl

theorem cell22_1878283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 4, 2, 4].length) (baseStart_1878283 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1878283 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1878283 prefixEnd_1878283 := by exact prefixLift 1878283
  have htrace : WordTrace (prefixWord ++ tailWord_1878283) baseStart_1878283 baseEnd_1878283 := by
    simpa [prefixWord, tailWord_1878283, baseEnd_1878283] using wordTrace_append hprefix tailTrace_1878283
  have hstable : (prefixWord ++ tailWord_1878283).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1878283).length < 2 ^ (prefixWord ++ tailWord_1878283).sum := by decide
  have hdescent : baseEnd_1878283 < baseStart_1878283 := by decide
  rcases family_descends (prefixWord ++ tailWord_1878283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1878302 : List Nat := [4, 3, 2, 1, 1, 1, 1, 3, 1, 5]
def baseStart_1878302 : Nat := 118140960795 + 1878302 * 2 ^ 59
def prefixEnd_1878302 : Nat := 4983230072969 + 3 ^ 40 * 1878302 * 2
def baseEnd_1878302 : Nat := 642981160200943578991235

theorem tailTrace_1878302 : CollatzResearch.WordTrace tailWord_1878302 prefixEnd_1878302 642981160200943578991235 := by
  unfold tailWord_1878302
  simp only [CollatzResearch.WordTrace]
  refine ⟨8563412755155014660929645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45671534694160078191624773 8563412755155014660929645)
  ·
    refine ⟨3211279783183130497848617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8563412755155014660929645 3211279783183130497848617)
    ·
      refine ⟨2408459837387347873386463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3211279783183130497848617 2408459837387347873386463)
      ·
        refine ⟨3612689756081021810079695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2408459837387347873386463 3612689756081021810079695)
        ·
          refine ⟨5419034634121532715119543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3612689756081021810079695 5419034634121532715119543)
          ·
            refine ⟨8128551951182299072679315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5419034634121532715119543 8128551951182299072679315)
            ·
              refine ⟨12192827926773448609018973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8128551951182299072679315 12192827926773448609018973)
              ·
                refine ⟨4572310472540043228382115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12192827926773448609018973 4572310472540043228382115)
                ·
                  refine ⟨6858465708810064842573173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4572310472540043228382115 6858465708810064842573173)
                  ·
                    refine ⟨642981160200943578991235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6858465708810064842573173 642981160200943578991235)
                    ·
                      rfl

theorem cell22_1878302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 3, 1, 5].length) (baseStart_1878302 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1878302 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1878302 prefixEnd_1878302 := by exact prefixLift 1878302
  have htrace : WordTrace (prefixWord ++ tailWord_1878302) baseStart_1878302 baseEnd_1878302 := by
    simpa [prefixWord, tailWord_1878302, baseEnd_1878302] using wordTrace_append hprefix tailTrace_1878302
  have hstable : (prefixWord ++ tailWord_1878302).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1878302).length < 2 ^ (prefixWord ++ tailWord_1878302).sum := by decide
  have hdescent : baseEnd_1878302 < baseStart_1878302 := by decide
  rcases family_descends (prefixWord ++ tailWord_1878302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1878317 : List Nat := [1, 5, 3, 1, 2, 1, 1, 1, 1, 6]
def baseStart_1878317 : Nat := 118140960795 + 1878317 * 2 ^ 59
def prefixEnd_1878317 : Nat := 4983230072969 + 3 ^ 40 * 1878317 * 2
def baseEnd_1878317 : Nat := 642986295007488539866189

theorem tailTrace_1878317 : CollatzResearch.WordTrace tailWord_1878317 prefixEnd_1878317 642986295007488539866189 := by
  unfold tailWord_1878317
  simp only [CollatzResearch.WordTrace]
  refine ⟨68507849136185774849233205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45671899424123849899488803 68507849136185774849233205)
  ·
    refine ⟨6422610856517416392115613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 68507849136185774849233205 6422610856517416392115613)
    ·
      refine ⟨2408479071194031147043355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6422610856517416392115613 2408479071194031147043355)
      ·
        refine ⟨3612718606791046720565033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2408479071194031147043355 3612718606791046720565033)
        ·
          refine ⟨2709538955093285040423775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3612718606791046720565033 2709538955093285040423775)
          ·
            refine ⟨4064308432639927560635663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2709538955093285040423775 4064308432639927560635663)
            ·
              refine ⟨6096462648959891340953495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4064308432639927560635663 6096462648959891340953495)
              ·
                refine ⟨9144693973439837011430243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6096462648959891340953495 9144693973439837011430243)
                ·
                  refine ⟨13717040960159755517145365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9144693973439837011430243 13717040960159755517145365)
                  ·
                    refine ⟨642986295007488539866189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13717040960159755517145365 642986295007488539866189)
                    ·
                      rfl

theorem cell22_1878317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 1, 1, 1, 6].length) (baseStart_1878317 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1878317 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1878317 prefixEnd_1878317 := by exact prefixLift 1878317
  have htrace : WordTrace (prefixWord ++ tailWord_1878317) baseStart_1878317 baseEnd_1878317 := by
    simpa [prefixWord, tailWord_1878317, baseEnd_1878317] using wordTrace_append hprefix tailTrace_1878317
  have hstable : (prefixWord ++ tailWord_1878317).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1878317).length < 2 ^ (prefixWord ++ tailWord_1878317).sum := by decide
  have hdescent : baseEnd_1878317 < baseStart_1878317 := by decide
  rcases family_descends (prefixWord ++ tailWord_1878317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1878343 : List Nat := [1, 1, 4, 1, 2, 2, 3, 1, 7]
def baseStart_1878343 : Nat := 118140960795 + 1878343 * 2 ^ 59
def prefixEnd_1878343 : Nat := 4983230072969 + 3 ^ 40 * 1878343 * 2
def baseEnd_1878343 : Nat := 214331731779611046238703

theorem tailTrace_1878343 : CollatzResearch.WordTrace tailWord_1878343 prefixEnd_1878343 214331731779611046238703 := by
  unfold tailWord_1878343
  simp only [CollatzResearch.WordTrace]
  refine ⟨68508797434091581289679683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45672531622727720859786455 68508797434091581289679683)
  ·
    refine ⟨102763196151137371934519525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68508797434091581289679683 102763196151137371934519525)
    ·
      refine ⟨19268099278338257237722411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 102763196151137371934519525 19268099278338257237722411)
      ·
        refine ⟨28902148917507385856583617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19268099278338257237722411 28902148917507385856583617)
        ·
          refine ⟨21676611688130539392437713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28902148917507385856583617 21676611688130539392437713)
          ·
            refine ⟨16257458766097904544328285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21676611688130539392437713 16257458766097904544328285)
            ·
              refine ⟨6096547037286714204123107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16257458766097904544328285 6096547037286714204123107)
              ·
                refine ⟨9144820555930071306184661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6096547037286714204123107 9144820555930071306184661)
                ·
                  refine ⟨214331731779611046238703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9144820555930071306184661 214331731779611046238703)
                  ·
                    rfl

theorem cell22_1878343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 3, 1, 7].length) (baseStart_1878343 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1878343 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1878343 prefixEnd_1878343 := by exact prefixLift 1878343
  have htrace : WordTrace (prefixWord ++ tailWord_1878343) baseStart_1878343 baseEnd_1878343 := by
    simpa [prefixWord, tailWord_1878343, baseEnd_1878343] using wordTrace_append hprefix tailTrace_1878343
  have hstable : (prefixWord ++ tailWord_1878343).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1878343).length < 2 ^ (prefixWord ++ tailWord_1878343).sum := by decide
  have hdescent : baseEnd_1878343 < baseStart_1878343 := by decide
  rcases family_descends (prefixWord ++ tailWord_1878343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1878366 : List Nat := [4, 4, 2, 1, 1, 1, 1, 8]
def baseStart_1878366 : Nat := 118140960795 + 1878366 * 2 ^ 59
def prefixEnd_1878366 : Nat := 4983230072969 + 3 ^ 40 * 1878366 * 2
def baseEnd_1878366 : Nat := 71444785412096527265671

theorem tailTrace_1878366 : CollatzResearch.WordTrace tailWord_1878366 prefixEnd_1878366 71444785412096527265671 := by
  unfold tailWord_1878366
  simp only [CollatzResearch.WordTrace]
  refine ⟨8563704539126032027220869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45673090875338837478511301 8563704539126032027220869)
  ·
    refine ⟨1605694601086131005103913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8563704539126032027220869 1605694601086131005103913)
    ·
      refine ⟨1204270950814598253827935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1605694601086131005103913 1204270950814598253827935)
      ·
        refine ⟨1806406426221897380741903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1204270950814598253827935 1806406426221897380741903)
        ·
          refine ⟨2709609639332846071112855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1806406426221897380741903 2709609639332846071112855)
          ·
            refine ⟨4064414458999269106669283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2709609639332846071112855 4064414458999269106669283)
            ·
              refine ⟨6096621688498903660003925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4064414458999269106669283 6096621688498903660003925)
              ·
                refine ⟨71444785412096527265671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6096621688498903660003925 71444785412096527265671)
                ·
                  rfl

theorem cell22_1878366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 1, 8].length) (baseStart_1878366 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1878366 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1878366 prefixEnd_1878366 := by exact prefixLift 1878366
  have htrace : WordTrace (prefixWord ++ tailWord_1878366) baseStart_1878366 baseEnd_1878366 := by
    simpa [prefixWord, tailWord_1878366, baseEnd_1878366] using wordTrace_append hprefix tailTrace_1878366
  have hstable : (prefixWord ++ tailWord_1878366).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1878366).length < 2 ^ (prefixWord ++ tailWord_1878366).sum := by decide
  have hdescent : baseEnd_1878366 < baseStart_1878366 := by decide
  rcases family_descends (prefixWord ++ tailWord_1878366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1878424 : List Nat := [2, 1, 2, 5, 1, 3, 1, 2, 1, 4]
def baseStart_1878424 : Nat := 118140960795 + 1878424 * 2 ^ 59
def prefixEnd_1878424 : Nat := 4983230072969 + 3 ^ 40 * 1878424 * 2
def baseEnd_1878424 : Nat := 643022923294175927440861

theorem tailTrace_1878424 : CollatzResearch.WordTrace tailWord_1878424 prefixEnd_1878424 643022923294175927440861 := by
  unfold tailWord_1878424
  simp only [CollatzResearch.WordTrace]
  refine ⟨34255875873399066061689163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45674501164532088082252217 34255875873399066061689163)
  ·
    refine ⟨51383813810098599092533745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34255875873399066061689163 51383813810098599092533745)
    ·
      refine ⟨38537860357573949319400309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51383813810098599092533745 38537860357573949319400309)
      ·
        refine ⟨3612924408522557748693779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 38537860357573949319400309 3612924408522557748693779)
        ·
          refine ⟨5419386612783836623040669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3612924408522557748693779 5419386612783836623040669)
          ·
            refine ⟨2032269979793938733640251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5419386612783836623040669 2032269979793938733640251)
            ·
              refine ⟨3048404969690908100460377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2032269979793938733640251 3048404969690908100460377)
              ·
                refine ⟨2286303727268181075345283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3048404969690908100460377 2286303727268181075345283)
                ·
                  refine ⟨3429455590902271613017925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2286303727268181075345283 3429455590902271613017925)
                  ·
                    refine ⟨643022923294175927440861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3429455590902271613017925 643022923294175927440861)
                    ·
                      rfl

theorem cell22_1878424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 3, 1, 2, 1, 4].length) (baseStart_1878424 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1878424 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1878424 prefixEnd_1878424 := by exact prefixLift 1878424
  have htrace : WordTrace (prefixWord ++ tailWord_1878424) baseStart_1878424 baseEnd_1878424 := by
    simpa [prefixWord, tailWord_1878424, baseEnd_1878424] using wordTrace_append hprefix tailTrace_1878424
  have hstable : (prefixWord ++ tailWord_1878424).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1878424).length < 2 ^ (prefixWord ++ tailWord_1878424).sum := by decide
  have hdescent : baseEnd_1878424 < baseStart_1878424 := by decide
  rcases family_descends (prefixWord ++ tailWord_1878424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1878435 : List Nat := [1, 1, 1, 4, 1, 4, 1, 3, 2, 4]
def baseStart_1878435 : Nat := 118140960795 + 1878435 * 2 ^ 59
def prefixEnd_1878435 : Nat := 4983230072969 + 3 ^ 40 * 1878435 * 2
def baseEnd_1878435 : Nat := 643026688818975565415827

theorem tailTrace_1878435 : CollatzResearch.WordTrace tailWord_1878435 prefixEnd_1878435 643026688818975565415827 := by
  unfold tailWord_1878435
  simp only [CollatzResearch.WordTrace]
  refine ⟨68512152949758281002028759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45674768633172187334685839 68512152949758281002028759)
  ·
    refine ⟨102768229424637421503043139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68512152949758281002028759 102768229424637421503043139)
    ·
      refine ⟨154152344136956132254564709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102768229424637421503043139 154152344136956132254564709)
      ·
        refine ⟨28903564525679274797730883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 154152344136956132254564709 28903564525679274797730883)
        ·
          refine ⟨43355346788518912196596325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28903564525679274797730883 43355346788518912196596325)
          ·
            refine ⟨8129127522847296036861811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43355346788518912196596325 8129127522847296036861811)
            ·
              refine ⟨12193691284270944055292717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8129127522847296036861811 12193691284270944055292717)
              ·
                refine ⟨4572634231601604020734769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12193691284270944055292717 4572634231601604020734769)
                ·
                  refine ⟨3429475673701203015551077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4572634231601604020734769 3429475673701203015551077)
                  ·
                    refine ⟨643026688818975565415827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3429475673701203015551077 643026688818975565415827)
                    ·
                      rfl

theorem cell22_1878435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 3, 2, 4].length) (baseStart_1878435 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1878435 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1878435 prefixEnd_1878435 := by exact prefixLift 1878435
  have htrace : WordTrace (prefixWord ++ tailWord_1878435) baseStart_1878435 baseEnd_1878435 := by
    simpa [prefixWord, tailWord_1878435, baseEnd_1878435] using wordTrace_append hprefix tailTrace_1878435
  have hstable : (prefixWord ++ tailWord_1878435).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1878435).length < 2 ^ (prefixWord ++ tailWord_1878435).sum := by decide
  have hdescent : baseEnd_1878435 < baseStart_1878435 := by decide
  rcases family_descends (prefixWord ++ tailWord_1878435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1878448 : List Nat := [2, 1, 1, 1, 2, 1, 1, 2, 4, 7]
def baseStart_1878448 : Nat := 118140960795 + 1878448 * 2 ^ 59
def prefixEnd_1878448 : Nat := 4983230072969 + 3 ^ 40 * 1878448 * 2
def baseEnd_1878448 : Nat := 643031138984647864840787

theorem tailTrace_1878448 : CollatzResearch.WordTrace tailWord_1878448 prefixEnd_1878448 643031138984647864840787 := by
  unfold tailWord_1878448
  simp only [CollatzResearch.WordTrace]
  refine ⟨34256313549355592111125999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45675084732474122814834665 34256313549355592111125999)
  ·
    refine ⟨51384470324033388166688999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34256313549355592111125999 51384470324033388166688999)
    ·
      refine ⟨77076705486050082250033499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51384470324033388166688999 77076705486050082250033499)
      ·
        refine ⟨115615058229075123375050249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77076705486050082250033499 115615058229075123375050249)
        ·
          refine ⟨86711293671806342531287687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115615058229075123375050249 86711293671806342531287687)
          ·
            refine ⟨130066940507709513796931531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86711293671806342531287687 130066940507709513796931531)
            ·
              refine ⟨195100410761564270695397297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130066940507709513796931531 195100410761564270695397297)
              ·
                refine ⟨146325308071173203021547973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 195100410761564270695397297 146325308071173203021547973)
                ·
                  refine ⟨27435995263344975566540245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 146325308071173203021547973 27435995263344975566540245)
                  ·
                    refine ⟨643031138984647864840787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 27435995263344975566540245 643031138984647864840787)
                    ·
                      rfl

theorem cell22_1878448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 4, 7].length) (baseStart_1878448 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1878448 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1878448 prefixEnd_1878448 := by exact prefixLift 1878448
  have htrace : WordTrace (prefixWord ++ tailWord_1878448) baseStart_1878448 baseEnd_1878448 := by
    simpa [prefixWord, tailWord_1878448, baseEnd_1878448] using wordTrace_append hprefix tailTrace_1878448
  have hstable : (prefixWord ++ tailWord_1878448).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1878448).length < 2 ^ (prefixWord ++ tailWord_1878448).sum := by decide
  have hdescent : baseEnd_1878448 < baseStart_1878448 := by decide
  rcases family_descends (prefixWord ++ tailWord_1878448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1878529 : List Nat := [1, 2, 4, 1, 3, 2, 3, 1, 5]
def baseStart_1878529 : Nat := 118140960795 + 1878529 * 2 ^ 59
def prefixEnd_1878529 : Nat := 4983230072969 + 3 ^ 40 * 1878529 * 2
def baseEnd_1878529 : Nat := 214352955646663551188513

theorem tailTrace_1878529 : CollatzResearch.WordTrace tailWord_1878529 prefixEnd_1878529 214352955646663551188513 := by
  unfold tailWord_1878529
  simp only [CollatzResearch.WordTrace]
  refine ⟨68515581411417735055950641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45677054274278490037300427 68515581411417735055950641)
  ·
    refine ⟨51386686058563301291962981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68515581411417735055950641 51386686058563301291962981)
    ·
      refine ⟨9635003635980618992243059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51386686058563301291962981 9635003635980618992243059)
      ·
        refine ⟨14452505453970928488364589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9635003635980618992243059 14452505453970928488364589)
        ·
          refine ⟨5419689545239098183136721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14452505453970928488364589 5419689545239098183136721)
          ·
            refine ⟨4064767158929323637352541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5419689545239098183136721 4064767158929323637352541)
            ·
              refine ⟨1524287684598496364007203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4064767158929323637352541 1524287684598496364007203)
              ·
                refine ⟨2286431526897744546010805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1524287684598496364007203 2286431526897744546010805)
                ·
                  refine ⟨214352955646663551188513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2286431526897744546010805 214352955646663551188513)
                  ·
                    rfl

theorem cell22_1878529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 3, 1, 5].length) (baseStart_1878529 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1878529 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1878529 prefixEnd_1878529 := by exact prefixLift 1878529
  have htrace : WordTrace (prefixWord ++ tailWord_1878529) baseStart_1878529 baseEnd_1878529 := by
    simpa [prefixWord, tailWord_1878529, baseEnd_1878529] using wordTrace_append hprefix tailTrace_1878529
  have hstable : (prefixWord ++ tailWord_1878529).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1878529).length < 2 ^ (prefixWord ++ tailWord_1878529).sum := by decide
  have hdescent : baseEnd_1878529 < baseStart_1878529 := by decide
  rcases family_descends (prefixWord ++ tailWord_1878529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1878580 : List Nat := [2, 5, 1, 3, 2, 1, 2, 1, 5]
def baseStart_1878580 : Nat := 118140960795 + 1878580 * 2 ^ 59
def prefixEnd_1878580 : Nat := 4983230072969 + 3 ^ 40 * 1878580 * 2
def baseEnd_1878580 : Nat := 214358775094081173513461

theorem tailTrace_1878580 : CollatzResearch.WordTrace tailWord_1878580 prefixEnd_1878580 214358775094081173513461 := by
  unfold tailWord_1878580
  simp only [CollatzResearch.WordTrace]
  refine ⟨34258720767116485383028597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45678294356155313844038129 34258720767116485383028597)
  ·
    refine ⟨3211755071917170504658931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 34258720767116485383028597 3211755071917170504658931)
    ·
      refine ⟨4817632607875755756988397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3211755071917170504658931 4817632607875755756988397)
      ·
        refine ⟨1806612227953408408870649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4817632607875755756988397 1806612227953408408870649)
        ·
          refine ⟨1354959170965056306652987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1806612227953408408870649 1354959170965056306652987)
          ·
            refine ⟨2032438756447584459979481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1354959170965056306652987 2032438756447584459979481)
            ·
              refine ⟨1524329067335688344984611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2032438756447584459979481 1524329067335688344984611)
              ·
                refine ⟨2286493601003532517476917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1524329067335688344984611 2286493601003532517476917)
                ·
                  refine ⟨214358775094081173513461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2286493601003532517476917 214358775094081173513461)
                  ·
                    rfl

theorem cell22_1878580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 2, 1, 2, 1, 5].length) (baseStart_1878580 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1878580 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1878580 prefixEnd_1878580 := by exact prefixLift 1878580
  have htrace : WordTrace (prefixWord ++ tailWord_1878580) baseStart_1878580 baseEnd_1878580 := by
    simpa [prefixWord, tailWord_1878580, baseEnd_1878580] using wordTrace_append hprefix tailTrace_1878580
  have hstable : (prefixWord ++ tailWord_1878580).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1878580).length < 2 ^ (prefixWord ++ tailWord_1878580).sum := by decide
  have hdescent : baseEnd_1878580 < baseStart_1878580 := by decide
  rcases family_descends (prefixWord ++ tailWord_1878580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1878600 : List Nat := [2, 1, 3, 1, 1, 1, 1, 3, 2, 7]
def baseStart_1878600 : Nat := 118140960795 + 1878600 * 2 ^ 59
def prefixEnd_1878600 : Nat := 4983230072969 + 3 ^ 40 * 1878600 * 2
def baseEnd_1878600 : Nat := 643083171690970135040321

theorem tailTrace_1878600 : CollatzResearch.WordTrace tailWord_1878600 prefixEnd_1878600 643083171690970135040321 := by
  unfold tailWord_1878600
  simp only [CollatzResearch.WordTrace]
  refine ⟨34259085497080257090892627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45678780662773676121190169 34259085497080257090892627)
  ·
    refine ⟨51388628245620385636338941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34259085497080257090892627 51388628245620385636338941)
    ·
      refine ⟨19270735592107644613627103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51388628245620385636338941 19270735592107644613627103)
      ·
        refine ⟨28906103388161466920440655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19270735592107644613627103 28906103388161466920440655)
        ·
          refine ⟨43359155082242200380660983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28906103388161466920440655 43359155082242200380660983)
          ·
            refine ⟨65038732623363300570991475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43359155082242200380660983 65038732623363300570991475)
            ·
              refine ⟨97558098935044950856487213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65038732623363300570991475 97558098935044950856487213)
              ·
                refine ⟨36584287100641856571182705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 97558098935044950856487213 36584287100641856571182705)
                ·
                  refine ⟨27438215325481392428387029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36584287100641856571182705 27438215325481392428387029)
                  ·
                    refine ⟨643083171690970135040321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 27438215325481392428387029 643083171690970135040321)
                    ·
                      rfl

theorem cell22_1878600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 3, 2, 7].length) (baseStart_1878600 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1878600 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1878600 prefixEnd_1878600 := by exact prefixLift 1878600
  have htrace : WordTrace (prefixWord ++ tailWord_1878600) baseStart_1878600 baseEnd_1878600 := by
    simpa [prefixWord, tailWord_1878600, baseEnd_1878600] using wordTrace_append hprefix tailTrace_1878600
  have hstable : (prefixWord ++ tailWord_1878600).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1878600).length < 2 ^ (prefixWord ++ tailWord_1878600).sum := by decide
  have hdescent : baseEnd_1878600 < baseStart_1878600 := by decide
  rcases family_descends (prefixWord ++ tailWord_1878600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1878634 : List Nat := [3, 1, 3, 2, 1, 1, 2, 3, 3, 3]
def baseStart_1878634 : Nat := 118140960795 + 1878634 * 2 ^ 59
def prefixEnd_1878634 : Nat := 4983230072969 + 3 ^ 40 * 1878634 * 2
def baseEnd_1878634 : Nat := 643094810585805379690217

theorem tailTrace_1878634 : CollatzResearch.WordTrace tailWord_1878634 prefixEnd_1878634 643094810585805379690217 := by
  unfold tailWord_1878634
  simp only [CollatzResearch.WordTrace]
  refine ⟨17129852769009334497130739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45679607384024891992348637 17129852769009334497130739)
  ·
    refine ⟨25694779153514001745696109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17129852769009334497130739 25694779153514001745696109)
    ·
      refine ⟨9635542182567750654636041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25694779153514001745696109 9635542182567750654636041)
      ·
        refine ⟨7226656636925812990977031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9635542182567750654636041 7226656636925812990977031)
        ·
          refine ⟨10839984955388719486465547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7226656636925812990977031 10839984955388719486465547)
          ·
            refine ⟨16259977433083079229698321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10839984955388719486465547 16259977433083079229698321)
            ·
              refine ⟨12194983074812309422273741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16259977433083079229698321 12194983074812309422273741)
              ·
                refine ⟨4573118653054616033352653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12194983074812309422273741 4573118653054616033352653)
                ·
                  refine ⟨1714919494895481012507245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4573118653054616033352653 1714919494895481012507245)
                  ·
                    refine ⟨643094810585805379690217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1714919494895481012507245 643094810585805379690217)
                    ·
                      rfl

theorem cell22_1878634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 3, 3, 3].length) (baseStart_1878634 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1878634 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1878634 prefixEnd_1878634 := by exact prefixLift 1878634
  have htrace : WordTrace (prefixWord ++ tailWord_1878634) baseStart_1878634 baseEnd_1878634 := by
    simpa [prefixWord, tailWord_1878634, baseEnd_1878634] using wordTrace_append hprefix tailTrace_1878634
  have hstable : (prefixWord ++ tailWord_1878634).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1878634).length < 2 ^ (prefixWord ++ tailWord_1878634).sum := by decide
  have hdescent : baseEnd_1878634 < baseStart_1878634 := by decide
  rcases family_descends (prefixWord ++ tailWord_1878634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1878647 : List Nat := [1, 1, 3, 1, 1, 3, 4, 3, 5]
def baseStart_1878647 : Nat := 118140960795 + 1878647 * 2 ^ 59
def prefixEnd_1878647 : Nat := 4983230072969 + 3 ^ 40 * 1878647 * 2
def baseEnd_1878647 : Nat := 214366420250492559705059

theorem tailTrace_1878647 : CollatzResearch.WordTrace tailWord_1878647 prefixEnd_1878647 214366420250492559705059 := by
  unfold tailWord_1878647
  simp only [CollatzResearch.WordTrace]
  refine ⟨68519885224990241208746195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45679923483326827472497463 68519885224990241208746195)
  ·
    refine ⟨102779827837485361813119293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68519885224990241208746195 102779827837485361813119293)
    ·
      refine ⟨38542435439057010679919735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102779827837485361813119293 38542435439057010679919735)
      ·
        refine ⟨57813653158585516019879603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38542435439057010679919735 57813653158585516019879603)
        ·
          refine ⟨86720479737878274029819405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57813653158585516019879603 86720479737878274029819405)
          ·
            refine ⟨32520179901704352761182277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86720479737878274029819405 32520179901704352761182277)
            ·
              refine ⟨6097533731569566142721677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32520179901704352761182277 6097533731569566142721677)
              ·
                refine ⟨2286575149338587303520629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6097533731569566142721677 2286575149338587303520629)
                ·
                  refine ⟨214366420250492559705059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2286575149338587303520629 214366420250492559705059)
                  ·
                    rfl

theorem cell22_1878647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 4, 3, 5].length) (baseStart_1878647 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1878647 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1878647 prefixEnd_1878647 := by exact prefixLift 1878647
  have htrace : WordTrace (prefixWord ++ tailWord_1878647) baseStart_1878647 baseEnd_1878647 := by
    simpa [prefixWord, tailWord_1878647, baseEnd_1878647] using wordTrace_append hprefix tailTrace_1878647
  have hstable : (prefixWord ++ tailWord_1878647).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1878647).length < 2 ^ (prefixWord ++ tailWord_1878647).sum := by decide
  have hdescent : baseEnd_1878647 < baseStart_1878647 := by decide
  rcases family_descends (prefixWord ++ tailWord_1878647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1878709 : List Nat := [1, 3, 3, 3, 1, 1, 2, 2, 6]
def baseStart_1878709 : Nat := 118140960795 + 1878709 * 2 ^ 59
def prefixEnd_1878709 : Nat := 4983230072969 + 3 ^ 40 * 1878709 * 2
def baseEnd_1878709 : Nat := 214373494872843394688329

theorem tailTrace_1878709 : CollatzResearch.WordTrace tailWord_1878709 prefixEnd_1878709 214373494872843394688329 := by
  unfold tailWord_1878709
  simp only [CollatzResearch.WordTrace]
  refine ⟨68522146550765625797503181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45681431033843750531668787 68522146550765625797503181)
  ·
    refine ⟨25695804956537109674063693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68522146550765625797503181 25695804956537109674063693)
    ·
      refine ⟨9635926858701416127773885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25695804956537109674063693 9635926858701416127773885)
      ·
        refine ⟨3613472572013031047915207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9635926858701416127773885 3613472572013031047915207)
        ·
          refine ⟨5420208858019546571872811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3613472572013031047915207 5420208858019546571872811)
          ·
            refine ⟨8130313287029319857809217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5420208858019546571872811 8130313287029319857809217)
            ·
              refine ⟨6097734965271989893356913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8130313287029319857809217 6097734965271989893356913)
              ·
                refine ⟨4573301223953992420017685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6097734965271989893356913 4573301223953992420017685)
                ·
                  refine ⟨214373494872843394688329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4573301223953992420017685 214373494872843394688329)
                  ·
                    rfl

theorem cell22_1878709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 2, 2, 6].length) (baseStart_1878709 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1878709 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1878709 prefixEnd_1878709 := by exact prefixLift 1878709
  have htrace : WordTrace (prefixWord ++ tailWord_1878709) baseStart_1878709 baseEnd_1878709 := by
    simpa [prefixWord, tailWord_1878709, baseEnd_1878709] using wordTrace_append hprefix tailTrace_1878709
  have hstable : (prefixWord ++ tailWord_1878709).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1878709).length < 2 ^ (prefixWord ++ tailWord_1878709).sum := by decide
  have hdescent : baseEnd_1878709 < baseStart_1878709 := by decide
  rcases family_descends (prefixWord ++ tailWord_1878709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1878711 : List Nat := [1, 1, 3, 1, 6, 1, 2, 2, 1, 4]
def baseStart_1878711 : Nat := 118140960795 + 1878711 * 2 ^ 59
def prefixEnd_1878711 : Nat := 4983230072969 + 3 ^ 40 * 1878711 * 2
def baseEnd_1878711 : Nat := 643121169259402845514981

theorem tailTrace_1878711 : CollatzResearch.WordTrace tailWord_1878711 prefixEnd_1878711 643121169259402845514981 := by
  unfold tailWord_1878711
  simp only [CollatzResearch.WordTrace]
  refine ⟨68522219496758380139075987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45681479664505586759383991 68522219496758380139075987)
  ·
    refine ⟨102783329245137570208613981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68522219496758380139075987 102783329245137570208613981)
    ·
      refine ⟨38543748466926588828230243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102783329245137570208613981 38543748466926588828230243)
      ·
        refine ⟨57815622700389883242345365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38543748466926588828230243 57815622700389883242345365)
        ·
          refine ⟨2710107314080775776984939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 57815622700389883242345365 2710107314080775776984939)
          ·
            refine ⟨4065160971121163665477409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2710107314080775776984939 4065160971121163665477409)
            ·
              refine ⟨3048870728340872749108057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4065160971121163665477409 3048870728340872749108057)
              ·
                refine ⟨2286653046255654561831043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3048870728340872749108057 2286653046255654561831043)
                ·
                  refine ⟨3429979569383481842746565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2286653046255654561831043 3429979569383481842746565)
                  ·
                    refine ⟨643121169259402845514981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3429979569383481842746565 643121169259402845514981)
                    ·
                      rfl

theorem cell22_1878711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 2, 2, 1, 4].length) (baseStart_1878711 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1878711 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1878711 prefixEnd_1878711 := by exact prefixLift 1878711
  have htrace : WordTrace (prefixWord ++ tailWord_1878711) baseStart_1878711 baseEnd_1878711 := by
    simpa [prefixWord, tailWord_1878711, baseEnd_1878711] using wordTrace_append hprefix tailTrace_1878711
  have hstable : (prefixWord ++ tailWord_1878711).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1878711).length < 2 ^ (prefixWord ++ tailWord_1878711).sum := by decide
  have hdescent : baseEnd_1878711 < baseStart_1878711 := by decide
  rcases family_descends (prefixWord ++ tailWord_1878711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1878769 : List Nat := [1, 2, 2, 2, 2, 2, 2, 1, 5, 3]
def baseStart_1878769 : Nat := 118140960795 + 1878769 * 2 ^ 59
def prefixEnd_1878769 : Nat := 4983230072969 + 3 ^ 40 * 1878769 * 2
def baseEnd_1878769 : Nat := 643141023844710027564803

theorem tailTrace_1878769 : CollatzResearch.WordTrace tailWord_1878769 prefixEnd_1878769 643141023844710027564803 := by
  unfold tailWord_1878769
  simp only [CollatzResearch.WordTrace]
  refine ⟨68524334930548256044687361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45682889953698837363124907 68524334930548256044687361)
  ·
    refine ⟨51393251197911192033515521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68524334930548256044687361 51393251197911192033515521)
    ·
      refine ⟨38544938398433394025136641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51393251197911192033515521 38544938398433394025136641)
      ·
        refine ⟨28908703798825045518852481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38544938398433394025136641 28908703798825045518852481)
        ·
          refine ⟨21681527849118784139139361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28908703798825045518852481 21681527849118784139139361)
          ·
            refine ⟨16261145886839088104354521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21681527849118784139139361 16261145886839088104354521)
            ·
              refine ⟨12195859415129316078265891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16261145886839088104354521 12195859415129316078265891)
              ·
                refine ⟨18293789122693974117398837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12195859415129316078265891 18293789122693974117398837)
                ·
                  refine ⟨1715042730252560073506141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 18293789122693974117398837 1715042730252560073506141)
                  ·
                    refine ⟨643141023844710027564803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1715042730252560073506141 643141023844710027564803)
                    ·
                      rfl

theorem cell22_1878769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 1, 5, 3].length) (baseStart_1878769 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1878769 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1878769 prefixEnd_1878769 := by exact prefixLift 1878769
  have htrace : WordTrace (prefixWord ++ tailWord_1878769) baseStart_1878769 baseEnd_1878769 := by
    simpa [prefixWord, tailWord_1878769, baseEnd_1878769] using wordTrace_append hprefix tailTrace_1878769
  have hstable : (prefixWord ++ tailWord_1878769).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1878769).length < 2 ^ (prefixWord ++ tailWord_1878769).sum := by decide
  have hdescent : baseEnd_1878769 < baseStart_1878769 := by decide
  rcases family_descends (prefixWord ++ tailWord_1878769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1878799 : List Nat := [1, 1, 2, 1, 1, 1, 8, 2, 5]
def baseStart_1878799 : Nat := 118140960795 + 1878799 * 2 ^ 59
def prefixEnd_1878799 : Nat := 4983230072969 + 3 ^ 40 * 1878799 * 2
def baseEnd_1878799 : Nat := 214383764485933316438237

theorem tailTrace_1878799 : CollatzResearch.WordTrace tailWord_1878799 prefixEnd_1878799 214383764485933316438237 := by
  unfold tailWord_1878799
  simp only [CollatzResearch.WordTrace]
  refine ⟨68525429120439571168279451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45683619413626380778852967 68525429120439571168279451)
  ·
    refine ⟨102788143680659356752419177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68525429120439571168279451 102788143680659356752419177)
    ·
      refine ⟨77091107760494517564314383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102788143680659356752419177 77091107760494517564314383)
      ·
        refine ⟨115636661640741776346471575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77091107760494517564314383 115636661640741776346471575)
        ·
          refine ⟨173454992461112664519707363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115636661640741776346471575 173454992461112664519707363)
          ·
            refine ⟨260182488691668996779561045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173454992461112664519707363 260182488691668996779561045)
            ·
              refine ⟨3049013539355496056010481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 260182488691668996779561045 3049013539355496056010481)
              ·
                refine ⟨2286760154516622042007861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3049013539355496056010481 2286760154516622042007861)
                ·
                  refine ⟨214383764485933316438237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2286760154516622042007861 214383764485933316438237)
                  ·
                    rfl

theorem cell22_1878799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 8, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 8, 2, 5].length) (baseStart_1878799 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1878799 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1878799 prefixEnd_1878799 := by exact prefixLift 1878799
  have htrace : WordTrace (prefixWord ++ tailWord_1878799) baseStart_1878799 baseEnd_1878799 := by
    simpa [prefixWord, tailWord_1878799, baseEnd_1878799] using wordTrace_append hprefix tailTrace_1878799
  have hstable : (prefixWord ++ tailWord_1878799).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1878799).length < 2 ^ (prefixWord ++ tailWord_1878799).sum := by decide
  have hdescent : baseEnd_1878799 < baseStart_1878799 := by decide
  rcases family_descends (prefixWord ++ tailWord_1878799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1878827 : List Nat := [1, 1, 1, 1, 2, 1, 2, 5, 8]
def baseStart_1878827 : Nat := 118140960795 + 1878827 * 2 ^ 59
def prefixEnd_1878827 : Nat := 4983230072969 + 3 ^ 40 * 1878827 * 2
def baseEnd_1878827 : Nat := 214386959476672403204875

theorem tailTrace_1878827 : CollatzResearch.WordTrace tailWord_1878827 prefixEnd_1878827 214386959476672403204875 := by
  unfold tailWord_1878827
  simp only [CollatzResearch.WordTrace]
  refine ⟨68526450364338131950298735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45684300242892087966865823 68526450364338131950298735)
  ·
    refine ⟨102789675546507197925448103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68526450364338131950298735 102789675546507197925448103)
    ·
      refine ⟨154184513319760796888172155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102789675546507197925448103 154184513319760796888172155)
      ·
        refine ⟨231276769979641195332258233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154184513319760796888172155 231276769979641195332258233)
        ·
          refine ⟨173457577484730896499193675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 231276769979641195332258233 173457577484730896499193675)
          ·
            refine ⟨260186366227096344748790513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173457577484730896499193675 260186366227096344748790513)
            ·
              refine ⟨195139774670322258561592885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 260186366227096344748790513 195139774670322258561592885)
              ·
                refine ⟨18294353875342711740149333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 195139774670322258561592885 18294353875342711740149333)
                ·
                  refine ⟨214386959476672403204875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 18294353875342711740149333 214386959476672403204875)
                  ·
                    rfl

theorem cell22_1878827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 5, 8].length) (baseStart_1878827 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1878827 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1878827 prefixEnd_1878827 := by exact prefixLift 1878827
  have htrace : WordTrace (prefixWord ++ tailWord_1878827) baseStart_1878827 baseEnd_1878827 := by
    simpa [prefixWord, tailWord_1878827, baseEnd_1878827] using wordTrace_append hprefix tailTrace_1878827
  have hstable : (prefixWord ++ tailWord_1878827).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1878827).length < 2 ^ (prefixWord ++ tailWord_1878827).sum := by decide
  have hdescent : baseEnd_1878827 < baseStart_1878827 := by decide
  rcases family_descends (prefixWord ++ tailWord_1878827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1878874 : List Nat := [3, 1, 1, 2, 1, 4, 1, 2, 1, 6]
def baseStart_1878874 : Nat := 118140960795 + 1878874 * 2 ^ 59
def prefixEnd_1878874 : Nat := 4983230072969 + 3 ^ 40 * 1878874 * 2
def baseEnd_1878874 : Nat := 643176967490524753689481

theorem tailTrace_1878874 : CollatzResearch.WordTrace tailWord_1878874 prefixEnd_1878874 643176967490524753689481 := by
  unfold tailWord_1878874
  simp only [CollatzResearch.WordTrace]
  refine ⟨17132041148791964744314919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45685443063445239318173117 17132041148791964744314919)
  ·
    refine ⟨25698061723187947116472379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17132041148791964744314919 25698061723187947116472379)
    ·
      refine ⟨38547092584781920674708569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25698061723187947116472379 38547092584781920674708569)
      ·
        refine ⟨28910319438586440506031427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38547092584781920674708569 28910319438586440506031427)
        ·
          refine ⟨43365479157879660759047141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28910319438586440506031427 43365479157879660759047141)
          ·
            refine ⟨8131027342102436392321339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43365479157879660759047141 8131027342102436392321339)
            ·
              refine ⟨12196541013153654588482009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8131027342102436392321339 12196541013153654588482009)
              ·
                refine ⟨9147405759865240941361507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12196541013153654588482009 9147405759865240941361507)
                ·
                  refine ⟨13721108639797861412042261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9147405759865240941361507 13721108639797861412042261)
                  ·
                    refine ⟨643176967490524753689481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13721108639797861412042261 643176967490524753689481)
                    ·
                      rfl

theorem cell22_1878874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 2, 1, 6].length) (baseStart_1878874 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1878874 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1878874 prefixEnd_1878874 := by exact prefixLift 1878874
  have htrace : WordTrace (prefixWord ++ tailWord_1878874) baseStart_1878874 baseEnd_1878874 := by
    simpa [prefixWord, tailWord_1878874, baseEnd_1878874] using wordTrace_append hprefix tailTrace_1878874
  have hstable : (prefixWord ++ tailWord_1878874).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1878874).length < 2 ^ (prefixWord ++ tailWord_1878874).sum := by decide
  have hdescent : baseEnd_1878874 < baseStart_1878874 := by decide
  rcases family_descends (prefixWord ++ tailWord_1878874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1878949 : List Nat := [1, 3, 1, 2, 1, 1, 1, 1, 6, 5]
def baseStart_1878949 : Nat := 118140960795 + 1878949 * 2 ^ 59
def prefixEnd_1878949 : Nat := 4983230072969 + 3 ^ 40 * 1878949 * 2
def baseEnd_1878949 : Nat := 643202641523249558064251

theorem tailTrace_1878949 : CollatzResearch.WordTrace tailWord_1878949 prefixEnd_1878949 643202641523249558064251 := by
  unfold tailWord_1878949
  simp only [CollatzResearch.WordTrace]
  refine ⟨68530900069896146786239901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45687266713264097857493267 68530900069896146786239901)
  ·
    refine ⟨25699087526211055044839963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68530900069896146786239901 25699087526211055044839963)
    ·
      refine ⟨38548631289316582567259945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25699087526211055044839963 38548631289316582567259945)
      ·
        refine ⟨28911473466987436925444959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38548631289316582567259945 28911473466987436925444959)
        ·
          refine ⟨43367210200481155388167439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28911473466987436925444959 43367210200481155388167439)
          ·
            refine ⟨65050815300721733082251159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43367210200481155388167439 65050815300721733082251159)
            ·
              refine ⟨97576222951082599623376739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65050815300721733082251159 97576222951082599623376739)
              ·
                refine ⟨146364334426623899435065109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97576222951082599623376739 146364334426623899435065109)
                ·
                  refine ⟨6860828176247995286018677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 146364334426623899435065109 6860828176247995286018677)
                  ·
                    refine ⟨643202641523249558064251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6860828176247995286018677 643202641523249558064251)
                    ·
                      rfl

theorem cell22_1878949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 6, 5].length) (baseStart_1878949 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1878949 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1878949 prefixEnd_1878949 := by exact prefixLift 1878949
  have htrace : WordTrace (prefixWord ++ tailWord_1878949) baseStart_1878949 baseEnd_1878949 := by
    simpa [prefixWord, tailWord_1878949, baseEnd_1878949] using wordTrace_append hprefix tailTrace_1878949
  have hstable : (prefixWord ++ tailWord_1878949).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1878949).length < 2 ^ (prefixWord ++ tailWord_1878949).sum := by decide
  have hdescent : baseEnd_1878949 < baseStart_1878949 := by decide
  rcases family_descends (prefixWord ++ tailWord_1878949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1878989 : List Nat := [1, 6, 3, 1, 1, 1, 1, 2, 3, 3]
def baseStart_1878989 : Nat := 118140960795 + 1878989 * 2 ^ 59
def prefixEnd_1878989 : Nat := 4983230072969 + 3 ^ 40 * 1878989 * 2
def baseEnd_1878989 : Nat := 643216334340702787064129

theorem tailTrace_1878989 : CollatzResearch.WordTrace tailWord_1878989 prefixEnd_1878989 643216334340702787064129 := by
  unfold tailWord_1878989
  simp only [CollatzResearch.WordTrace]
  refine ⟨68532358989751233617696021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45688239326500822411797347 68532358989751233617696021)
  ·
    refine ⟨3212454327644589075829501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 68532358989751233617696021 3212454327644589075829501)
    ·
      refine ⟨1204670372866720903436063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3212454327644589075829501 1204670372866720903436063)
      ·
        refine ⟨1807005559300081355154095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1204670372866720903436063 1807005559300081355154095)
        ·
          refine ⟨2710508338950122032731143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1807005559300081355154095 2710508338950122032731143)
          ·
            refine ⟨4065762508425183049096715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2710508338950122032731143 4065762508425183049096715)
            ·
              refine ⟨6098643762637774573645073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4065762508425183049096715 6098643762637774573645073)
              ·
                refine ⟨4573982821978330930233805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6098643762637774573645073 4573982821978330930233805)
                ·
                  refine ⟨1715243558241874098837677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4573982821978330930233805 1715243558241874098837677)
                  ·
                    refine ⟨643216334340702787064129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1715243558241874098837677 643216334340702787064129)
                    ·
                      rfl

theorem cell22_1878989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 1, 2, 3, 3].length) (baseStart_1878989 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1878989 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1878989 prefixEnd_1878989 := by exact prefixLift 1878989
  have htrace : WordTrace (prefixWord ++ tailWord_1878989) baseStart_1878989 baseEnd_1878989 := by
    simpa [prefixWord, tailWord_1878989, baseEnd_1878989] using wordTrace_append hprefix tailTrace_1878989
  have hstable : (prefixWord ++ tailWord_1878989).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1878989).length < 2 ^ (prefixWord ++ tailWord_1878989).sum := by decide
  have hdescent : baseEnd_1878989 < baseStart_1878989 := by decide
  rcases family_descends (prefixWord ++ tailWord_1878989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1878996 : List Nat := [2, 4, 1, 2, 1, 2, 1, 1, 8]
def baseStart_1878996 : Nat := 118140960795 + 1878996 * 2 ^ 59
def prefixEnd_1878996 : Nat := 4983230072969 + 3 ^ 40 * 1878996 * 2
def baseEnd_1878996 : Nat := 214406243527919034046369

theorem tailTrace_1878996 : CollatzResearch.WordTrace tailWord_1878996 prefixEnd_1878996 214406243527919034046369 := by
  unfold tailWord_1878996
  simp only [CollatzResearch.WordTrace]
  refine ⟨34266307150362936906600421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45688409533817249208800561 34266307150362936906600421)
  ·
    refine ⟨6424932590693050669987579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34266307150362936906600421 6424932590693050669987579)
    ·
      refine ⟨9637398886039576004981369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6424932590693050669987579 9637398886039576004981369)
      ·
        refine ⟨7228049164529682003736027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9637398886039576004981369 7228049164529682003736027)
        ·
          refine ⟨10842073746794523005604041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7228049164529682003736027 10842073746794523005604041)
          ·
            refine ⟨8131555310095892254203031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10842073746794523005604041 8131555310095892254203031)
            ·
              refine ⟨12197332965143838381304547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8131555310095892254203031 12197332965143838381304547)
              ·
                refine ⟨18295999447715757571956821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12197332965143838381304547 18295999447715757571956821)
                ·
                  refine ⟨214406243527919034046369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 18295999447715757571956821 214406243527919034046369)
                  ·
                    rfl

theorem cell22_1878996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 1, 8].length) (baseStart_1878996 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1878996 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1878996 prefixEnd_1878996 := by exact prefixLift 1878996
  have htrace : WordTrace (prefixWord ++ tailWord_1878996) baseStart_1878996 baseEnd_1878996 := by
    simpa [prefixWord, tailWord_1878996, baseEnd_1878996] using wordTrace_append hprefix tailTrace_1878996
  have hstable : (prefixWord ++ tailWord_1878996).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1878996).length < 2 ^ (prefixWord ++ tailWord_1878996).sum := by decide
  have hdescent : baseEnd_1878996 < baseStart_1878996 := by decide
  rcases family_descends (prefixWord ++ tailWord_1878996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1879011 : List Nat := [1, 1, 1, 6, 1, 1, 1, 4, 1, 5]
def baseStart_1879011 : Nat := 118140960795 + 1879011 * 2 ^ 59
def prefixEnd_1879011 : Nat := 4983230072969 + 3 ^ 40 * 1879011 * 2
def baseEnd_1879011 : Nat := 643223865390302063014061

theorem tailTrace_1879011 : CollatzResearch.WordTrace tailWord_1879011 prefixEnd_1879011 643223865390302063014061 := by
  unfold tailWord_1879011
  simp only [CollatzResearch.WordTrace]
  refine ⟨68533161395671531374996887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45688774263781020916664591 68533161395671531374996887)
  ·
    refine ⟨102799742093507297062495331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68533161395671531374996887 102799742093507297062495331)
    ·
      refine ⟨154199613140260945593742997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102799742093507297062495331 154199613140260945593742997)
      ·
        refine ⟨7228106865949731824706703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 154199613140260945593742997 7228106865949731824706703)
        ·
          refine ⟨10842160298924597737060055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7228106865949731824706703 10842160298924597737060055)
          ·
            refine ⟨16263240448386896605590083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10842160298924597737060055 16263240448386896605590083)
            ·
              refine ⟨24394860672580344908385125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16263240448386896605590083 24394860672580344908385125)
              ·
                refine ⟨4574036376108814670322211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24394860672580344908385125 4574036376108814670322211)
                ·
                  refine ⟨6861054564163222005483317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4574036376108814670322211 6861054564163222005483317)
                  ·
                    refine ⟨643223865390302063014061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6861054564163222005483317 643223865390302063014061)
                    ·
                      rfl

theorem cell22_1879011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 4, 1, 5].length) (baseStart_1879011 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1879011 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1879011 prefixEnd_1879011 := by exact prefixLift 1879011
  have htrace : WordTrace (prefixWord ++ tailWord_1879011) baseStart_1879011 baseEnd_1879011 := by
    simpa [prefixWord, tailWord_1879011, baseEnd_1879011] using wordTrace_append hprefix tailTrace_1879011
  have hstable : (prefixWord ++ tailWord_1879011).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1879011).length < 2 ^ (prefixWord ++ tailWord_1879011).sum := by decide
  have hdescent : baseEnd_1879011 < baseStart_1879011 := by decide
  rcases family_descends (prefixWord ++ tailWord_1879011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1879015 : List Nat := [1, 1, 5, 2, 2, 1, 4, 1, 1, 4]
def baseStart_1879015 : Nat := 118140960795 + 1879015 * 2 ^ 59
def prefixEnd_1879015 : Nat := 4983230072969 + 3 ^ 40 * 1879015 * 2
def baseEnd_1879015 : Nat := 643225234672047385914049

theorem tailTrace_1879015 : CollatzResearch.WordTrace tailWord_1879015 prefixEnd_1879015 643225234672047385914049 := by
  unfold tailWord_1879015
  simp only [CollatzResearch.WordTrace]
  refine ⟨68533307287657040058142499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45688871525104693372094999 68533307287657040058142499)
  ·
    refine ⟨102799960931485560087213749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68533307287657040058142499 102799960931485560087213749)
    ·
      refine ⟨9637496337326771258176289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 102799960931485560087213749 9637496337326771258176289)
      ·
        refine ⟨7228122252995078443632217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9637496337326771258176289 7228122252995078443632217)
        ·
          refine ⟨5421091689746308832724163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7228122252995078443632217 5421091689746308832724163)
          ·
            refine ⟨8131637534619463249086245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5421091689746308832724163 8131637534619463249086245)
            ·
              refine ⟨1524682037741149359203671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8131637534619463249086245 1524682037741149359203671)
              ·
                refine ⟨2287023056611724038805507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1524682037741149359203671 2287023056611724038805507)
                ·
                  refine ⟨3430534584917586058208261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2287023056611724038805507 3430534584917586058208261)
                  ·
                    refine ⟨643225234672047385914049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3430534584917586058208261 643225234672047385914049)
                    ·
                      rfl

theorem cell22_1879015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 4, 1, 1, 4].length) (baseStart_1879015 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1879015 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1879015 prefixEnd_1879015 := by exact prefixLift 1879015
  have htrace : WordTrace (prefixWord ++ tailWord_1879015) baseStart_1879015 baseEnd_1879015 := by
    simpa [prefixWord, tailWord_1879015, baseEnd_1879015] using wordTrace_append hprefix tailTrace_1879015
  have hstable : (prefixWord ++ tailWord_1879015).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1879015).length < 2 ^ (prefixWord ++ tailWord_1879015).sum := by decide
  have hdescent : baseEnd_1879015 < baseStart_1879015 := by decide
  rcases family_descends (prefixWord ++ tailWord_1879015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1879030 : List Nat := [5, 1, 1, 1, 3, 1, 2, 4, 4]
def baseStart_1879030 : Nat := 118140960795 + 1879030 * 2 ^ 59
def prefixEnd_1879030 : Nat := 4983230072969 + 3 ^ 40 * 1879030 * 2
def baseEnd_1879030 : Nat := 214410123159530782263001

theorem tailTrace_1879030 : CollatzResearch.WordTrace tailWord_1879030 prefixEnd_1879030 214410123159530782263001 := by
  unfold tailWord_1879030
  simp only [CollatzResearch.WordTrace]
  refine ⟨4283365898912668601246159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 45689236255068465079959029 4283365898912668601246159)
  ·
    refine ⟨6425048848369002901869239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4283365898912668601246159 6425048848369002901869239)
    ·
      refine ⟨9637573272553504352803859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6425048848369002901869239 9637573272553504352803859)
      ·
        refine ⟨14456359908830256529205789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9637573272553504352803859 14456359908830256529205789)
        ·
          refine ⟨5421134965811346198452171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14456359908830256529205789 5421134965811346198452171)
          ·
            refine ⟨8131702448717019297678257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5421134965811346198452171 8131702448717019297678257)
            ·
              refine ⟨6098776836537764473258693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8131702448717019297678257 6098776836537764473258693)
              ·
                refine ⟨1143520656850830838736005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6098776836537764473258693 1143520656850830838736005)
                ·
                  refine ⟨214410123159530782263001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1143520656850830838736005 214410123159530782263001)
                  ·
                    rfl

theorem cell22_1879030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 2, 4, 4].length) (baseStart_1879030 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1879030 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1879030 prefixEnd_1879030 := by exact prefixLift 1879030
  have htrace : WordTrace (prefixWord ++ tailWord_1879030) baseStart_1879030 baseEnd_1879030 := by
    simpa [prefixWord, tailWord_1879030, baseEnd_1879030] using wordTrace_append hprefix tailTrace_1879030
  have hstable : (prefixWord ++ tailWord_1879030).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1879030).length < 2 ^ (prefixWord ++ tailWord_1879030).sum := by decide
  have hdescent : baseEnd_1879030 < baseStart_1879030 := by decide
  rcases family_descends (prefixWord ++ tailWord_1879030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1879045 : List Nat := [1, 3, 1, 1, 2, 3, 5, 1, 2, 3]
def baseStart_1879045 : Nat := 118140960795 + 1879045 * 2 ^ 59
def prefixEnd_1879045 : Nat := 4983230072969 + 3 ^ 40 * 1879045 * 2
def baseEnd_1879045 : Nat := 643235504285137307663957

theorem tailTrace_1879045 : CollatzResearch.WordTrace tailWord_1879045 prefixEnd_1879045 643235504285137307663957 := by
  unfold tailWord_1879045
  simp only [CollatzResearch.WordTrace]
  refine ⟨68534401477548355181734589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45689600985032236787823059 68534401477548355181734589)
  ·
    refine ⟨25700400554080633193150471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68534401477548355181734589 25700400554080633193150471)
    ·
      refine ⟨38550600831120949789725707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25700400554080633193150471 38550600831120949789725707)
      ·
        refine ⟨57825901246681424684588561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38550600831120949789725707 57825901246681424684588561)
        ·
          refine ⟨43369425935011068513441421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57825901246681424684588561 43369425935011068513441421)
          ·
            refine ⟨16263534725629150692540533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43369425935011068513441421 16263534725629150692540533)
            ·
              refine ⟨1524706380527732877425675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16263534725629150692540533 1524706380527732877425675)
              ·
                refine ⟨2287059570791599316138513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1524706380527732877425675 2287059570791599316138513)
                ·
                  refine ⟨1715294678093699487103885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2287059570791599316138513 1715294678093699487103885)
                  ·
                    refine ⟨643235504285137307663957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1715294678093699487103885 643235504285137307663957)
                    ·
                      rfl

theorem cell22_1879045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 5, 1, 2, 3].length) (baseStart_1879045 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1879045 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1879045 prefixEnd_1879045 := by exact prefixLift 1879045
  have htrace : WordTrace (prefixWord ++ tailWord_1879045) baseStart_1879045 baseEnd_1879045 := by
    simpa [prefixWord, tailWord_1879045, baseEnd_1879045] using wordTrace_append hprefix tailTrace_1879045
  have hstable : (prefixWord ++ tailWord_1879045).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1879045).length < 2 ^ (prefixWord ++ tailWord_1879045).sum := by decide
  have hdescent : baseEnd_1879045 < baseStart_1879045 := by decide
  rcases family_descends (prefixWord ++ tailWord_1879045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1879178 : List Nat := [3, 1, 2, 3, 1, 1, 3, 1, 1, 6]
def baseStart_1879178 : Nat := 118140960795 + 1879178 * 2 ^ 59
def prefixEnd_1879178 : Nat := 4983230072969 + 3 ^ 40 * 1879178 * 2
def baseEnd_1879178 : Nat := 643281032903169294088549

theorem tailTrace_1879178 : CollatzResearch.WordTrace tailWord_1879178 prefixEnd_1879178 643281032903169294088549 := by
  unfold tailWord_1879178
  simp only [CollatzResearch.WordTrace]
  refine ⟨17134813096516629724081547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45692834924044345930884125 17134813096516629724081547)
  ·
    refine ⟨25702219644774944586122321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17134813096516629724081547 25702219644774944586122321)
    ·
      refine ⟨19276664733581208439591741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25702219644774944586122321 19276664733581208439591741)
      ·
        refine ⟨7228749275092953164846903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19276664733581208439591741 7228749275092953164846903)
        ·
          refine ⟨10843123912639429747270355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7228749275092953164846903 10843123912639429747270355)
          ·
            refine ⟨16264685868959144620905533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10843123912639429747270355 16264685868959144620905533)
            ·
              refine ⟨6099257200859679232839575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16264685868959144620905533 6099257200859679232839575)
              ·
                refine ⟨9148885801289518849259363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6099257200859679232839575 9148885801289518849259363)
                ·
                  refine ⟨13723328701934278273889045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9148885801289518849259363 13723328701934278273889045)
                  ·
                    refine ⟨643281032903169294088549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13723328701934278273889045 643281032903169294088549)
                    ·
                      rfl

theorem cell22_1879178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 3, 1, 1, 6].length) (baseStart_1879178 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1879178 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1879178 prefixEnd_1879178 := by exact prefixLift 1879178
  have htrace : WordTrace (prefixWord ++ tailWord_1879178) baseStart_1879178 baseEnd_1879178 := by
    simpa [prefixWord, tailWord_1879178, baseEnd_1879178] using wordTrace_append hprefix tailTrace_1879178
  have hstable : (prefixWord ++ tailWord_1879178).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1879178).length < 2 ^ (prefixWord ++ tailWord_1879178).sum := by decide
  have hdescent : baseEnd_1879178 < baseStart_1879178 := by decide
  rcases family_descends (prefixWord ++ tailWord_1879178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1879182 : List Nat := [4, 1, 1, 3, 2, 2, 2, 3, 4]
def baseStart_1879182 : Nat := 118140960795 + 1879182 * 2 ^ 59
def prefixEnd_1879182 : Nat := 4983230072969 + 3 ^ 40 * 1879182 * 2
def baseEnd_1879182 : Nat := 214427467394971538996179

theorem tailTrace_1879182 : CollatzResearch.WordTrace tailWord_1879182 prefixEnd_1879182 214427467394971538996179 := by
  unfold tailWord_1879182
  simp only [CollatzResearch.WordTrace]
  refine ⟨8567424784756503447433975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45692932185368018386314533 8567424784756503447433975)
  ·
    refine ⟨12851137177134755171150963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8567424784756503447433975 12851137177134755171150963)
    ·
      refine ⟨19276705765702132756726445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12851137177134755171150963 19276705765702132756726445)
      ·
        refine ⟨7228764662138299783772417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19276705765702132756726445 7228764662138299783772417)
        ·
          refine ⟨5421573496603724837829313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7228764662138299783772417 5421573496603724837829313)
          ·
            refine ⟨4066180122452793628371985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5421573496603724837829313 4066180122452793628371985)
            ·
              refine ⟨3049635091839595221278989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4066180122452793628371985 3049635091839595221278989)
              ·
                refine ⟨1143613159439848207979621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3049635091839595221278989 1143613159439848207979621)
                ·
                  refine ⟨214427467394971538996179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1143613159439848207979621 214427467394971538996179)
                  ·
                    rfl

theorem cell22_1879182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 2, 3, 4].length) (baseStart_1879182 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1879182 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1879182 prefixEnd_1879182 := by exact prefixLift 1879182
  have htrace : WordTrace (prefixWord ++ tailWord_1879182) baseStart_1879182 baseEnd_1879182 := by
    simpa [prefixWord, tailWord_1879182, baseEnd_1879182] using wordTrace_append hprefix tailTrace_1879182
  have hstable : (prefixWord ++ tailWord_1879182).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1879182).length < 2 ^ (prefixWord ++ tailWord_1879182).sum := by decide
  have hdescent : baseEnd_1879182 < baseStart_1879182 := by decide
  rcases family_descends (prefixWord ++ tailWord_1879182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1879225 : List Nat := [1, 2, 1, 4, 1, 3, 2, 2, 3, 3]
def baseStart_1879225 : Nat := 118140960795 + 1879225 * 2 ^ 59
def prefixEnd_1879225 : Nat := 4983230072969 + 3 ^ 40 * 1879225 * 2
def baseEnd_1879225 : Nat := 643297121963676838163405

theorem tailTrace_1879225 : CollatzResearch.WordTrace tailWord_1879225 prefixEnd_1879225 643297121963676838163405 := by
  unfold tailWord_1879225
  simp only [CollatzResearch.WordTrace]
  refine ⟨68540966616896245923287129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45693977744597497282191419 68540966616896245923287129)
  ·
    refine ⟨51405724962672184442465347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68540966616896245923287129 51405724962672184442465347)
    ·
      refine ⟨77108587444008276663698021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51405724962672184442465347 77108587444008276663698021)
      ·
        refine ⟨14457860145751551874443379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 77108587444008276663698021 14457860145751551874443379)
        ·
          refine ⟨21686790218627327811665069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14457860145751551874443379 21686790218627327811665069)
          ·
            refine ⟨8132546331985247929374401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21686790218627327811665069 8132546331985247929374401)
            ·
              refine ⟨6099409748988935947030801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8132546331985247929374401 6099409748988935947030801)
              ·
                refine ⟨4574557311741701960273101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6099409748988935947030801 4574557311741701960273101)
                ·
                  refine ⟨1715458991903138235102413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4574557311741701960273101 1715458991903138235102413)
                  ·
                    refine ⟨643297121963676838163405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1715458991903138235102413 643297121963676838163405)
                    ·
                      rfl

theorem cell22_1879225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 2, 2, 3, 3].length) (baseStart_1879225 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1879225 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1879225 prefixEnd_1879225 := by exact prefixLift 1879225
  have htrace : WordTrace (prefixWord ++ tailWord_1879225) baseStart_1879225 baseEnd_1879225 := by
    simpa [prefixWord, tailWord_1879225, baseEnd_1879225] using wordTrace_append hprefix tailTrace_1879225
  have hstable : (prefixWord ++ tailWord_1879225).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1879225).length < 2 ^ (prefixWord ++ tailWord_1879225).sum := by decide
  have hdescent : baseEnd_1879225 < baseStart_1879225 := by decide
  rcases family_descends (prefixWord ++ tailWord_1879225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1879332 : List Nat := [2, 3, 1, 3, 1, 1, 1, 5, 2, 3]
def baseStart_1879332 : Nat := 118140960795 + 1879332 * 2 ^ 59
def prefixEnd_1879332 : Nat := 4983230072969 + 3 ^ 40 * 1879332 * 2
def baseEnd_1879332 : Nat := 643333750250364225738077

theorem tailTrace_1879332 : CollatzResearch.WordTrace tailWord_1879332 prefixEnd_1879332 643333750250364225738077 := by
  unfold tailWord_1879332
  simp only [CollatzResearch.WordTrace]
  refine ⟨34272434613754301598716125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45696579485005735464954833 34272434613754301598716125)
  ·
    refine ⟨12852162980157863099518547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34272434613754301598716125 12852162980157863099518547)
    ·
      refine ⟨19278244470236794649277821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12852162980157863099518547 19278244470236794649277821)
      ·
        refine ⟨7229341676338797993479183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19278244470236794649277821 7229341676338797993479183)
        ·
          refine ⟨10844012514508196990218775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7229341676338797993479183 10844012514508196990218775)
          ·
            refine ⟨16266018771762295485328163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10844012514508196990218775 16266018771762295485328163)
            ·
              refine ⟨24399028157643443227992245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16266018771762295485328163 24399028157643443227992245)
              ·
                refine ⟨2287408889779072802624273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24399028157643443227992245 2287408889779072802624273)
                ·
                  refine ⟨1715556667334304601968205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2287408889779072802624273 1715556667334304601968205)
                  ·
                    refine ⟨643333750250364225738077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1715556667334304601968205 643333750250364225738077)
                    ·
                      rfl

theorem cell22_1879332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 5, 2, 3].length) (baseStart_1879332 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1879332 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1879332 prefixEnd_1879332 := by exact prefixLift 1879332
  have htrace : WordTrace (prefixWord ++ tailWord_1879332) baseStart_1879332 baseEnd_1879332 := by
    simpa [prefixWord, tailWord_1879332, baseEnd_1879332] using wordTrace_append hprefix tailTrace_1879332
  have hstable : (prefixWord ++ tailWord_1879332).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1879332).length < 2 ^ (prefixWord ++ tailWord_1879332).sum := by decide
  have hdescent : baseEnd_1879332 < baseStart_1879332 := by decide
  rcases family_descends (prefixWord ++ tailWord_1879332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1879347 : List Nat := [1, 1, 1, 2, 5, 4, 1, 1, 2, 4]
def baseStart_1879347 : Nat := 118140960795 + 1879347 * 2 ^ 59
def prefixEnd_1879347 : Nat := 4983230072969 + 3 ^ 40 * 1879347 * 2
def baseEnd_1879347 : Nat := 643338885056909186613031

theorem tailTrace_1879347 : CollatzResearch.WordTrace tailWord_1879347 prefixEnd_1879347 643338885056909186613031 := by
  unfold tailWord_1879347
  simp only [CollatzResearch.WordTrace]
  refine ⟨68545416322454260759228295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45696944214969507172818863 68545416322454260759228295)
  ·
    refine ⟨102818124483681391138842443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68545416322454260759228295 102818124483681391138842443)
    ·
      refine ⟨154227186725522086708263665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102818124483681391138842443 154227186725522086708263665)
      ·
        refine ⟨115670390044141565031197749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154227186725522086708263665 115670390044141565031197749)
        ·
          refine ⟨10844099066638271721674789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 115670390044141565031197749 10844099066638271721674789)
          ·
            refine ⟨2033268574994675947814023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10844099066638271721674789 2033268574994675947814023)
            ·
              refine ⟨3049902862492013921721035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2033268574994675947814023 3049902862492013921721035)
              ·
                refine ⟨4574854293738020882581553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3049902862492013921721035 4574854293738020882581553)
                ·
                  refine ⟨3431140720303515661936165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4574854293738020882581553 3431140720303515661936165)
                  ·
                    refine ⟨643338885056909186613031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3431140720303515661936165 643338885056909186613031)
                    ·
                      rfl

theorem cell22_1879347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 4, 1, 1, 2, 4].length) (baseStart_1879347 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1879347 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1879347 prefixEnd_1879347 := by exact prefixLift 1879347
  have htrace : WordTrace (prefixWord ++ tailWord_1879347) baseStart_1879347 baseEnd_1879347 := by
    simpa [prefixWord, tailWord_1879347, baseEnd_1879347] using wordTrace_append hprefix tailTrace_1879347
  have hstable : (prefixWord ++ tailWord_1879347).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1879347).length < 2 ^ (prefixWord ++ tailWord_1879347).sum := by decide
  have hdescent : baseEnd_1879347 < baseStart_1879347 := by decide
  rcases family_descends (prefixWord ++ tailWord_1879347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1879360 : List Nat := [2, 1, 1, 2, 2, 1, 3, 2, 5, 3]
def baseStart_1879360 : Nat := 118140960795 + 1879360 * 2 ^ 59
def prefixEnd_1879360 : Nat := 4983230072969 + 3 ^ 40 * 1879360 * 2
def baseEnd_1879360 : Nat := 643343335222581486037991

theorem tailTrace_1879360 : CollatzResearch.WordTrace tailWord_1879360 prefixEnd_1879360 643343335222581486037991 := by
  unfold tailWord_1879360
  simp only [CollatzResearch.WordTrace]
  refine ⟨34272945235703581989725767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45697260314271442652967689 34272945235703581989725767)
  ·
    refine ⟨51409417853555372984588651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34272945235703581989725767 51409417853555372984588651)
    ·
      refine ⟨77114126780333059476882977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51409417853555372984588651 77114126780333059476882977)
      ·
        refine ⟨57835595085249794607662233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77114126780333059476882977 57835595085249794607662233)
        ·
          refine ⟨43376696313937345955746675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57835595085249794607662233 43376696313937345955746675)
          ·
            refine ⟨65065044470906018933620013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43376696313937345955746675 65065044470906018933620013)
            ·
              refine ⟨24399391676589757100107505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65065044470906018933620013 24399391676589757100107505)
              ·
                refine ⟨18299543757442317825080629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24399391676589757100107505 18299543757442317825080629)
                ·
                  refine ⟨1715582227260217296101309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 18299543757442317825080629 1715582227260217296101309)
                  ·
                    refine ⟨643343335222581486037991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1715582227260217296101309 643343335222581486037991)
                    ·
                      rfl

theorem cell22_1879360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 2, 5, 3].length) (baseStart_1879360 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1879360 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1879360 prefixEnd_1879360 := by exact prefixLift 1879360
  have htrace : WordTrace (prefixWord ++ tailWord_1879360) baseStart_1879360 baseEnd_1879360 := by
    simpa [prefixWord, tailWord_1879360, baseEnd_1879360] using wordTrace_append hprefix tailTrace_1879360
  have hstable : (prefixWord ++ tailWord_1879360).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1879360).length < 2 ^ (prefixWord ++ tailWord_1879360).sum := by decide
  have hdescent : baseEnd_1879360 < baseStart_1879360 := by decide
  rcases family_descends (prefixWord ++ tailWord_1879360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1879377 : List Nat := [1, 2, 2, 1, 4, 1, 4, 1, 3, 3]
def baseStart_1879377 : Nat := 118140960795 + 1879377 * 2 ^ 59
def prefixEnd_1879377 : Nat := 4983230072969 + 3 ^ 40 * 1879377 * 2
def baseEnd_1879377 : Nat := 643349154669999108362939

theorem tailTrace_1879377 : CollatzResearch.WordTrace tailWord_1879377 prefixEnd_1879377 643349154669999108362939 := by
  unfold tailWord_1879377
  simp only [CollatzResearch.WordTrace]
  refine ⟨68546510512345575882820385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45697673674897050588546923 68546510512345575882820385)
  ·
    refine ⟨51409882884259181912115289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68546510512345575882820385 51409882884259181912115289)
    ·
      refine ⟨38557412163194386434086467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51409882884259181912115289 38557412163194386434086467)
      ·
        refine ⟨57836118244791579651129701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38557412163194386434086467 57836118244791579651129701)
        ·
          refine ⟨10844272170898421184586819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57836118244791579651129701 10844272170898421184586819)
          ·
            refine ⟨16266408256347631776880229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10844272170898421184586819 16266408256347631776880229)
            ·
              refine ⟨3049951548065180958165043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16266408256347631776880229 3049951548065180958165043)
              ·
                refine ⟨4574927322097771437247565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3049951548065180958165043 4574927322097771437247565)
                ·
                  refine ⟨1715597745786664288967837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4574927322097771437247565 1715597745786664288967837)
                  ·
                    refine ⟨643349154669999108362939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1715597745786664288967837 643349154669999108362939)
                    ·
                      rfl

theorem cell22_1879377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 4, 1, 3, 3].length) (baseStart_1879377 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1879377 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1879377 prefixEnd_1879377 := by exact prefixLift 1879377
  have htrace : WordTrace (prefixWord ++ tailWord_1879377) baseStart_1879377 baseEnd_1879377 := by
    simpa [prefixWord, tailWord_1879377, baseEnd_1879377] using wordTrace_append hprefix tailTrace_1879377
  have hstable : (prefixWord ++ tailWord_1879377).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1879377).length < 2 ^ (prefixWord ++ tailWord_1879377).sum := by decide
  have hdescent : baseEnd_1879377 < baseStart_1879377 := by decide
  rcases family_descends (prefixWord ++ tailWord_1879377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1879512 : List Nat := [2, 1, 2, 2, 2, 1, 3, 1, 5, 3]
def baseStart_1879512 : Nat := 118140960795 + 1879512 * 2 ^ 59
def prefixEnd_1879512 : Nat := 4983230072969 + 3 ^ 40 * 1879512 * 2
def baseEnd_1879512 : Nat := 643395367928903756237525

theorem tailTrace_1879512 : CollatzResearch.WordTrace tailWord_1879512 prefixEnd_1879512 643395367928903756237525 := by
  unfold tailWord_1879512
  simp only [CollatzResearch.WordTrace]
  refine ⟨34275717183428246969492395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45700956244570995959323193 34275717183428246969492395)
  ·
    refine ⟨51413575775142370454238593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34275717183428246969492395 51413575775142370454238593)
    ·
      refine ⟨38560181831356777840678945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51413575775142370454238593 38560181831356777840678945)
      ·
        refine ⟨28920136373517583380509209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38560181831356777840678945 28920136373517583380509209)
        ·
          refine ⟨21690102280138187535381907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28920136373517583380509209 21690102280138187535381907)
          ·
            refine ⟨32535153420207281303072861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21690102280138187535381907 32535153420207281303072861)
            ·
              refine ⟨12200682532577730488652323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32535153420207281303072861 12200682532577730488652323)
              ·
                refine ⟨18301023798866595732978485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12200682532577730488652323 18301023798866595732978485)
                ·
                  refine ⟨1715720981143743349966733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 18301023798866595732978485 1715720981143743349966733)
                  ·
                    refine ⟨643395367928903756237525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1715720981143743349966733 643395367928903756237525)
                    ·
                      rfl

theorem cell22_1879512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 1, 5, 3].length) (baseStart_1879512 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1879512 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1879512 prefixEnd_1879512 := by exact prefixLift 1879512
  have htrace : WordTrace (prefixWord ++ tailWord_1879512) baseStart_1879512 baseEnd_1879512 := by
    simpa [prefixWord, tailWord_1879512, baseEnd_1879512] using wordTrace_append hprefix tailTrace_1879512
  have hstable : (prefixWord ++ tailWord_1879512).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1879512).length < 2 ^ (prefixWord ++ tailWord_1879512).sum := by decide
  have hdescent : baseEnd_1879512 < baseStart_1879512 := by decide
  rcases family_descends (prefixWord ++ tailWord_1879512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1879555 : List Nat := [1, 1, 1, 3, 2, 1, 2, 1, 2, 8]
def baseStart_1879555 : Nat := 118140960795 + 1879555 * 2 ^ 59
def prefixEnd_1879555 : Nat := 4983230072969 + 3 ^ 40 * 1879555 * 2
def baseEnd_1879555 : Nat := 643410087707665977412393

theorem tailTrace_1879555 : CollatzResearch.WordTrace tailWord_1879555 prefixEnd_1879555 643410087707665977412393 := by
  unfold tailWord_1879555
  simp only [CollatzResearch.WordTrace]
  refine ⟨68553002705700712282800119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45702001803800474855200079 68553002705700712282800119)
  ·
    refine ⟨102829504058551068424200179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68553002705700712282800119 102829504058551068424200179)
    ·
      refine ⟨154244256087826602636300269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102829504058551068424200179 154244256087826602636300269)
      ·
        refine ⟨57841596032934975988612601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 154244256087826602636300269 57841596032934975988612601)
        ·
          refine ⟨43381197024701231991459451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57841596032934975988612601 43381197024701231991459451)
          ·
            refine ⟨65071795537051847987189177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43381197024701231991459451 65071795537051847987189177)
            ·
              refine ⟨48803846652788885990391883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65071795537051847987189177 48803846652788885990391883)
              ·
                refine ⟨73205769979183328985587825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48803846652788885990391883 73205769979183328985587825)
                ·
                  refine ⟨54904327484387496739190869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73205769979183328985587825 54904327484387496739190869)
                  ·
                    refine ⟨643410087707665977412393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 54904327484387496739190869 643410087707665977412393)
                    ·
                      rfl

theorem cell22_1879555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 1, 2, 8].length) (baseStart_1879555 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1879555 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1879555 prefixEnd_1879555 := by exact prefixLift 1879555
  have htrace : WordTrace (prefixWord ++ tailWord_1879555) baseStart_1879555 baseEnd_1879555 := by
    simpa [prefixWord, tailWord_1879555, baseEnd_1879555] using wordTrace_append hprefix tailTrace_1879555
  have hstable : (prefixWord ++ tailWord_1879555).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1879555).length < 2 ^ (prefixWord ++ tailWord_1879555).sum := by decide
  have hdescent : baseEnd_1879555 < baseStart_1879555 := by decide
  rcases family_descends (prefixWord ++ tailWord_1879555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1879565 : List Nat := [1, 7, 1, 1, 3, 1, 2, 6]
def baseStart_1879565 : Nat := 118140960795 + 1879565 * 2 ^ 59
def prefixEnd_1879565 : Nat := 4983230072969 + 3 ^ 40 * 1879565 * 2
def baseEnd_1879565 : Nat := 71490390101336587184707

theorem tailTrace_1879565 : CollatzResearch.WordTrace tailWord_1879565 prefixEnd_1879565 71490390101336587184707 := by
  unfold tailWord_1879565
  simp only [CollatzResearch.WordTrace]
  refine ⟨68553367435664483990664149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45702244957109655993776099 68553367435664483990664149)
  ·
    refine ⟨1606719549273386343531191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 68553367435664483990664149 1606719549273386343531191)
    ·
      refine ⟨2410079323910079515296787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1606719549273386343531191 2410079323910079515296787)
      ·
        refine ⟨3615118985865119272945181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2410079323910079515296787 3615118985865119272945181)
        ·
          refine ⟨1355669619699419727354443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3615118985865119272945181 1355669619699419727354443)
          ·
            refine ⟨2033504429549129591031665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1355669619699419727354443 2033504429549129591031665)
            ·
              refine ⟨1525128322161847193273749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2033504429549129591031665 1525128322161847193273749)
              ·
                refine ⟨71490390101336587184707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1525128322161847193273749 71490390101336587184707)
                ·
                  rfl

theorem cell22_1879565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 3, 1, 2, 6].length) (baseStart_1879565 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1879565 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1879565 prefixEnd_1879565 := by exact prefixLift 1879565
  have htrace : WordTrace (prefixWord ++ tailWord_1879565) baseStart_1879565 baseEnd_1879565 := by
    simpa [prefixWord, tailWord_1879565, baseEnd_1879565] using wordTrace_append hprefix tailTrace_1879565
  have hstable : (prefixWord ++ tailWord_1879565).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1879565).length < 2 ^ (prefixWord ++ tailWord_1879565).sum := by decide
  have hdescent : baseEnd_1879565 < baseStart_1879565 := by decide
  rcases family_descends (prefixWord ++ tailWord_1879565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1879623 : List Nat := [1, 1, 4, 1, 6, 1, 1, 2, 1, 4]
def baseStart_1879623 : Nat := 118140960795 + 1879623 * 2 ^ 59
def prefixEnd_1879623 : Nat := 4983230072969 + 3 ^ 40 * 1879623 * 2
def baseEnd_1879623 : Nat := 643433365497336466712185

theorem tailTrace_1879623 : CollatzResearch.WordTrace tailWord_1879623 prefixEnd_1879623 643433365497336466712185 := by
  unfold tailWord_1879623
  simp only [CollatzResearch.WordTrace]
  refine ⟨68555482869454359896275523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45703655246302906597517015 68555482869454359896275523)
  ·
    refine ⟨102833224304181539844413285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68555482869454359896275523 102833224304181539844413285)
    ·
      refine ⟨19281229557034038720827491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 102833224304181539844413285 19281229557034038720827491)
      ·
        refine ⟨28921844335551058081241237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19281229557034038720827491 28921844335551058081241237)
        ·
          refine ⟨1355711453228955847558183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 28921844335551058081241237 1355711453228955847558183)
          ·
            refine ⟨2033567179843433771337275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1355711453228955847558183 2033567179843433771337275)
            ·
              refine ⟨3050350769765150657005913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2033567179843433771337275 3050350769765150657005913)
              ·
                refine ⟨2287763077323862992754435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3050350769765150657005913 2287763077323862992754435)
                ·
                  refine ⟨3431644615985794489131653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2287763077323862992754435 3431644615985794489131653)
                  ·
                    refine ⟨643433365497336466712185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3431644615985794489131653 643433365497336466712185)
                    ·
                      rfl

theorem cell22_1879623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 6, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 6, 1, 1, 2, 1, 4].length) (baseStart_1879623 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1879623 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1879623 prefixEnd_1879623 := by exact prefixLift 1879623
  have htrace : WordTrace (prefixWord ++ tailWord_1879623) baseStart_1879623 baseEnd_1879623 := by
    simpa [prefixWord, tailWord_1879623, baseEnd_1879623] using wordTrace_append hprefix tailTrace_1879623
  have hstable : (prefixWord ++ tailWord_1879623).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1879623).length < 2 ^ (prefixWord ++ tailWord_1879623).sum := by decide
  have hdescent : baseEnd_1879623 < baseStart_1879623 := by decide
  rcases family_descends (prefixWord ++ tailWord_1879623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1879634 : List Nat := [3, 2, 2, 1, 2, 2, 1, 3, 2, 4]
def baseStart_1879634 : Nat := 118140960795 + 1879634 * 2 ^ 59
def prefixEnd_1879634 : Nat := 4983230072969 + 3 ^ 40 * 1879634 * 2
def baseEnd_1879634 : Nat := 643437131022136104687151

theorem tailTrace_1879634 : CollatzResearch.WordTrace tailWord_1879634 prefixEnd_1879634 643437131022136104687151 := by
  unfold tailWord_1879634
  simp only [CollatzResearch.WordTrace]
  refine ⟨17138971018103627193731489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45703922714943005849950637 17138971018103627193731489)
  ·
    refine ⟨12854228263577720395298617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17138971018103627193731489 12854228263577720395298617)
    ·
      refine ⟨9640671197683290296473963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12854228263577720395298617 9640671197683290296473963)
      ·
        refine ⟨14461006796524935444710945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9640671197683290296473963 14461006796524935444710945)
        ·
          refine ⟨10845755097393701583533209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14461006796524935444710945 10845755097393701583533209)
          ·
            refine ⟨8134316323045276187649907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10845755097393701583533209 8134316323045276187649907)
            ·
              refine ⟨12201474484567914281474861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8134316323045276187649907 12201474484567914281474861)
              ·
                refine ⟨4575552931712967855553073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12201474484567914281474861 4575552931712967855553073)
                ·
                  refine ⟨3431664698784725891664805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4575552931712967855553073 3431664698784725891664805)
                  ·
                    refine ⟨643437131022136104687151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3431664698784725891664805 643437131022136104687151)
                    ·
                      rfl

theorem cell22_1879634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 3, 2, 4].length) (baseStart_1879634 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1879634 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1879634 prefixEnd_1879634 := by exact prefixLift 1879634
  have htrace : WordTrace (prefixWord ++ tailWord_1879634) baseStart_1879634 baseEnd_1879634 := by
    simpa [prefixWord, tailWord_1879634, baseEnd_1879634] using wordTrace_append hprefix tailTrace_1879634
  have hstable : (prefixWord ++ tailWord_1879634).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1879634).length < 2 ^ (prefixWord ++ tailWord_1879634).sum := by decide
  have hdescent : baseEnd_1879634 < baseStart_1879634 := by decide
  rcases family_descends (prefixWord ++ tailWord_1879634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1879681 : List Nat := [1, 2, 4, 2, 1, 3, 1, 2, 3, 3]
def baseStart_1879681 : Nat := 118140960795 + 1879681 * 2 ^ 59
def prefixEnd_1879681 : Nat := 4983230072969 + 3 ^ 40 * 1879681 * 2
def baseEnd_1879681 : Nat := 643453220082643648762007

theorem tailTrace_1879681 : CollatzResearch.WordTrace tailWord_1879681 prefixEnd_1879681 643453220082643648762007 := by
  unfold tailWord_1879681
  simp only [CollatzResearch.WordTrace]
  refine ⟨68557598303244235801886897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45705065535496157201257931 68557598303244235801886897)
  ·
    refine ⟨51418198727433176851415173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68557598303244235801886897 51418198727433176851415173)
    ·
      refine ⟨9640912261393720659640345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51418198727433176851415173 9640912261393720659640345)
      ·
        refine ⟨7230684196045290494730259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9640912261393720659640345 7230684196045290494730259)
        ·
          refine ⟨10846026294067935742095389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7230684196045290494730259 10846026294067935742095389)
          ·
            refine ⟨4067259860275475903285771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10846026294067935742095389 4067259860275475903285771)
            ·
              refine ⟨6100889790413213854928657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4067259860275475903285771 6100889790413213854928657)
              ·
                refine ⟨4575667342809910391196493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6100889790413213854928657 4575667342809910391196493)
                ·
                  refine ⟨1715875253553716396698685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4575667342809910391196493 1715875253553716396698685)
                  ·
                    refine ⟨643453220082643648762007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1715875253553716396698685 643453220082643648762007)
                    ·
                      rfl

theorem cell22_1879681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 1, 2, 3, 3].length) (baseStart_1879681 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1879681 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1879681 prefixEnd_1879681 := by exact prefixLift 1879681
  have htrace : WordTrace (prefixWord ++ tailWord_1879681) baseStart_1879681 baseEnd_1879681 := by
    simpa [prefixWord, tailWord_1879681, baseEnd_1879681] using wordTrace_append hprefix tailTrace_1879681
  have hstable : (prefixWord ++ tailWord_1879681).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1879681).length < 2 ^ (prefixWord ++ tailWord_1879681).sum := by decide
  have hdescent : baseEnd_1879681 < baseStart_1879681 := by decide
  rcases family_descends (prefixWord ++ tailWord_1879681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1879692 : List Nat := [2, 2, 1, 2, 1, 1, 3, 2, 1, 7]
def baseStart_1879692 : Nat := 118140960795 + 1879692 * 2 ^ 59
def prefixEnd_1879692 : Nat := 4983230072969 + 3 ^ 40 * 1879692 * 2
def baseEnd_1879692 : Nat := 643456985607443286736973

theorem tailTrace_1879692 : CollatzResearch.WordTrace tailWord_1879692 prefixEnd_1879692 643456985607443286736973 := by
  unfold tailWord_1879692
  simp only [CollatzResearch.WordTrace]
  refine ⟨34278999753102192340268665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45705333004136256453691553 34278999753102192340268665)
  ·
    refine ⟨25709249814826644255201499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34278999753102192340268665 25709249814826644255201499)
    ·
      refine ⟨38563874722239966382802249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25709249814826644255201499 38563874722239966382802249)
      ·
        refine ⟨28922906041679974787101687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38563874722239966382802249 28922906041679974787101687)
        ·
          refine ⟨43384359062519962180652531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28922906041679974787101687 43384359062519962180652531)
          ·
            refine ⟨65076538593779943270978797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43384359062519962180652531 65076538593779943270978797)
            ·
              refine ⟨24403701972667478726617049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65076538593779943270978797 24403701972667478726617049)
              ·
                refine ⟨18302776479500609044962787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24403701972667478726617049 18302776479500609044962787)
                ·
                  refine ⟨27454164719250913567444181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18302776479500609044962787 27454164719250913567444181)
                  ·
                    refine ⟨643456985607443286736973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 27454164719250913567444181 643456985607443286736973)
                    ·
                      rfl

theorem cell22_1879692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 2, 1, 7].length) (baseStart_1879692 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1879692 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1879692 prefixEnd_1879692 := by exact prefixLift 1879692
  have htrace : WordTrace (prefixWord ++ tailWord_1879692) baseStart_1879692 baseEnd_1879692 := by
    simpa [prefixWord, tailWord_1879692, baseEnd_1879692] using wordTrace_append hprefix tailTrace_1879692
  have hstable : (prefixWord ++ tailWord_1879692).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1879692).length < 2 ^ (prefixWord ++ tailWord_1879692).sum := by decide
  have hdescent : baseEnd_1879692 < baseStart_1879692 := by decide
  rcases family_descends (prefixWord ++ tailWord_1879692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1879711 : List Nat := [1, 1, 2, 7, 1, 1, 1, 1, 7]
def baseStart_1879711 : Nat := 118140960795 + 1879711 * 2 ^ 59
def prefixEnd_1879711 : Nat := 4983230072969 + 3 ^ 40 * 1879711 * 2
def baseEnd_1879711 : Nat := 214487829898577856837305

theorem tailTrace_1879711 : CollatzResearch.WordTrace tailWord_1879711 prefixEnd_1879711 214487829898577856837305 := by
  unfold tailWord_1879711
  simp only [CollatzResearch.WordTrace]
  refine ⟨68558692493135550925478987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45705794995423700616985991 68558692493135550925478987)
  ·
    refine ⟨102838038739703326388218481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68558692493135550925478987 102838038739703326388218481)
    ·
      refine ⟨77128529054777494791163861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102838038739703326388218481 77128529054777494791163861)
      ·
        refine ⟨1807699899721347534167903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 77128529054777494791163861 1807699899721347534167903)
        ·
          refine ⟨2711549849582021301251855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1807699899721347534167903 2711549849582021301251855)
          ·
            refine ⟨4067324774373031951877783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2711549849582021301251855 4067324774373031951877783)
            ·
              refine ⟨6100987161559547927816675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4067324774373031951877783 6100987161559547927816675)
              ·
                refine ⟨9151480742339321891725013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6100987161559547927816675 9151480742339321891725013)
                ·
                  refine ⟨214487829898577856837305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9151480742339321891725013 214487829898577856837305)
                  ·
                    rfl

theorem cell22_1879711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 1, 1, 7].length) (baseStart_1879711 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1879711 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1879711 prefixEnd_1879711 := by exact prefixLift 1879711
  have htrace : WordTrace (prefixWord ++ tailWord_1879711) baseStart_1879711 baseEnd_1879711 := by
    simpa [prefixWord, tailWord_1879711, baseEnd_1879711] using wordTrace_append hprefix tailTrace_1879711
  have hstable : (prefixWord ++ tailWord_1879711).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1879711).length < 2 ^ (prefixWord ++ tailWord_1879711).sum := by decide
  have hdescent : baseEnd_1879711 < baseStart_1879711 := by decide
  rcases family_descends (prefixWord ++ tailWord_1879711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1879741 : List Nat := [1, 4, 1, 2, 1, 2, 4, 2, 1, 4]
def baseStart_1879741 : Nat := 118140960795 + 1879741 * 2 ^ 59
def prefixEnd_1879741 : Nat := 4983230072969 + 3 ^ 40 * 1879741 * 2
def baseEnd_1879741 : Nat := 643473759308823492261823

theorem tailTrace_1879741 : CollatzResearch.WordTrace tailWord_1879741 prefixEnd_1879741 643473759308823492261823 := by
  unfold tailWord_1879741
  simp only [CollatzResearch.WordTrace]
  refine ⟨68559786683026866049071077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45706524455351244032714051 68559786683026866049071077)
  ·
    refine ⟨12854960003067537384200827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 68559786683026866049071077 12854960003067537384200827)
    ·
      refine ⟨19282440004601306076301241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12854960003067537384200827 19282440004601306076301241)
      ·
        refine ⟨14461830003450979557225931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19282440004601306076301241 14461830003450979557225931)
        ·
          refine ⟨21692745005176469335838897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14461830003450979557225931 21692745005176469335838897)
          ·
            refine ⟨16269558753882352001879173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21692745005176469335838897 16269558753882352001879173)
            ·
              refine ⟨3050542266352941000352345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16269558753882352001879173 3050542266352941000352345)
              ·
                refine ⟨2287906699764705750264259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3050542266352941000352345 2287906699764705750264259)
                ·
                  refine ⟨3431860049647058625396389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2287906699764705750264259 3431860049647058625396389)
                  ·
                    refine ⟨643473759308823492261823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3431860049647058625396389 643473759308823492261823)
                    ·
                      rfl

theorem cell22_1879741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 4, 2, 1, 4].length) (baseStart_1879741 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1879741 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1879741 prefixEnd_1879741 := by exact prefixLift 1879741
  have htrace : WordTrace (prefixWord ++ tailWord_1879741) baseStart_1879741 baseEnd_1879741 := by
    simpa [prefixWord, tailWord_1879741, baseEnd_1879741] using wordTrace_append hprefix tailTrace_1879741
  have hstable : (prefixWord ++ tailWord_1879741).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1879741).length < 2 ^ (prefixWord ++ tailWord_1879741).sum := by decide
  have hdescent : baseEnd_1879741 < baseStart_1879741 := by decide
  rcases family_descends (prefixWord ++ tailWord_1879741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1879769 : List Nat := [1, 2, 1, 2, 3, 3, 1, 1, 4, 4]
def baseStart_1879769 : Nat := 118140960795 + 1879769 * 2 ^ 59
def prefixEnd_1879769 : Nat := 4983230072969 + 3 ^ 40 * 1879769 * 2
def baseEnd_1879769 : Nat := 643483344281040752561737

theorem tailTrace_1879769 : CollatzResearch.WordTrace tailWord_1879769 prefixEnd_1879769 643483344281040752561737 := by
  unfold tailWord_1879769
  simp only [CollatzResearch.WordTrace]
  refine ⟨68560807926925426831090361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45707205284616951220726907 68560807926925426831090361)
  ·
    refine ⟨51420605945194070123317771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68560807926925426831090361 51420605945194070123317771)
    ·
      refine ⟨77130908917791105184976657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51420605945194070123317771 77130908917791105184976657)
      ·
        refine ⟨57848181688343328888732493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77130908917791105184976657 57848181688343328888732493)
        ·
          refine ⟨21693068133128748333274685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57848181688343328888732493 21693068133128748333274685)
          ·
            refine ⟨8134900549923280624978007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21693068133128748333274685 8134900549923280624978007)
            ·
              refine ⟨12202350824884920937467011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8134900549923280624978007 12202350824884920937467011)
              ·
                refine ⟨18303526237327381406200517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12202350824884920937467011 18303526237327381406200517)
                ·
                  refine ⟨3431911169498884013662597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18303526237327381406200517 3431911169498884013662597)
                  ·
                    refine ⟨643483344281040752561737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3431911169498884013662597 643483344281040752561737)
                    ·
                      rfl

theorem cell22_1879769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 1, 4, 4].length) (baseStart_1879769 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1879769 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1879769 prefixEnd_1879769 := by exact prefixLift 1879769
  have htrace : WordTrace (prefixWord ++ tailWord_1879769) baseStart_1879769 baseEnd_1879769 := by
    simpa [prefixWord, tailWord_1879769, baseEnd_1879769] using wordTrace_append hprefix tailTrace_1879769
  have hstable : (prefixWord ++ tailWord_1879769).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1879769).length < 2 ^ (prefixWord ++ tailWord_1879769).sum := by decide
  have hdescent : baseEnd_1879769 < baseStart_1879769 := by decide
  rcases family_descends (prefixWord ++ tailWord_1879769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1879784 : List Nat := [2, 1, 4, 1, 3, 1, 1, 9]
def baseStart_1879784 : Nat := 118140960795 + 1879784 * 2 ^ 59
def prefixEnd_1879784 : Nat := 4983230072969 + 3 ^ 40 * 1879784 * 2
def baseEnd_1879784 : Nat := 71498719898620634826299

theorem tailTrace_1879784 : CollatzResearch.WordTrace tailWord_1879784 prefixEnd_1879784 71498719898620634826299 := by
  unfold tailWord_1879784
  simp only [CollatzResearch.WordTrace]
  refine ⟨34280677510935542196443203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45707570014580722928590937 34280677510935542196443203)
  ·
    refine ⟨51421016266403313294664805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34280677510935542196443203 51421016266403313294664805)
    ·
      refine ⟨9641440549950621242749651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51421016266403313294664805 9641440549950621242749651)
      ·
        refine ⟨14462160824925931864124477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9641440549950621242749651 14462160824925931864124477)
        ·
          refine ⟨5423310309347224449046679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14462160824925931864124477 5423310309347224449046679)
          ·
            refine ⟨8134965464020836673570019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5423310309347224449046679 8134965464020836673570019)
            ·
              refine ⟨12202448196031255010355029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8134965464020836673570019 12202448196031255010355029)
              ·
                refine ⟨71498719898620634826299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 12202448196031255010355029 71498719898620634826299)
                ·
                  rfl

theorem cell22_1879784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 9].length) (baseStart_1879784 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1879784 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1879784 prefixEnd_1879784 := by exact prefixLift 1879784
  have htrace : WordTrace (prefixWord ++ tailWord_1879784) baseStart_1879784 baseEnd_1879784 := by
    simpa [prefixWord, tailWord_1879784, baseEnd_1879784] using wordTrace_append hprefix tailTrace_1879784
  have hstable : (prefixWord ++ tailWord_1879784).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1879784).length < 2 ^ (prefixWord ++ tailWord_1879784).sum := by decide
  have hdescent : baseEnd_1879784 < baseStart_1879784 := by decide
  rcases family_descends (prefixWord ++ tailWord_1879784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1879788 : List Nat := [2, 2, 1, 1, 2, 2, 6, 1, 2, 3]
def baseStart_1879788 : Nat := 118140960795 + 1879788 * 2 ^ 59
def prefixEnd_1879788 : Nat := 4983230072969 + 3 ^ 40 * 1879788 * 2
def baseEnd_1879788 : Nat := 643489848369331036336679

theorem tailTrace_1879788 : CollatzResearch.WordTrace tailWord_1879788 prefixEnd_1879788 643489848369331036336679 := by
  unfold tailWord_1879788
  simp only [CollatzResearch.WordTrace]
  refine ⟨34280750456928296538016009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45707667275904395384021345 34280750456928296538016009)
  ·
    refine ⟨25710562842696222403512007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34280750456928296538016009 25710562842696222403512007)
    ·
      refine ⟨38565844264044333605268011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25710562842696222403512007 38565844264044333605268011)
      ·
        refine ⟨57848766396066500407902017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38565844264044333605268011 57848766396066500407902017)
        ·
          refine ⟨43386574797049875305926513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57848766396066500407902017 43386574797049875305926513)
          ·
            refine ⟨32539931097787406479444885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43386574797049875305926513 32539931097787406479444885)
            ·
              refine ⟨1525309270208784678723979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 32539931097787406479444885 1525309270208784678723979)
              ·
                refine ⟨2287963905313177018085969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1525309270208784678723979 2287963905313177018085969)
                ·
                  refine ⟨1715972928984882763564477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2287963905313177018085969 1715972928984882763564477)
                  ·
                    refine ⟨643489848369331036336679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1715972928984882763564477 643489848369331036336679)
                    ·
                      rfl

theorem cell22_1879788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 2, 3].length) (baseStart_1879788 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1879788 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1879788 prefixEnd_1879788 := by exact prefixLift 1879788
  have htrace : WordTrace (prefixWord ++ tailWord_1879788) baseStart_1879788 baseEnd_1879788 := by
    simpa [prefixWord, tailWord_1879788, baseEnd_1879788] using wordTrace_append hprefix tailTrace_1879788
  have hstable : (prefixWord ++ tailWord_1879788).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1879788).length < 2 ^ (prefixWord ++ tailWord_1879788).sum := by decide
  have hdescent : baseEnd_1879788 < baseStart_1879788 := by decide
  rcases family_descends (prefixWord ++ tailWord_1879788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1879921 : List Nat := [1, 2, 2, 2, 1, 3, 2, 3, 2, 4]
def baseStart_1879921 : Nat := 118140960795 + 1879921 * 2 ^ 59
def prefixEnd_1879921 : Nat := 4983230072969 + 3 ^ 40 * 1879921 * 2
def baseEnd_1879921 : Nat := 643535376987363022761271

theorem tailTrace_1879921 : CollatzResearch.WordTrace tailWord_1879921 prefixEnd_1879921 643535376987363022761271 := by
  unfold tailWord_1879921
  simp only [CollatzResearch.WordTrace]
  refine ⟨68566351822374756790623617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45710901214916504527082411 68566351822374756790623617)
  ·
    refine ⟨51424763866781067592967713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68566351822374756790623617 51424763866781067592967713)
    ·
      refine ⟨38568572900085800694725785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51424763866781067592967713 38568572900085800694725785)
      ·
        refine ⟨28926429675064350521044339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38568572900085800694725785 28926429675064350521044339)
        ·
          refine ⟨43389644512596525781566509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28926429675064350521044339 43389644512596525781566509)
          ·
            refine ⟨16271116692223697168087441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43389644512596525781566509 16271116692223697168087441)
            ·
              refine ⟨12203337519167772876065581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16271116692223697168087441 12203337519167772876065581)
              ·
                refine ⟨4576251569687914828524593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12203337519167772876065581 4576251569687914828524593)
                ·
                  refine ⟨3432188677265936121393445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4576251569687914828524593 3432188677265936121393445)
                  ·
                    refine ⟨643535376987363022761271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3432188677265936121393445 643535376987363022761271)
                    ·
                      rfl

theorem cell22_1879921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 3, 2, 4].length) (baseStart_1879921 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1879921 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1879921 prefixEnd_1879921 := by exact prefixLift 1879921
  have htrace : WordTrace (prefixWord ++ tailWord_1879921) baseStart_1879921 baseEnd_1879921 := by
    simpa [prefixWord, tailWord_1879921, baseEnd_1879921] using wordTrace_append hprefix tailTrace_1879921
  have hstable : (prefixWord ++ tailWord_1879921).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1879921).length < 2 ^ (prefixWord ++ tailWord_1879921).sum := by decide
  have hdescent : baseEnd_1879921 < baseStart_1879921 := by decide
  rcases family_descends (prefixWord ++ tailWord_1879921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1879998 : List Nat := [4, 2, 1, 1, 1, 3, 1, 4, 5]
def baseStart_1879998 : Nat := 118140960795 + 1879998 * 2 ^ 59
def prefixEnd_1879998 : Nat := 4983230072969 + 3 ^ 40 * 1879998 * 2
def baseEnd_1879998 : Nat := 214520578553653496195345

theorem tailTrace_1879998 : CollatzResearch.WordTrace tailWord_1879998 prefixEnd_1879998 214520578553653496195345 := by
  unfold tailWord_1879998
  simp only [CollatzResearch.WordTrace]
  refine ⟨8571145030386974867647081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45712773495397199294117765 8571145030386974867647081)
  ·
    refine ⟨6428358772790231150735311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8571145030386974867647081 6428358772790231150735311)
    ·
      refine ⟨9642538159185346726102967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6428358772790231150735311 9642538159185346726102967)
      ·
        refine ⟨14463807238778020089154451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9642538159185346726102967 14463807238778020089154451)
        ·
          refine ⟨21695710858167030133731677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14463807238778020089154451 21695710858167030133731677)
          ·
            refine ⟨8135891571812636300149379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21695710858167030133731677 8135891571812636300149379)
            ·
              refine ⟨12203837357718954450224069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8135891571812636300149379 12203837357718954450224069)
              ·
                refine ⟨2288219504572303959417013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12203837357718954450224069 2288219504572303959417013)
                ·
                  refine ⟨214520578553653496195345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2288219504572303959417013 214520578553653496195345)
                  ·
                    rfl

theorem cell22_1879998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 4, 5].length) (baseStart_1879998 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1879998 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1879998 prefixEnd_1879998 := by exact prefixLift 1879998
  have htrace : WordTrace (prefixWord ++ tailWord_1879998) baseStart_1879998 baseEnd_1879998 := by
    simpa [prefixWord, tailWord_1879998, baseEnd_1879998] using wordTrace_append hprefix tailTrace_1879998
  have hstable : (prefixWord ++ tailWord_1879998).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1879998).length < 2 ^ (prefixWord ++ tailWord_1879998).sum := by decide
  have hdescent : baseEnd_1879998 < baseStart_1879998 := by decide
  rcases family_descends (prefixWord ++ tailWord_1879998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1880011 : List Nat := [1, 1, 1, 1, 3, 4, 1, 1, 5, 4]
def baseStart_1880011 : Nat := 118140960795 + 1880011 * 2 ^ 59
def prefixEnd_1880011 : Nat := 4983230072969 + 3 ^ 40 * 1880011 * 2
def baseEnd_1880011 : Nat := 643566185826632788010995

theorem tailTrace_1880011 : CollatzResearch.WordTrace tailWord_1880011 prefixEnd_1880011 643566185826632788010995 := by
  unfold tailWord_1880011
  simp only [CollatzResearch.WordTrace]
  refine ⟨68569634392048702161399887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45713089594699134774266591 68569634392048702161399887)
  ·
    refine ⟨102854451588073053242099831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68569634392048702161399887 102854451588073053242099831)
    ·
      refine ⟨154281677382109579863149747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102854451588073053242099831 154281677382109579863149747)
      ·
        refine ⟨231422516073164369794724621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154281677382109579863149747 231422516073164369794724621)
        ·
          refine ⟨86783443527436638673021733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 231422516073164369794724621 86783443527436638673021733)
          ·
            refine ⟨16271895661394369751191575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 86783443527436638673021733 16271895661394369751191575)
            ·
              refine ⟨24407843492091554626787363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16271895661394369751191575 24407843492091554626787363)
              ·
                refine ⟨36611765238137331940181045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24407843492091554626787363 36611765238137331940181045)
                ·
                  refine ⟨3432352991075374869391973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 36611765238137331940181045 3432352991075374869391973)
                  ·
                    refine ⟨643566185826632788010995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3432352991075374869391973 643566185826632788010995)
                    ·
                      rfl

theorem cell22_1880011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 1, 5, 4].length) (baseStart_1880011 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1880011 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1880011 prefixEnd_1880011 := by exact prefixLift 1880011
  have htrace : WordTrace (prefixWord ++ tailWord_1880011) baseStart_1880011 baseEnd_1880011 := by
    simpa [prefixWord, tailWord_1880011, baseEnd_1880011] using wordTrace_append hprefix tailTrace_1880011
  have hstable : (prefixWord ++ tailWord_1880011).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1880011).length < 2 ^ (prefixWord ++ tailWord_1880011).sum := by decide
  have hdescent : baseEnd_1880011 < baseStart_1880011 := by decide
  rcases family_descends (prefixWord ++ tailWord_1880011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1880126 : List Nat := [4, 2, 1, 3, 2, 2, 2, 1, 2, 3]
def baseStart_1880126 : Nat := 118140960795 + 1880126 * 2 ^ 59
def prefixEnd_1880126 : Nat := 4983230072969 + 3 ^ 40 * 1880126 * 2
def baseEnd_1880126 : Nat := 643605552676810821385643

theorem tailTrace_1880126 : CollatzResearch.WordTrace tailWord_1880126 prefixEnd_1880126 643605552676810821385643 := by
  unfold tailWord_1880126
  simp only [CollatzResearch.WordTrace]
  refine ⟨8571728598329009600229529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45715885857754717867890821 8571728598329009600229529)
  ·
    refine ⟨6428796448746757200172147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8571728598329009600229529 6428796448746757200172147)
    ·
      refine ⟨9643194673120135800258221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6428796448746757200172147 9643194673120135800258221)
      ·
        refine ⟨3616198002420050925096833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9643194673120135800258221 3616198002420050925096833)
        ·
          refine ⟨2712148501815038193822625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3616198002420050925096833 2712148501815038193822625)
          ·
            refine ⟨2034111376361278645366969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2712148501815038193822625 2034111376361278645366969)
            ·
              refine ⟨1525583532270958984025227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2034111376361278645366969 1525583532270958984025227)
              ·
                refine ⟨2288375298406438476037841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1525583532270958984025227 2288375298406438476037841)
                ·
                  refine ⟨1716281473804828857028381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2288375298406438476037841 1716281473804828857028381)
                  ·
                    refine ⟨643605552676810821385643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1716281473804828857028381 643605552676810821385643)
                    ·
                      rfl

theorem cell22_1880126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 2, 2, 1, 2, 3].length) (baseStart_1880126 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1880126 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1880126 prefixEnd_1880126 := by exact prefixLift 1880126
  have htrace : WordTrace (prefixWord ++ tailWord_1880126) baseStart_1880126 baseEnd_1880126 := by
    simpa [prefixWord, tailWord_1880126, baseEnd_1880126] using wordTrace_append hprefix tailTrace_1880126
  have hstable : (prefixWord ++ tailWord_1880126).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1880126).length < 2 ^ (prefixWord ++ tailWord_1880126).sum := by decide
  have hdescent : baseEnd_1880126 < baseStart_1880126 := by decide
  rcases family_descends (prefixWord ++ tailWord_1880126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1880148 : List Nat := [2, 4, 1, 1, 1, 1, 1, 2, 4, 5]
def baseStart_1880148 : Nat := 118140960795 + 1880148 * 2 ^ 59
def prefixEnd_1880148 : Nat := 4983230072969 + 3 ^ 40 * 1880148 * 2
def baseEnd_1880148 : Nat := 643613083726410097335575

theorem tailTrace_1880148 : CollatzResearch.WordTrace tailWord_1880148 prefixEnd_1880148 643613083726410097335575 := by
  unfold tailWord_1880148
  simp only [CollatzResearch.WordTrace]
  refine ⟨34287315596276187279568549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45716420795034916372758065 34287315596276187279568549)
  ·
    refine ⟨6428871674301785114919103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34287315596276187279568549 6428871674301785114919103)
    ·
      refine ⟨9643307511452677672378655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6428871674301785114919103 9643307511452677672378655)
      ·
        refine ⟨14464961267179016508567983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9643307511452677672378655 14464961267179016508567983)
        ·
          refine ⟨21697441900768524762851975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14464961267179016508567983 21697441900768524762851975)
          ·
            refine ⟨32546162851152787144277963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21697441900768524762851975 32546162851152787144277963)
            ·
              refine ⟨48819244276729180716416945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32546162851152787144277963 48819244276729180716416945)
              ·
                refine ⟨36614433207546885537312709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48819244276729180716416945 36614433207546885537312709)
                ·
                  refine ⟨6865206226415041038246133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36614433207546885537312709 6865206226415041038246133)
                  ·
                    refine ⟨643613083726410097335575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6865206226415041038246133 643613083726410097335575)
                    ·
                      rfl

theorem cell22_1880148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 2, 4, 5].length) (baseStart_1880148 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1880148 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1880148 prefixEnd_1880148 := by exact prefixLift 1880148
  have htrace : WordTrace (prefixWord ++ tailWord_1880148) baseStart_1880148 baseEnd_1880148 := by
    simpa [prefixWord, tailWord_1880148, baseEnd_1880148] using wordTrace_append hprefix tailTrace_1880148
  have hstable : (prefixWord ++ tailWord_1880148).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1880148).length < 2 ^ (prefixWord ++ tailWord_1880148).sum := by decide
  have hdescent : baseEnd_1880148 < baseStart_1880148 := by decide
  rcases family_descends (prefixWord ++ tailWord_1880148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1880208 : List Nat := [2, 1, 1, 1, 1, 1, 7, 1, 1, 6]
def baseStart_1880208 : Nat := 118140960795 + 1880208 * 2 ^ 59
def prefixEnd_1880208 : Nat := 4983230072969 + 3 ^ 40 * 1880208 * 2
def baseEnd_1880208 : Nat := 643633622952589940835391

theorem tailTrace_1880208 : CollatzResearch.WordTrace tailWord_1880208 prefixEnd_1880208 643633622952589940835391 := by
  unfold tailWord_1880208
  simp only [CollatzResearch.WordTrace]
  refine ⟨34288409786167502403160639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45717879714890003204214185 34288409786167502403160639)
  ·
    refine ⟨51432614679251253604740959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34288409786167502403160639 51432614679251253604740959)
    ·
      refine ⟨77148922018876880407111439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51432614679251253604740959 77148922018876880407111439)
      ·
        refine ⟨115723383028315320610667159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77148922018876880407111439 115723383028315320610667159)
        ·
          refine ⟨173585074542472980916000739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115723383028315320610667159 173585074542472980916000739)
          ·
            refine ⟨260377611813709471374001109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173585074542472980916000739 260377611813709471374001109)
            ·
              refine ⟨6102600276883815735328151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 260377611813709471374001109 6102600276883815735328151)
              ·
                refine ⟨9153900415325723602992227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6102600276883815735328151 9153900415325723602992227)
                ·
                  refine ⟨13730850622988585404488341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9153900415325723602992227 13730850622988585404488341)
                  ·
                    refine ⟨643633622952589940835391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13730850622988585404488341 643633622952589940835391)
                    ·
                      rfl

theorem cell22_1880208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 7, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 7, 1, 1, 6].length) (baseStart_1880208 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1880208 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1880208 prefixEnd_1880208 := by exact prefixLift 1880208
  have htrace : WordTrace (prefixWord ++ tailWord_1880208) baseStart_1880208 baseEnd_1880208 := by
    simpa [prefixWord, tailWord_1880208, baseEnd_1880208] using wordTrace_append hprefix tailTrace_1880208
  have hstable : (prefixWord ++ tailWord_1880208).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1880208).length < 2 ^ (prefixWord ++ tailWord_1880208).sum := by decide
  have hdescent : baseEnd_1880208 < baseStart_1880208 := by decide
  rcases family_descends (prefixWord ++ tailWord_1880208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1880210 : List Nat := [3, 2, 3, 1, 1, 1, 1, 4, 1, 5]
def baseStart_1880210 : Nat := 118140960795 + 1880210 * 2 ^ 59
def prefixEnd_1880210 : Nat := 4983230072969 + 3 ^ 40 * 1880210 * 2
def baseEnd_1880210 : Nat := 643634307593462602285385

theorem tailTrace_1880210 : CollatzResearch.WordTrace tailWord_1880210 prefixEnd_1880210 643634307593462602285385 := by
  unfold tailWord_1880210
  simp only [CollatzResearch.WordTrace]
  refine ⟨17144223129581939786973521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45717928345551839431929389 17144223129581939786973521)
  ·
    refine ⟨12858167347186454840230141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17144223129581939786973521 12858167347186454840230141)
    ·
      refine ⟨4821812755194920565086303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12858167347186454840230141 4821812755194920565086303)
      ·
        refine ⟨7232719132792380847629455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4821812755194920565086303 7232719132792380847629455)
        ·
          refine ⟨10849078699188571271444183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7232719132792380847629455 10849078699188571271444183)
          ·
            refine ⟨16273618048782856907166275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10849078699188571271444183 16273618048782856907166275)
            ·
              refine ⟨24410427073174285360749413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16273618048782856907166275 24410427073174285360749413)
              ·
                refine ⟨4576955076220178505140515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24410427073174285360749413 4576955076220178505140515)
                ·
                  refine ⟨6865432614330267757710773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4576955076220178505140515 6865432614330267757710773)
                  ·
                    refine ⟨643634307593462602285385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6865432614330267757710773 643634307593462602285385)
                    ·
                      rfl

theorem cell22_1880210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 4, 1, 5].length) (baseStart_1880210 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1880210 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1880210 prefixEnd_1880210 := by exact prefixLift 1880210
  have htrace : WordTrace (prefixWord ++ tailWord_1880210) baseStart_1880210 baseEnd_1880210 := by
    simpa [prefixWord, tailWord_1880210, baseEnd_1880210] using wordTrace_append hprefix tailTrace_1880210
  have hstable : (prefixWord ++ tailWord_1880210).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1880210).length < 2 ^ (prefixWord ++ tailWord_1880210).sum := by decide
  have hdescent : baseEnd_1880210 < baseStart_1880210 := by decide
  rcases family_descends (prefixWord ++ tailWord_1880210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1880257 : List Nat := [1, 2, 6, 1, 2, 1, 1, 8]
def baseStart_1880257 : Nat := 118140960795 + 1880257 * 2 ^ 59
def prefixEnd_1880257 : Nat := 4983230072969 + 3 ^ 40 * 1880257 * 2
def baseEnd_1880257 : Nat := 71516710739330016262249

theorem tailTrace_1880257 : CollatzResearch.WordTrace tailWord_1880257 prefixEnd_1880257 71516710739330016262249 := by
  unfold tailWord_1880257
  simp only [CollatzResearch.WordTrace]
  refine ⟨68578606749157486174855025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45719071166104990783236683 68578606749157486174855025)
  ·
    refine ⟨51433955061868114631141269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68578606749157486174855025 51433955061868114631141269)
    ·
      refine ⟨2410966643525067873334747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 51433955061868114631141269 2410966643525067873334747)
      ·
        refine ⟨3616449965287601810002121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2410966643525067873334747 3616449965287601810002121)
        ·
          refine ⟨2712337473965701357501591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3616449965287601810002121 2712337473965701357501591)
          ·
            refine ⟨4068506210948552036252387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2712337473965701357501591 4068506210948552036252387)
            ·
              refine ⟨6102759316422828054378581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4068506210948552036252387 6102759316422828054378581)
              ·
                refine ⟨71516710739330016262249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6102759316422828054378581 71516710739330016262249)
                ·
                  rfl

theorem cell22_1880257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 1, 8].length) (baseStart_1880257 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1880257 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1880257 prefixEnd_1880257 := by exact prefixLift 1880257
  have htrace : WordTrace (prefixWord ++ tailWord_1880257) baseStart_1880257 baseEnd_1880257 := by
    simpa [prefixWord, tailWord_1880257, baseEnd_1880257] using wordTrace_append hprefix tailTrace_1880257
  have hstable : (prefixWord ++ tailWord_1880257).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1880257).length < 2 ^ (prefixWord ++ tailWord_1880257).sum := by decide
  have hdescent : baseEnd_1880257 < baseStart_1880257 := by decide
  rcases family_descends (prefixWord ++ tailWord_1880257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1880377 : List Nat := [1, 2, 1, 6, 1, 2, 1, 1, 1, 6]
def baseStart_1880377 : Nat := 118140960795 + 1880377 * 2 ^ 59
def prefixEnd_1880377 : Nat := 4983230072969 + 3 ^ 40 * 1880377 * 2
def baseEnd_1880377 : Nat := 643691475106329833359873

theorem tailTrace_1880377 : CollatzResearch.WordTrace tailWord_1880377 prefixEnd_1880377 643691475106329833359873 := by
  unfold tailWord_1880377
  simp only [CollatzResearch.WordTrace]
  refine ⟨68582983508722746669223385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45721989005815164446148923 68582983508722746669223385)
  ·
    refine ⟨51437237631542060001917539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68582983508722746669223385 51437237631542060001917539)
    ·
      refine ⟨77155856447313090002876309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51437237631542060001917539 77155856447313090002876309)
      ·
        refine ⟨3616680770967801093884827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 77155856447313090002876309 3616680770967801093884827)
        ·
          refine ⟨5425021156451701640827241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3616680770967801093884827 5425021156451701640827241)
          ·
            refine ⟨4068765867338776230620431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5425021156451701640827241 4068765867338776230620431)
            ·
              refine ⟨6103148801008164345930647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4068765867338776230620431 6103148801008164345930647)
              ·
                refine ⟨9154723201512246518895971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6103148801008164345930647 9154723201512246518895971)
                ·
                  refine ⟨13732084802268369778343957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9154723201512246518895971 13732084802268369778343957)
                  ·
                    refine ⟨643691475106329833359873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13732084802268369778343957 643691475106329833359873)
                    ·
                      rfl

theorem cell22_1880377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 1, 1, 1, 6].length) (baseStart_1880377 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1880377 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1880377 prefixEnd_1880377 := by exact prefixLift 1880377
  have htrace : WordTrace (prefixWord ++ tailWord_1880377) baseStart_1880377 baseEnd_1880377 := by
    simpa [prefixWord, tailWord_1880377, baseEnd_1880377] using wordTrace_append hprefix tailTrace_1880377
  have hstable : (prefixWord ++ tailWord_1880377).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1880377).length < 2 ^ (prefixWord ++ tailWord_1880377).sum := by decide
  have hdescent : baseEnd_1880377 < baseStart_1880377 := by decide
  rcases family_descends (prefixWord ++ tailWord_1880377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1880424 : List Nat := [2, 1, 4, 2, 2, 1, 2, 2, 3, 3]
def baseStart_1880424 : Nat := 118140960795 + 1880424 * 2 ^ 59
def prefixEnd_1880424 : Nat := 4983230072969 + 3 ^ 40 * 1880424 * 2
def baseEnd_1880424 : Nat := 643707564166837377434729

theorem tailTrace_1880424 : CollatzResearch.WordTrace tailWord_1880424 prefixEnd_1880424 643707564166837377434729 := by
  unfold tailWord_1880424
  simp only [CollatzResearch.WordTrace]
  refine ⟨34292348869776236848092163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45723131826368315797456217 34292348869776236848092163)
  ·
    refine ⟨51438523304664355272138245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34292348869776236848092163 51438523304664355272138245)
    ·
      refine ⟨9644723119624566613525921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51438523304664355272138245 9644723119624566613525921)
      ·
        refine ⟨7233542339718424960144441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9644723119624566613525921 7233542339718424960144441)
        ·
          refine ⟨5425156754788818720108331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7233542339718424960144441 5425156754788818720108331)
          ·
            refine ⟨8137735132183228080162497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5425156754788818720108331 8137735132183228080162497)
            ·
              refine ⟨6103301349137421060121873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8137735132183228080162497 6103301349137421060121873)
              ·
                refine ⟨4577476011853065795091405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6103301349137421060121873 4577476011853065795091405)
                ·
                  refine ⟨1716553504444899673159277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4577476011853065795091405 1716553504444899673159277)
                  ·
                    refine ⟨643707564166837377434729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1716553504444899673159277 643707564166837377434729)
                    ·
                      rfl

theorem cell22_1880424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 2, 2, 3, 3].length) (baseStart_1880424 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1880424 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1880424 prefixEnd_1880424 := by exact prefixLift 1880424
  have htrace : WordTrace (prefixWord ++ tailWord_1880424) baseStart_1880424 baseEnd_1880424 := by
    simpa [prefixWord, tailWord_1880424, baseEnd_1880424] using wordTrace_append hprefix tailTrace_1880424
  have hstable : (prefixWord ++ tailWord_1880424).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1880424).length < 2 ^ (prefixWord ++ tailWord_1880424).sum := by decide
  have hdescent : baseEnd_1880424 < baseStart_1880424 := by decide
  rcases family_descends (prefixWord ++ tailWord_1880424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1880437 : List Nat := [1, 3, 4, 1, 2, 1, 1, 2, 7]
def baseStart_1880437 : Nat := 118140960795 + 1880437 * 2 ^ 59
def prefixEnd_1880437 : Nat := 4983230072969 + 3 ^ 40 * 1880437 * 2
def baseEnd_1880437 : Nat := 214570671444169892286563

theorem tailTrace_1880437 : CollatzResearch.WordTrace tailWord_1880437 prefixEnd_1880437 214570671444169892286563 := by
  unfold tailWord_1880437
  simp only [CollatzResearch.WordTrace]
  refine ⟨68585171888505376916407565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45723447925670251277605043 68585171888505376916407565)
  ·
    refine ⟨25719439458189516343652837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68585171888505376916407565 25719439458189516343652837)
    ·
      refine ⟨4822394898410534314434907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25719439458189516343652837 4822394898410534314434907)
      ·
        refine ⟨7233592347615801471652361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4822394898410534314434907 7233592347615801471652361)
        ·
          refine ⟨5425194260711851103739271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7233592347615801471652361 5425194260711851103739271)
          ·
            refine ⟨8137791391067776655608907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5425194260711851103739271 8137791391067776655608907)
            ·
              refine ⟨12206687086601664983413361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8137791391067776655608907 12206687086601664983413361)
              ·
                refine ⟨9155015314951248737560021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12206687086601664983413361 9155015314951248737560021)
                ·
                  refine ⟨214570671444169892286563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9155015314951248737560021 214570671444169892286563)
                  ·
                    rfl

theorem cell22_1880437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 2, 7].length) (baseStart_1880437 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1880437 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1880437 prefixEnd_1880437 := by exact prefixLift 1880437
  have htrace : WordTrace (prefixWord ++ tailWord_1880437) baseStart_1880437 baseEnd_1880437 := by
    simpa [prefixWord, tailWord_1880437, baseEnd_1880437] using wordTrace_append hprefix tailTrace_1880437
  have hstable : (prefixWord ++ tailWord_1880437).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1880437).length < 2 ^ (prefixWord ++ tailWord_1880437).sum := by decide
  have hdescent : baseEnd_1880437 < baseStart_1880437 := by decide
  rcases family_descends (prefixWord ++ tailWord_1880437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1880458 : List Nat := [3, 1, 2, 5, 1, 2, 1, 1, 3, 3]
def baseStart_1880458 : Nat := 118140960795 + 1880458 * 2 ^ 59
def prefixEnd_1880458 : Nat := 4983230072969 + 3 ^ 40 * 1880458 * 2
def baseEnd_1880458 : Nat := 643719203061672622084625

theorem tailTrace_1880458 : CollatzResearch.WordTrace tailWord_1880458 prefixEnd_1880458 643719203061672622084625 := by
  unfold tailWord_1880458
  simp only [CollatzResearch.WordTrace]
  refine ⟨17146484455357324375730507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45723958547619531668614685 17146484455357324375730507)
  ·
    refine ⟨25719726683035986563595761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17146484455357324375730507 25719726683035986563595761)
    ·
      refine ⟨19289795012276989922696821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25719726683035986563595761 19289795012276989922696821)
      ·
        refine ⟨1808418282400967805252827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 19289795012276989922696821 1808418282400967805252827)
        ·
          refine ⟨2712627423601451707879241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1808418282400967805252827 2712627423601451707879241)
          ·
            refine ⟨2034470567701088780909431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2712627423601451707879241 2034470567701088780909431)
            ·
              refine ⟨3051705851551633171364147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2034470567701088780909431 3051705851551633171364147)
              ·
                refine ⟨4577558777327449757046221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3051705851551633171364147 4577558777327449757046221)
                ·
                  refine ⟨1716584541497793658892333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4577558777327449757046221 1716584541497793658892333)
                  ·
                    refine ⟨643719203061672622084625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1716584541497793658892333 643719203061672622084625)
                    ·
                      rfl

theorem cell22_1880458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 2, 1, 1, 3, 3].length) (baseStart_1880458 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1880458 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1880458 prefixEnd_1880458 := by exact prefixLift 1880458
  have htrace : WordTrace (prefixWord ++ tailWord_1880458) baseStart_1880458 baseEnd_1880458 := by
    simpa [prefixWord, tailWord_1880458, baseEnd_1880458] using wordTrace_append hprefix tailTrace_1880458
  have hstable : (prefixWord ++ tailWord_1880458).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1880458).length < 2 ^ (prefixWord ++ tailWord_1880458).sum := by decide
  have hdescent : baseEnd_1880458 < baseStart_1880458 := by decide
  rcases family_descends (prefixWord ++ tailWord_1880458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1880482 : List Nat := [3, 3, 1, 2, 1, 1, 2, 1, 8]
def baseStart_1880482 : Nat := 118140960795 + 1880482 * 2 ^ 59
def prefixEnd_1880482 : Nat := 4983230072969 + 3 ^ 40 * 1880482 * 2
def baseEnd_1880482 : Nat := 214575806250714853161517

theorem tailTrace_1880482 : CollatzResearch.WordTrace tailWord_1880482 prefixEnd_1880482 214575806250714853161517 := by
  unfold tailWord_1880482
  simp only [CollatzResearch.WordTrace]
  refine ⟨17146703293335587400448925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45724542115561566401197133 17146703293335587400448925)
  ·
    refine ⟨6430013735000845275168347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17146703293335587400448925 6430013735000845275168347)
    ·
      refine ⟨9645020602501267912752521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6430013735000845275168347 9645020602501267912752521)
      ·
        refine ⟨7233765451875950934564391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9645020602501267912752521 7233765451875950934564391)
        ·
          refine ⟨10850648177813926401846587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7233765451875950934564391 10850648177813926401846587)
          ·
            refine ⟨16275972266720889602769881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10850648177813926401846587 16275972266720889602769881)
            ·
              refine ⟨12206979200040667202077411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16275972266720889602769881 12206979200040667202077411)
              ·
                refine ⟨18310468800061000803116117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12206979200040667202077411 18310468800061000803116117)
                ·
                  refine ⟨214575806250714853161517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 18310468800061000803116117 214575806250714853161517)
                  ·
                    rfl

theorem cell22_1880482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 1, 8].length) (baseStart_1880482 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1880482 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1880482 prefixEnd_1880482 := by exact prefixLift 1880482
  have htrace : WordTrace (prefixWord ++ tailWord_1880482) baseStart_1880482 baseEnd_1880482 := by
    simpa [prefixWord, tailWord_1880482, baseEnd_1880482] using wordTrace_append hprefix tailTrace_1880482
  have hstable : (prefixWord ++ tailWord_1880482).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1880482).length < 2 ^ (prefixWord ++ tailWord_1880482).sum := by decide
  have hdescent : baseEnd_1880482 < baseStart_1880482 := by decide
  rcases family_descends (prefixWord ++ tailWord_1880482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1880484 : List Nat := [2, 3, 1, 2, 1, 1, 5, 2, 1, 4]
def baseStart_1880484 : Nat := 118140960795 + 1880484 * 2 ^ 59
def prefixEnd_1880484 : Nat := 4983230072969 + 3 ^ 40 * 1880484 * 2
def baseEnd_1880484 : Nat := 643728103393017220934545

theorem tailTrace_1880484 : CollatzResearch.WordTrace tailWord_1880484 prefixEnd_1880484 643728103393017220934545 := by
  unfold tailWord_1880484
  simp only [CollatzResearch.WordTrace]
  refine ⟨34293443059667551971684253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45724590746223402628912337 34293443059667551971684253)
  ·
    refine ⟨12860041147375331989381595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34293443059667551971684253 12860041147375331989381595)
    ·
      refine ⟨19290061721062997984072393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12860041147375331989381595 19290061721062997984072393)
      ·
        refine ⟨14467546290797248488054295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19290061721062997984072393 14467546290797248488054295)
        ·
          refine ⟨21701319436195872732081443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14467546290797248488054295 21701319436195872732081443)
          ·
            refine ⟨32551979154293809098122165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21701319436195872732081443 32551979154293809098122165)
            ·
              refine ⟨3051748045715044602948953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 32551979154293809098122165 3051748045715044602948953)
              ·
                refine ⟨2288811034286283452211715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3051748045715044602948953 2288811034286283452211715)
                ·
                  refine ⟨3433216551429425178317573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2288811034286283452211715 3433216551429425178317573)
                  ·
                    refine ⟨643728103393017220934545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3433216551429425178317573 643728103393017220934545)
                    ·
                      rfl

theorem cell22_1880484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 5, 2, 1, 4].length) (baseStart_1880484 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1880484 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1880484 prefixEnd_1880484 := by exact prefixLift 1880484
  have htrace : WordTrace (prefixWord ++ tailWord_1880484) baseStart_1880484 baseEnd_1880484 := by
    simpa [prefixWord, tailWord_1880484, baseEnd_1880484] using wordTrace_append hprefix tailTrace_1880484
  have hstable : (prefixWord ++ tailWord_1880484).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1880484).length < 2 ^ (prefixWord ++ tailWord_1880484).sum := by decide
  have hdescent : baseEnd_1880484 < baseStart_1880484 := by decide
  rcases family_descends (prefixWord ++ tailWord_1880484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1880497 : List Nat := [1, 2, 2, 4, 1, 2, 1, 1, 3, 5]
def baseStart_1880497 : Nat := 118140960795 + 1880497 * 2 ^ 59
def prefixEnd_1880497 : Nat := 4983230072969 + 3 ^ 40 * 1880497 * 2
def baseEnd_1880497 : Nat := 643732553558689520359505

theorem tailTrace_1880497 : CollatzResearch.WordTrace tailWord_1880497 prefixEnd_1880497 643732553558689520359505 := by
  unfold tailWord_1880497
  simp only [CollatzResearch.WordTrace]
  refine ⟨68587360268288007163591745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45724906845525338109061163 68587360268288007163591745)
  ·
    refine ⟨51440520201216005372693809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68587360268288007163591745 51440520201216005372693809)
    ·
      refine ⟨38580390150912004029520357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51440520201216005372693809 38580390150912004029520357)
      ·
        refine ⟨7233823153296000755535067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38580390150912004029520357 7233823153296000755535067)
        ·
          refine ⟨10850734729944001133302601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7233823153296000755535067 10850734729944001133302601)
          ·
            refine ⟨8138051047458000849976951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10850734729944001133302601 8138051047458000849976951)
            ·
              refine ⟨12207076571187001274965427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8138051047458000849976951 12207076571187001274965427)
              ·
                refine ⟨18310614856780501912448141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12207076571187001274965427 18310614856780501912448141)
                ·
                  refine ⟨6866480571292688217168053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18310614856780501912448141 6866480571292688217168053)
                  ·
                    refine ⟨643732553558689520359505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6866480571292688217168053 643732553558689520359505)
                    ·
                      rfl

theorem cell22_1880497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 1, 3, 5].length) (baseStart_1880497 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1880497 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1880497 prefixEnd_1880497 := by exact prefixLift 1880497
  have htrace : WordTrace (prefixWord ++ tailWord_1880497) baseStart_1880497 baseEnd_1880497 := by
    simpa [prefixWord, tailWord_1880497, baseEnd_1880497] using wordTrace_append hprefix tailTrace_1880497
  have hstable : (prefixWord ++ tailWord_1880497).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1880497).length < 2 ^ (prefixWord ++ tailWord_1880497).sum := by decide
  have hdescent : baseEnd_1880497 < baseStart_1880497 := by decide
  rcases family_descends (prefixWord ++ tailWord_1880497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1880565 : List Nat := [1, 3, 5, 1, 2, 2, 1, 2, 2, 3]
def baseStart_1880565 : Nat := 118140960795 + 1880565 * 2 ^ 59
def prefixEnd_1880565 : Nat := 4983230072969 + 3 ^ 40 * 1880565 * 2
def baseEnd_1880565 : Nat := 643755831348360009659297

theorem tailTrace_1880565 : CollatzResearch.WordTrace tailWord_1880565 prefixEnd_1880565 643755831348360009659297 := by
  unfold tailWord_1880565
  simp only [CollatzResearch.WordTrace]
  refine ⟨68589840432041654777067149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45726560288027769851378099 68589840432041654777067149)
  ·
    refine ⟨25721190162015620541400181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68589840432041654777067149 25721190162015620541400181)
    ·
      refine ⟨2411361577688964425756267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 25721190162015620541400181 2411361577688964425756267)
      ·
        refine ⟨3617042366533446638634401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2411361577688964425756267 3617042366533446638634401)
        ·
          refine ⟨2712781774900084978975801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3617042366533446638634401 2712781774900084978975801)
          ·
            refine ⟨2034586331175063734231851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2712781774900084978975801 2034586331175063734231851)
            ·
              refine ⟨3051879496762595601347777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2034586331175063734231851 3051879496762595601347777)
              ·
                refine ⟨2288909622571946701010833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3051879496762595601347777 2288909622571946701010833)
                ·
                  refine ⟨1716682216928960025758125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2288909622571946701010833 1716682216928960025758125)
                  ·
                    refine ⟨643755831348360009659297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1716682216928960025758125 643755831348360009659297)
                    ·
                      rfl

theorem cell22_1880565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 2, 1, 2, 2, 3].length) (baseStart_1880565 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1880565 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1880565 prefixEnd_1880565 := by exact prefixLift 1880565
  have htrace : WordTrace (prefixWord ++ tailWord_1880565) baseStart_1880565 baseEnd_1880565 := by
    simpa [prefixWord, tailWord_1880565, baseEnd_1880565] using wordTrace_append hprefix tailTrace_1880565
  have hstable : (prefixWord ++ tailWord_1880565).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1880565).length < 2 ^ (prefixWord ++ tailWord_1880565).sum := by decide
  have hdescent : baseEnd_1880565 < baseStart_1880565 := by decide
  rcases family_descends (prefixWord ++ tailWord_1880565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1880634 : List Nat := [3, 1, 1, 1, 3, 3, 3, 1, 6]
def baseStart_1880634 : Nat := 118140960795 + 1880634 * 2 ^ 59
def prefixEnd_1880634 : Nat := 4983230072969 + 3 ^ 40 * 1880634 * 2
def baseEnd_1880634 : Nat := 214593150486155609894695

theorem tailTrace_1880634 : CollatzResearch.WordTrace tailWord_1880634 prefixEnd_1880634 214593150486155609894695 := by
  unfold tailWord_1880634
  simp only [CollatzResearch.WordTrace]
  refine ⟨17148089267197919890332239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45728238045861119707552637 17148089267197919890332239)
  ·
    refine ⟨25722133900796879835498359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17148089267197919890332239 25722133900796879835498359)
    ·
      refine ⟨38583200851195319753247539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25722133900796879835498359 38583200851195319753247539)
      ·
        refine ⟨57874801276792979629871309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38583200851195319753247539 57874801276792979629871309)
        ·
          refine ⟨21703050478797367361201741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57874801276792979629871309 21703050478797367361201741)
          ·
            refine ⟨8138643929549012760450653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21703050478797367361201741 8138643929549012760450653)
            ·
              refine ⟨3051991473580879785168995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8138643929549012760450653 3051991473580879785168995)
              ·
                refine ⟨4577987210371319677753493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3051991473580879785168995 4577987210371319677753493)
                ·
                  refine ⟨214593150486155609894695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4577987210371319677753493 214593150486155609894695)
                  ·
                    rfl

theorem cell22_1880634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 3, 1, 6].length) (baseStart_1880634 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1880634 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1880634 prefixEnd_1880634 := by exact prefixLift 1880634
  have htrace : WordTrace (prefixWord ++ tailWord_1880634) baseStart_1880634 baseEnd_1880634 := by
    simpa [prefixWord, tailWord_1880634, baseEnd_1880634] using wordTrace_append hprefix tailTrace_1880634
  have hstable : (prefixWord ++ tailWord_1880634).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1880634).length < 2 ^ (prefixWord ++ tailWord_1880634).sum := by decide
  have hdescent : baseEnd_1880634 < baseStart_1880634 := by decide
  rcases family_descends (prefixWord ++ tailWord_1880634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1880653 : List Nat := [1, 6, 1, 1, 2, 1, 3, 2, 1, 4]
def baseStart_1880653 : Nat := 118140960795 + 1880653 * 2 ^ 59
def prefixEnd_1880653 : Nat := 4983230072969 + 3 ^ 40 * 1880653 * 2
def baseEnd_1880653 : Nat := 643785955546757113459027

theorem tailTrace_1880653 : CollatzResearch.WordTrace tailWord_1880653 prefixEnd_1880653 643785955546757113459027 := by
  unfold tailWord_1880653
  simp only [CollatzResearch.WordTrace]
  refine ⟨68593050055722845806270613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45728700037148563870847075 68593050055722845806270613)
  ·
    refine ⟨3215299221362008397168935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 68593050055722845806270613 3215299221362008397168935)
    ·
      refine ⟨4822948832043012595753403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3215299221362008397168935 4822948832043012595753403)
      ·
        refine ⟨7234423248064518893630105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4822948832043012595753403 7234423248064518893630105)
        ·
          refine ⟨5425817436048389170222579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7234423248064518893630105 5425817436048389170222579)
          ·
            refine ⟨8138726154072583755333869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5425817436048389170222579 8138726154072583755333869)
            ·
              refine ⟨3052022307777218908250201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8138726154072583755333869 3052022307777218908250201)
              ·
                refine ⟨2289016730832914181187651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3052022307777218908250201 2289016730832914181187651)
                ·
                  refine ⟨3433525096249371271781477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2289016730832914181187651 3433525096249371271781477)
                  ·
                    refine ⟨643785955546757113459027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3433525096249371271781477 643785955546757113459027)
                    ·
                      rfl

theorem cell22_1880653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 3, 2, 1, 4].length) (baseStart_1880653 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1880653 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1880653 prefixEnd_1880653 := by exact prefixLift 1880653
  have htrace : WordTrace (prefixWord ++ tailWord_1880653) baseStart_1880653 baseEnd_1880653 := by
    simpa [prefixWord, tailWord_1880653, baseEnd_1880653] using wordTrace_append hprefix tailTrace_1880653
  have hstable : (prefixWord ++ tailWord_1880653).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1880653).length < 2 ^ (prefixWord ++ tailWord_1880653).sum := by decide
  have hdescent : baseEnd_1880653 < baseStart_1880653 := by decide
  rcases family_descends (prefixWord ++ tailWord_1880653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1880664 : List Nat := [2, 1, 2, 2, 1, 2, 3, 3, 2, 4]
def baseStart_1880664 : Nat := 118140960795 + 1880664 * 2 ^ 59
def prefixEnd_1880664 : Nat := 4983230072969 + 3 ^ 40 * 1880664 * 2
def baseEnd_1880664 : Nat := 643789721071556751433993

theorem tailTrace_1880664 : CollatzResearch.WordTrace tailWord_1880664 prefixEnd_1880664 643789721071556751433993 := by
  unfold tailWord_1880664
  simp only [CollatzResearch.WordTrace]
  refine ⟨34296725629341497342460523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45728967505788663123280697 34296725629341497342460523)
  ·
    refine ⟨51445088444012246013690785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34296725629341497342460523 51445088444012246013690785)
    ·
      refine ⟨38583816333009184510268089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51445088444012246013690785 38583816333009184510268089)
      ·
        refine ⟨28937862249756888382701067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38583816333009184510268089 28937862249756888382701067)
        ·
          refine ⟨43406793374635332574051601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28937862249756888382701067 43406793374635332574051601)
          ·
            refine ⟨32555095030976499430538701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43406793374635332574051601 32555095030976499430538701)
            ·
              refine ⟨12208160636616187286452013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32555095030976499430538701 12208160636616187286452013)
              ·
                refine ⟨4578060238731070232419505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12208160636616187286452013 4578060238731070232419505)
                ·
                  refine ⟨3433545179048302674314629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4578060238731070232419505 3433545179048302674314629)
                  ·
                    refine ⟨643789721071556751433993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3433545179048302674314629 643789721071556751433993)
                    ·
                      rfl

theorem cell22_1880664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 3, 2, 4].length) (baseStart_1880664 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1880664 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1880664 prefixEnd_1880664 := by exact prefixLift 1880664
  have htrace : WordTrace (prefixWord ++ tailWord_1880664) baseStart_1880664 baseEnd_1880664 := by
    simpa [prefixWord, tailWord_1880664, baseEnd_1880664] using wordTrace_append hprefix tailTrace_1880664
  have hstable : (prefixWord ++ tailWord_1880664).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1880664).length < 2 ^ (prefixWord ++ tailWord_1880664).sum := by decide
  have hdescent : baseEnd_1880664 < baseStart_1880664 := by decide
  rcases family_descends (prefixWord ++ tailWord_1880664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1880685 : List Nat := [1, 5, 1, 1, 3, 3, 2, 2, 4]
def baseStart_1880685 : Nat := 118140960795 + 1880685 * 2 ^ 59
def prefixEnd_1880685 : Nat := 4983230072969 + 3 ^ 40 * 1880685 * 2
def baseEnd_1880685 : Nat := 214598969933573232219643

theorem tailTrace_1880685 : CollatzResearch.WordTrace tailWord_1880685 prefixEnd_1880685 214598969933573232219643 := by
  unfold tailWord_1880685
  simp only [CollatzResearch.WordTrace]
  refine ⟨68594217191606915271435509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45729478127737943514290339 68594217191606915271435509)
  ·
    refine ⟨6430707861713148306697079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 68594217191606915271435509 6430707861713148306697079)
    ·
      refine ⟨9646061792569722460045619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6430707861713148306697079 9646061792569722460045619)
      ·
        refine ⟨14469092688854583690068429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9646061792569722460045619 14469092688854583690068429)
        ·
          refine ⟨5425909758320468883775661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14469092688854583690068429 5425909758320468883775661)
          ·
            refine ⟨2034716159370175831415873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5425909758320468883775661 2034716159370175831415873)
            ·
              refine ⟨1526037119527631873561905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2034716159370175831415873 1526037119527631873561905)
              ·
                refine ⟨1144527839645723905171429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1526037119527631873561905 1144527839645723905171429)
                ·
                  refine ⟨214598969933573232219643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1144527839645723905171429 214598969933573232219643)
                  ·
                    rfl

theorem cell22_1880685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 3, 2, 2, 4].length) (baseStart_1880685 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1880685 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1880685 prefixEnd_1880685 := by exact prefixLift 1880685
  have htrace : WordTrace (prefixWord ++ tailWord_1880685) baseStart_1880685 baseEnd_1880685 := by
    simpa [prefixWord, tailWord_1880685, baseEnd_1880685] using wordTrace_append hprefix tailTrace_1880685
  have hstable : (prefixWord ++ tailWord_1880685).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1880685).length < 2 ^ (prefixWord ++ tailWord_1880685).sum := by decide
  have hdescent : baseEnd_1880685 < baseStart_1880685 := by decide
  rcases family_descends (prefixWord ++ tailWord_1880685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1880711 : List Nat := [1, 1, 4, 2, 1, 2, 3, 2, 3, 3]
def baseStart_1880711 : Nat := 118140960795 + 1880711 * 2 ^ 59
def prefixEnd_1880711 : Nat := 4983230072969 + 3 ^ 40 * 1880711 * 2
def baseEnd_1880711 : Nat := 643805810132064295508849

theorem tailTrace_1880711 : CollatzResearch.WordTrace tailWord_1880711 prefixEnd_1880711 643805810132064295508849 := by
  unfold tailWord_1880711
  simp only [CollatzResearch.WordTrace]
  refine ⟨68595165489512721711881987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45730110326341814474587991 68595165489512721711881987)
  ·
    refine ⟨102892748234269082567822981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68595165489512721711881987 102892748234269082567822981)
    ·
      refine ⟨19292390293925452981466809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 102892748234269082567822981 19292390293925452981466809)
      ·
        refine ⟨14469292720444089736100107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19292390293925452981466809 14469292720444089736100107)
        ·
          refine ⟨21703939080666134604150161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14469292720444089736100107 21703939080666134604150161)
          ·
            refine ⟨16277954310499600953112621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21703939080666134604150161 16277954310499600953112621)
            ·
              refine ⟨6104232866437350357417233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16277954310499600953112621 6104232866437350357417233)
              ·
                refine ⟨4578174649828012768062925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6104232866437350357417233 4578174649828012768062925)
                ·
                  refine ⟨1716815493685504788023597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4578174649828012768062925 1716815493685504788023597)
                  ·
                    refine ⟨643805810132064295508849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1716815493685504788023597 643805810132064295508849)
                    ·
                      rfl

theorem cell22_1880711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 3, 2, 3, 3].length) (baseStart_1880711 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1880711 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1880711 prefixEnd_1880711 := by exact prefixLift 1880711
  have htrace : WordTrace (prefixWord ++ tailWord_1880711) baseStart_1880711 baseEnd_1880711 := by
    simpa [prefixWord, tailWord_1880711, baseEnd_1880711] using wordTrace_append hprefix tailTrace_1880711
  have hstable : (prefixWord ++ tailWord_1880711).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1880711).length < 2 ^ (prefixWord ++ tailWord_1880711).sum := by decide
  have hdescent : baseEnd_1880711 < baseStart_1880711 := by decide
  rcases family_descends (prefixWord ++ tailWord_1880711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1880803 : List Nat := [1, 1, 1, 7, 1, 3, 1, 1, 6]
def baseStart_1880803 : Nat := 118140960795 + 1880803 * 2 ^ 59
def prefixEnd_1880803 : Nat := 4983230072969 + 3 ^ 40 * 1880803 * 2
def baseEnd_1880803 : Nat := 214612434537402240736189

theorem tailTrace_1880803 : CollatzResearch.WordTrace tailWord_1880803 prefixEnd_1880803 214612434537402240736189 := by
  unfold tailWord_1880803
  simp only [CollatzResearch.WordTrace]
  refine ⟨68598521005179421424231063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45732347336786280949487375 68598521005179421424231063)
  ·
    refine ⟨102897781507769132136346595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68598521005179421424231063 102897781507769132136346595)
    ·
      refine ⟨154346672261653698204519893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102897781507769132136346595 154346672261653698204519893)
      ·
        refine ⟨3617500131132508551668435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 154346672261653698204519893 3617500131132508551668435)
        ·
          refine ⟨5426250196698762827502653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3617500131132508551668435 5426250196698762827502653)
          ·
            refine ⟨2034843823762036060313495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5426250196698762827502653 2034843823762036060313495)
            ·
              refine ⟨3052265735643054090470243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2034843823762036060313495 3052265735643054090470243)
              ·
                refine ⟨4578398603464581135705365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3052265735643054090470243 4578398603464581135705365)
                ·
                  refine ⟨214612434537402240736189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4578398603464581135705365 214612434537402240736189)
                  ·
                    rfl

theorem cell22_1880803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 3, 1, 1, 6].length) (baseStart_1880803 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1880803 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1880803 prefixEnd_1880803 := by exact prefixLift 1880803
  have htrace : WordTrace (prefixWord ++ tailWord_1880803) baseStart_1880803 baseEnd_1880803 := by
    simpa [prefixWord, tailWord_1880803, baseEnd_1880803] using wordTrace_append hprefix tailTrace_1880803
  have hstable : (prefixWord ++ tailWord_1880803).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1880803).length < 2 ^ (prefixWord ++ tailWord_1880803).sum := by decide
  have hdescent : baseEnd_1880803 < baseStart_1880803 := by decide
  rcases family_descends (prefixWord ++ tailWord_1880803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1880876 : List Nat := [2, 2, 1, 1, 1, 4, 1, 5, 5]
def baseStart_1880876 : Nat := 118140960795 + 1880876 * 2 ^ 59
def prefixEnd_1880876 : Nat := 4983230072969 + 3 ^ 40 * 1880876 * 2
def baseEnd_1880876 : Nat := 214620764334686288377781

theorem tailTrace_1880876 : CollatzResearch.WordTrace tailWord_1880876 prefixEnd_1880876 214620764334686288377781 := by
  unfold tailWord_1880876
  simp only [CollatzResearch.WordTrace]
  refine ⟨34300591766957477445819241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45734122355943303261092321 34300591766957477445819241)
  ·
    refine ⟨25725443825218108084364431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34300591766957477445819241 25725443825218108084364431)
    ·
      refine ⟨38588165737827162126546647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25725443825218108084364431 38588165737827162126546647)
      ·
        refine ⟨57882248606740743189819971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38588165737827162126546647 57882248606740743189819971)
        ·
          refine ⟨86823372910111114784729957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57882248606740743189819971 86823372910111114784729957)
          ·
            refine ⟨16279382420645834022136867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 86823372910111114784729957 16279382420645834022136867)
            ·
              refine ⟨24419073630968751033205301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16279382420645834022136867 24419073630968751033205301)
              ·
                refine ⟨2289288152903320409362997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24419073630968751033205301 2289288152903320409362997)
                ·
                  refine ⟨214620764334686288377781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2289288152903320409362997 214620764334686288377781)
                  ·
                    rfl

theorem cell22_1880876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 5].length) (baseStart_1880876 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1880876 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1880876 prefixEnd_1880876 := by exact prefixLift 1880876
  have htrace : WordTrace (prefixWord ++ tailWord_1880876) baseStart_1880876 baseEnd_1880876 := by
    simpa [prefixWord, tailWord_1880876, baseEnd_1880876] using wordTrace_append hprefix tailTrace_1880876
  have hstable : (prefixWord ++ tailWord_1880876).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1880876).length < 2 ^ (prefixWord ++ tailWord_1880876).sum := by decide
  have hdescent : baseEnd_1880876 < baseStart_1880876 := by decide
  rcases family_descends (prefixWord ++ tailWord_1880876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1880906 : List Nat := [3, 1, 2, 1, 1, 1, 2, 2, 5, 4]
def baseStart_1880906 : Nat := 118140960795 + 1880906 * 2 ^ 59
def prefixEnd_1880906 : Nat := 4983230072969 + 3 ^ 40 * 1880906 * 2
def baseEnd_1880906 : Nat := 643872562617148786883251

theorem tailTrace_1880906 : CollatzResearch.WordTrace tailWord_1880906 prefixEnd_1880906 643872562617148786883251 := by
  unfold tailWord_1880906
  simp only [CollatzResearch.WordTrace]
  refine ⟨17150569430951567503807643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45734851815870846676820381 17150569430951567503807643)
  ·
    refine ⟨25725854146427351255711465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17150569430951567503807643 25725854146427351255711465)
    ·
      refine ⟨19294390609820513441783599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25725854146427351255711465 19294390609820513441783599)
      ·
        refine ⟨28941585914730770162675399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19294390609820513441783599 28941585914730770162675399)
        ·
          refine ⟨43412378872096155244013099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28941585914730770162675399 43412378872096155244013099)
          ·
            refine ⟨65118568308144232866019649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43412378872096155244013099 65118568308144232866019649)
            ·
              refine ⟨48838926231108174649514737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65118568308144232866019649 48838926231108174649514737)
              ·
                refine ⟨36629194673331130987136053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48838926231108174649514737 36629194673331130987136053)
                ·
                  refine ⟨3433987000624793530044005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 36629194673331130987136053 3433987000624793530044005)
                  ·
                    refine ⟨643872562617148786883251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3433987000624793530044005 643872562617148786883251)
                    ·
                      rfl

theorem cell22_1880906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 2, 5, 4].length) (baseStart_1880906 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1880906 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1880906 prefixEnd_1880906 := by exact prefixLift 1880906
  have htrace : WordTrace (prefixWord ++ tailWord_1880906) baseStart_1880906 baseEnd_1880906 := by
    simpa [prefixWord, tailWord_1880906, baseEnd_1880906] using wordTrace_append hprefix tailTrace_1880906
  have hstable : (prefixWord ++ tailWord_1880906).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1880906).length < 2 ^ (prefixWord ++ tailWord_1880906).sum := by decide
  have hdescent : baseEnd_1880906 < baseStart_1880906 := by decide
  rcases family_descends (prefixWord ++ tailWord_1880906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1880921 : List Nat := [1, 2, 1, 2, 2, 4, 1, 3, 6]
def baseStart_1880921 : Nat := 118140960795 + 1880921 * 2 ^ 59
def prefixEnd_1880921 : Nat := 4983230072969 + 3 ^ 40 * 1880921 * 2
def baseEnd_1880921 : Nat := 214625899141231249252735

theorem tailTrace_1880921 : CollatzResearch.WordTrace tailWord_1880921 prefixEnd_1880921 214625899141231249252735 := by
  unfold tailWord_1880921
  simp only [CollatzResearch.WordTrace]
  refine ⟨68602824818751927577026617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45735216545834618384684411 68602824818751927577026617)
  ·
    refine ⟨51452118614063945682769963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68602824818751927577026617 51452118614063945682769963)
    ·
      refine ⟨77178177921095918524154945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51452118614063945682769963 77178177921095918524154945)
      ·
        refine ⟨57883633440821938893116209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77178177921095918524154945 57883633440821938893116209)
        ·
          refine ⟨43412725080616454169837157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57883633440821938893116209 43412725080616454169837157)
          ·
            refine ⟨8139885952615585156844467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43412725080616454169837157 8139885952615585156844467)
            ·
              refine ⟨12209828928923377735266701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8139885952615585156844467 12209828928923377735266701)
              ·
                refine ⟨4578685848346266650725013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12209828928923377735266701 4578685848346266650725013)
                ·
                  refine ⟨214625899141231249252735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4578685848346266650725013 214625899141231249252735)
                  ·
                    rfl

theorem cell22_1880921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 3, 6].length) (baseStart_1880921 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1880921 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1880921 prefixEnd_1880921 := by exact prefixLift 1880921
  have htrace : WordTrace (prefixWord ++ tailWord_1880921) baseStart_1880921 baseEnd_1880921 := by
    simpa [prefixWord, tailWord_1880921, baseEnd_1880921] using wordTrace_append hprefix tailTrace_1880921
  have hstable : (prefixWord ++ tailWord_1880921).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1880921).length < 2 ^ (prefixWord ++ tailWord_1880921).sum := by decide
  have hdescent : baseEnd_1880921 < baseStart_1880921 := by decide
  rcases family_descends (prefixWord ++ tailWord_1880921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1880951 : List Nat := [1, 1, 3, 1, 1, 2, 1, 2, 6, 4]
def baseStart_1880951 : Nat := 118140960795 + 1880951 * 2 ^ 59
def prefixEnd_1880951 : Nat := 4983230072969 + 3 ^ 40 * 1880951 * 2
def baseEnd_1880951 : Nat := 643887967036783669508113

theorem tailTrace_1880951 : CollatzResearch.WordTrace tailWord_1880951 prefixEnd_1880951 643887967036783669508113 := by
  unfold tailWord_1880951
  simp only [CollatzResearch.WordTrace]
  refine ⟨68603919008643242700618707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45735946005762161800412471 68603919008643242700618707)
  ·
    refine ⟨102905878512964864050928061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68603919008643242700618707 102905878512964864050928061)
    ·
      refine ⟨38589704442361824019098023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102905878512964864050928061 38589704442361824019098023)
      ·
        refine ⟨57884556663542736028647035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38589704442361824019098023 57884556663542736028647035)
        ·
          refine ⟨86826834995314104042970553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57884556663542736028647035 86826834995314104042970553)
          ·
            refine ⟨65120126246485578032227915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86826834995314104042970553 65120126246485578032227915)
            ·
              refine ⟨97680189369728367048341873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65120126246485578032227915 97680189369728367048341873)
              ·
                refine ⟨73260142027296275286256405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 97680189369728367048341873 73260142027296275286256405)
                ·
                  refine ⟨3434069157529512904043269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 73260142027296275286256405 3434069157529512904043269)
                  ·
                    refine ⟨643887967036783669508113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3434069157529512904043269 643887967036783669508113)
                    ·
                      rfl

theorem cell22_1880951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 2, 6, 4].length) (baseStart_1880951 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1880951 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1880951 prefixEnd_1880951 := by exact prefixLift 1880951
  have htrace : WordTrace (prefixWord ++ tailWord_1880951) baseStart_1880951 baseEnd_1880951 := by
    simpa [prefixWord, tailWord_1880951, baseEnd_1880951] using wordTrace_append hprefix tailTrace_1880951
  have hstable : (prefixWord ++ tailWord_1880951).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1880951).length < 2 ^ (prefixWord ++ tailWord_1880951).sum := by decide
  have hdescent : baseEnd_1880951 < baseStart_1880951 := by decide
  rcases family_descends (prefixWord ++ tailWord_1880951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1880953 : List Nat := [1, 2, 1, 3, 2, 3, 1, 2, 4, 3]
def baseStart_1880953 : Nat := 118140960795 + 1880953 * 2 ^ 59
def prefixEnd_1880953 : Nat := 4983230072969 + 3 ^ 40 * 1880953 * 2
def baseEnd_1880953 : Nat := 643888651677656330958107

theorem tailTrace_1880953 : CollatzResearch.WordTrace tailWord_1880953 prefixEnd_1880953 643888651677656330958107 := by
  unfold tailWord_1880953
  simp only [CollatzResearch.WordTrace]
  refine ⟨68603991954635997042191513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45735994636423998028127675 68603991954635997042191513)
  ·
    refine ⟨51452993965976997781643635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68603991954635997042191513 51452993965976997781643635)
    ·
      refine ⟨77179490948965496672465453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51452993965976997781643635 77179490948965496672465453)
      ·
        refine ⟨28942309105862061252174545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77179490948965496672465453 28942309105862061252174545)
        ·
          refine ⟨21706731829396545939130909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28942309105862061252174545 21706731829396545939130909)
          ·
            refine ⟨8140024436023704727174091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21706731829396545939130909 8140024436023704727174091)
            ·
              refine ⟨12210036654035557090761137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8140024436023704727174091 12210036654035557090761137)
              ·
                refine ⟨9157527490526667818070853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12210036654035557090761137 9157527490526667818070853)
                ·
                  refine ⟨1717036404473750215888285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9157527490526667818070853 1717036404473750215888285)
                  ·
                    refine ⟨643888651677656330958107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1717036404473750215888285 643888651677656330958107)
                    ·
                      rfl

theorem cell22_1880953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 2, 4, 3].length) (baseStart_1880953 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1880953 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1880953 prefixEnd_1880953 := by exact prefixLift 1880953
  have htrace : WordTrace (prefixWord ++ tailWord_1880953) baseStart_1880953 baseEnd_1880953 := by
    simpa [prefixWord, tailWord_1880953, baseEnd_1880953] using wordTrace_append hprefix tailTrace_1880953
  have hstable : (prefixWord ++ tailWord_1880953).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1880953).length < 2 ^ (prefixWord ++ tailWord_1880953).sum := by decide
  have hdescent : baseEnd_1880953 < baseStart_1880953 := by decide
  rcases family_descends (prefixWord ++ tailWord_1880953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1880968 : List Nat := [2, 1, 3, 3, 2, 1, 1, 1, 4, 4]
def baseStart_1880968 : Nat := 118140960795 + 1880968 * 2 ^ 59
def prefixEnd_1880968 : Nat := 4983230072969 + 3 ^ 40 * 1880968 * 2
def baseEnd_1880968 : Nat := 643893786484201291833061

theorem tailTrace_1880968 : CollatzResearch.WordTrace tailWord_1880968 prefixEnd_1880968 643893786484201291833061 := by
  unfold tailWord_1880968
  simp only [CollatzResearch.WordTrace]
  refine ⟨34302269524790827301993779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45736359366387769735991705 34302269524790827301993779)
  ·
    refine ⟨51453404287186240952990669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34302269524790827301993779 51453404287186240952990669)
    ·
      refine ⟨19295026607694840357371501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51453404287186240952990669 19295026607694840357371501)
      ·
        refine ⟨7235634977885565134014313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19295026607694840357371501 7235634977885565134014313)
        ·
          refine ⟨5426726233414173850510735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7235634977885565134014313 5426726233414173850510735)
          ·
            refine ⟨8140089350121260775766103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5426726233414173850510735 8140089350121260775766103)
            ·
              refine ⟨12210134025181891163649155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8140089350121260775766103 12210134025181891163649155)
              ·
                refine ⟨18315201037772836745473733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12210134025181891163649155 18315201037772836745473733)
                ·
                  refine ⟨3434100194582406889776325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18315201037772836745473733 3434100194582406889776325)
                  ·
                    refine ⟨643893786484201291833061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3434100194582406889776325 643893786484201291833061)
                    ·
                      rfl

theorem cell22_1880968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 1, 4, 4].length) (baseStart_1880968 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1880968 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1880968 prefixEnd_1880968 := by exact prefixLift 1880968
  have htrace : WordTrace (prefixWord ++ tailWord_1880968) baseStart_1880968 baseEnd_1880968 := by
    simpa [prefixWord, tailWord_1880968, baseEnd_1880968] using wordTrace_append hprefix tailTrace_1880968
  have hstable : (prefixWord ++ tailWord_1880968).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1880968).length < 2 ^ (prefixWord ++ tailWord_1880968).sum := by decide
  have hdescent : baseEnd_1880968 < baseStart_1880968 := by decide
  rcases family_descends (prefixWord ++ tailWord_1880968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1880970 : List Nat := [3, 1, 2, 4, 1, 1, 2, 1, 4, 3]
def baseStart_1880970 : Nat := 118140960795 + 1880970 * 2 ^ 59
def prefixEnd_1880970 : Nat := 4983230072969 + 3 ^ 40 * 1880970 * 2
def baseEnd_1880970 : Nat := 643894471125073953283055

theorem tailTrace_1880970 : CollatzResearch.WordTrace tailWord_1880970 prefixEnd_1880970 643894471125073953283055 := by
  unfold tailWord_1880970
  simp only [CollatzResearch.WordTrace]
  refine ⟨17151152998893602236390091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45736407997049605963706909 17151152998893602236390091)
  ·
    refine ⟨25726729498340403354585137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17151152998893602236390091 25726729498340403354585137)
    ·
      refine ⟨19295047123755302515938853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25726729498340403354585137 19295047123755302515938853)
      ·
        refine ⟨3617821335704119221738535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19295047123755302515938853 3617821335704119221738535)
        ·
          refine ⟨5426732003556178832607803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3617821335704119221738535 5426732003556178832607803)
          ·
            refine ⟨8140098005334268248911705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5426732003556178832607803 8140098005334268248911705)
            ·
              refine ⟨6105073504000701186683779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8140098005334268248911705 6105073504000701186683779)
              ·
                refine ⟨9157610256001051780025669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6105073504000701186683779 9157610256001051780025669)
                ·
                  refine ⟨1717051923000197208754813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9157610256001051780025669 1717051923000197208754813)
                  ·
                    refine ⟨643894471125073953283055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1717051923000197208754813 643894471125073953283055)
                    ·
                      rfl

theorem cell22_1880970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 2, 1, 4, 3].length) (baseStart_1880970 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1880970 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1880970 prefixEnd_1880970 := by exact prefixLift 1880970
  have htrace : WordTrace (prefixWord ++ tailWord_1880970) baseStart_1880970 baseEnd_1880970 := by
    simpa [prefixWord, tailWord_1880970, baseEnd_1880970] using wordTrace_append hprefix tailTrace_1880970
  have hstable : (prefixWord ++ tailWord_1880970).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1880970).length < 2 ^ (prefixWord ++ tailWord_1880970).sum := by decide
  have hdescent : baseEnd_1880970 < baseStart_1880970 := by decide
  rcases family_descends (prefixWord ++ tailWord_1880970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1881011 : List Nat := [1, 1, 1, 2, 3, 1, 2, 4, 7]
def baseStart_1881011 : Nat := 118140960795 + 1881011 * 2 ^ 59
def prefixEnd_1881011 : Nat := 4983230072969 + 3 ^ 40 * 1881011 * 2
def baseEnd_1881011 : Nat := 214636168754321171002643

theorem tailTrace_1881011 : CollatzResearch.WordTrace tailWord_1881011 prefixEnd_1881011 214636168754321171002643 := by
  unfold tailWord_1881011
  simp only [CollatzResearch.WordTrace]
  refine ⟨68606107388425872947802887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45737404925617248631868591 68606107388425872947802887)
  ·
    refine ⟨102909161082638809421704331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68606107388425872947802887 102909161082638809421704331)
    ·
      refine ⟨154363741623958214132556497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102909161082638809421704331 154363741623958214132556497)
      ·
        refine ⟨115772806217968660599417373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154363741623958214132556497 115772806217968660599417373)
        ·
          refine ⟨43414802331738247724781515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 115772806217968660599417373 43414802331738247724781515)
          ·
            refine ⟨65122203497607371587172273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43414802331738247724781515 65122203497607371587172273)
            ·
              refine ⟨48841652623205528690379205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65122203497607371587172273 48841652623205528690379205)
              ·
                refine ⟨9157809866851036629446101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48841652623205528690379205 9157809866851036629446101)
                ·
                  refine ⟨214636168754321171002643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9157809866851036629446101 214636168754321171002643)
                  ·
                    rfl

theorem cell22_1881011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 4, 7].length) (baseStart_1881011 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1881011 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1881011 prefixEnd_1881011 := by exact prefixLift 1881011
  have htrace : WordTrace (prefixWord ++ tailWord_1881011) baseStart_1881011 baseEnd_1881011 := by
    simpa [prefixWord, tailWord_1881011, baseEnd_1881011] using wordTrace_append hprefix tailTrace_1881011
  have hstable : (prefixWord ++ tailWord_1881011).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1881011).length < 2 ^ (prefixWord ++ tailWord_1881011).sum := by decide
  have hdescent : baseEnd_1881011 < baseStart_1881011 := by decide
  rcases family_descends (prefixWord ++ tailWord_1881011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1881105 : List Nat := [1, 2, 2, 1, 1, 2, 1, 7, 2, 3]
def baseStart_1881105 : Nat := 118140960795 + 1881105 * 2 ^ 59
def prefixEnd_1881105 : Nat := 4983230072969 + 3 ^ 40 * 1881105 * 2
def baseEnd_1881105 : Nat := 643940684383978601157641

theorem tailTrace_1881105 : CollatzResearch.WordTrace tailWord_1881105 prefixEnd_1881105 643940684383978601157641 := by
  unfold tailWord_1881105
  simp only [CollatzResearch.WordTrace]
  refine ⟨68609535850085327001724769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45739690566723551334483179 68609535850085327001724769)
  ·
    refine ⟨51457151887563995251293577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68609535850085327001724769 51457151887563995251293577)
    ·
      refine ⟨38592863915672996438470183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51457151887563995251293577 38592863915672996438470183)
      ·
        refine ⟨57889295873509494657705275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38592863915672996438470183 57889295873509494657705275)
        ·
          refine ⟨86833943810264241986557913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57889295873509494657705275 86833943810264241986557913)
          ·
            refine ⟨65125457857698181489918435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86833943810264241986557913 65125457857698181489918435)
            ·
              refine ⟨97688186786547272234877653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65125457857698181489918435 97688186786547272234877653)
              ·
                refine ⟨2289566877809701693004945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 97688186786547272234877653 2289566877809701693004945)
                ·
                  refine ⟨1717175158357276269753709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2289566877809701693004945 1717175158357276269753709)
                  ·
                    refine ⟨643940684383978601157641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1717175158357276269753709 643940684383978601157641)
                    ·
                      rfl

theorem cell22_1881105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 7, 2, 3].length) (baseStart_1881105 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1881105 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1881105 prefixEnd_1881105 := by exact prefixLift 1881105
  have htrace : WordTrace (prefixWord ++ tailWord_1881105) baseStart_1881105 baseEnd_1881105 := by
    simpa [prefixWord, tailWord_1881105, baseEnd_1881105] using wordTrace_append hprefix tailTrace_1881105
  have hstable : (prefixWord ++ tailWord_1881105).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1881105).length < 2 ^ (prefixWord ++ tailWord_1881105).sum := by decide
  have hdescent : baseEnd_1881105 < baseStart_1881105 := by decide
  rcases family_descends (prefixWord ++ tailWord_1881105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1881124 : List Nat := [2, 3, 1, 4, 1, 3, 1, 3, 4]
def baseStart_1881124 : Nat := 118140960795 + 1881124 * 2 ^ 59
def prefixEnd_1881124 : Nat := 4983230072969 + 3 ^ 40 * 1881124 * 2
def baseEnd_1881124 : Nat := 214649062824089628310861

theorem tailTrace_1881124 : CollatzResearch.WordTrace tailWord_1881124 prefixEnd_1881124 214649062824089628310861 := by
  unfold tailWord_1881124
  simp only [CollatzResearch.WordTrace]
  refine ⟨34305114418508246623333213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45740152558010995497777617 34305114418508246623333213)
  ·
    refine ⟨12864417906940592483749955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34305114418508246623333213 12864417906940592483749955)
    ·
      refine ⟨19296626860410888725624933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12864417906940592483749955 19296626860410888725624933)
      ·
        refine ⟨3618117536327041636054675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19296626860410888725624933 3618117536327041636054675)
        ·
          refine ⟨5427176304490562454082013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3618117536327041636054675 5427176304490562454082013)
          ·
            refine ⟨2035191114183960920280755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5427176304490562454082013 2035191114183960920280755)
            ·
              refine ⟨3052786671275941380421133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2035191114183960920280755 3052786671275941380421133)
              ·
                refine ⟨1144795001728478017657925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3052786671275941380421133 1144795001728478017657925)
                ·
                  refine ⟨214649062824089628310861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1144795001728478017657925 214649062824089628310861)
                  ·
                    rfl

theorem cell22_1881124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 3, 1, 3, 4].length) (baseStart_1881124 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1881124 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1881124 prefixEnd_1881124 := by exact prefixLift 1881124
  have htrace : WordTrace (prefixWord ++ tailWord_1881124) baseStart_1881124 baseEnd_1881124 := by
    simpa [prefixWord, tailWord_1881124, baseEnd_1881124] using wordTrace_append hprefix tailTrace_1881124
  have hstable : (prefixWord ++ tailWord_1881124).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1881124).length < 2 ^ (prefixWord ++ tailWord_1881124).sum := by decide
  have hdescent : baseEnd_1881124 < baseStart_1881124 := by decide
  rcases family_descends (prefixWord ++ tailWord_1881124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1881178 : List Nat := [3, 1, 1, 2, 1, 1, 2, 1, 3, 7]
def baseStart_1881178 : Nat := 118140960795 + 1881178 * 2 ^ 59
def prefixEnd_1881178 : Nat := 4983230072969 + 3 ^ 40 * 1881178 * 2
def baseEnd_1881178 : Nat := 643965673775830744082417

theorem tailTrace_1881178 : CollatzResearch.WordTrace tailWord_1881178 prefixEnd_1881178 643965673775830744082417 := by
  unfold tailWord_1881178
  simp only [CollatzResearch.WordTrace]
  refine ⟨17153049594705215117283047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45741465585880573646088125 17153049594705215117283047)
  ·
    refine ⟨25729574392057822675924571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17153049594705215117283047 25729574392057822675924571)
    ·
      refine ⟨38594361588086734013886857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25729574392057822675924571 38594361588086734013886857)
      ·
        refine ⟨28945771191065050510415143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38594361588086734013886857 28945771191065050510415143)
        ·
          refine ⟨43418656786597575765622715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28945771191065050510415143 43418656786597575765622715)
          ·
            refine ⟨65127985179896363648434073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43418656786597575765622715 65127985179896363648434073)
            ·
              refine ⟨48845988884922272736325555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65127985179896363648434073 48845988884922272736325555)
              ·
                refine ⟨73268983327383409104488333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48845988884922272736325555 73268983327383409104488333)
                ·
                  refine ⟨27475868747768778414183125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 73268983327383409104488333 27475868747768778414183125)
                  ·
                    refine ⟨643965673775830744082417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 27475868747768778414183125 643965673775830744082417)
                    ·
                      rfl

theorem cell22_1881178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 1, 3, 7].length) (baseStart_1881178 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1881178 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1881178 prefixEnd_1881178 := by exact prefixLift 1881178
  have htrace : WordTrace (prefixWord ++ tailWord_1881178) baseStart_1881178 baseEnd_1881178 := by
    simpa [prefixWord, tailWord_1881178, baseEnd_1881178] using wordTrace_append hprefix tailTrace_1881178
  have hstable : (prefixWord ++ tailWord_1881178).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1881178).length < 2 ^ (prefixWord ++ tailWord_1881178).sum := by decide
  have hdescent : baseEnd_1881178 < baseStart_1881178 := by decide
  rcases family_descends (prefixWord ++ tailWord_1881178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1881197 : List Nat := [1, 5, 1, 1, 2, 3, 2, 2, 5]
def baseStart_1881197 : Nat := 118140960795 + 1881197 * 2 ^ 59
def prefixEnd_1881197 : Nat := 4983230072969 + 3 ^ 40 * 1881197 * 2
def baseEnd_1881197 : Nat := 214657392621373675952453

theorem tailTrace_1881197 : CollatzResearch.WordTrace tailWord_1881197 prefixEnd_1881197 214657392621373675952453 := by
  unfold tailWord_1881197
  simp only [CollatzResearch.WordTrace]
  refine ⟨68612891365752026714073845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45741927577168017809382563 68612891365752026714073845)
  ·
    refine ⟨6432458565539252504444423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 68612891365752026714073845 6432458565539252504444423)
    ·
      refine ⟨9648687848308878756666635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6432458565539252504444423 9648687848308878756666635)
      ·
        refine ⟨14473031772463318134999953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9648687848308878756666635 14473031772463318134999953)
        ·
          refine ⟨10854773829347488601249965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14473031772463318134999953 10854773829347488601249965)
          ·
            refine ⟨4070540186005308225468737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10854773829347488601249965 4070540186005308225468737)
            ·
              refine ⟨3052905139503981169101553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4070540186005308225468737 3052905139503981169101553)
              ·
                refine ⟨2289678854627985876826165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3052905139503981169101553 2289678854627985876826165)
                ·
                  refine ⟨214657392621373675952453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2289678854627985876826165 214657392621373675952453)
                  ·
                    rfl

theorem cell22_1881197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 2, 2, 5].length) (baseStart_1881197 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1881197 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1881197 prefixEnd_1881197 := by exact prefixLift 1881197
  have htrace : WordTrace (prefixWord ++ tailWord_1881197) baseStart_1881197 baseEnd_1881197 := by
    simpa [prefixWord, tailWord_1881197, baseEnd_1881197] using wordTrace_append hprefix tailTrace_1881197
  have hstable : (prefixWord ++ tailWord_1881197).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1881197).length < 2 ^ (prefixWord ++ tailWord_1881197).sum := by decide
  have hdescent : baseEnd_1881197 < baseStart_1881197 := by decide
  rcases family_descends (prefixWord ++ tailWord_1881197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1881225 : List Nat := [1, 2, 1, 1, 4, 4, 1, 2, 6]
def baseStart_1881225 : Nat := 118140960795 + 1881225 * 2 ^ 59
def prefixEnd_1881225 : Nat := 4983230072969 + 3 ^ 40 * 1881225 * 2
def baseEnd_1881225 : Nat := 214660587612112762719091

theorem tailTrace_1881225 : CollatzResearch.WordTrace tailWord_1881225 prefixEnd_1881225 214660587612112762719091 := by
  unfold tailWord_1881225
  simp only [CollatzResearch.WordTrace]
  refine ⟨68613912609650587496093129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45742608406433724997395419 68613912609650587496093129)
  ·
    refine ⟨51460434457237940622069847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68613912609650587496093129 51460434457237940622069847)
    ·
      refine ⟨77190651685856910933104771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51460434457237940622069847 77190651685856910933104771)
      ·
        refine ⟨115785977528785366399657157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77190651685856910933104771 115785977528785366399657157)
        ·
          refine ⟨21709870786647256199935717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 115785977528785366399657157 21709870786647256199935717)
          ·
            refine ⟨4070600772496360537487947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21709870786647256199935717 4070600772496360537487947)
            ·
              refine ⟨6105901158744540806231921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4070600772496360537487947 6105901158744540806231921)
              ·
                refine ⟨4579425869058405604673941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6105901158744540806231921 4579425869058405604673941)
                ·
                  refine ⟨214660587612112762719091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4579425869058405604673941 214660587612112762719091)
                  ·
                    rfl

theorem cell22_1881225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 1, 2, 6].length) (baseStart_1881225 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1881225 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1881225 prefixEnd_1881225 := by exact prefixLift 1881225
  have htrace : WordTrace (prefixWord ++ tailWord_1881225) baseStart_1881225 baseEnd_1881225 := by
    simpa [prefixWord, tailWord_1881225, baseEnd_1881225] using wordTrace_append hprefix tailTrace_1881225
  have hstable : (prefixWord ++ tailWord_1881225).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1881225).length < 2 ^ (prefixWord ++ tailWord_1881225).sum := by decide
  have hdescent : baseEnd_1881225 < baseStart_1881225 := by decide
  rcases family_descends (prefixWord ++ tailWord_1881225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1881244 : List Nat := [2, 2, 3, 2, 1, 2, 4, 1, 1, 4]
def baseStart_1881244 : Nat := 118140960795 + 1881244 * 2 ^ 59
def prefixEnd_1881244 : Nat := 4983230072969 + 3 ^ 40 * 1881244 * 2
def baseEnd_1881244 : Nat := 643988266924628571932215

theorem tailTrace_1881244 : CollatzResearch.WordTrace tailWord_1881244 prefixEnd_1881244 643988266924628571932215 := by
  unfold tailWord_1881244
  simp only [CollatzResearch.WordTrace]
  refine ⟨34307302798290876870517393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45743070397721169160689857 34307302798290876870517393)
  ·
    refine ⟨25730477098718157652888045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34307302798290876870517393 25730477098718157652888045)
    ·
      refine ⟨9648928912019309119833017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25730477098718157652888045 9648928912019309119833017)
      ·
        refine ⟨7236696684014481839874763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9648928912019309119833017 7236696684014481839874763)
        ·
          refine ⟨10855045026021722759812145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7236696684014481839874763 10855045026021722759812145)
          ·
            refine ⟨8141283769516292069859109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10855045026021722759812145 8141283769516292069859109)
            ·
              refine ⟨1526490706784304763098583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8141283769516292069859109 1526490706784304763098583)
              ·
                refine ⟨2289736060176457144647875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1526490706784304763098583 2289736060176457144647875)
                ·
                  refine ⟨3434604090264685716971813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2289736060176457144647875 3434604090264685716971813)
                  ·
                    refine ⟨643988266924628571932215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3434604090264685716971813 643988266924628571932215)
                    ·
                      rfl

theorem cell22_1881244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 4, 1, 1, 4].length) (baseStart_1881244 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1881244 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1881244 prefixEnd_1881244 := by exact prefixLift 1881244
  have htrace : WordTrace (prefixWord ++ tailWord_1881244) baseStart_1881244 baseEnd_1881244 := by
    simpa [prefixWord, tailWord_1881244, baseEnd_1881244] using wordTrace_append hprefix tailTrace_1881244
  have hstable : (prefixWord ++ tailWord_1881244).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1881244).length < 2 ^ (prefixWord ++ tailWord_1881244).sum := by decide
  have hdescent : baseEnd_1881244 < baseStart_1881244 := by decide
  rcases family_descends (prefixWord ++ tailWord_1881244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1881392 : List Nat := [2, 1, 1, 1, 2, 2, 6, 1, 1, 5]
def baseStart_1881392 : Nat := 118140960795 + 1881392 * 2 ^ 59
def prefixEnd_1881392 : Nat := 4983230072969 + 3 ^ 40 * 1881392 * 2
def baseEnd_1881392 : Nat := 644038930349205519231761

theorem tailTrace_1881392 : CollatzResearch.WordTrace tailWord_1881392 prefixEnd_1881392 644038930349205519231761 := by
  unfold tailWord_1881392
  simp only [CollatzResearch.WordTrace]
  refine ⟨34310001800022787508711215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45746669066697050011614953 34310001800022787508711215)
  ·
    refine ⟨51465002700034181263066823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34310001800022787508711215 51465002700034181263066823)
    ·
      refine ⟨77197504050051271894600235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51465002700034181263066823 77197504050051271894600235)
      ·
        refine ⟨115796256075076907841900353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77197504050051271894600235 115796256075076907841900353)
        ·
          refine ⟨86847192056307680881425265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115796256075076907841900353 86847192056307680881425265)
          ·
            refine ⟨65135394042230760661068949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86847192056307680881425265 65135394042230760661068949)
            ·
              refine ⟨3053221595729566905987607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 65135394042230760661068949 3053221595729566905987607)
              ·
                refine ⟨4579832393594350358981411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3053221595729566905987607 4579832393594350358981411)
                ·
                  refine ⟨6869748590391525538472117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4579832393594350358981411 6869748590391525538472117)
                  ·
                    refine ⟨644038930349205519231761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6869748590391525538472117 644038930349205519231761)
                    ·
                      rfl

theorem cell22_1881392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 6, 1, 1, 5].length) (baseStart_1881392 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1881392 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1881392 prefixEnd_1881392 := by exact prefixLift 1881392
  have htrace : WordTrace (prefixWord ++ tailWord_1881392) baseStart_1881392 baseEnd_1881392 := by
    simpa [prefixWord, tailWord_1881392, baseEnd_1881392] using wordTrace_append hprefix tailTrace_1881392
  have hstable : (prefixWord ++ tailWord_1881392).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1881392).length < 2 ^ (prefixWord ++ tailWord_1881392).sum := by decide
  have hdescent : baseEnd_1881392 < baseStart_1881392 := by decide
  rcases family_descends (prefixWord ++ tailWord_1881392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1881407 : List Nat := [1, 1, 2, 2, 4, 3, 1, 1, 1, 6]
def baseStart_1881407 : Nat := 118140960795 + 1881407 * 2 ^ 59
def prefixEnd_1881407 : Nat := 4983230072969 + 3 ^ 40 * 1881407 * 2
def baseEnd_1881407 : Nat := 644044065155750480106715

theorem tailTrace_1881407 : CollatzResearch.WordTrace tailWord_1881407 prefixEnd_1881407 644044065155750480106715 := by
  unfold tailWord_1881407
  simp only [CollatzResearch.WordTrace]
  refine ⟨68620550694991232579218475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45747033796660821719478983 68620550694991232579218475)
  ·
    refine ⟨102930826042486848868827713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68620550694991232579218475 102930826042486848868827713)
    ·
      refine ⟨77198119531865136651620785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102930826042486848868827713 77198119531865136651620785)
      ·
        refine ⟨57898589648898852488715589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77198119531865136651620785 57898589648898852488715589)
        ·
          refine ⟨10855985559168534841634173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57898589648898852488715589 10855985559168534841634173)
          ·
            refine ⟨4070994584688200565612815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10855985559168534841634173 4070994584688200565612815)
            ·
              refine ⟨6106491877032300848419223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4070994584688200565612815 6106491877032300848419223)
              ·
                refine ⟨9159737815548451272628835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6106491877032300848419223 9159737815548451272628835)
                ·
                  refine ⟨13739606723322676908943253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9159737815548451272628835 13739606723322676908943253)
                  ·
                    refine ⟨644044065155750480106715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13739606723322676908943253 644044065155750480106715)
                    ·
                      rfl

theorem cell22_1881407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 1, 1, 1, 6].length) (baseStart_1881407 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1881407 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1881407 prefixEnd_1881407 := by exact prefixLift 1881407
  have htrace : WordTrace (prefixWord ++ tailWord_1881407) baseStart_1881407 baseEnd_1881407 := by
    simpa [prefixWord, tailWord_1881407, baseEnd_1881407] using wordTrace_append hprefix tailTrace_1881407
  have hstable : (prefixWord ++ tailWord_1881407).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1881407).length < 2 ^ (prefixWord ++ tailWord_1881407).sum := by decide
  have hdescent : baseEnd_1881407 < baseStart_1881407 := by decide
  rcases family_descends (prefixWord ++ tailWord_1881407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1881409 : List Nat := [1, 2, 5, 2, 1, 1, 2, 2, 1, 5]
def baseStart_1881409 : Nat := 118140960795 + 1881409 * 2 ^ 59
def prefixEnd_1881409 : Nat := 4983230072969 + 3 ^ 40 * 1881409 * 2
def baseEnd_1881409 : Nat := 644044749796623141556709

theorem tailTrace_1881409 : CollatzResearch.WordTrace tailWord_1881409 prefixEnd_1881409 644044749796623141556709 := by
  unfold tailWord_1881409
  simp only [CollatzResearch.WordTrace]
  refine ⟨68620623640983986920791281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45747082427322657947194187 68620623640983986920791281)
  ·
    refine ⟨51465467730737990190593461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68620623640983986920791281 51465467730737990190593461)
    ·
      refine ⟨4824887599756686580368137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 51465467730737990190593461 4824887599756686580368137)
      ·
        refine ⟨3618665699817514935276103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4824887599756686580368137 3618665699817514935276103)
        ·
          refine ⟨5427998549726272402914155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3618665699817514935276103 5427998549726272402914155)
          ·
            refine ⟨8141997824589408604371233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5427998549726272402914155 8141997824589408604371233)
            ·
              refine ⟨6106498368442056453278425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8141997824589408604371233 6106498368442056453278425)
              ·
                refine ⟨4579873776331542339958819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6106498368442056453278425 4579873776331542339958819)
                ·
                  refine ⟨6869810664497313509938229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4579873776331542339958819 6869810664497313509938229)
                  ·
                    refine ⟨644044749796623141556709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6869810664497313509938229 644044749796623141556709)
                    ·
                      rfl

theorem cell22_1881409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 2, 2, 1, 5].length) (baseStart_1881409 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1881409 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1881409 prefixEnd_1881409 := by exact prefixLift 1881409
  have htrace : WordTrace (prefixWord ++ tailWord_1881409) baseStart_1881409 baseEnd_1881409 := by
    simpa [prefixWord, tailWord_1881409, baseEnd_1881409] using wordTrace_append hprefix tailTrace_1881409
  have hstable : (prefixWord ++ tailWord_1881409).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1881409).length < 2 ^ (prefixWord ++ tailWord_1881409).sum := by decide
  have hdescent : baseEnd_1881409 < baseStart_1881409 := by decide
  rcases family_descends (prefixWord ++ tailWord_1881409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1881501 : List Nat := [1, 4, 2, 1, 3, 1, 4, 1, 5]
def baseStart_1881501 : Nat := 118140960795 + 1881501 * 2 ^ 59
def prefixEnd_1881501 : Nat := 4983230072969 + 3 ^ 40 * 1881501 * 2
def baseEnd_1881501 : Nat := 214692081092255189418809

theorem tailTrace_1881501 : CollatzResearch.WordTrace tailWord_1881501 prefixEnd_1881501 214692081092255189418809 := by
  unfold tailWord_1881501
  simp only [CollatzResearch.WordTrace]
  refine ⟨68623979156650686633140357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45749319437767124422093571 68623979156650686633140357)
  ·
    refine ⟨12866996091872003743713817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 68623979156650686633140357 12866996091872003743713817)
    ·
      refine ⟨9650247068904002807785363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12866996091872003743713817 9650247068904002807785363)
      ·
        refine ⟨14475370603356004211678045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9650247068904002807785363 14475370603356004211678045)
        ·
          refine ⟨5428263976258501579379267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14475370603356004211678045 5428263976258501579379267)
          ·
            refine ⟨8142395964387752369068901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5428263976258501579379267 8142395964387752369068901)
            ·
              refine ⟨1526699243322703569200419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8142395964387752369068901 1526699243322703569200419)
              ·
                refine ⟨2290048864984055353800629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1526699243322703569200419 2290048864984055353800629)
                ·
                  refine ⟨214692081092255189418809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2290048864984055353800629 214692081092255189418809)
                  ·
                    rfl

theorem cell22_1881501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 4, 1, 5].length) (baseStart_1881501 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1881501 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1881501 prefixEnd_1881501 := by exact prefixLift 1881501
  have htrace : WordTrace (prefixWord ++ tailWord_1881501) baseStart_1881501 baseEnd_1881501 := by
    simpa [prefixWord, tailWord_1881501, baseEnd_1881501] using wordTrace_append hprefix tailTrace_1881501
  have hstable : (prefixWord ++ tailWord_1881501).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1881501).length < 2 ^ (prefixWord ++ tailWord_1881501).sum := by decide
  have hdescent : baseEnd_1881501 < baseStart_1881501 := by decide
  rcases family_descends (prefixWord ++ tailWord_1881501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1881546 : List Nat := [3, 1, 2, 1, 2, 4, 1, 4, 4]
def baseStart_1881546 : Nat := 118140960795 + 1881546 * 2 ^ 59
def prefixEnd_1881546 : Nat := 4983230072969 + 3 ^ 40 * 1881546 * 2
def baseEnd_1881546 : Nat := 214697215898800150293763

theorem tailTrace_1881546 : CollatzResearch.WordTrace tailWord_1881546 prefixEnd_1881546 214697215898800150293763 := by
  unfold tailWord_1881546
  simp only [CollatzResearch.WordTrace]
  refine ⟨17156405110371914829632123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45750413627658439545685661 17156405110371914829632123)
  ·
    refine ⟨25734607665557872244448185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17156405110371914829632123 25734607665557872244448185)
    ·
      refine ⟨19300955749168404183336139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25734607665557872244448185 19300955749168404183336139)
      ·
        refine ⟨28951433623752606275004209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19300955749168404183336139 28951433623752606275004209)
        ·
          refine ⟨21713575217814454706253157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28951433623752606275004209 21713575217814454706253157)
          ·
            refine ⟨4071295353340210257422467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21713575217814454706253157 4071295353340210257422467)
            ·
              refine ⟨6106943030010315386133701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4071295353340210257422467 6106943030010315386133701)
              ·
                refine ⟨1145051818126934134900069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6106943030010315386133701 1145051818126934134900069)
                ·
                  refine ⟨214697215898800150293763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1145051818126934134900069 214697215898800150293763)
                  ·
                    rfl

theorem cell22_1881546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 1, 4, 4].length) (baseStart_1881546 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1881546 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1881546 prefixEnd_1881546 := by exact prefixLift 1881546
  have htrace : WordTrace (prefixWord ++ tailWord_1881546) baseStart_1881546 baseEnd_1881546 := by
    simpa [prefixWord, tailWord_1881546, baseEnd_1881546] using wordTrace_append hprefix tailTrace_1881546
  have hstable : (prefixWord ++ tailWord_1881546).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1881546).length < 2 ^ (prefixWord ++ tailWord_1881546).sum := by decide
  have hdescent : baseEnd_1881546 < baseStart_1881546 := by decide
  rcases family_descends (prefixWord ++ tailWord_1881546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1881561 : List Nat := [1, 2, 1, 2, 4, 2, 2, 3, 2, 3]
def baseStart_1881561 : Nat := 118140960795 + 1881561 * 2 ^ 59
def prefixEnd_1881561 : Nat := 4983230072969 + 3 ^ 40 * 1881561 * 2
def baseEnd_1881561 : Nat := 644096782502945411756243

theorem tailTrace_1881561 : CollatzResearch.WordTrace tailWord_1881561 prefixEnd_1881561 644096782502945411756243 := by
  unfold tailWord_1881561
  simp only [CollatzResearch.WordTrace]
  refine ⟨68626167536433316880324537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45750778357622211253549691 68626167536433316880324537)
  ·
    refine ⟨51469625652324987660243403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68626167536433316880324537 51469625652324987660243403)
    ·
      refine ⟨77204438478487481490365105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51469625652324987660243403 77204438478487481490365105)
      ·
        refine ⟨57903328858865611117773829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77204438478487481490365105 57903328858865611117773829)
        ·
          refine ⟨10856874161037302084582593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57903328858865611117773829 10856874161037302084582593)
          ·
            refine ⟨8142655620777976563436945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10856874161037302084582593 8142655620777976563436945)
            ·
              refine ⟨6106991715583482422577709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8142655620777976563436945 6106991715583482422577709)
              ·
                refine ⟨2290121893343805908466641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6106991715583482422577709 2290121893343805908466641)
                ·
                  refine ⟨1717591420007854431349981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2290121893343805908466641 1717591420007854431349981)
                  ·
                    refine ⟨644096782502945411756243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1717591420007854431349981 644096782502945411756243)
                    ·
                      rfl

theorem cell22_1881561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 2, 3, 2, 3].length) (baseStart_1881561 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1881561 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1881561 prefixEnd_1881561 := by exact prefixLift 1881561
  have htrace : WordTrace (prefixWord ++ tailWord_1881561) baseStart_1881561 baseEnd_1881561 := by
    simpa [prefixWord, tailWord_1881561, baseEnd_1881561] using wordTrace_append hprefix tailTrace_1881561
  have hstable : (prefixWord ++ tailWord_1881561).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1881561).length < 2 ^ (prefixWord ++ tailWord_1881561).sum := by decide
  have hdescent : baseEnd_1881561 < baseStart_1881561 := by decide
  rcases family_descends (prefixWord ++ tailWord_1881561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1881587 : List Nat := [1, 1, 1, 2, 2, 2, 2, 2, 1, 8]
def baseStart_1881587 : Nat := 118140960795 + 1881587 * 2 ^ 59
def prefixEnd_1881587 : Nat := 4983230072969 + 3 ^ 40 * 1881587 * 2
def baseEnd_1881587 : Nat := 644105682834290010606163

theorem tailTrace_1881587 : CollatzResearch.WordTrace tailWord_1881587 prefixEnd_1881587 644105682834290010606163 := by
  unfold tailWord_1881587
  simp only [CollatzResearch.WordTrace]
  refine ⟨68627115834339123320771015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45751410556226082213847343 68627115834339123320771015)
  ·
    refine ⟨102940673751508684981156523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68627115834339123320771015 102940673751508684981156523)
    ·
      refine ⟨154411010627263027471734785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102940673751508684981156523 154411010627263027471734785)
      ·
        refine ⟨115808257970447270603801089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154411010627263027471734785 115808257970447270603801089)
        ·
          refine ⟨86856193477835452952850817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115808257970447270603801089 86856193477835452952850817)
          ·
            refine ⟨65142145108376589714638113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86856193477835452952850817 65142145108376589714638113)
            ·
              refine ⟨48856608831282442285978585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65142145108376589714638113 48856608831282442285978585)
              ·
                refine ⟨36642456623461831714483939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48856608831282442285978585 36642456623461831714483939)
                ·
                  refine ⟨54963684935192747571725909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36642456623461831714483939 54963684935192747571725909)
                  ·
                    refine ⟨644105682834290010606163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 54963684935192747571725909 644105682834290010606163)
                    ·
                      rfl

theorem cell22_1881587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 1, 8].length) (baseStart_1881587 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1881587 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1881587 prefixEnd_1881587 := by exact prefixLift 1881587
  have htrace : WordTrace (prefixWord ++ tailWord_1881587) baseStart_1881587 baseEnd_1881587 := by
    simpa [prefixWord, tailWord_1881587, baseEnd_1881587] using wordTrace_append hprefix tailTrace_1881587
  have hstable : (prefixWord ++ tailWord_1881587).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1881587).length < 2 ^ (prefixWord ++ tailWord_1881587).sum := by decide
  have hdescent : baseEnd_1881587 < baseStart_1881587 := by decide
  rcases family_descends (prefixWord ++ tailWord_1881587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1881634 : List Nat := [3, 3, 1, 1, 1, 1, 2, 2, 1, 7]
def baseStart_1881634 : Nat := 118140960795 + 1881634 * 2 ^ 59
def prefixEnd_1881634 : Nat := 4983230072969 + 3 ^ 40 * 1881634 * 2
def baseEnd_1881634 : Nat := 644121771894797554681019

theorem tailTrace_1881634 : CollatzResearch.WordTrace tailWord_1881634 prefixEnd_1881634 644121771894797554681019 := by
  unfold tailWord_1881634
  simp only [CollatzResearch.WordTrace]
  refine ⟨17157207516292212586932989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45752553376779233565154637 17157207516292212586932989)
  ·
    refine ⟨6433952818609579720099871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17157207516292212586932989 6433952818609579720099871)
    ·
      refine ⟨9650929227914369580149807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6433952818609579720099871 9650929227914369580149807)
      ·
        refine ⟨14476393841871554370224711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9650929227914369580149807 14476393841871554370224711)
        ·
          refine ⟨21714590762807331555337067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14476393841871554370224711 21714590762807331555337067)
          ·
            refine ⟨32571886144210997333005601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21714590762807331555337067 32571886144210997333005601)
            ·
              refine ⟨24428914608158247999754201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32571886144210997333005601 24428914608158247999754201)
              ·
                refine ⟨18321685956118685999815651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24428914608158247999754201 18321685956118685999815651)
                ·
                  refine ⟨27482528934178028999723477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18321685956118685999815651 27482528934178028999723477)
                  ·
                    refine ⟨644121771894797554681019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 27482528934178028999723477 644121771894797554681019)
                    ·
                      rfl

theorem cell22_1881634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 2, 1, 7].length) (baseStart_1881634 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1881634 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1881634 prefixEnd_1881634 := by exact prefixLift 1881634
  have htrace : WordTrace (prefixWord ++ tailWord_1881634) baseStart_1881634 baseEnd_1881634 := by
    simpa [prefixWord, tailWord_1881634, baseEnd_1881634] using wordTrace_append hprefix tailTrace_1881634
  have hstable : (prefixWord ++ tailWord_1881634).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1881634).length < 2 ^ (prefixWord ++ tailWord_1881634).sum := by decide
  have hdescent : baseEnd_1881634 < baseStart_1881634 := by decide
  rcases family_descends (prefixWord ++ tailWord_1881634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
