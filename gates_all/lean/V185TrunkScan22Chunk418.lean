import V185TrunkScan22Chunk417

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_3727391 : List Nat := [1, 1, 2, 4, 1, 2, 2, 2, 7]
def baseStart_3727391 : Nat := 118140960795 + 3727391 * 2 ^ 59
def prefixEnd_3727391 : Nat := 4983230072969 + 3 ^ 40 * 3727391 * 2
def baseEnd_3727391 : Nat := 425320704498429177615677

theorem tailTrace_3727391 : CollatzResearch.WordTrace tailWord_3727391 prefixEnd_3727391 425320704498429177615677 := by
  unfold tailWord_3727391
  simp only [CollatzResearch.WordTrace]
  refine ⟨135949118439306469546574027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90632745626204313031049351 135949118439306469546574027)
  ·
    refine ⟨203923677658959704319861041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135949118439306469546574027 203923677658959704319861041)
    ·
      refine ⟨152942758244219778239895781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 203923677658959704319861041 152942758244219778239895781)
      ·
        refine ⟨28676767170791208419980459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 152942758244219778239895781 28676767170791208419980459)
        ·
          refine ⟨43015150756186812629970689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28676767170791208419980459 43015150756186812629970689)
          ·
            refine ⟨32261363067140109472478017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43015150756186812629970689 32261363067140109472478017)
            ·
              refine ⟨24196022300355082104358513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32261363067140109472478017 24196022300355082104358513)
              ·
                refine ⟨18147016725266311578268885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24196022300355082104358513 18147016725266311578268885)
                ·
                  refine ⟨425320704498429177615677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18147016725266311578268885 425320704498429177615677)
                  ·
                    rfl

theorem cell22_3727391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 2, 7].length) (baseStart_3727391 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3727391 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3727391 prefixEnd_3727391 := by exact prefixLift 3727391
  have htrace : WordTrace (prefixWord ++ tailWord_3727391) baseStart_3727391 baseEnd_3727391 := by
    simpa [prefixWord, tailWord_3727391, baseEnd_3727391] using wordTrace_append hprefix tailTrace_3727391
  have hstable : (prefixWord ++ tailWord_3727391).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3727391).length < 2 ^ (prefixWord ++ tailWord_3727391).sum := by decide
  have hdescent : baseEnd_3727391 < baseStart_3727391 := by decide
  rcases family_descends (prefixWord ++ tailWord_3727391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3727408 : List Nat := [2, 1, 1, 1, 2, 5, 3, 2, 5]
def baseStart_3727408 : Nat := 118140960795 + 3727408 * 2 ^ 59
def prefixEnd_3727408 : Nat := 4983230072969 + 3 ^ 40 * 3727408 * 2
def baseEnd_3727408 : Nat := 425322644314235051723993

theorem tailTrace_3727408 : CollatzResearch.WordTrace tailWord_3727408 prefixEnd_3727408 425322644314235051723993 := by
  unfold tailWord_3727408
  simp only [CollatzResearch.WordTrace]
  refine ⟨67974869240122440724971439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90633158986829920966628585 67974869240122440724971439)
  ·
    refine ⟨101962303860183661087457159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67974869240122440724971439 101962303860183661087457159)
    ·
      refine ⟨152943455790275491631185739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101962303860183661087457159 152943455790275491631185739)
      ·
        refine ⟨229415183685413237446778609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152943455790275491631185739 229415183685413237446778609)
        ·
          refine ⟨172061387764059928085083957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 229415183685413237446778609 172061387764059928085083957)
          ·
            refine ⟨16130755102880618257976621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 172061387764059928085083957 16130755102880618257976621)
            ·
              refine ⟨6049033163580231846741233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16130755102880618257976621 6049033163580231846741233)
              ·
                refine ⟨4536774872685173885055925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6049033163580231846741233 4536774872685173885055925)
                ·
                  refine ⟨425322644314235051723993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4536774872685173885055925 425322644314235051723993)
                  ·
                    rfl

theorem cell22_3727408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 3, 2, 5].length) (baseStart_3727408 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3727408 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3727408 prefixEnd_3727408 := by exact prefixLift 3727408
  have htrace : WordTrace (prefixWord ++ tailWord_3727408) baseStart_3727408 baseEnd_3727408 := by
    simpa [prefixWord, tailWord_3727408, baseEnd_3727408] using wordTrace_append hprefix tailTrace_3727408
  have hstable : (prefixWord ++ tailWord_3727408).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3727408).length < 2 ^ (prefixWord ++ tailWord_3727408).sum := by decide
  have hdescent : baseEnd_3727408 < baseStart_3727408 := by decide
  rcases family_descends (prefixWord ++ tailWord_3727408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3727446 : List Nat := [5, 2, 2, 1, 1, 1, 3, 3, 1, 3]
def baseStart_3727446 : Nat := 118140960795 + 3727446 * 2 ^ 59
def prefixEnd_3727446 : Nat := 4983230072969 + 3 ^ 40 * 3727446 * 2
def baseEnd_3727446 : Nat := 1275980941119285722721863

theorem tailTrace_3727446 : CollatzResearch.WordTrace tailWord_3727446 prefixEnd_3727446 1275980941119285722721863 := by
  unfold tailWord_3727446
  simp only [CollatzResearch.WordTrace]
  refine ⟨8496945278381700871239137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 90634082969404809293217461 8496945278381700871239137)
  ·
    refine ⟨6372708958786275653429353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8496945278381700871239137 6372708958786275653429353)
    ·
      refine ⟨4779531719089706740072015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6372708958786275653429353 4779531719089706740072015)
      ·
        refine ⟨7169297578634560110108023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4779531719089706740072015 7169297578634560110108023)
        ·
          refine ⟨10753946367951840165162035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7169297578634560110108023 10753946367951840165162035)
          ·
            refine ⟨16130919551927760247743053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10753946367951840165162035 16130919551927760247743053)
            ·
              refine ⟨6049094831972910092903645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16130919551927760247743053 6049094831972910092903645)
              ·
                refine ⟨2268410561989841284838867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6049094831972910092903645 2268410561989841284838867)
                ·
                  refine ⟨3402615842984761927258301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2268410561989841284838867 3402615842984761927258301)
                  ·
                    refine ⟨1275980941119285722721863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3402615842984761927258301 1275980941119285722721863)
                    ·
                      rfl

theorem cell22_3727446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 3, 3, 1, 3].length) (baseStart_3727446 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3727446 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3727446 prefixEnd_3727446 := by exact prefixLift 3727446
  have htrace : WordTrace (prefixWord ++ tailWord_3727446) baseStart_3727446 baseEnd_3727446 := by
    simpa [prefixWord, tailWord_3727446, baseEnd_3727446] using wordTrace_append hprefix tailTrace_3727446
  have hstable : (prefixWord ++ tailWord_3727446).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3727446).length < 2 ^ (prefixWord ++ tailWord_3727446).sum := by decide
  have hdescent : baseEnd_3727446 < baseStart_3727446 := by decide
  rcases family_descends (prefixWord ++ tailWord_3727446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3727489 : List Nat := [1, 2, 4, 2, 4, 1, 1, 2, 1, 4]
def baseStart_3727489 : Nat := 118140960795 + 3727489 * 2 ^ 59
def prefixEnd_3727489 : Nat := 4983230072969 + 3 ^ 40 * 3727489 * 2
def baseEnd_3727489 : Nat := 1275995660898047943896731

theorem tailTrace_3727489 : CollatzResearch.WordTrace tailWord_3727489 prefixEnd_3727489 1275995660898047943896731 := by
  unfold tailWord_3727489
  simp only [CollatzResearch.WordTrace]
  refine ⟨135952692792951432283641521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90635128528634288189094347 135952692792951432283641521)
  ·
    refine ⟨101964519594713574212731141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135952692792951432283641521 101964519594713574212731141)
    ·
      refine ⟨19118347424008795164887089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 101964519594713574212731141 19118347424008795164887089)
      ·
        refine ⟨14338760568006596373665317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19118347424008795164887089 14338760568006596373665317)
        ·
          refine ⟨2688517606501236820062247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14338760568006596373665317 2688517606501236820062247)
          ·
            refine ⟨4032776409751855230093371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2688517606501236820062247 4032776409751855230093371)
            ·
              refine ⟨6049164614627782845140057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4032776409751855230093371 6049164614627782845140057)
              ·
                refine ⟨4536873460970837133855043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6049164614627782845140057 4536873460970837133855043)
                ·
                  refine ⟨6805310191456255700782565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4536873460970837133855043 6805310191456255700782565)
                  ·
                    refine ⟨1275995660898047943896731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6805310191456255700782565 1275995660898047943896731)
                    ·
                      rfl

theorem cell22_3727489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 4, 1, 1, 2, 1, 4].length) (baseStart_3727489 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3727489 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3727489 prefixEnd_3727489 := by exact prefixLift 3727489
  have htrace : WordTrace (prefixWord ++ tailWord_3727489) baseStart_3727489 baseEnd_3727489 := by
    simpa [prefixWord, tailWord_3727489, baseEnd_3727489] using wordTrace_append hprefix tailTrace_3727489
  have hstable : (prefixWord ++ tailWord_3727489).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3727489).length < 2 ^ (prefixWord ++ tailWord_3727489).sum := by decide
  have hdescent : baseEnd_3727489 < baseStart_3727489 := by decide
  rcases family_descends (prefixWord ++ tailWord_3727489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3727498 : List Nat := [3, 1, 2, 3, 1, 2, 2, 8]
def baseStart_3727498 : Nat := 118140960795 + 3727498 * 2 ^ 59
def prefixEnd_3727498 : Nat := 4983230072969 + 3 ^ 40 * 3727498 * 2
def baseEnd_3727498 : Nat := 141777637975774991157967

theorem tailTrace_3727498 : CollatzResearch.WordTrace tailWord_3727498 prefixEnd_3727498 141777637975774991157967 := by
  unfold tailWord_3727498
  simp only [CollatzResearch.WordTrace]
  refine ⟨33988255262479706705179787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90635347366612551213812765 33988255262479706705179787)
  ·
    refine ⟨50982382893719560057769681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33988255262479706705179787 50982382893719560057769681)
    ·
      refine ⟨38236787170289670043327261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50982382893719560057769681 38236787170289670043327261)
      ·
        refine ⟨14338795188858626266247723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38236787170289670043327261 14338795188858626266247723)
        ·
          refine ⟨21508192783287939399371585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14338795188858626266247723 21508192783287939399371585)
          ·
            refine ⟨16131144587465954549528689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21508192783287939399371585 16131144587465954549528689)
            ·
              refine ⟨12098358440599465912146517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16131144587465954549528689 12098358440599465912146517)
              ·
                refine ⟨141777637975774991157967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12098358440599465912146517 141777637975774991157967)
                ·
                  rfl

theorem cell22_3727498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 2, 8].length) (baseStart_3727498 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3727498 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3727498 prefixEnd_3727498 := by exact prefixLift 3727498
  have htrace : WordTrace (prefixWord ++ tailWord_3727498) baseStart_3727498 baseEnd_3727498 := by
    simpa [prefixWord, tailWord_3727498, baseEnd_3727498] using wordTrace_append hprefix tailTrace_3727498
  have hstable : (prefixWord ++ tailWord_3727498).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3727498).length < 2 ^ (prefixWord ++ tailWord_3727498).sum := by decide
  have hdescent : baseEnd_3727498 < baseStart_3727498 := by decide
  rcases family_descends (prefixWord ++ tailWord_3727498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3727633 : List Nat := [1, 2, 2, 1, 1, 5, 10]
def baseStart_3727633 : Nat := 118140960795 + 3727633 * 2 ^ 59
def prefixEnd_3727633 : Nat := 4983230072969 + 3 ^ 40 * 3727633 * 2
def baseEnd_3727633 : Nat := 47260924260773317344307

theorem tailTrace_3727633 : CollatzResearch.WordTrace tailWord_3727633 prefixEnd_3727633 47260924260773317344307 := by
  unfold tailWord_3727633
  simp only [CollatzResearch.WordTrace]
  refine ⟨135957944904429744876883553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90638629936286496584589035 135957944904429744876883553)
  ·
    refine ⟨101968458678322308657662665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135957944904429744876883553 101968458678322308657662665)
    ·
      refine ⟨76476344008741731493246999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101968458678322308657662665 76476344008741731493246999)
      ·
        refine ⟨114714516013112597239870499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76476344008741731493246999 114714516013112597239870499)
        ·
          refine ⟨172071774019668895859805749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114714516013112597239870499 172071774019668895859805749)
          ·
            refine ⟨16131728814343958986856789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 172071774019668895859805749 16131728814343958986856789)
            ·
              refine ⟨47260924260773317344307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 16131728814343958986856789 47260924260773317344307)
              ·
                rfl

theorem cell22_3727633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 10].length) (baseStart_3727633 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3727633 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3727633 prefixEnd_3727633 := by exact prefixLift 3727633
  have htrace : WordTrace (prefixWord ++ tailWord_3727633) baseStart_3727633 baseEnd_3727633 := by
    simpa [prefixWord, tailWord_3727633, baseEnd_3727633] using wordTrace_append hprefix tailTrace_3727633
  have hstable : (prefixWord ++ tailWord_3727633).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3727633).length < 2 ^ (prefixWord ++ tailWord_3727633).sum := by decide
  have hdescent : baseEnd_3727633 < baseStart_3727633 := by decide
  rcases family_descends (prefixWord ++ tailWord_3727633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3727639 : List Nat := [1, 1, 3, 4, 1, 3, 3, 2, 4]
def baseStart_3727639 : Nat := 118140960795 + 3727639 * 2 ^ 59
def prefixEnd_3727639 : Nat := 4983230072969 + 3 ^ 40 * 3727639 * 2
def baseEnd_3727639 : Nat := 425349002987832517548757

theorem tailTrace_3727639 : CollatzResearch.WordTrace tailWord_3727639 prefixEnd_3727639 425349002987832517548757 := by
  unfold tailWord_3727639
  simp only [CollatzResearch.WordTrace]
  refine ⟨135958163742408007901601971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90638775828272005267734647 135958163742408007901601971)
  ·
    refine ⟨203937245613612011852402957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135958163742408007901601971 203937245613612011852402957)
    ·
      refine ⟨76476467105104504444651109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 203937245613612011852402957 76476467105104504444651109)
      ·
        refine ⟨14339337582207094583372083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 76476467105104504444651109 14339337582207094583372083)
        ·
          refine ⟨21509006373310641875058125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14339337582207094583372083 21509006373310641875058125)
          ·
            refine ⟨8065877389991490703146797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21509006373310641875058125 8065877389991490703146797)
            ·
              refine ⟨3024704021246809013680049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8065877389991490703146797 3024704021246809013680049)
              ·
                refine ⟨2268528015935106760260037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3024704021246809013680049 2268528015935106760260037)
                ·
                  refine ⟨425349002987832517548757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2268528015935106760260037 425349002987832517548757)
                  ·
                    rfl

theorem cell22_3727639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 3, 2, 4].length) (baseStart_3727639 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3727639 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3727639 prefixEnd_3727639 := by exact prefixLift 3727639
  have htrace : WordTrace (prefixWord ++ tailWord_3727639) baseStart_3727639 baseEnd_3727639 := by
    simpa [prefixWord, tailWord_3727639, baseEnd_3727639] using wordTrace_append hprefix tailTrace_3727639
  have hstable : (prefixWord ++ tailWord_3727639).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3727639).length < 2 ^ (prefixWord ++ tailWord_3727639).sum := by decide
  have hdescent : baseEnd_3727639 < baseStart_3727639 := by decide
  rcases family_descends (prefixWord ++ tailWord_3727639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3727650 : List Nat := [3, 3, 1, 1, 3, 1, 1, 9]
def baseStart_3727650 : Nat := 118140960795 + 3727650 * 2 ^ 59
def prefixEnd_3727650 : Nat := 4983230072969 + 3 ^ 40 * 3727650 * 2
def baseEnd_3727650 : Nat := 141783419387588576735693

theorem tailTrace_3727650 : CollatzResearch.WordTrace tailWord_3727650 prefixEnd_3727650 141783419387588576735693 := by
  unfold tailWord_3727650
  simp only [CollatzResearch.WordTrace]
  refine ⟨33989641236342039195063101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90639043296912104520168269 33989641236342039195063101)
  ·
    refine ⟨12746115463628264698148663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33989641236342039195063101 12746115463628264698148663)
    ·
      refine ⟨19119173195442397047222995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12746115463628264698148663 19119173195442397047222995)
      ·
        refine ⟨28678759793163595570834493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19119173195442397047222995 28678759793163595570834493)
        ·
          refine ⟨10754534922436348339062935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28678759793163595570834493 10754534922436348339062935)
          ·
            refine ⟨16131802383654522508594403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10754534922436348339062935 16131802383654522508594403)
            ·
              refine ⟨24197703575481783762891605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16131802383654522508594403 24197703575481783762891605)
              ·
                refine ⟨141783419387588576735693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 24197703575481783762891605 141783419387588576735693)
                ·
                  rfl

theorem cell22_3727650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 9].length) (baseStart_3727650 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3727650 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3727650 prefixEnd_3727650 := by exact prefixLift 3727650
  have htrace : WordTrace (prefixWord ++ tailWord_3727650) baseStart_3727650 baseEnd_3727650 := by
    simpa [prefixWord, tailWord_3727650, baseEnd_3727650] using wordTrace_append hprefix tailTrace_3727650
  have hstable : (prefixWord ++ tailWord_3727650).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3727650).length < 2 ^ (prefixWord ++ tailWord_3727650).sum := by decide
  have hdescent : baseEnd_3727650 < baseStart_3727650 := by decide
  rcases family_descends (prefixWord ++ tailWord_3727650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3727774 : List Nat := [4, 3, 1, 2, 1, 1, 2, 2, 6]
def baseStart_3727774 : Nat := 118140960795 + 3727774 * 2 ^ 59
def prefixEnd_3727774 : Nat := 4983230072969 + 3 ^ 40 * 3727774 * 2
def baseEnd_3727774 : Nat := 425364407407467400173619

theorem tailTrace_3727774 : CollatzResearch.WordTrace tailWord_3727774 prefixEnd_3727774 425364407407467400173619 := by
  unfold tailWord_3727774
  simp only [CollatzResearch.WordTrace]
  refine ⟨16995385949614865744720797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 90642058397945950638510917 16995385949614865744720797)
  ·
    refine ⟨6373269731105574654270299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16995385949614865744720797 6373269731105574654270299)
    ·
      refine ⟨9559904596658361981405449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6373269731105574654270299 9559904596658361981405449)
      ·
        refine ⟨7169928447493771486054087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9559904596658361981405449 7169928447493771486054087)
        ·
          refine ⟨10754892671240657229081131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7169928447493771486054087 10754892671240657229081131)
          ·
            refine ⟨16132339006860985843621697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10754892671240657229081131 16132339006860985843621697)
            ·
              refine ⟨12099254255145739382716273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16132339006860985843621697 12099254255145739382716273)
              ·
                refine ⟨9074440691359304537037205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12099254255145739382716273 9074440691359304537037205)
                ·
                  refine ⟨425364407407467400173619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9074440691359304537037205 425364407407467400173619)
                  ·
                    rfl

theorem cell22_3727774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 2, 2, 6].length) (baseStart_3727774 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3727774 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3727774 prefixEnd_3727774 := by exact prefixLift 3727774
  have htrace : WordTrace (prefixWord ++ tailWord_3727774) baseStart_3727774 baseEnd_3727774 := by
    simpa [prefixWord, tailWord_3727774, baseEnd_3727774] using wordTrace_append hprefix tailTrace_3727774
  have hstable : (prefixWord ++ tailWord_3727774).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3727774).length < 2 ^ (prefixWord ++ tailWord_3727774).sum := by decide
  have hdescent : baseEnd_3727774 < baseStart_3727774 := by decide
  rcases family_descends (prefixWord ++ tailWord_3727774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3727804 : List Nat := [2, 2, 2, 4, 1, 2, 1, 2, 2, 4]
def baseStart_3727804 : Nat := 118140960795 + 3727804 * 2 ^ 59
def prefixEnd_3727804 : Nat := 4983230072969 + 3 ^ 40 * 3727804 * 2
def baseEnd_3727804 : Nat := 1276103491835492122270765

theorem tailTrace_3727804 : CollatzResearch.WordTrace tailWord_3727804 prefixEnd_3727804 1276103491835492122270765 := by
  unfold tailWord_3727804
  simp only [CollatzResearch.WordTrace]
  refine ⟨67982090893405120540679233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90642787857873494054238977 67982090893405120540679233)
  ·
    refine ⟨50986568170053840405509425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67982090893405120540679233 50986568170053840405509425)
    ·
      refine ⟨38239926127540380304132069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50986568170053840405509425 38239926127540380304132069)
      ·
        refine ⟨7169986148913821307024763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38239926127540380304132069 7169986148913821307024763)
        ·
          refine ⟨10754979223370731960537145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7169986148913821307024763 10754979223370731960537145)
          ·
            refine ⟨8066234417528048970402859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10754979223370731960537145 8066234417528048970402859)
            ·
              refine ⟨12099351626292073455604289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8066234417528048970402859 12099351626292073455604289)
              ·
                refine ⟨9074513719719055091703217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12099351626292073455604289 9074513719719055091703217)
                ·
                  refine ⟨6805885289789291318777413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9074513719719055091703217 6805885289789291318777413)
                  ·
                    refine ⟨1276103491835492122270765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6805885289789291318777413 1276103491835492122270765)
                    ·
                      rfl

theorem cell22_3727804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 1, 2, 2, 4].length) (baseStart_3727804 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3727804 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3727804 prefixEnd_3727804 := by exact prefixLift 3727804
  have htrace : WordTrace (prefixWord ++ tailWord_3727804) baseStart_3727804 baseEnd_3727804 := by
    simpa [prefixWord, tailWord_3727804, baseEnd_3727804] using wordTrace_append hprefix tailTrace_3727804
  have hstable : (prefixWord ++ tailWord_3727804).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3727804).length < 2 ^ (prefixWord ++ tailWord_3727804).sum := by decide
  have hdescent : baseEnd_3727804 < baseStart_3727804 := by decide
  rcases family_descends (prefixWord ++ tailWord_3727804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3727877 : List Nat := [1, 3, 1, 1, 2, 2, 3, 2, 3, 4]
def baseStart_3727877 : Nat := 118140960795 + 3727877 * 2 ^ 59
def prefixEnd_3727877 : Nat := 4983230072969 + 3 ^ 40 * 3727877 * 2
def baseEnd_3727877 : Nat := 1276128481227344265195541

theorem tailTrace_3727877 : CollatzResearch.WordTrace tailWord_3727877 prefixEnd_3727877 1276128481227344265195541 := by
  unfold tailWord_3727877
  simp only [CollatzResearch.WordTrace]
  refine ⟨135966844315545774548765885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90644562877030516365843923 135966844315545774548765885)
  ·
    refine ⟨50987566618329665455787207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135966844315545774548765885 50987566618329665455787207)
    ·
      refine ⟨76481349927494498183680811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50987566618329665455787207 76481349927494498183680811)
      ·
        refine ⟨114722024891241747275521217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76481349927494498183680811 114722024891241747275521217)
        ·
          refine ⟨86041518668431310456640913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114722024891241747275521217 86041518668431310456640913)
          ·
            refine ⟨64531139001323482842480685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86041518668431310456640913 64531139001323482842480685)
            ·
              refine ⟨24199177125496306065930257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64531139001323482842480685 24199177125496306065930257)
              ·
                refine ⟨18149382844122229549447693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24199177125496306065930257 18149382844122229549447693)
                ·
                  refine ⟨6806018566545836081042885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18149382844122229549447693 6806018566545836081042885)
                  ·
                    refine ⟨1276128481227344265195541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6806018566545836081042885 1276128481227344265195541)
                    ·
                      rfl

theorem cell22_3727877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 2, 3, 4].length) (baseStart_3727877 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3727877 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3727877 prefixEnd_3727877 := by exact prefixLift 3727877
  have htrace : WordTrace (prefixWord ++ tailWord_3727877) baseStart_3727877 baseEnd_3727877 := by
    simpa [prefixWord, tailWord_3727877, baseEnd_3727877] using wordTrace_append hprefix tailTrace_3727877
  have hstable : (prefixWord ++ tailWord_3727877).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3727877).length < 2 ^ (prefixWord ++ tailWord_3727877).sum := by decide
  have hdescent : baseEnd_3727877 < baseStart_3727877 := by decide
  rcases family_descends (prefixWord ++ tailWord_3727877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3727879 : List Nat := [1, 1, 4, 3, 3, 1, 1, 1, 2, 5]
def baseStart_3727879 : Nat := 118140960795 + 3727879 * 2 ^ 59
def prefixEnd_3727879 : Nat := 4983230072969 + 3 ^ 40 * 3727879 * 2
def baseEnd_3727879 : Nat := 1276129165868216926645535

theorem tailTrace_3727879 : CollatzResearch.WordTrace tailWord_3727879 prefixEnd_3727879 1276129165868216926645535 := by
  unfold tailWord_3727879
  simp only [CollatzResearch.WordTrace]
  refine ⟨135966917261538528890338691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90644611507692352593559127 135966917261538528890338691)
  ·
    refine ⟨203950375892307793335508037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135966917261538528890338691 203950375892307793335508037)
    ·
      refine ⟨38240695479807711250407757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 203950375892307793335508037 38240695479807711250407757)
      ·
        refine ⟨14340260804927891718902909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38240695479807711250407757 14340260804927891718902909)
        ·
          refine ⟨5377597801847959394588591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14340260804927891718902909 5377597801847959394588591)
          ·
            refine ⟨8066396702771939091882887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5377597801847959394588591 8066396702771939091882887)
            ·
              refine ⟨12099595054157908637824331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8066396702771939091882887 12099595054157908637824331)
              ·
                refine ⟨18149392581236862956736497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12099595054157908637824331 18149392581236862956736497)
                ·
                  refine ⟨13612044435927647217552373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18149392581236862956736497 13612044435927647217552373)
                  ·
                    refine ⟨1276129165868216926645535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13612044435927647217552373 1276129165868216926645535)
                    ·
                      rfl

theorem cell22_3727879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 1, 1, 2, 5].length) (baseStart_3727879 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3727879 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3727879 prefixEnd_3727879 := by exact prefixLift 3727879
  have htrace : WordTrace (prefixWord ++ tailWord_3727879) baseStart_3727879 baseEnd_3727879 := by
    simpa [prefixWord, tailWord_3727879, baseEnd_3727879] using wordTrace_append hprefix tailTrace_3727879
  have hstable : (prefixWord ++ tailWord_3727879).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3727879).length < 2 ^ (prefixWord ++ tailWord_3727879).sum := by decide
  have hdescent : baseEnd_3727879 < baseStart_3727879 := by decide
  rcases family_descends (prefixWord ++ tailWord_3727879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3727909 : List Nat := [1, 3, 1, 2, 2, 1, 3, 5, 4]
def baseStart_3727909 : Nat := 118140960795 + 3727909 * 2 ^ 59
def prefixEnd_3727909 : Nat := 4983230072969 + 3 ^ 40 * 3727909 * 2
def baseEnd_3727909 : Nat := 425379811827102282798481

theorem tailTrace_3727909 : CollatzResearch.WordTrace tailWord_3727909 prefixEnd_3727909 425379811827102282798481 := by
  unfold tailWord_3727909
  simp only [CollatzResearch.WordTrace]
  refine ⟨135968011451429844013930781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90645340967619896009287187 135968011451429844013930781)
  ·
    refine ⟨50988004294286191505224043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135968011451429844013930781 50988004294286191505224043)
    ·
      refine ⟨76482006441429287257836065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50988004294286191505224043 76482006441429287257836065)
      ·
        refine ⟨57361504831071965443377049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76482006441429287257836065 57361504831071965443377049)
        ·
          refine ⟨43021128623303974082532787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57361504831071965443377049 43021128623303974082532787)
          ·
            refine ⟨64531692934955961123799181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43021128623303974082532787 64531692934955961123799181)
            ·
              refine ⟨24199384850608485421424693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64531692934955961123799181 24199384850608485421424693)
              ·
                refine ⟨2268692329744545508258565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24199384850608485421424693 2268692329744545508258565)
                ·
                  refine ⟨425379811827102282798481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2268692329744545508258565 425379811827102282798481)
                  ·
                    rfl

theorem cell22_3727909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 5, 4].length) (baseStart_3727909 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3727909 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3727909 prefixEnd_3727909 := by exact prefixLift 3727909
  have htrace : WordTrace (prefixWord ++ tailWord_3727909) baseStart_3727909 baseEnd_3727909 := by
    simpa [prefixWord, tailWord_3727909, baseEnd_3727909] using wordTrace_append hprefix tailTrace_3727909
  have hstable : (prefixWord ++ tailWord_3727909).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3727909).length < 2 ^ (prefixWord ++ tailWord_3727909).sum := by decide
  have hdescent : baseEnd_3727909 < baseStart_3727909 := by decide
  rcases family_descends (prefixWord ++ tailWord_3727909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3727926 : List Nat := [5, 1, 2, 1, 2, 2, 2, 1, 6]
def baseStart_3727926 : Nat := 118140960795 + 3727926 * 2 ^ 59
def prefixEnd_3727926 : Nat := 4983230072969 + 3 ^ 40 * 3727926 * 2
def baseEnd_3727926 : Nat := 425381751642908156906797

theorem tailTrace_3727926 : CollatzResearch.WordTrace tailWord_3727926 prefixEnd_3727926 425381751642908156906797 := by
  unfold tailWord_3727926
  simp only [CollatzResearch.WordTrace]
  refine ⟨8498039468273015994831227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 90645754328245503944866421 8498039468273015994831227)
  ·
    refine ⟨12747059202409523992246841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8498039468273015994831227 12747059202409523992246841)
    ·
      refine ⟨9560294401807142994185131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12747059202409523992246841 9560294401807142994185131)
      ·
        refine ⟨14340441602710714491277697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9560294401807142994185131 14340441602710714491277697)
        ·
          refine ⟨10755331202033035868458273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14340441602710714491277697 10755331202033035868458273)
          ·
            refine ⟨8066498401524776901343705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10755331202033035868458273 8066498401524776901343705)
            ·
              refine ⟨6049873801143582676007779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8066498401524776901343705 6049873801143582676007779)
              ·
                refine ⟨9074810701715374014011669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6049873801143582676007779 9074810701715374014011669)
                ·
                  refine ⟨425381751642908156906797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9074810701715374014011669 425381751642908156906797)
                  ·
                    rfl

theorem cell22_3727926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 2, 1, 6].length) (baseStart_3727926 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3727926 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3727926 prefixEnd_3727926 := by exact prefixLift 3727926
  have htrace : WordTrace (prefixWord ++ tailWord_3727926) baseStart_3727926 baseEnd_3727926 := by
    simpa [prefixWord, tailWord_3727926, baseEnd_3727926] using wordTrace_append hprefix tailTrace_3727926
  have hstable : (prefixWord ++ tailWord_3727926).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3727926).length < 2 ^ (prefixWord ++ tailWord_3727926).sum := by decide
  have hdescent : baseEnd_3727926 < baseStart_3727926 := by decide
  rcases family_descends (prefixWord ++ tailWord_3727926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3728059 : List Nat := [1, 1, 1, 1, 1, 2, 3, 1, 8, 3]
def baseStart_3728059 : Nat := 118140960795 + 3728059 * 2 ^ 59
def prefixEnd_3728059 : Nat := 4983230072969 + 3 ^ 40 * 3728059 * 2
def baseEnd_3728059 : Nat := 1276190783546756457144983

theorem tailTrace_3728059 : CollatzResearch.WordTrace tailWord_3728059 prefixEnd_3728059 1276190783546756457144983 := by
  unfold tailWord_3728059
  simp only [CollatzResearch.WordTrace]
  refine ⟨135973482400886419631891231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90648988267257613087927487 135973482400886419631891231)
  ·
    refine ⟨203960223601329629447836847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135973482400886419631891231 203960223601329629447836847)
    ·
      refine ⟨305940335401994444171755271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203960223601329629447836847 305940335401994444171755271)
      ·
        refine ⟨458910503102991666257632907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 305940335401994444171755271 458910503102991666257632907)
        ·
          refine ⟨688365754654487499386449361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 458910503102991666257632907 688365754654487499386449361)
          ·
            refine ⟨516274315990865624539837021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 688365754654487499386449361 516274315990865624539837021)
            ·
              refine ⟨193602868496574609202438883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 516274315990865624539837021 193602868496574609202438883)
              ·
                refine ⟨290404302744861913803658325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 193602868496574609202438883 290404302744861913803658325)
                ·
                  refine ⟨3403175422791350552386621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 290404302744861913803658325 3403175422791350552386621)
                  ·
                    refine ⟨1276190783546756457144983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3403175422791350552386621 1276190783546756457144983)
                    ·
                      rfl

theorem cell22_3728059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 1, 8, 3].length) (baseStart_3728059 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3728059 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3728059 prefixEnd_3728059 := by exact prefixLift 3728059
  have htrace : WordTrace (prefixWord ++ tailWord_3728059) baseStart_3728059 baseEnd_3728059 := by
    simpa [prefixWord, tailWord_3728059, baseEnd_3728059] using wordTrace_append hprefix tailTrace_3728059
  have hstable : (prefixWord ++ tailWord_3728059).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3728059).length < 2 ^ (prefixWord ++ tailWord_3728059).sum := by decide
  have hdescent : baseEnd_3728059 < baseStart_3728059 := by decide
  rcases family_descends (prefixWord ++ tailWord_3728059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3728076 : List Nat := [2, 2, 1, 5, 1, 1, 2, 2, 1, 5]
def baseStart_3728076 : Nat := 118140960795 + 3728076 * 2 ^ 59
def prefixEnd_3728076 : Nat := 4983230072969 + 3 ^ 40 * 3728076 * 2
def baseEnd_3728076 : Nat := 1276196602994174079469931

theorem tailTrace_3728076 : CollatzResearch.WordTrace tailWord_3728076 prefixEnd_3728076 1276196602994174079469931 := by
  unfold tailWord_3728076
  simp only [CollatzResearch.WordTrace]
  refine ⟨67987051220912415767630041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90649401627883221023506721 67987051220912415767630041)
  ·
    refine ⟨50990288415684311825722531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67987051220912415767630041 50990288415684311825722531)
    ·
      refine ⟨76485432623526467738583797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50990288415684311825722531 76485432623526467738583797)
      ·
        refine ⟨7170509308455606350492231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 76485432623526467738583797 7170509308455606350492231)
        ·
          refine ⟨10755763962683409525738347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7170509308455606350492231 10755763962683409525738347)
          ·
            refine ⟨16133645944025114288607521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10755763962683409525738347 16133645944025114288607521)
            ·
              refine ⟨12100234458018835716455641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16133645944025114288607521 12100234458018835716455641)
              ·
                refine ⟨9075175843514126787341731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12100234458018835716455641 9075175843514126787341731)
                ·
                  refine ⟨13612763765271190181012597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9075175843514126787341731 13612763765271190181012597)
                  ·
                    refine ⟨1276196602994174079469931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13612763765271190181012597 1276196602994174079469931)
                    ·
                      rfl

theorem cell22_3728076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 2, 2, 1, 5].length) (baseStart_3728076 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3728076 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3728076 prefixEnd_3728076 := by exact prefixLift 3728076
  have htrace : WordTrace (prefixWord ++ tailWord_3728076) baseStart_3728076 baseEnd_3728076 := by
    simpa [prefixWord, tailWord_3728076, baseEnd_3728076] using wordTrace_append hprefix tailTrace_3728076
  have hstable : (prefixWord ++ tailWord_3728076).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3728076).length < 2 ^ (prefixWord ++ tailWord_3728076).sum := by decide
  have hdescent : baseEnd_3728076 < baseStart_3728076 := by decide
  rcases family_descends (prefixWord ++ tailWord_3728076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3728078 : List Nat := [4, 1, 1, 1, 3, 3, 2, 3, 4]
def baseStart_3728078 : Nat := 118140960795 + 3728078 * 2 ^ 59
def prefixEnd_3728078 : Nat := 4983230072969 + 3 ^ 40 * 3728078 * 2
def baseEnd_3728078 : Nat := 425399095878348913639975

theorem tailTrace_3728078 : CollatzResearch.WordTrace tailWord_3728078 prefixEnd_3728078 425399095878348913639975 := by
  unfold tailWord_3728078
  simp only [CollatzResearch.WordTrace]
  refine ⟨16996771923477198234604111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 90649450258545057251221925 16996771923477198234604111)
  ·
    refine ⟨25495157885215797351906167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16996771923477198234604111 25495157885215797351906167)
    ·
      refine ⟨38242736827823696027859251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25495157885215797351906167 38242736827823696027859251)
      ·
        refine ⟨57364105241735544041788877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38242736827823696027859251 57364105241735544041788877)
        ·
          refine ⟨21511539465650829015670829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57364105241735544041788877 21511539465650829015670829)
          ·
            refine ⟨8066827299619060880876561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21511539465650829015670829 8066827299619060880876561)
            ·
              refine ⟨6050120474714295660657421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8066827299619060880876561 6050120474714295660657421)
              ·
                refine ⟨2268795178017860872746533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6050120474714295660657421 2268795178017860872746533)
                ·
                  refine ⟨425399095878348913639975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2268795178017860872746533 425399095878348913639975)
                  ·
                    rfl

theorem cell22_3728078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 2, 3, 4].length) (baseStart_3728078 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3728078 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3728078 prefixEnd_3728078 := by exact prefixLift 3728078
  have htrace : WordTrace (prefixWord ++ tailWord_3728078) baseStart_3728078 baseEnd_3728078 := by
    simpa [prefixWord, tailWord_3728078, baseEnd_3728078] using wordTrace_append hprefix tailTrace_3728078
  have hstable : (prefixWord ++ tailWord_3728078).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3728078).length < 2 ^ (prefixWord ++ tailWord_3728078).sum := by decide
  have hdescent : baseEnd_3728078 < baseStart_3728078 := by decide
  rcases family_descends (prefixWord ++ tailWord_3728078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3728110 : List Nat := [4, 1, 2, 1, 1, 4, 3, 1, 2, 3]
def baseStart_3728110 : Nat := 118140960795 + 3728110 * 2 ^ 59
def prefixEnd_3728110 : Nat := 4983230072969 + 3 ^ 40 * 3728110 * 2
def baseEnd_3728110 : Nat := 1276208241889009324119827

theorem tailTrace_3728110 : CollatzResearch.WordTrace tailWord_3728110 prefixEnd_3728110 1276208241889009324119827 := by
  unfold tailWord_3728110
  simp only [CollatzResearch.WordTrace]
  refine ⟨16996917815462706917749723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 90650228349134436894665189 16996917815462706917749723)
  ·
    refine ⟨25495376723194060376624585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16996917815462706917749723 25495376723194060376624585)
    ·
      refine ⟨19121532542395545282468439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25495376723194060376624585 19121532542395545282468439)
      ·
        refine ⟨28682298813593317923702659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19121532542395545282468439 28682298813593317923702659)
        ·
          refine ⟨43023448220389976885553989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28682298813593317923702659 43023448220389976885553989)
          ·
            refine ⟨8066896541323120666041373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43023448220389976885553989 8066896541323120666041373)
            ·
              refine ⟨3025086202996170249765515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8066896541323120666041373 3025086202996170249765515)
              ·
                refine ⟨4537629304494255374648273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3025086202996170249765515 4537629304494255374648273)
                ·
                  refine ⟨3403221978370691530986205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4537629304494255374648273 3403221978370691530986205)
                  ·
                    refine ⟨1276208241889009324119827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3403221978370691530986205 1276208241889009324119827)
                    ·
                      rfl

theorem cell22_3728110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 3, 1, 2, 3].length) (baseStart_3728110 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3728110 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3728110 prefixEnd_3728110 := by exact prefixLift 3728110
  have htrace : WordTrace (prefixWord ++ tailWord_3728110) baseStart_3728110 baseEnd_3728110 := by
    simpa [prefixWord, tailWord_3728110, baseEnd_3728110] using wordTrace_append hprefix tailTrace_3728110
  have hstable : (prefixWord ++ tailWord_3728110).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3728110).length < 2 ^ (prefixWord ++ tailWord_3728110).sum := by decide
  have hdescent : baseEnd_3728110 < baseStart_3728110 := by decide
  rcases family_descends (prefixWord ++ tailWord_3728110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3728211 : List Nat := [1, 1, 1, 2, 1, 1, 3, 5, 4, 3]
def baseStart_3728211 : Nat := 118140960795 + 3728211 * 2 ^ 59
def prefixEnd_3728211 : Nat := 4983230072969 + 3 ^ 40 * 3728211 * 2
def baseEnd_3728211 : Nat := 1276242816253078727344517

theorem tailTrace_3728211 : CollatzResearch.WordTrace tailWord_3728211 prefixEnd_3728211 1276242816253078727344517 := by
  unfold tailWord_3728211
  simp only [CollatzResearch.WordTrace]
  refine ⟨135979026296335749591424487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90652684197557166394282991 135979026296335749591424487)
  ·
    refine ⟨203968539444503624387136731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135979026296335749591424487 203968539444503624387136731)
    ·
      refine ⟨305952809166755436580705097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203968539444503624387136731 305952809166755436580705097)
      ·
        refine ⟨229464606875066577435528823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 305952809166755436580705097 229464606875066577435528823)
        ·
          refine ⟨344196910312599866153293235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 229464606875066577435528823 344196910312599866153293235)
          ·
            refine ⟨516295365468899799229939853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 344196910312599866153293235 516295365468899799229939853)
            ·
              refine ⟨193610762050837424711227445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 516295365468899799229939853 193610762050837424711227445)
              ·
                refine ⟨18151008942266008566677573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 193610762050837424711227445 18151008942266008566677573)
                ·
                  refine ⟨3403314176674876606252045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18151008942266008566677573 3403314176674876606252045)
                  ·
                    refine ⟨1276242816253078727344517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3403314176674876606252045 1276242816253078727344517)
                    ·
                      rfl

theorem cell22_3728211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 5, 4, 3].length) (baseStart_3728211 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3728211 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3728211 prefixEnd_3728211 := by exact prefixLift 3728211
  have htrace : WordTrace (prefixWord ++ tailWord_3728211) baseStart_3728211 baseEnd_3728211 := by
    simpa [prefixWord, tailWord_3728211, baseEnd_3728211] using wordTrace_append hprefix tailTrace_3728211
  have hstable : (prefixWord ++ tailWord_3728211).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3728211).length < 2 ^ (prefixWord ++ tailWord_3728211).sum := by decide
  have hdescent : baseEnd_3728211 < baseStart_3728211 := by decide
  rcases family_descends (prefixWord ++ tailWord_3728211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3728213 : List Nat := [1, 3, 2, 2, 2, 1, 3, 4, 4]
def baseStart_3728213 : Nat := 118140960795 + 3728213 * 2 ^ 59
def prefixEnd_3728213 : Nat := 4983230072969 + 3 ^ 40 * 3728213 * 2
def baseEnd_3728213 : Nat := 425414500297983796264837

theorem tailTrace_3728213 : CollatzResearch.WordTrace tailWord_3728213 prefixEnd_3728213 425414500297983796264837 := by
  unfold tailWord_3728213
  simp only [CollatzResearch.WordTrace]
  refine ⟨135979099242328503932997293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90652732828219002621998195 135979099242328503932997293)
  ·
    refine ⟨50992162215873188974873985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135979099242328503932997293 50992162215873188974873985)
    ·
      refine ⟨38244121661904891731155489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50992162215873188974873985 38244121661904891731155489)
      ·
        refine ⟨28683091246428668798366617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38244121661904891731155489 28683091246428668798366617)
        ·
          refine ⟨21512318434821501598774963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28683091246428668798366617 21512318434821501598774963)
          ·
            refine ⟨32268477652232252398162445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21512318434821501598774963 32268477652232252398162445)
            ·
              refine ⟨12100679119587094649310917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32268477652232252398162445 12100679119587094649310917)
              ·
                refine ⟨2268877334922580246745797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12100679119587094649310917 2268877334922580246745797)
                ·
                  refine ⟨425414500297983796264837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2268877334922580246745797 425414500297983796264837)
                  ·
                    rfl

theorem cell22_3728213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 3, 4, 4].length) (baseStart_3728213 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3728213 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3728213 prefixEnd_3728213 := by exact prefixLift 3728213
  have htrace : WordTrace (prefixWord ++ tailWord_3728213) baseStart_3728213 baseEnd_3728213 := by
    simpa [prefixWord, tailWord_3728213, baseEnd_3728213] using wordTrace_append hprefix tailTrace_3728213
  have hstable : (prefixWord ++ tailWord_3728213).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3728213).length < 2 ^ (prefixWord ++ tailWord_3728213).sum := by decide
  have hdescent : baseEnd_3728213 < baseStart_3728213 := by decide
  rcases family_descends (prefixWord ++ tailWord_3728213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3728228 : List Nat := [2, 3, 1, 1, 4, 2, 2, 1, 1, 5]
def baseStart_3728228 : Nat := 118140960795 + 3728228 * 2 ^ 59
def prefixEnd_3728228 : Nat := 4983230072969 + 3 ^ 40 * 3728228 * 2
def baseEnd_3728228 : Nat := 1276248635700496349669465

theorem tailTrace_3728228 : CollatzResearch.WordTrace tailWord_3728228 prefixEnd_3728228 1276248635700496349669465 := by
  unfold tailWord_3728228
  simp only [CollatzResearch.WordTrace]
  refine ⟨67989823168637080747396669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90653097558182774329862225 67989823168637080747396669)
  ·
    refine ⟨25496183688238905280273751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67989823168637080747396669 25496183688238905280273751)
    ·
      refine ⟨38244275532358357920410627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25496183688238905280273751 38244275532358357920410627)
      ·
        refine ⟨57366413298537536880615941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38244275532358357920410627 57366413298537536880615941)
        ·
          refine ⟨10756202493475788165115489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57366413298537536880615941 10756202493475788165115489)
          ·
            refine ⟨8067151870106841123836617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10756202493475788165115489 8067151870106841123836617)
            ·
              refine ⟨6050363902580130842877463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8067151870106841123836617 6050363902580130842877463)
              ·
                refine ⟨9075545853870196264316195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6050363902580130842877463 9075545853870196264316195)
                ·
                  refine ⟨13613318780805294396474293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9075545853870196264316195 13613318780805294396474293)
                  ·
                    refine ⟨1276248635700496349669465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13613318780805294396474293 1276248635700496349669465)
                    ·
                      rfl

theorem cell22_3728228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 2, 1, 1, 5].length) (baseStart_3728228 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3728228 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3728228 prefixEnd_3728228 := by exact prefixLift 3728228
  have htrace : WordTrace (prefixWord ++ tailWord_3728228) baseStart_3728228 baseEnd_3728228 := by
    simpa [prefixWord, tailWord_3728228, baseEnd_3728228] using wordTrace_append hprefix tailTrace_3728228
  have hstable : (prefixWord ++ tailWord_3728228).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3728228).length < 2 ^ (prefixWord ++ tailWord_3728228).sum := by decide
  have hdescent : baseEnd_3728228 < baseStart_3728228 := by decide
  rcases family_descends (prefixWord ++ tailWord_3728228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3728290 : List Nat := [3, 3, 1, 2, 2, 1, 2, 2, 3, 3]
def baseStart_3728290 : Nat := 118140960795 + 3728290 * 2 ^ 59
def prefixEnd_3728290 : Nat := 4983230072969 + 3 ^ 40 * 3728290 * 2
def baseEnd_3728290 : Nat := 1276269859567548854619275

theorem tailTrace_3728290 : CollatzResearch.WordTrace tailWord_3728290 prefixEnd_3728290 1276269859567548854619275 := by
  unfold tailWord_3728290
  simp only [CollatzResearch.WordTrace]
  refine ⟨33995476915762386520887581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90654605108699697389033549 33995476915762386520887581)
  ·
    refine ⟨12748303843410894945332843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33995476915762386520887581 12748303843410894945332843)
    ·
      refine ⟨19122455765116342417999265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12748303843410894945332843 19122455765116342417999265)
      ·
        refine ⟨14341841823837256813499449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19122455765116342417999265 14341841823837256813499449)
        ·
          refine ⟨10756381367877942610124587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14341841823837256813499449 10756381367877942610124587)
          ·
            refine ⟨16134572051816913915186881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10756381367877942610124587 16134572051816913915186881)
            ·
              refine ⟨12100929038862685436390161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16134572051816913915186881 12100929038862685436390161)
              ·
                refine ⟨9075696779147014077292621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12100929038862685436390161 9075696779147014077292621)
                ·
                  refine ⟨3403386292180130278984733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9075696779147014077292621 3403386292180130278984733)
                  ·
                    refine ⟨1276269859567548854619275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3403386292180130278984733 1276269859567548854619275)
                    ·
                      rfl

theorem cell22_3728290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 2, 2, 3, 3].length) (baseStart_3728290 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3728290 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3728290 prefixEnd_3728290 := by exact prefixLift 3728290
  have htrace : WordTrace (prefixWord ++ tailWord_3728290) baseStart_3728290 baseEnd_3728290 := by
    simpa [prefixWord, tailWord_3728290, baseEnd_3728290] using wordTrace_append hprefix tailTrace_3728290
  have hstable : (prefixWord ++ tailWord_3728290).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3728290).length < 2 ^ (prefixWord ++ tailWord_3728290).sum := by decide
  have hdescent : baseEnd_3728290 < baseStart_3728290 := by decide
  rcases family_descends (prefixWord ++ tailWord_3728290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3728324 : List Nat := [2, 3, 3, 3, 1, 2, 1, 1, 3, 3]
def baseStart_3728324 : Nat := 118140960795 + 3728324 * 2 ^ 59
def prefixEnd_3728324 : Nat := 4983230072969 + 3 ^ 40 * 3728324 * 2
def baseEnd_3728324 : Nat := 1276281498462384099269171

theorem tailTrace_3728324 : CollatzResearch.WordTrace tailWord_3728324 prefixEnd_3728324 1276281498462384099269171 := by
  unfold tailWord_3728324
  simp only [CollatzResearch.WordTrace]
  refine ⟨67991573872463184945144013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90655431829950913260192017 67991573872463184945144013)
  ·
    refine ⟨25496840202173694354429005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67991573872463184945144013 25496840202173694354429005)
    ·
      refine ⟨9561315075815135382910877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25496840202173694354429005 9561315075815135382910877)
      ·
        refine ⟨3585493153430675768591579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9561315075815135382910877 3585493153430675768591579)
        ·
          refine ⟨5378239730146013652887369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3585493153430675768591579 5378239730146013652887369)
          ·
            refine ⟨4033679797609510239665527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5378239730146013652887369 4033679797609510239665527)
            ·
              refine ⟨6050519696414265359498291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4033679797609510239665527 6050519696414265359498291)
              ·
                refine ⟨9075779544621398039247437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6050519696414265359498291 9075779544621398039247437)
                ·
                  refine ⟨3403417329233024264717789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9075779544621398039247437 3403417329233024264717789)
                  ·
                    refine ⟨1276281498462384099269171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3403417329233024264717789 1276281498462384099269171)
                    ·
                      rfl

theorem cell22_3728324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 2, 1, 1, 3, 3].length) (baseStart_3728324 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3728324 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3728324 prefixEnd_3728324 := by exact prefixLift 3728324
  have htrace : WordTrace (prefixWord ++ tailWord_3728324) baseStart_3728324 baseEnd_3728324 := by
    simpa [prefixWord, tailWord_3728324, baseEnd_3728324] using wordTrace_append hprefix tailTrace_3728324
  have hstable : (prefixWord ++ tailWord_3728324).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3728324).length < 2 ^ (prefixWord ++ tailWord_3728324).sum := by decide
  have hdescent : baseEnd_3728324 < baseStart_3728324 := by decide
  rcases family_descends (prefixWord ++ tailWord_3728324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3728380 : List Nat := [2, 2, 2, 1, 2, 3, 1, 4, 2, 3]
def baseStart_3728380 : Nat := 118140960795 + 3728380 * 2 ^ 59
def prefixEnd_3728380 : Nat := 4983230072969 + 3 ^ 40 * 3728380 * 2
def baseEnd_3728380 : Nat := 1276300668406818619868999

theorem tailTrace_3728380 : CollatzResearch.WordTrace tailWord_3728380 prefixEnd_3728380 1276300668406818619868999 := by
  unfold tailWord_3728380
  simp only [CollatzResearch.WordTrace]
  refine ⟨67992595116361745727163297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90656793488482327636217729 67992595116361745727163297)
  ·
    refine ⟨50994446337271309295372473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67992595116361745727163297 50994446337271309295372473)
    ·
      refine ⟨38245834752953481971529355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50994446337271309295372473 38245834752953481971529355)
      ·
        refine ⟨57368752129430222957294033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38245834752953481971529355 57368752129430222957294033)
        ·
          refine ⟨43026564097072667217970525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57368752129430222957294033 43026564097072667217970525)
          ·
            refine ⟨16134961536402250206738947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43026564097072667217970525 16134961536402250206738947)
            ·
              refine ⟨24202442304603375310108421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16134961536402250206738947 24202442304603375310108421)
              ·
                refine ⟨4537957932113132870645329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24202442304603375310108421 4537957932113132870645329)
                ·
                  refine ⟨3403468449084849652983997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4537957932113132870645329 3403468449084849652983997)
                  ·
                    refine ⟨1276300668406818619868999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3403468449084849652983997 1276300668406818619868999)
                    ·
                      rfl

theorem cell22_3728380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 4, 2, 3].length) (baseStart_3728380 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3728380 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3728380 prefixEnd_3728380 := by exact prefixLift 3728380
  have htrace : WordTrace (prefixWord ++ tailWord_3728380) baseStart_3728380 baseEnd_3728380 := by
    simpa [prefixWord, tailWord_3728380, baseEnd_3728380] using wordTrace_append hprefix tailTrace_3728380
  have hstable : (prefixWord ++ tailWord_3728380).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3728380).length < 2 ^ (prefixWord ++ tailWord_3728380).sum := by decide
  have hdescent : baseEnd_3728380 < baseStart_3728380 := by decide
  rcases family_descends (prefixWord ++ tailWord_3728380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3728412 : List Nat := [2, 2, 3, 1, 4, 2, 1, 1, 2, 4]
def baseStart_3728412 : Nat := 118140960795 + 3728412 * 2 ^ 59
def prefixEnd_3728412 : Nat := 4983230072969 + 3 ^ 40 * 3728412 * 2
def baseEnd_3728412 : Nat := 1276311622660781203068901

theorem tailTrace_3728412 : CollatzResearch.WordTrace tailWord_3728412 prefixEnd_3728412 1276311622660781203068901 := by
  unfold tailWord_3728412
  simp only [CollatzResearch.WordTrace]
  refine ⟨67993178684303780459745745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90657571579071707279660993 67993178684303780459745745)
  ·
    refine ⟨50994884013227835344809309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67993178684303780459745745 50994884013227835344809309)
    ·
      refine ⟨19123081504960438254303491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50994884013227835344809309 19123081504960438254303491)
      ·
        refine ⟨28684622257440657381455237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19123081504960438254303491 28684622257440657381455237)
        ·
          refine ⟨5378366673270123259022857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28684622257440657381455237 5378366673270123259022857)
          ·
            refine ⟨4033775004952592444267143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5378366673270123259022857 4033775004952592444267143)
            ·
              refine ⟨6050662507428888666400715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4033775004952592444267143 6050662507428888666400715)
              ·
                refine ⟨9075993761143332999601073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6050662507428888666400715 9075993761143332999601073)
                ·
                  refine ⟨6806995320857499749700805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9075993761143332999601073 6806995320857499749700805)
                  ·
                    refine ⟨1276311622660781203068901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6806995320857499749700805 1276311622660781203068901)
                    ·
                      rfl

theorem cell22_3728412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 2, 1, 1, 2, 4].length) (baseStart_3728412 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3728412 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3728412 prefixEnd_3728412 := by exact prefixLift 3728412
  have htrace : WordTrace (prefixWord ++ tailWord_3728412) baseStart_3728412 baseEnd_3728412 := by
    simpa [prefixWord, tailWord_3728412, baseEnd_3728412] using wordTrace_append hprefix tailTrace_3728412
  have hstable : (prefixWord ++ tailWord_3728412).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3728412).length < 2 ^ (prefixWord ++ tailWord_3728412).sum := by decide
  have hdescent : baseEnd_3728412 < baseStart_3728412 := by decide
  rcases family_descends (prefixWord ++ tailWord_3728412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3728442 : List Nat := [3, 1, 1, 1, 3, 1, 4, 4, 1, 3]
def baseStart_3728442 : Nat := 118140960795 + 3728442 * 2 ^ 59
def prefixEnd_3728442 : Nat := 4983230072969 + 3 ^ 40 * 3728442 * 2
def baseEnd_3728442 : Nat := 1276321892273871124818809

theorem tailTrace_3728442 : CollatzResearch.WordTrace tailWord_3728442 prefixEnd_3728442 1276321892273871124818809 := by
  unfold tailWord_3728442
  simp only [CollatzResearch.WordTrace]
  refine ⟨33996862889624719010770895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90658301038999250695389053 33996862889624719010770895)
  ·
    refine ⟨50995294334437078516156343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33996862889624719010770895 50995294334437078516156343)
    ·
      refine ⟨76492941501655617774234515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50995294334437078516156343 76492941501655617774234515)
      ·
        refine ⟨114739412252483426661351773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76492941501655617774234515 114739412252483426661351773)
        ·
          refine ⟨43027279594681284998006915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 114739412252483426661351773 43027279594681284998006915)
          ·
            refine ⟨64540919392021927497010373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43027279594681284998006915 64540919392021927497010373)
            ·
              refine ⟨12101422386004111405689445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64540919392021927497010373 12101422386004111405689445)
              ·
                refine ⟨2269016697375770888566771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12101422386004111405689445 2269016697375770888566771)
                ·
                  refine ⟨3403525046063656332850157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2269016697375770888566771 3403525046063656332850157)
                  ·
                    refine ⟨1276321892273871124818809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3403525046063656332850157 1276321892273871124818809)
                    ·
                      rfl

theorem cell22_3728442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 4, 4, 1, 3].length) (baseStart_3728442 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3728442 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3728442 prefixEnd_3728442 := by exact prefixLift 3728442
  have htrace : WordTrace (prefixWord ++ tailWord_3728442) baseStart_3728442 baseEnd_3728442 := by
    simpa [prefixWord, tailWord_3728442, baseEnd_3728442] using wordTrace_append hprefix tailTrace_3728442
  have hstable : (prefixWord ++ tailWord_3728442).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3728442).length < 2 ^ (prefixWord ++ tailWord_3728442).sum := by decide
  have hdescent : baseEnd_3728442 < baseStart_3728442 := by decide
  rcases family_descends (prefixWord ++ tailWord_3728442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3728453 : List Nat := [1, 3, 1, 1, 1, 3, 4, 1, 2, 5]
def baseStart_3728453 : Nat := 118140960795 + 3728453 * 2 ^ 59
def prefixEnd_3728453 : Nat := 4983230072969 + 3 ^ 40 * 3728453 * 2
def baseEnd_3728453 : Nat := 1276325657798670762793775

theorem tailTrace_3728453 : CollatzResearch.WordTrace tailWord_3728453 prefixEnd_3728453 1276325657798670762793775 := by
  unfold tailWord_3728453
  simp only [CollatzResearch.WordTrace]
  refine ⟨135987852761459024921734013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90658568507639349947822675 135987852761459024921734013)
  ·
    refine ⟨50995444785547134345650255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135987852761459024921734013 50995444785547134345650255)
    ·
      refine ⟨76493167178320701518475383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50995444785547134345650255 76493167178320701518475383)
      ·
        refine ⟨114739750767481052277713075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76493167178320701518475383 114739750767481052277713075)
        ·
          refine ⟨172109626151221578416569613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114739750767481052277713075 172109626151221578416569613)
          ·
            refine ⟨64541109806708091906213605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 172109626151221578416569613 64541109806708091906213605)
            ·
              refine ⟨12101458088757767232415051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64541109806708091906213605 12101458088757767232415051)
              ·
                refine ⟨18152187133136650848622577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12101458088757767232415051 18152187133136650848622577)
                ·
                  refine ⟨13614140349852488136466933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18152187133136650848622577 13614140349852488136466933)
                  ·
                    refine ⟨1276325657798670762793775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13614140349852488136466933 1276325657798670762793775)
                    ·
                      rfl

theorem cell22_3728453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 4, 1, 2, 5].length) (baseStart_3728453 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3728453 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3728453 prefixEnd_3728453 := by exact prefixLift 3728453
  have htrace : WordTrace (prefixWord ++ tailWord_3728453) baseStart_3728453 baseEnd_3728453 := by
    simpa [prefixWord, tailWord_3728453, baseEnd_3728453] using wordTrace_append hprefix tailTrace_3728453
  have hstable : (prefixWord ++ tailWord_3728453).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3728453).length < 2 ^ (prefixWord ++ tailWord_3728453).sum := by decide
  have hdescent : baseEnd_3728453 < baseStart_3728453 := by decide
  rcases family_descends (prefixWord ++ tailWord_3728453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3728485 : List Nat := [1, 3, 1, 3, 2, 1, 1, 5, 1, 4]
def baseStart_3728485 : Nat := 118140960795 + 3728485 * 2 ^ 59
def prefixEnd_3728485 : Nat := 4983230072969 + 3 ^ 40 * 3728485 * 2
def baseEnd_3728485 : Nat := 1276336612052633345993677

theorem tailTrace_3728485 : CollatzResearch.WordTrace tailWord_3728485 prefixEnd_3728485 1276336612052633345993677 := by
  unfold tailWord_3728485
  simp only [CollatzResearch.WordTrace]
  refine ⟨135989019897343094386898909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90659346598228729591265939 135989019897343094386898909)
  ·
    refine ⟨50995882461503660395087091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135989019897343094386898909 50995882461503660395087091)
    ·
      refine ⟨76493823692255490592630637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50995882461503660395087091 76493823692255490592630637)
      ·
        refine ⟨28685183884595808972236489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76493823692255490592630637 28685183884595808972236489)
        ·
          refine ⟨21513887913446856729177367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28685183884595808972236489 21513887913446856729177367)
          ·
            refine ⟨32270831870170285093766051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21513887913446856729177367 32270831870170285093766051)
            ·
              refine ⟨48406247805255427640649077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32270831870170285093766051 48406247805255427640649077)
              ·
                refine ⟨4538085731742696341310851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 48406247805255427640649077 4538085731742696341310851)
                ·
                  refine ⟨6807128597614044511966277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4538085731742696341310851 6807128597614044511966277)
                  ·
                    refine ⟨1276336612052633345993677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6807128597614044511966277 1276336612052633345993677)
                    ·
                      rfl

theorem cell22_3728485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 5, 1, 4].length) (baseStart_3728485 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3728485 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3728485 prefixEnd_3728485 := by exact prefixLift 3728485
  have htrace : WordTrace (prefixWord ++ tailWord_3728485) baseStart_3728485 baseEnd_3728485 := by
    simpa [prefixWord, tailWord_3728485, baseEnd_3728485] using wordTrace_append hprefix tailTrace_3728485
  have hstable : (prefixWord ++ tailWord_3728485).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3728485).length < 2 ^ (prefixWord ++ tailWord_3728485).sum := by decide
  have hdescent : baseEnd_3728485 < baseStart_3728485 := by decide
  rcases family_descends (prefixWord ++ tailWord_3728485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3728551 : List Nat := [1, 1, 6, 2, 1, 3, 2, 2, 4]
def baseStart_3728551 : Nat := 118140960795 + 3728551 * 2 ^ 59
def prefixEnd_3728551 : Nat := 4983230072969 + 3 ^ 40 * 3728551 * 2
def baseEnd_3728551 : Nat := 425453068400477057947825

theorem tailTrace_3728551 : CollatzResearch.WordTrace tailWord_3728551 prefixEnd_3728551 425453068400477057947825 := by
  unfold tailWord_3728551
  simp only [CollatzResearch.WordTrace]
  refine ⟨135991427115103987658801507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90660951410069325105867671 135991427115103987658801507)
  ·
    refine ⟨203987140672655981488202261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135991427115103987658801507 203987140672655981488202261)
    ·
      refine ⟨9561897219030749132259481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 203987140672655981488202261 9561897219030749132259481)
      ·
        refine ⟨7171422914273061849194611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9561897219030749132259481 7171422914273061849194611)
        ·
          refine ⟨10757134371409592773791917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7171422914273061849194611 10757134371409592773791917)
          ·
            refine ⟨4033925389278597290171969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10757134371409592773791917 4033925389278597290171969)
            ·
              refine ⟨3025444041958947967628977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4033925389278597290171969 3025444041958947967628977)
              ·
                refine ⟨2269083031469210975721733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3025444041958947967628977 2269083031469210975721733)
                ·
                  refine ⟨425453068400477057947825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2269083031469210975721733 425453068400477057947825)
                  ·
                    rfl

theorem cell22_3728551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 3, 2, 2, 4].length) (baseStart_3728551 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3728551 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3728551 prefixEnd_3728551 := by exact prefixLift 3728551
  have htrace : WordTrace (prefixWord ++ tailWord_3728551) baseStart_3728551 baseEnd_3728551 := by
    simpa [prefixWord, tailWord_3728551, baseEnd_3728551] using wordTrace_append hprefix tailTrace_3728551
  have hstable : (prefixWord ++ tailWord_3728551).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3728551).length < 2 ^ (prefixWord ++ tailWord_3728551).sum := by decide
  have hdescent : baseEnd_3728551 < baseStart_3728551 := by decide
  rcases family_descends (prefixWord ++ tailWord_3728551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3728566 : List Nat := [5, 1, 3, 2, 1, 1, 2, 1, 1, 5]
def baseStart_3728566 : Nat := 118140960795 + 3728566 * 2 ^ 59
def prefixEnd_3728566 : Nat := 4983230072969 + 3 ^ 40 * 3728566 * 2
def baseEnd_3728566 : Nat := 1276364340007976134718429

theorem tailTrace_3728566 : CollatzResearch.WordTrace tailWord_3728566 prefixEnd_3728566 1276364340007976134718429 := by
  unfold tailWord_3728566
  simp only [CollatzResearch.WordTrace]
  refine ⟨8499498388128102826287347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 90661316140033096813731701 8499498388128102826287347)
  ·
    refine ⟨12749247582192154239431021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8499498388128102826287347 12749247582192154239431021)
    ·
      refine ⟨4780967843322057839786633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12749247582192154239431021 4780967843322057839786633)
      ·
        refine ⟨3585725882491543379839975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4780967843322057839786633 3585725882491543379839975)
        ·
          refine ⟨5378588823737315069759963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3585725882491543379839975 5378588823737315069759963)
          ·
            refine ⟨8067883235605972604639945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5378588823737315069759963 8067883235605972604639945)
            ·
              refine ⟨6050912426704479453479959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8067883235605972604639945 6050912426704479453479959)
              ·
                refine ⟨9076368640056719180219939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6050912426704479453479959 9076368640056719180219939)
                ·
                  refine ⟨13614552960085078770329909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9076368640056719180219939 13614552960085078770329909)
                  ·
                    refine ⟨1276364340007976134718429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13614552960085078770329909 1276364340007976134718429)
                    ·
                      rfl

theorem cell22_3728566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 2, 1, 1, 5].length) (baseStart_3728566 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3728566 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3728566 prefixEnd_3728566 := by exact prefixLift 3728566
  have htrace : WordTrace (prefixWord ++ tailWord_3728566) baseStart_3728566 baseEnd_3728566 := by
    simpa [prefixWord, tailWord_3728566, baseEnd_3728566] using wordTrace_append hprefix tailTrace_3728566
  have hstable : (prefixWord ++ tailWord_3728566).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3728566).length < 2 ^ (prefixWord ++ tailWord_3728566).sum := by decide
  have hdescent : baseEnd_3728566 < baseStart_3728566 := by decide
  rcases family_descends (prefixWord ++ tailWord_3728566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3728603 : List Nat := [1, 1, 1, 1, 1, 1, 1, 4, 1, 10]
def baseStart_3728603 : Nat := 118140960795 + 3728603 * 2 ^ 59
def prefixEnd_3728603 : Nat := 4983230072969 + 3 ^ 40 * 3728603 * 2
def baseEnd_3728603 : Nat := 1276377005864120371543315

theorem tailTrace_3728603 : CollatzResearch.WordTrace tailWord_3728603 prefixEnd_3728603 1276377005864120371543315 := by
  unfold tailWord_3728603
  simp only [CollatzResearch.WordTrace]
  refine ⟨135993323710915600539694463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90662215807277067026462975 135993323710915600539694463)
  ·
    refine ⟨203989985566373400809541695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135993323710915600539694463 203989985566373400809541695)
    ·
      refine ⟨305984978349560101214312543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203989985566373400809541695 305984978349560101214312543)
      ·
        refine ⟨458977467524340151821468815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 305984978349560101214312543 458977467524340151821468815)
        ·
          refine ⟨688466201286510227732203223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 458977467524340151821468815 688466201286510227732203223)
          ·
            refine ⟨1032699301929765341598304835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 688466201286510227732203223 1032699301929765341598304835)
            ·
              refine ⟨1549048952894648012397457253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1032699301929765341598304835 1549048952894648012397457253)
              ·
                refine ⟨290446678667746502324523235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1549048952894648012397457253 290446678667746502324523235)
                ·
                  refine ⟨435670018001619753486784853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 290446678667746502324523235 435670018001619753486784853)
                  ·
                    refine ⟨1276377005864120371543315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 435670018001619753486784853 1276377005864120371543315)
                    ·
                      rfl

theorem cell22_3728603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 1, 10].length) (baseStart_3728603 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3728603 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3728603 prefixEnd_3728603 := by exact prefixLift 3728603
  have htrace : WordTrace (prefixWord ++ tailWord_3728603) baseStart_3728603 baseEnd_3728603 := by
    simpa [prefixWord, tailWord_3728603, baseEnd_3728603] using wordTrace_append hprefix tailTrace_3728603
  have hstable : (prefixWord ++ tailWord_3728603).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3728603).length < 2 ^ (prefixWord ++ tailWord_3728603).sum := by decide
  have hdescent : baseEnd_3728603 < baseStart_3728603 := by decide
  rcases family_descends (prefixWord ++ tailWord_3728603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3728650 : List Nat := [3, 1, 2, 2, 1, 1, 1, 3, 3, 5]
def baseStart_3728650 : Nat := 118140960795 + 3728650 * 2 ^ 59
def prefixEnd_3728650 : Nat := 4983230072969 + 3 ^ 40 * 3728650 * 2
def baseEnd_3728650 : Nat := 1276393094924627915618171

theorem tailTrace_3728650 : CollatzResearch.WordTrace tailWord_3728650 prefixEnd_3728650 1276393094924627915618171 := by
  unfold tailWord_3728650
  simp only [CollatzResearch.WordTrace]
  refine ⟨33998759485436331891663851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90663358627830218377770269 33998759485436331891663851)
  ·
    refine ⟨50998139228154497837495777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33998759485436331891663851 50998139228154497837495777)
    ·
      refine ⟨38248604421115873378121833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50998139228154497837495777 38248604421115873378121833)
      ·
        refine ⟨28686453315836905033591375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38248604421115873378121833 28686453315836905033591375)
        ·
          refine ⟨43029679973755357550387063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28686453315836905033591375 43029679973755357550387063)
          ·
            refine ⟨64544519960633036325580595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43029679973755357550387063 64544519960633036325580595)
            ·
              refine ⟨96816779940949554488370893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64544519960633036325580595 96816779940949554488370893)
              ·
                refine ⟨36306292477856082933139085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 96816779940949554488370893 36306292477856082933139085)
                ·
                  refine ⟨13614859679196031099927157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36306292477856082933139085 13614859679196031099927157)
                  ·
                    refine ⟨1276393094924627915618171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13614859679196031099927157 1276393094924627915618171)
                    ·
                      rfl

theorem cell22_3728650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 3, 3, 5].length) (baseStart_3728650 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3728650 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3728650 prefixEnd_3728650 := by exact prefixLift 3728650
  have htrace : WordTrace (prefixWord ++ tailWord_3728650) baseStart_3728650 baseEnd_3728650 := by
    simpa [prefixWord, tailWord_3728650, baseEnd_3728650] using wordTrace_append hprefix tailTrace_3728650
  have hstable : (prefixWord ++ tailWord_3728650).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3728650).length < 2 ^ (prefixWord ++ tailWord_3728650).sum := by decide
  have hdescent : baseEnd_3728650 < baseStart_3728650 := by decide
  rcases family_descends (prefixWord ++ tailWord_3728650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3728667 : List Nat := [1, 1, 1, 1, 1, 1, 5, 6, 2, 3]
def baseStart_3728667 : Nat := 118140960795 + 3728667 * 2 ^ 59
def prefixEnd_3728667 : Nat := 4983230072969 + 3 ^ 40 * 3728667 * 2
def baseEnd_3728667 : Nat := 1276398914372045537943119

theorem tailTrace_3728667 : CollatzResearch.WordTrace tailWord_3728667 prefixEnd_3728667 1276398914372045537943119 := by
  unfold tailWord_3728667
  simp only [CollatzResearch.WordTrace]
  refine ⟨135995657982683739470024255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90663771988455826313349503 135995657982683739470024255)
  ·
    refine ⟨203993486974025609205036383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135995657982683739470024255 203993486974025609205036383)
    ·
      refine ⟨305990230461038413807554575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203993486974025609205036383 305990230461038413807554575)
      ·
        refine ⟨458985345691557620711331863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 305990230461038413807554575 458985345691557620711331863)
        ·
          refine ⟨688478018537336431066997795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 458985345691557620711331863 688478018537336431066997795)
          ·
            refine ⟨1032717027806004646600496693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 688478018537336431066997795 1032717027806004646600496693)
            ·
              refine ⟨96817221356812935618796565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1032717027806004646600496693 96817221356812935618796565)
              ·
                refine ⟨4538307251100606357131089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 96817221356812935618796565 4538307251100606357131089)
                ·
                  refine ⟨3403730438325454767848317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4538307251100606357131089 3403730438325454767848317)
                  ·
                    refine ⟨1276398914372045537943119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3403730438325454767848317 1276398914372045537943119)
                    ·
                      rfl

theorem cell22_3728667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 6, 2, 3].length) (baseStart_3728667 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3728667 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3728667 prefixEnd_3728667 := by exact prefixLift 3728667
  have htrace : WordTrace (prefixWord ++ tailWord_3728667) baseStart_3728667 baseEnd_3728667 := by
    simpa [prefixWord, tailWord_3728667, baseEnd_3728667] using wordTrace_append hprefix tailTrace_3728667
  have hstable : (prefixWord ++ tailWord_3728667).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3728667).length < 2 ^ (prefixWord ++ tailWord_3728667).sum := by decide
  have hdescent : baseEnd_3728667 < baseStart_3728667 := by decide
  rcases family_descends (prefixWord ++ tailWord_3728667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3728669 : List Nat := [1, 4, 2, 3, 1, 3, 1, 1, 6]
def baseStart_3728669 : Nat := 118140960795 + 3728669 * 2 ^ 59
def prefixEnd_3728669 : Nat := 4983230072969 + 3 ^ 40 * 3728669 * 2
def baseEnd_3728669 : Nat := 425466533004306066464371

theorem tailTrace_3728669 : CollatzResearch.WordTrace tailWord_3728669 prefixEnd_3728669 425466533004306066464371 := by
  unfold tailWord_3728669
  simp only [CollatzResearch.WordTrace]
  refine ⟨135995730928676493811597061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90663820619117662541064707 135995730928676493811597061)
  ·
    refine ⟨25499199549126842589674449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 135995730928676493811597061 25499199549126842589674449)
    ·
      refine ⟨19124399661845131942255837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25499199549126842589674449 19124399661845131942255837)
      ·
        refine ⟨7171649873191924478345939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19124399661845131942255837 7171649873191924478345939)
        ·
          refine ⟨10757474809787886717518909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7171649873191924478345939 10757474809787886717518909)
          ·
            refine ⟨4034053053670457519069591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10757474809787886717518909 4034053053670457519069591)
            ·
              refine ⟨6051079580505686278604387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4034053053670457519069591 6051079580505686278604387)
              ·
                refine ⟨9076619370758529417906581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6051079580505686278604387 9076619370758529417906581)
                ·
                  refine ⟨425466533004306066464371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9076619370758529417906581 425466533004306066464371)
                  ·
                    rfl

theorem cell22_3728669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 3, 1, 1, 6].length) (baseStart_3728669 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3728669 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3728669 prefixEnd_3728669 := by exact prefixLift 3728669
  have htrace : WordTrace (prefixWord ++ tailWord_3728669) baseStart_3728669 baseEnd_3728669 := by
    simpa [prefixWord, tailWord_3728669, baseEnd_3728669] using wordTrace_append hprefix tailTrace_3728669
  have hstable : (prefixWord ++ tailWord_3728669).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3728669).length < 2 ^ (prefixWord ++ tailWord_3728669).sum := by decide
  have hdescent : baseEnd_3728669 < baseStart_3728669 := by decide
  rcases family_descends (prefixWord ++ tailWord_3728669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3728746 : List Nat := [3, 1, 3, 3, 2, 1, 1, 2, 3, 3]
def baseStart_3728746 : Nat := 118140960795 + 3728746 * 2 ^ 59
def prefixEnd_3728746 : Nat := 4983230072969 + 3 ^ 40 * 3728746 * 2
def baseEnd_3728746 : Nat := 1276425957686515665217877

theorem tailTrace_3728746 : CollatzResearch.WordTrace tailWord_3728746 prefixEnd_3728746 1276425957686515665217877 := by
  unfold tailWord_3728746
  simp only [CollatzResearch.WordTrace]
  refine ⟨33999634837349383990537523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90665692899598357308100061 33999634837349383990537523)
  ·
    refine ⟨50999452256024075985806285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33999634837349383990537523 50999452256024075985806285)
    ·
      refine ⟨19124794596009028494677357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50999452256024075985806285 19124794596009028494677357)
      ·
        refine ⟨7171797973503385685504009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19124794596009028494677357 7171797973503385685504009)
        ·
          refine ⟨5378848480127539264128007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7171797973503385685504009 5378848480127539264128007)
          ·
            refine ⟨8068272720191308896192011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5378848480127539264128007 8068272720191308896192011)
            ·
              refine ⟨12102409080286963344288017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8068272720191308896192011 12102409080286963344288017)
              ·
                refine ⟨9076806810215222508216013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12102409080286963344288017 9076806810215222508216013)
                ·
                  refine ⟨3403802553830708440581005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9076806810215222508216013 3403802553830708440581005)
                  ·
                    refine ⟨1276425957686515665217877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3403802553830708440581005 1276425957686515665217877)
                    ·
                      rfl

theorem cell22_3728746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 1, 2, 3, 3].length) (baseStart_3728746 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3728746 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3728746 prefixEnd_3728746 := by exact prefixLift 3728746
  have htrace : WordTrace (prefixWord ++ tailWord_3728746) baseStart_3728746 baseEnd_3728746 := by
    simpa [prefixWord, tailWord_3728746, baseEnd_3728746] using wordTrace_append hprefix tailTrace_3728746
  have hstable : (prefixWord ++ tailWord_3728746).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3728746).length < 2 ^ (prefixWord ++ tailWord_3728746).sum := by decide
  have hdescent : baseEnd_3728746 < baseStart_3728746 := by decide
  rcases family_descends (prefixWord ++ tailWord_3728746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3728817 : List Nat := [1, 2, 2, 4, 1, 1, 1, 3, 1, 6]
def baseStart_3728817 : Nat := 118140960795 + 3728817 * 2 ^ 59
def prefixEnd_3728817 : Nat := 4983230072969 + 3 ^ 40 * 3728817 * 2
def baseEnd_3728817 : Nat := 1276450262437495146692659

theorem tailTrace_3728817 : CollatzResearch.WordTrace tailWord_3728817 prefixEnd_3728817 1276450262437495146692659 := by
  unfold tailWord_3728817
  simp only [CollatzResearch.WordTrace]
  refine ⟨136001128932140315087984705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90667419288093543391989803 136001128932140315087984705)
  ·
    refine ⟨102000846699105236315988529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136001128932140315087984705 102000846699105236315988529)
    ·
      refine ⟨76500635024328927236991397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102000846699105236315988529 76500635024328927236991397)
      ·
        refine ⟨14343869067061673856935887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 76500635024328927236991397 14343869067061673856935887)
        ·
          refine ⟨21515803600592510785403831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14343869067061673856935887 21515803600592510785403831)
          ·
            refine ⟨32273705400888766178105747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21515803600592510785403831 32273705400888766178105747)
            ·
              refine ⟨48410558101333149267158621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32273705400888766178105747 48410558101333149267158621)
              ·
                refine ⟨18153959287999930975184483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48410558101333149267158621 18153959287999930975184483)
                ·
                  refine ⟨27230938931999896462776725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18153959287999930975184483 27230938931999896462776725)
                  ·
                    refine ⟨1276450262437495146692659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27230938931999896462776725 1276450262437495146692659)
                    ·
                      rfl

theorem cell22_3728817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 3, 1, 6].length) (baseStart_3728817 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3728817 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3728817 prefixEnd_3728817 := by exact prefixLift 3728817
  have htrace : WordTrace (prefixWord ++ tailWord_3728817) baseStart_3728817 baseEnd_3728817 := by
    simpa [prefixWord, tailWord_3728817, baseEnd_3728817] using wordTrace_append hprefix tailTrace_3728817
  have hstable : (prefixWord ++ tailWord_3728817).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3728817).length < 2 ^ (prefixWord ++ tailWord_3728817).sum := by decide
  have hdescent : baseEnd_3728817 < baseStart_3728817 := by decide
  rcases family_descends (prefixWord ++ tailWord_3728817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3728821 : List Nat := [1, 3, 3, 2, 2, 1, 3, 3, 4]
def baseStart_3728821 : Nat := 118140960795 + 3728821 * 2 ^ 59
def prefixEnd_3728821 : Nat := 4983230072969 + 3 ^ 40 * 3728821 * 2
def baseEnd_3728821 : Nat := 425483877239746823197549

theorem tailTrace_3728821 : CollatzResearch.WordTrace tailWord_3728821 prefixEnd_3728821 425483877239746823197549 := by
  unfold tailWord_3728821
  simp only [CollatzResearch.WordTrace]
  refine ⟨136001274824125823771130317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90667516549417215847420211 136001274824125823771130317)
  ·
    refine ⟨51000478059047183914173869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136001274824125823771130317 51000478059047183914173869)
    ·
      refine ⟨19125179272142693967815201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51000478059047183914173869 19125179272142693967815201)
      ·
        refine ⟨14343884454107020475861401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19125179272142693967815201 14343884454107020475861401)
        ·
          refine ⟨10757913340580265356896051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14343884454107020475861401 10757913340580265356896051)
          ·
            refine ⟨16136870010870398035344077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10757913340580265356896051 16136870010870398035344077)
            ·
              refine ⟨6051326254076399263254029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16136870010870398035344077 6051326254076399263254029)
              ·
                refine ⟨2269247345278649723720261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6051326254076399263254029 2269247345278649723720261)
                ·
                  refine ⟨425483877239746823197549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2269247345278649723720261 425483877239746823197549)
                  ·
                    rfl

theorem cell22_3728821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 3, 3, 4].length) (baseStart_3728821 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3728821 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3728821 prefixEnd_3728821 := by exact prefixLift 3728821
  have htrace : WordTrace (prefixWord ++ tailWord_3728821) baseStart_3728821 baseEnd_3728821 := by
    simpa [prefixWord, tailWord_3728821, baseEnd_3728821] using wordTrace_append hprefix tailTrace_3728821
  have hstable : (prefixWord ++ tailWord_3728821).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3728821).length < 2 ^ (prefixWord ++ tailWord_3728821).sum := by decide
  have hdescent : baseEnd_3728821 < baseStart_3728821 := by decide
  rcases family_descends (prefixWord ++ tailWord_3728821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3728836 : List Nat := [2, 3, 3, 2, 1, 1, 2, 1, 4, 3]
def baseStart_3728836 : Nat := 118140960795 + 3728836 * 2 ^ 59
def prefixEnd_3728836 : Nat := 4983230072969 + 3 ^ 40 * 3728836 * 2
def baseEnd_3728836 : Nat := 1276456766525785430467601

theorem tailTrace_3728836 : CollatzResearch.WordTrace tailWord_3728836 prefixEnd_3728836 1276456766525785430467601 := by
  unfold tailWord_3728836
  simp only [CollatzResearch.WordTrace]
  refine ⟨68000910959535740666463181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90667881279380987555284241 68000910959535740666463181)
  ·
    refine ⟨25500341609825902749923693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68000910959535740666463181 25500341609825902749923693)
    ·
      refine ⟨9562628103684713531221385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25500341609825902749923693 9562628103684713531221385)
      ·
        refine ⟨7171971077763535148416039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9562628103684713531221385 7171971077763535148416039)
        ·
          refine ⟨10757956616645302722624059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7171971077763535148416039 10757956616645302722624059)
          ·
            refine ⟨16136934924967954083936089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10757956616645302722624059 16136934924967954083936089)
            ·
              refine ⟨12102701193725965562952067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16136934924967954083936089 12102701193725965562952067)
              ·
                refine ⟨18154051790588948344428101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12102701193725965562952067 18154051790588948344428101)
                ·
                  refine ⟨3403884710735427814580269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18154051790588948344428101 3403884710735427814580269)
                  ·
                    refine ⟨1276456766525785430467601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3403884710735427814580269 1276456766525785430467601)
                    ·
                      rfl

theorem cell22_3728836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 2, 1, 4, 3].length) (baseStart_3728836 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3728836 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3728836 prefixEnd_3728836 := by exact prefixLift 3728836
  have htrace : WordTrace (prefixWord ++ tailWord_3728836) baseStart_3728836 baseEnd_3728836 := by
    simpa [prefixWord, tailWord_3728836, baseEnd_3728836] using wordTrace_append hprefix tailTrace_3728836
  have hstable : (prefixWord ++ tailWord_3728836).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3728836).length < 2 ^ (prefixWord ++ tailWord_3728836).sum := by decide
  have hdescent : baseEnd_3728836 < baseStart_3728836 := by decide
  rcases family_descends (prefixWord ++ tailWord_3728836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3728924 : List Nat := [2, 2, 3, 1, 2, 1, 1, 3, 3, 4]
def baseStart_3728924 : Nat := 118140960795 + 3728924 * 2 ^ 59
def prefixEnd_3728924 : Nat := 4983230072969 + 3 ^ 40 * 3728924 * 2
def baseEnd_3728924 : Nat := 1276486890724182534267331

theorem tailTrace_3728924 : CollatzResearch.WordTrace tailWord_3728924 prefixEnd_3728924 1276486890724182534267331 := by
  unfold tailWord_3728924
  simp only [CollatzResearch.WordTrace]
  refine ⟨68002515771376336181064913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90670021028501781574753217 68002515771376336181064913)
  ·
    refine ⟨51001886828532252135798685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68002515771376336181064913 51001886828532252135798685)
    ·
      refine ⟨19125707560699594550924507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51001886828532252135798685 19125707560699594550924507)
      ·
        refine ⟨28688561341049391826386761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19125707560699594550924507 28688561341049391826386761)
        ·
          refine ⟨21516421005787043869790071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28688561341049391826386761 21516421005787043869790071)
          ·
            refine ⟨32274631508680565804685107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21516421005787043869790071 32274631508680565804685107)
            ·
              refine ⟨48411947263020848707027661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32274631508680565804685107 48411947263020848707027661)
              ·
                refine ⟨18154480223632818265135373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48411947263020848707027661 18154480223632818265135373)
                ·
                  refine ⟨6807930083862306849425765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18154480223632818265135373 6807930083862306849425765)
                  ·
                    refine ⟨1276486890724182534267331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6807930083862306849425765 1276486890724182534267331)
                    ·
                      rfl

theorem cell22_3728924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 3, 3, 4].length) (baseStart_3728924 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3728924 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3728924 prefixEnd_3728924 := by exact prefixLift 3728924
  have htrace : WordTrace (prefixWord ++ tailWord_3728924) baseStart_3728924 baseEnd_3728924 := by
    simpa [prefixWord, tailWord_3728924, baseEnd_3728924] using wordTrace_append hprefix tailTrace_3728924
  have hstable : (prefixWord ++ tailWord_3728924).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3728924).length < 2 ^ (prefixWord ++ tailWord_3728924).sum := by decide
  have hdescent : baseEnd_3728924 < baseStart_3728924 := by decide
  rcases family_descends (prefixWord ++ tailWord_3728924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3728956 : List Nat := [2, 2, 2, 2, 4, 1, 2, 1, 6]
def baseStart_3728956 : Nat := 118140960795 + 3728956 * 2 ^ 59
def prefixEnd_3728956 : Nat := 4983230072969 + 3 ^ 40 * 3728956 * 2
def baseEnd_3728956 : Nat := 425499281659381705822411

theorem tailTrace_3728956 : CollatzResearch.WordTrace tailWord_3728956 prefixEnd_3728956 425499281659381705822411 := by
  unfold tailWord_3728956
  simp only [CollatzResearch.WordTrace]
  refine ⟨68003099339318370913647361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90670799119091161218196481 68003099339318370913647361)
  ·
    refine ⟨51002324504488778185235521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68003099339318370913647361 51002324504488778185235521)
    ·
      refine ⟨38251743378366583638926641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51002324504488778185235521 38251743378366583638926641)
      ·
        refine ⟨28688807533774937729194981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38251743378366583638926641 28688807533774937729194981)
        ·
          refine ⟨5379151412582800824224059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28688807533774937729194981 5379151412582800824224059)
          ·
            refine ⟨8068727118874201236336089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5379151412582800824224059 8068727118874201236336089)
            ·
              refine ⟨6051545339155650927252067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8068727118874201236336089 6051545339155650927252067)
              ·
                refine ⟨9077318008733476390878101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6051545339155650927252067 9077318008733476390878101)
                ·
                  refine ⟨425499281659381705822411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9077318008733476390878101 425499281659381705822411)
                  ·
                    rfl

theorem cell22_3728956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 2, 1, 6].length) (baseStart_3728956 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3728956 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3728956 prefixEnd_3728956 := by exact prefixLift 3728956
  have htrace : WordTrace (prefixWord ++ tailWord_3728956) baseStart_3728956 baseEnd_3728956 := by
    simpa [prefixWord, tailWord_3728956, baseEnd_3728956] using wordTrace_append hprefix tailTrace_3728956
  have hstable : (prefixWord ++ tailWord_3728956).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3728956).length < 2 ^ (prefixWord ++ tailWord_3728956).sum := by decide
  have hdescent : baseEnd_3728956 < baseStart_3728956 := by decide
  rcases family_descends (prefixWord ++ tailWord_3728956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3729078 : List Nat := [5, 1, 3, 1, 1, 1, 1, 1, 1, 7]
def baseStart_3729078 : Nat := 118140960795 + 3729078 * 2 ^ 59
def prefixEnd_3729078 : Nat := 4983230072969 + 3 ^ 40 * 3729078 * 2
def baseEnd_3729078 : Nat := 1276539608071377465916859

theorem tailTrace_3729078 : CollatzResearch.WordTrace tailWord_3729078 prefixEnd_3729078 1276539608071377465916859 := by
  unfold tailWord_3729078
  simp only [CollatzResearch.WordTrace]
  refine ⟨8500665524012172291452243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 90673765589463171108823925 8500665524012172291452243)
  ·
    refine ⟨12750998286018258437178365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8500665524012172291452243 12750998286018258437178365)
    ·
      refine ⟨4781624357256846913941887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12750998286018258437178365 4781624357256846913941887)
      ·
        refine ⟨7172436535885270370912831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4781624357256846913941887 7172436535885270370912831)
        ·
          refine ⟨10758654803827905556369247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7172436535885270370912831 10758654803827905556369247)
          ·
            refine ⟨16137982205741858334553871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10758654803827905556369247 16137982205741858334553871)
            ·
              refine ⟨24206973308612787501830807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16137982205741858334553871 24206973308612787501830807)
              ·
                refine ⟨36310459962919181252746211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24206973308612787501830807 36310459962919181252746211)
                ·
                  refine ⟨54465689944378771879119317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36310459962919181252746211 54465689944378771879119317)
                  ·
                    refine ⟨1276539608071377465916859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 54465689944378771879119317 1276539608071377465916859)
                    ·
                      rfl

theorem cell22_3729078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 1, 1, 7].length) (baseStart_3729078 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3729078 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3729078 prefixEnd_3729078 := by exact prefixLift 3729078
  have htrace : WordTrace (prefixWord ++ tailWord_3729078) baseStart_3729078 baseEnd_3729078 := by
    simpa [prefixWord, tailWord_3729078, baseEnd_3729078] using wordTrace_append hprefix tailTrace_3729078
  have hstable : (prefixWord ++ tailWord_3729078).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3729078).length < 2 ^ (prefixWord ++ tailWord_3729078).sum := by decide
  have hdescent : baseEnd_3729078 < baseStart_3729078 := by decide
  rcases family_descends (prefixWord ++ tailWord_3729078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3729119 : List Nat := [1, 1, 2, 3, 2, 2, 11]
def baseStart_3729119 : Nat := 118140960795 + 3729119 * 2 ^ 59
def prefixEnd_3729119 : Nat := 4983230072969 + 3 ^ 40 * 3729119 * 2
def baseEnd_3729119 : Nat := 47279764563306186134879

theorem tailTrace_3729119 : CollatzResearch.WordTrace tailWord_3729119 prefixEnd_3729119 47279764563306186134879 := by
  unfold tailWord_3729119
  simp only [CollatzResearch.WordTrace]
  refine ⟨136012143777046220665478411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90674762518030813776985607 136012143777046220665478411)
  ·
    refine ⟨204018215665569330998217617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136012143777046220665478411 204018215665569330998217617)
    ·
      refine ⟨153013661749176998248663213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 204018215665569330998217617 153013661749176998248663213)
      ·
        refine ⟨57380123155941374343248705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 153013661749176998248663213 57380123155941374343248705)
        ·
          refine ⟨43035092366956030757436529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57380123155941374343248705 43035092366956030757436529)
          ·
            refine ⟨32276319275217023068077397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43035092366956030757436529 32276319275217023068077397)
            ·
              refine ⟨47279764563306186134879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 32276319275217023068077397 47279764563306186134879)
              ·
                rfl

theorem cell22_3729119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 11].length) (baseStart_3729119 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3729119 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3729119 prefixEnd_3729119 := by exact prefixLift 3729119
  have htrace : WordTrace (prefixWord ++ tailWord_3729119) baseStart_3729119 baseEnd_3729119 := by
    simpa [prefixWord, tailWord_3729119, baseEnd_3729119] using wordTrace_append hprefix tailTrace_3729119
  have hstable : (prefixWord ++ tailWord_3729119).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3729119).length < 2 ^ (prefixWord ++ tailWord_3729119).sum := by decide
  have hdescent : baseEnd_3729119 < baseStart_3729119 := by decide
  rcases family_descends (prefixWord ++ tailWord_3729119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3729185 : List Nat := [1, 2, 3, 2, 1, 5, 1, 1, 3, 3]
def baseStart_3729185 : Nat := 118140960795 + 3729185 * 2 ^ 59
def prefixEnd_3729185 : Nat := 4983230072969 + 3 ^ 40 * 3729185 * 2
def baseEnd_3729185 : Nat := 1276576236358064853491531

theorem tailTrace_3729185 : CollatzResearch.WordTrace tailWord_3729185 prefixEnd_3729185 1276576236358064853491531 := by
  unfold tailWord_3729185
  simp only [CollatzResearch.WordTrace]
  refine ⟨136014550994807113937381009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90676367329871409291587339 136014550994807113937381009)
  ·
    refine ⟨102010913246105335453035757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136014550994807113937381009 102010913246105335453035757)
    ·
      refine ⟨38254092467289500794888409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102010913246105335453035757 38254092467289500794888409)
      ·
        refine ⟨28690569350467125596166307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38254092467289500794888409 28690569350467125596166307)
        ·
          refine ⟨43035854025700688394249461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28690569350467125596166307 43035854025700688394249461)
          ·
            refine ⟨4034611314909439536960887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 43035854025700688394249461 4034611314909439536960887)
            ·
              refine ⟨6051916972364159305441331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4034611314909439536960887 6051916972364159305441331)
              ·
                refine ⟨9077875458546238958161997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6051916972364159305441331 9077875458546238958161997)
                ·
                  refine ⟨3404203296954839609310749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9077875458546238958161997 3404203296954839609310749)
                  ·
                    refine ⟨1276576236358064853491531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3404203296954839609310749 1276576236358064853491531)
                    ·
                      rfl

theorem cell22_3729185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 5, 1, 1, 3, 3].length) (baseStart_3729185 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3729185 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3729185 prefixEnd_3729185 := by exact prefixLift 3729185
  have htrace : WordTrace (prefixWord ++ tailWord_3729185) baseStart_3729185 baseEnd_3729185 := by
    simpa [prefixWord, tailWord_3729185, baseEnd_3729185] using wordTrace_append hprefix tailTrace_3729185
  have hstable : (prefixWord ++ tailWord_3729185).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3729185).length < 2 ^ (prefixWord ++ tailWord_3729185).sum := by decide
  have hdescent : baseEnd_3729185 < baseStart_3729185 := by decide
  rcases family_descends (prefixWord ++ tailWord_3729185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3729241 : List Nat := [1, 2, 1, 2, 2, 3, 1, 2, 3, 5]
def baseStart_3729241 : Nat := 118140960795 + 3729241 * 2 ^ 59
def prefixEnd_3729241 : Nat := 4983230072969 + 3 ^ 40 * 3729241 * 2
def baseEnd_3729241 : Nat := 1276595406302499374091359

theorem tailTrace_3729241 : CollatzResearch.WordTrace tailWord_3729241 prefixEnd_3729241 1276595406302499374091359 := by
  unfold tailWord_3729241
  simp only [CollatzResearch.WordTrace]
  refine ⟨136016593482604235501419577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90677728988402823667613051 136016593482604235501419577)
  ·
    refine ⟨102012445111953176626064683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136016593482604235501419577 102012445111953176626064683)
    ·
      refine ⟨153018667667929764939097025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102012445111953176626064683 153018667667929764939097025)
      ·
        refine ⟨114764000750947323704322769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153018667667929764939097025 114764000750947323704322769)
        ·
          refine ⟨86073000563210492778242077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114764000750947323704322769 86073000563210492778242077)
          ·
            refine ⟨32277375211203934791840779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86073000563210492778242077 32277375211203934791840779)
            ·
              refine ⟨48416062816805902187761169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32277375211203934791840779 48416062816805902187761169)
              ·
                refine ⟨36312047112604426640820877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48416062816805902187761169 36312047112604426640820877)
                ·
                  refine ⟨13617017667226659990307829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36312047112604426640820877 13617017667226659990307829)
                  ·
                    refine ⟨1276595406302499374091359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13617017667226659990307829 1276595406302499374091359)
                    ·
                      rfl

theorem cell22_3729241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 2, 3, 5].length) (baseStart_3729241 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3729241 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3729241 prefixEnd_3729241 := by exact prefixLift 3729241
  have htrace : WordTrace (prefixWord ++ tailWord_3729241) baseStart_3729241 baseEnd_3729241 := by
    simpa [prefixWord, tailWord_3729241, baseEnd_3729241] using wordTrace_append hprefix tailTrace_3729241
  have hstable : (prefixWord ++ tailWord_3729241).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3729241).length < 2 ^ (prefixWord ++ tailWord_3729241).sum := by decide
  have hdescent : baseEnd_3729241 < baseStart_3729241 := by decide
  rcases family_descends (prefixWord ++ tailWord_3729241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3729288 : List Nat := [2, 1, 3, 3, 3, 1, 9]
def baseStart_3729288 : Nat := 118140960795 + 3729288 * 2 ^ 59
def prefixEnd_3729288 : Nat := 4983230072969 + 3 ^ 40 * 3729288 * 2
def baseEnd_3729288 : Nat := 47281907235666922895045

theorem tailTrace_3729288 : CollatzResearch.WordTrace tailWord_3729288 prefixEnd_3729288 47281907235666922895045 := by
  unfold tailWord_3729288
  simp only [CollatzResearch.WordTrace]
  refine ⟨68009153856716981264190259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90678871808955975018920345 68009153856716981264190259)
  ·
    refine ⟨102013730785075471896285389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68009153856716981264190259 102013730785075471896285389)
    ·
      refine ⟨38255149044403301961107021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102013730785075471896285389 38255149044403301961107021)
      ·
        refine ⟨14345680891651238235415133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38255149044403301961107021 14345680891651238235415133)
        ·
          refine ⟨5379630334369214338280675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14345680891651238235415133 5379630334369214338280675)
          ·
            refine ⟨8069445501553821507421013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5379630334369214338280675 8069445501553821507421013)
            ·
              refine ⟨47281907235666922895045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8069445501553821507421013 47281907235666922895045)
              ·
                rfl

theorem cell22_3729288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 9].length) (baseStart_3729288 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3729288 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3729288 prefixEnd_3729288 := by exact prefixLift 3729288
  have htrace : WordTrace (prefixWord ++ tailWord_3729288) baseStart_3729288 baseEnd_3729288 := by
    simpa [prefixWord, tailWord_3729288, baseEnd_3729288] using wordTrace_append hprefix tailTrace_3729288
  have hstable : (prefixWord ++ tailWord_3729288).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3729288).length < 2 ^ (prefixWord ++ tailWord_3729288).sum := by decide
  have hdescent : baseEnd_3729288 < baseStart_3729288 := by decide
  rcases family_descends (prefixWord ++ tailWord_3729288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3729333 : List Nat := [1, 3, 3, 2, 1, 2, 1, 2, 7]
def baseStart_3729333 : Nat := 118140960795 + 3729333 * 2 ^ 59
def prefixEnd_3729333 : Nat := 4983230072969 + 3 ^ 40 * 3729333 * 2
def baseEnd_3729333 : Nat := 425542299927547266930359

theorem tailTrace_3729333 : CollatzResearch.WordTrace tailWord_3729333 prefixEnd_3729333 425542299927547266930359 := by
  unfold tailWord_3729333
  simp only [CollatzResearch.WordTrace]
  refine ⟨136019948998270935213768653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90679965998847290142512435 136019948998270935213768653)
  ·
    refine ⟨51007480874351600705163245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136019948998270935213768653 51007480874351600705163245)
    ·
      refine ⟨19127805327881850264436217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51007480874351600705163245 19127805327881850264436217)
      ·
        refine ⟨14345853995911387698327163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19127805327881850264436217 14345853995911387698327163)
        ·
          refine ⟨21518780993867081547490745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14345853995911387698327163 21518780993867081547490745)
          ·
            refine ⟨16139085745400311160618059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21518780993867081547490745 16139085745400311160618059)
            ·
              refine ⟨24208628618100466740927089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16139085745400311160618059 24208628618100466740927089)
              ·
                refine ⟨18156471463575350055695317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24208628618100466740927089 18156471463575350055695317)
                ·
                  refine ⟨425542299927547266930359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18156471463575350055695317 425542299927547266930359)
                  ·
                    rfl

theorem cell22_3729333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 2, 7].length) (baseStart_3729333 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3729333 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3729333 prefixEnd_3729333 := by exact prefixLift 3729333
  have htrace : WordTrace (prefixWord ++ tailWord_3729333) baseStart_3729333 baseEnd_3729333 := by
    simpa [prefixWord, tailWord_3729333, baseEnd_3729333] using wordTrace_append hprefix tailTrace_3729333
  have hstable : (prefixWord ++ tailWord_3729333).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3729333).length < 2 ^ (prefixWord ++ tailWord_3729333).sum := by decide
  have hdescent : baseEnd_3729333 < baseStart_3729333 := by decide
  rcases family_descends (prefixWord ++ tailWord_3729333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3729408 : List Nat := [2, 1, 1, 2, 1, 1, 1, 5, 4, 4]
def baseStart_3729408 : Nat := 118140960795 + 3729408 * 2 ^ 59
def prefixEnd_3729408 : Nat := 4983230072969 + 3 ^ 40 * 3729408 * 2
def baseEnd_3729408 : Nat := 1276652573815366605165847

theorem tailTrace_3729408 : CollatzResearch.WordTrace tailWord_3729408 prefixEnd_3729408 1276652573815366605165847 := by
  unfold tailWord_3729408
  simp only [CollatzResearch.WordTrace]
  refine ⟨68011342236499611511374439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90681789648666148681832585 68011342236499611511374439)
  ·
    refine ⟨102017013354749417267061659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68011342236499611511374439 102017013354749417267061659)
    ·
      refine ⟨153025520032124125900592489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102017013354749417267061659 153025520032124125900592489)
      ·
        refine ⟨114769140024093094425444367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153025520032124125900592489 114769140024093094425444367)
        ·
          refine ⟨172153710036139641638166551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114769140024093094425444367 172153710036139641638166551)
          ·
            refine ⟨258230565054209462457249827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 172153710036139641638166551 258230565054209462457249827)
            ·
              refine ⟨387345847581314193685874741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 258230565054209462457249827 387345847581314193685874741)
              ·
                refine ⟨36313673210748205658050757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 387345847581314193685874741 36313673210748205658050757)
                ·
                  refine ⟨6808813727015288560884517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36313673210748205658050757 6808813727015288560884517)
                  ·
                    refine ⟨1276652573815366605165847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6808813727015288560884517 1276652573815366605165847)
                    ·
                      rfl

theorem cell22_3729408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 5, 4, 4].length) (baseStart_3729408 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3729408 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3729408 prefixEnd_3729408 := by exact prefixLift 3729408
  have htrace : WordTrace (prefixWord ++ tailWord_3729408) baseStart_3729408 baseEnd_3729408 := by
    simpa [prefixWord, tailWord_3729408, baseEnd_3729408] using wordTrace_append hprefix tailTrace_3729408
  have hstable : (prefixWord ++ tailWord_3729408).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3729408).length < 2 ^ (prefixWord ++ tailWord_3729408).sum := by decide
  have hdescent : baseEnd_3729408 < baseStart_3729408 := by decide
  rcases family_descends (prefixWord ++ tailWord_3729408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3729448 : List Nat := [2, 1, 5, 3, 2, 1, 2, 1, 1, 4]
def baseStart_3729448 : Nat := 118140960795 + 3729448 * 2 ^ 59
def prefixEnd_3729448 : Nat := 4983230072969 + 3 ^ 40 * 3729448 * 2
def baseEnd_3729448 : Nat := 1276666266632819834165725

theorem tailTrace_3729448 : CollatzResearch.WordTrace tailWord_3729448 prefixEnd_3729448 1276666266632819834165725 := by
  unfold tailWord_3729448
  simp only [CollatzResearch.WordTrace]
  refine ⟨68012071696427154927102499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90682762261902873236136665 68012071696427154927102499)
  ·
    refine ⟨102018107544640732390653749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68012071696427154927102499 102018107544640732390653749)
    ·
      refine ⟨9564197582310068661623789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 102018107544640732390653749 9564197582310068661623789)
      ·
        refine ⟨3586574093366275748108921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9564197582310068661623789 3586574093366275748108921)
        ·
          refine ⟨2689930570024706811081691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3586574093366275748108921 2689930570024706811081691)
          ·
            refine ⟨4034895855037060216622537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2689930570024706811081691 4034895855037060216622537)
            ·
              refine ⟨3026171891277795162466903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4034895855037060216622537 3026171891277795162466903)
              ·
                refine ⟨4539257836916692743700355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3026171891277795162466903 4539257836916692743700355)
                ·
                  refine ⟨6808886755375039115550533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4539257836916692743700355 6808886755375039115550533)
                  ·
                    refine ⟨1276666266632819834165725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6808886755375039115550533 1276666266632819834165725)
                    ·
                      rfl

theorem cell22_3729448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 2, 1, 2, 1, 1, 4].length) (baseStart_3729448 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3729448 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3729448 prefixEnd_3729448 := by exact prefixLift 3729448
  have htrace : WordTrace (prefixWord ++ tailWord_3729448) baseStart_3729448 baseEnd_3729448 := by
    simpa [prefixWord, tailWord_3729448, baseEnd_3729448] using wordTrace_append hprefix tailTrace_3729448
  have hstable : (prefixWord ++ tailWord_3729448).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3729448).length < 2 ^ (prefixWord ++ tailWord_3729448).sum := by decide
  have hdescent : baseEnd_3729448 < baseStart_3729448 := by decide
  rcases family_descends (prefixWord ++ tailWord_3729448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3729472 : List Nat := [2, 1, 1, 2, 2, 5, 2, 1, 3, 3]
def baseStart_3729472 : Nat := 118140960795 + 3729472 * 2 ^ 59
def prefixEnd_3729472 : Nat := 4983230072969 + 3 ^ 40 * 3729472 * 2
def baseEnd_3729472 : Nat := 1276674482323291771565651

theorem tailTrace_3729472 : CollatzResearch.WordTrace tailWord_3729472 prefixEnd_3729472 1276674482323291771565651 := by
  unfold tailWord_3729472
  simp only [CollatzResearch.WordTrace]
  refine ⟨68012509372383680976539335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90683345829844907968719113 68012509372383680976539335)
  ·
    refine ⟨102018764058575521464809003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68012509372383680976539335 102018764058575521464809003)
    ·
      refine ⟨153028146087863282197213505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102018764058575521464809003 153028146087863282197213505)
      ·
        refine ⟨114771109565897461647910129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153028146087863282197213505 114771109565897461647910129)
        ·
          refine ⟨86078332174423096235932597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114771109565897461647910129 86078332174423096235932597)
          ·
            refine ⟨8069843641352165272118681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 86078332174423096235932597 8069843641352165272118681)
            ·
              refine ⟨6052382731014123954089011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8069843641352165272118681 6052382731014123954089011)
              ·
                refine ⟨9078574096521185931133517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6052382731014123954089011 9078574096521185931133517)
                ·
                  refine ⟨3404465286195444724175069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9078574096521185931133517 3404465286195444724175069)
                  ·
                    refine ⟨1276674482323291771565651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3404465286195444724175069 1276674482323291771565651)
                    ·
                      rfl

theorem cell22_3729472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 2, 1, 3, 3].length) (baseStart_3729472 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3729472 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3729472 prefixEnd_3729472 := by exact prefixLift 3729472
  have htrace : WordTrace (prefixWord ++ tailWord_3729472) baseStart_3729472 baseEnd_3729472 := by
    simpa [prefixWord, tailWord_3729472, baseEnd_3729472] using wordTrace_append hprefix tailTrace_3729472
  have hstable : (prefixWord ++ tailWord_3729472).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3729472).length < 2 ^ (prefixWord ++ tailWord_3729472).sum := by decide
  have hdescent : baseEnd_3729472 < baseStart_3729472 := by decide
  rcases family_descends (prefixWord ++ tailWord_3729472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3729545 : List Nat := [1, 2, 1, 1, 4, 2, 2, 3, 1, 5]
def baseStart_3729545 : Nat := 118140960795 + 3729545 * 2 ^ 59
def prefixEnd_3729545 : Nat := 4983230072969 + 3 ^ 40 * 3729545 * 2
def baseEnd_3729545 : Nat := 1276699471715143914490427

theorem tailTrace_3729545 : CollatzResearch.WordTrace tailWord_3729545 prefixEnd_3729545 1276699471715143914490427 := by
  unfold tailWord_3729545
  simp only [CollatzResearch.WordTrace]
  refine ⟨136027681273502895420486089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90685120849001930280324059 136027681273502895420486089)
  ·
    refine ⟨102020760955127171565364567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136027681273502895420486089 102020760955127171565364567)
    ·
      refine ⟨153031141432690757348046851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102020760955127171565364567 153031141432690757348046851)
      ·
        refine ⟨229546712149036136022070277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153031141432690757348046851 229546712149036136022070277)
        ·
          refine ⟨43040008527944275504138177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 229546712149036136022070277 43040008527944275504138177)
          ·
            refine ⟨32280006395958206628103633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43040008527944275504138177 32280006395958206628103633)
            ·
              refine ⟨24210004796968654971077725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32280006395958206628103633 24210004796968654971077725)
              ·
                refine ⟨9078751798863245614154147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24210004796968654971077725 9078751798863245614154147)
                ·
                  refine ⟨13618127698294868421231221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9078751798863245614154147 13618127698294868421231221)
                  ·
                    refine ⟨1276699471715143914490427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13618127698294868421231221 1276699471715143914490427)
                    ·
                      rfl

theorem cell22_3729545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 3, 1, 5].length) (baseStart_3729545 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3729545 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3729545 prefixEnd_3729545 := by exact prefixLift 3729545
  have htrace : WordTrace (prefixWord ++ tailWord_3729545) baseStart_3729545 baseEnd_3729545 := by
    simpa [prefixWord, tailWord_3729545, baseEnd_3729545] using wordTrace_append hprefix tailTrace_3729545
  have hstable : (prefixWord ++ tailWord_3729545).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3729545).length < 2 ^ (prefixWord ++ tailWord_3729545).sum := by decide
  have hdescent : baseEnd_3729545 < baseStart_3729545 := by decide
  rcases family_descends (prefixWord ++ tailWord_3729545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3729575 : List Nat := [1, 1, 6, 2, 12]
def baseStart_3729575 : Nat := 118140960795 + 3729575 * 2 ^ 59
def prefixEnd_3729575 : Nat := 4983230072969 + 3 ^ 40 * 3729575 * 2
def baseEnd_3729575 : Nat := 5253949552791085745845

theorem tailTrace_3729575 : CollatzResearch.WordTrace tailWord_3729575 prefixEnd_3729575 5253949552791085745845 := by
  unfold tailWord_3729575
  simp only [CollatzResearch.WordTrace]
  refine ⟨136028775463394210544078179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90685850308929473696052119 136028775463394210544078179)
  ·
    refine ⟨204043163195091315816117269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136028775463394210544078179 204043163195091315816117269)
    ·
      refine ⟨9564523274769905428880497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 204043163195091315816117269 9564523274769905428880497)
      ·
        refine ⟨7173392456077429071660373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9564523274769905428880497 7173392456077429071660373)
        ·
          refine ⟨5253949552791085745845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 7173392456077429071660373 5253949552791085745845)
          ·
            rfl

theorem cell22_3729575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 12].length) (baseStart_3729575 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3729575 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3729575 prefixEnd_3729575 := by exact prefixLift 3729575
  have htrace : WordTrace (prefixWord ++ tailWord_3729575) baseStart_3729575 baseEnd_3729575 := by
    simpa [prefixWord, tailWord_3729575, baseEnd_3729575] using wordTrace_append hprefix tailTrace_3729575
  have hstable : (prefixWord ++ tailWord_3729575).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3729575).length < 2 ^ (prefixWord ++ tailWord_3729575).sum := by decide
  have hdescent : baseEnd_3729575 < baseStart_3729575 := by decide
  rcases family_descends (prefixWord ++ tailWord_3729575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3729581 : List Nat := [1, 5, 2, 1, 2, 1, 4, 2, 4]
def baseStart_3729581 : Nat := 118140960795 + 3729581 * 2 ^ 59
def prefixEnd_3729581 : Nat := 4983230072969 + 3 ^ 40 * 3729581 * 2
def baseEnd_3729581 : Nat := 425570598416950606863439

theorem tailTrace_3729581 : CollatzResearch.WordTrace tailWord_3729581 prefixEnd_3729581 425570598416950606863439 := by
  unfold tailWord_3729581
  simp only [CollatzResearch.WordTrace]
  refine ⟨136028994301372473568796597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90685996200914982379197731 136028994301372473568796597)
  ·
    refine ⟨12752718215753669397074681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 136028994301372473568796597 12752718215753669397074681)
    ·
      refine ⟨9564538661815252047806011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12752718215753669397074681 9564538661815252047806011)
      ·
        refine ⟨14346807992722878071709017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9564538661815252047806011 14346807992722878071709017)
        ·
          refine ⟨10760105994542158553781763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14346807992722878071709017 10760105994542158553781763)
          ·
            refine ⟨16140158991813237830672645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10760105994542158553781763 16140158991813237830672645)
            ·
              refine ⟨3026279810964982093251121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16140158991813237830672645 3026279810964982093251121)
              ·
                refine ⟨2269709858223736569938341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3026279810964982093251121 2269709858223736569938341)
                ·
                  refine ⟨425570598416950606863439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2269709858223736569938341 425570598416950606863439)
                  ·
                    rfl

theorem cell22_3729581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 4, 2, 4].length) (baseStart_3729581 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3729581 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3729581 prefixEnd_3729581 := by exact prefixLift 3729581
  have htrace : WordTrace (prefixWord ++ tailWord_3729581) baseStart_3729581 baseEnd_3729581 := by
    simpa [prefixWord, tailWord_3729581, baseEnd_3729581] using wordTrace_append hprefix tailTrace_3729581
  have hstable : (prefixWord ++ tailWord_3729581).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3729581).length < 2 ^ (prefixWord ++ tailWord_3729581).sum := by decide
  have hdescent : baseEnd_3729581 < baseStart_3729581 := by decide
  rcases family_descends (prefixWord ++ tailWord_3729581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3729637 : List Nat := [1, 3, 1, 4, 2, 2, 1, 1, 7]
def baseStart_3729637 : Nat := 118140960795 + 3729637 * 2 ^ 59
def prefixEnd_3729637 : Nat := 4983230072969 + 3 ^ 40 * 3729637 * 2
def baseEnd_3729637 : Nat := 425576988398428780396715

theorem tailTrace_3729637 : CollatzResearch.WordTrace tailWord_3729637 prefixEnd_3729637 425576988398428780396715 := by
  unfold tailWord_3729637
  simp only [CollatzResearch.WordTrace]
  refine ⟨136031036789169595132835165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90687357859446396755223443 136031036789169595132835165)
  ·
    refine ⟨51011638795938598174813187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136031036789169595132835165 51011638795938598174813187)
    ·
      refine ⟨76517458193907897262219781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51011638795938598174813187 76517458193907897262219781)
      ·
        refine ⟨14347023411357730736666209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 76517458193907897262219781 14347023411357730736666209)
        ·
          refine ⟨10760267558518298052499657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14347023411357730736666209 10760267558518298052499657)
          ·
            refine ⟨8070200668888723539374743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10760267558518298052499657 8070200668888723539374743)
            ·
              refine ⟨12105301003333085309062115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8070200668888723539374743 12105301003333085309062115)
              ·
                refine ⟨18157951504999627963593173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12105301003333085309062115 18157951504999627963593173)
                ·
                  refine ⟨425576988398428780396715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18157951504999627963593173 425576988398428780396715)
                  ·
                    rfl

theorem cell22_3729637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 1, 1, 7].length) (baseStart_3729637 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3729637 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3729637 prefixEnd_3729637 := by exact prefixLift 3729637
  have htrace : WordTrace (prefixWord ++ tailWord_3729637) baseStart_3729637 baseEnd_3729637 := by
    simpa [prefixWord, tailWord_3729637, baseEnd_3729637] using wordTrace_append hprefix tailTrace_3729637
  have hstable : (prefixWord ++ tailWord_3729637).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3729637).length < 2 ^ (prefixWord ++ tailWord_3729637).sum := by decide
  have hdescent : baseEnd_3729637 < baseStart_3729637 := by decide
  rcases family_descends (prefixWord ++ tailWord_3729637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3729793 : List Nat := [1, 2, 4, 3, 1, 1, 1, 5, 1, 3]
def baseStart_3729793 : Nat := 118140960795 + 3729793 * 2 ^ 59
def prefixEnd_3729793 : Nat := 4983230072969 + 3 ^ 40 * 3729793 * 2
def baseEnd_3729793 : Nat := 1276784367183353934289667

theorem tailTrace_3729793 : CollatzResearch.WordTrace tailWord_3729793 prefixEnd_3729793 1276784367183353934289667 := by
  unfold tailWord_3729793
  simp only [CollatzResearch.WordTrace]
  refine ⟨136036726576604433775514033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90691151051069622517009355 136036726576604433775514033)
  ·
    refine ⟨102027544932453325331635525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136036726576604433775514033 102027544932453325331635525)
    ·
      refine ⟨19130164674834998499681661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 102027544932453325331635525 19130164674834998499681661)
      ·
        refine ⟨7173811753063124437380623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19130164674834998499681661 7173811753063124437380623)
        ·
          refine ⟨10760717629594686656070935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7173811753063124437380623 10760717629594686656070935)
          ·
            refine ⟨16141076444392029984106403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10760717629594686656070935 16141076444392029984106403)
            ·
              refine ⟨24211614666588044976159605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16141076444392029984106403 24211614666588044976159605)
              ·
                refine ⟨2269838874992629216514963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24211614666588044976159605 2269838874992629216514963)
                ·
                  refine ⟨3404758312488943824772445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2269838874992629216514963 3404758312488943824772445)
                  ·
                    refine ⟨1276784367183353934289667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3404758312488943824772445 1276784367183353934289667)
                    ·
                      rfl

theorem cell22_3729793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 5, 1, 3].length) (baseStart_3729793 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3729793 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3729793 prefixEnd_3729793 := by exact prefixLift 3729793
  have htrace : WordTrace (prefixWord ++ tailWord_3729793) baseStart_3729793 baseEnd_3729793 := by
    simpa [prefixWord, tailWord_3729793, baseEnd_3729793] using wordTrace_append hprefix tailTrace_3729793
  have hstable : (prefixWord ++ tailWord_3729793).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3729793).length < 2 ^ (prefixWord ++ tailWord_3729793).sum := by decide
  have hdescent : baseEnd_3729793 < baseStart_3729793 := by decide
  rcases family_descends (prefixWord ++ tailWord_3729793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3729806 : List Nat := [4, 1, 1, 4, 1, 1, 3, 2, 5]
def baseStart_3729806 : Nat := 118140960795 + 3729806 * 2 ^ 59
def prefixEnd_3729806 : Nat := 4983230072969 + 3 ^ 40 * 3729806 * 2
def baseEnd_3729806 : Nat := 425596272449675411238209

theorem tailTrace_3729806 : CollatzResearch.WordTrace tailWord_3729806 prefixEnd_3729806 425596272449675411238209 := by
  unfold tailWord_3729806
  simp only [CollatzResearch.WordTrace]
  refine ⟨17004650090694667124467159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 90691467150371557997158181 17004650090694667124467159)
  ·
    refine ⟨25506975136042000686700739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17004650090694667124467159 25506975136042000686700739)
    ·
      refine ⟨38260462704063001030051109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25506975136042000686700739 38260462704063001030051109)
      ·
        refine ⟨7173836757011812693134583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38260462704063001030051109 7173836757011812693134583)
        ·
          refine ⟨10760755135517719039701875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7173836757011812693134583 10760755135517719039701875)
          ·
            refine ⟨16141132703276578559552813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10760755135517719039701875 16141132703276578559552813)
            ·
              refine ⟨6052924763728716959832305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16141132703276578559552813 6052924763728716959832305)
              ·
                refine ⟨4539693572796537719874229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6052924763728716959832305 4539693572796537719874229)
                ·
                  refine ⟨425596272449675411238209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4539693572796537719874229 425596272449675411238209)
                  ·
                    rfl

theorem cell22_3729806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 3, 2, 5].length) (baseStart_3729806 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3729806 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3729806 prefixEnd_3729806 := by exact prefixLift 3729806
  have htrace : WordTrace (prefixWord ++ tailWord_3729806) baseStart_3729806 baseEnd_3729806 := by
    simpa [prefixWord, tailWord_3729806, baseEnd_3729806] using wordTrace_append hprefix tailTrace_3729806
  have hstable : (prefixWord ++ tailWord_3729806).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3729806).length < 2 ^ (prefixWord ++ tailWord_3729806).sum := by decide
  have hdescent : baseEnd_3729806 < baseStart_3729806 := by decide
  rcases family_descends (prefixWord ++ tailWord_3729806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3729844 : List Nat := [2, 5, 2, 2, 1, 2, 1, 3, 1, 3]
def baseStart_3729844 : Nat := 118140960795 + 3729844 * 2 ^ 59
def prefixEnd_3729844 : Nat := 4983230072969 + 3 ^ 40 * 3729844 * 2
def baseEnd_3729844 : Nat := 1276801825525606801264511

theorem tailTrace_3729844 : CollatzResearch.WordTrace tailWord_3729844 prefixEnd_3729844 1276801825525606801264511 := by
  unfold tailWord_3729844
  simp only [CollatzResearch.WordTrace]
  refine ⟨68019293349709834742810293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90692391132946446323747057 68019293349709834742810293)
  ·
    refine ⟨6376808751535297007138465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 68019293349709834742810293 6376808751535297007138465)
    ·
      refine ⟨4782606563651472755353849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6376808751535297007138465 4782606563651472755353849)
      ·
        refine ⟨3586954922738604566515387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4782606563651472755353849 3586954922738604566515387)
        ·
          refine ⟨5380432384107906849773081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3586954922738604566515387 5380432384107906849773081)
          ·
            refine ⟨4035324288080930137329811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5380432384107906849773081 4035324288080930137329811)
            ·
              refine ⟨6052986432121395205994717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4035324288080930137329811 6052986432121395205994717)
              ·
                refine ⟨2269869912045523202248019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6052986432121395205994717 2269869912045523202248019)
                ·
                  refine ⟨3404804868068284803372029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2269869912045523202248019 3404804868068284803372029)
                  ·
                    refine ⟨1276801825525606801264511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3404804868068284803372029 1276801825525606801264511)
                    ·
                      rfl

theorem cell22_3729844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 2, 1, 3, 1, 3].length) (baseStart_3729844 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3729844 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3729844 prefixEnd_3729844 := by exact prefixLift 3729844
  have htrace : WordTrace (prefixWord ++ tailWord_3729844) baseStart_3729844 baseEnd_3729844 := by
    simpa [prefixWord, tailWord_3729844, baseEnd_3729844] using wordTrace_append hprefix tailTrace_3729844
  have hstable : (prefixWord ++ tailWord_3729844).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3729844).length < 2 ^ (prefixWord ++ tailWord_3729844).sum := by decide
  have hdescent : baseEnd_3729844 < baseStart_3729844 := by decide
  rcases family_descends (prefixWord ++ tailWord_3729844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3729864 : List Nat := [2, 1, 3, 1, 3, 2, 1, 1, 4, 4]
def baseStart_3729864 : Nat := 118140960795 + 3729864 * 2 ^ 59
def prefixEnd_3729864 : Nat := 4983230072969 + 3 ^ 40 * 3729864 * 2
def baseEnd_3729864 : Nat := 1276808671934333415764449

theorem tailTrace_3729864 : CollatzResearch.WordTrace tailWord_3729864 prefixEnd_3729864 1276808671934333415764449 := by
  unfold tailWord_3729864
  simp only [CollatzResearch.WordTrace]
  refine ⟨68019658079673606450674323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90692877439564808600899097 68019658079673606450674323)
  ·
    refine ⟨102029487119510409676011485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68019658079673606450674323 102029487119510409676011485)
    ·
      refine ⟨38261057669816403628504307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102029487119510409676011485 38261057669816403628504307)
      ·
        refine ⟨57391586504724605442756461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38261057669816403628504307 57391586504724605442756461)
        ·
          refine ⟨21521844939271727041033673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57391586504724605442756461 21521844939271727041033673)
          ·
            refine ⟨16141383704453795280775255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21521844939271727041033673 16141383704453795280775255)
            ·
              refine ⟨24212075556680692921162883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16141383704453795280775255 24212075556680692921162883)
              ·
                refine ⟨36318113335021039381744325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24212075556680692921162883 36318113335021039381744325)
                ·
                  refine ⟨6809646250316444884077061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36318113335021039381744325 6809646250316444884077061)
                  ·
                    refine ⟨1276808671934333415764449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6809646250316444884077061 1276808671934333415764449)
                    ·
                      rfl

theorem cell22_3729864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 1, 4, 4].length) (baseStart_3729864 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3729864 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3729864 prefixEnd_3729864 := by exact prefixLift 3729864
  have htrace : WordTrace (prefixWord ++ tailWord_3729864) baseStart_3729864 baseEnd_3729864 := by
    simpa [prefixWord, tailWord_3729864, baseEnd_3729864] using wordTrace_append hprefix tailTrace_3729864
  have hstable : (prefixWord ++ tailWord_3729864).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3729864).length < 2 ^ (prefixWord ++ tailWord_3729864).sum := by decide
  have hdescent : baseEnd_3729864 < baseStart_3729864 := by decide
  rcases family_descends (prefixWord ++ tailWord_3729864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3729866 : List Nat := [3, 1, 2, 1, 2, 2, 2, 4, 2, 3]
def baseStart_3729866 : Nat := 118140960795 + 3729866 * 2 ^ 59
def prefixEnd_3729866 : Nat := 4983230072969 + 3 ^ 40 * 3729866 * 2
def baseEnd_3729866 : Nat := 1276809356575206077214443

theorem tailTrace_3729866 : CollatzResearch.WordTrace tailWord_3729866 prefixEnd_3729866 1276809356575206077214443 := by
  unfold tailWord_3729866
  simp only [CollatzResearch.WordTrace]
  refine ⟨34009847276334991810730363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90692926070226644828614301 34009847276334991810730363)
  ·
    refine ⟨51014770914502487716095545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34009847276334991810730363 51014770914502487716095545)
    ·
      refine ⟨38261078185876865787071659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51014770914502487716095545 38261078185876865787071659)
      ·
        refine ⟨57391617278815298680607489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38261078185876865787071659 57391617278815298680607489)
        ·
          refine ⟨43043712959111474010455617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57391617278815298680607489 43043712959111474010455617)
          ·
            refine ⟨32282784719333605507841713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43043712959111474010455617 32282784719333605507841713)
            ·
              refine ⟨24212088539500204130881285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32282784719333605507841713 24212088539500204130881285)
              ·
                refine ⟨4539766601156288274540241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24212088539500204130881285 4539766601156288274540241)
                ·
                  refine ⟨3404824950867216205905181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4539766601156288274540241 3404824950867216205905181)
                  ·
                    refine ⟨1276809356575206077214443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3404824950867216205905181 1276809356575206077214443)
                    ·
                      rfl

theorem cell22_3729866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 4, 2, 3].length) (baseStart_3729866 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3729866 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3729866 prefixEnd_3729866 := by exact prefixLift 3729866
  have htrace : WordTrace (prefixWord ++ tailWord_3729866) baseStart_3729866 baseEnd_3729866 := by
    simpa [prefixWord, tailWord_3729866, baseEnd_3729866] using wordTrace_append hprefix tailTrace_3729866
  have hstable : (prefixWord ++ tailWord_3729866).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3729866).length < 2 ^ (prefixWord ++ tailWord_3729866).sum := by decide
  have hdescent : baseEnd_3729866 < baseStart_3729866 := by decide
  rcases family_descends (prefixWord ++ tailWord_3729866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3729868 : List Nat := [2, 2, 1, 4, 4, 1, 1, 1, 6]
def baseStart_3729868 : Nat := 118140960795 + 3729868 * 2 ^ 59
def prefixEnd_3729868 : Nat := 4983230072969 + 3 ^ 40 * 3729868 * 2
def baseEnd_3729868 : Nat := 425603347072026246221479

theorem tailTrace_3729868 : CollatzResearch.WordTrace tailWord_3729868 prefixEnd_3729868 425603347072026246221479 := by
  unfold tailWord_3729868
  simp only [CollatzResearch.WordTrace]
  refine ⟨68019731025666360792247129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90692974700888481056329505 68019731025666360792247129)
  ·
    refine ⟨51014798269249770594185347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68019731025666360792247129 51014798269249770594185347)
    ·
      refine ⟨76522197403874655891278021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51014798269249770594185347 76522197403874655891278021)
      ·
        refine ⟨14347912013226497979614629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 76522197403874655891278021 14347912013226497979614629)
        ·
          refine ⟨2690233502479968371177743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14347912013226497979614629 2690233502479968371177743)
          ·
            refine ⟨4035350253719952556766615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2690233502479968371177743 4035350253719952556766615)
            ·
              refine ⟨6053025380579928835149923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4035350253719952556766615 6053025380579928835149923)
              ·
                refine ⟨9079538070869893252724885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6053025380579928835149923 9079538070869893252724885)
                ·
                  refine ⟨425603347072026246221479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9079538070869893252724885 425603347072026246221479)
                  ·
                    rfl

theorem cell22_3729868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 4, 1, 1, 1, 6].length) (baseStart_3729868 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3729868 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3729868 prefixEnd_3729868 := by exact prefixLift 3729868
  have htrace : WordTrace (prefixWord ++ tailWord_3729868) baseStart_3729868 baseEnd_3729868 := by
    simpa [prefixWord, tailWord_3729868, baseEnd_3729868] using wordTrace_append hprefix tailTrace_3729868
  have hstable : (prefixWord ++ tailWord_3729868).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3729868).length < 2 ^ (prefixWord ++ tailWord_3729868).sum := by decide
  have hdescent : baseEnd_3729868 < baseStart_3729868 := by decide
  rcases family_descends (prefixWord ++ tailWord_3729868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3729939 : List Nat := [1, 1, 1, 2, 1, 5, 3, 1, 2, 5]
def baseStart_3729939 : Nat := 118140960795 + 3729939 * 2 ^ 59
def prefixEnd_3729939 : Nat := 4983230072969 + 3 ^ 40 * 3729939 * 2
def baseEnd_3729939 : Nat := 1276834345967058220139219

theorem tailTrace_3729939 : CollatzResearch.WordTrace tailWord_3729939 prefixEnd_3729939 1276834345967058220139219 := by
  unfold tailWord_3729939
  simp only [CollatzResearch.WordTrace]
  refine ⟨136042051634075500710328871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90694701089383667140219247 136042051634075500710328871)
  ·
    refine ⟨204063077451113251065493307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136042051634075500710328871 204063077451113251065493307)
    ·
      refine ⟨306094616176669876598239961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204063077451113251065493307 306094616176669876598239961)
      ·
        refine ⟨229570962132502407448679971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 306094616176669876598239961 229570962132502407448679971)
        ·
          refine ⟨344356443198753611173019957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 229570962132502407448679971 344356443198753611173019957)
          ·
            refine ⟨32283416549883151047470621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 344356443198753611173019957 32283416549883151047470621)
            ·
              refine ⟨12106281206206181642801483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32283416549883151047470621 12106281206206181642801483)
              ·
                refine ⟨18159421809309272464202225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12106281206206181642801483 18159421809309272464202225)
                ·
                  refine ⟨13619566356981954348151669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18159421809309272464202225 13619566356981954348151669)
                  ·
                    refine ⟨1276834345967058220139219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13619566356981954348151669 1276834345967058220139219)
                    ·
                      rfl

theorem cell22_3729939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 3, 1, 2, 5].length) (baseStart_3729939 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3729939 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3729939 prefixEnd_3729939 := by exact prefixLift 3729939
  have htrace : WordTrace (prefixWord ++ tailWord_3729939) baseStart_3729939 baseEnd_3729939 := by
    simpa [prefixWord, tailWord_3729939, baseEnd_3729939] using wordTrace_append hprefix tailTrace_3729939
  have hstable : (prefixWord ++ tailWord_3729939).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3729939).length < 2 ^ (prefixWord ++ tailWord_3729939).sum := by decide
  have hdescent : baseEnd_3729939 < baseStart_3729939 := by decide
  rcases family_descends (prefixWord ++ tailWord_3729939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3729971 : List Nat := [1, 1, 1, 2, 4, 2, 3, 3, 1, 4]
def baseStart_3729971 : Nat := 118140960795 + 3729971 * 2 ^ 59
def prefixEnd_3729971 : Nat := 4983230072969 + 3 ^ 40 * 3729971 * 2
def baseEnd_3729971 : Nat := 1276845300221020803339121

theorem tailTrace_3729971 : CollatzResearch.WordTrace tailWord_3729971 prefixEnd_3729971 1276845300221020803339121 := by
  unfold tailWord_3729971
  simp only [CollatzResearch.WordTrace]
  refine ⟨136043218769959570175493767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90695479179973046783662511 136043218769959570175493767)
  ·
    refine ⟨204064828154939355263240651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136043218769959570175493767 204064828154939355263240651)
    ·
      refine ⟨306097242232409032894860977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204064828154939355263240651 306097242232409032894860977)
      ·
        refine ⟨229572931674306774671145733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 306097242232409032894860977 229572931674306774671145733)
        ·
          refine ⟨43044924688932520250839825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 229572931674306774671145733 43044924688932520250839825)
          ·
            refine ⟨32283693516699390188129869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43044924688932520250839825 32283693516699390188129869)
            ·
              refine ⟨12106385068762271320548701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32283693516699390188129869 12106385068762271320548701)
              ·
                refine ⟨4539894400785851745205763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12106385068762271320548701 4539894400785851745205763)
                ·
                  refine ⟨6809841601178777617808645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4539894400785851745205763 6809841601178777617808645)
                  ·
                    refine ⟨1276845300221020803339121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6809841601178777617808645 1276845300221020803339121)
                    ·
                      rfl

theorem cell22_3729971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 3, 3, 1, 4].length) (baseStart_3729971 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3729971 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3729971 prefixEnd_3729971 := by exact prefixLift 3729971
  have htrace : WordTrace (prefixWord ++ tailWord_3729971) baseStart_3729971 baseEnd_3729971 := by
    simpa [prefixWord, tailWord_3729971, baseEnd_3729971] using wordTrace_append hprefix tailTrace_3729971
  have hstable : (prefixWord ++ tailWord_3729971).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3729971).length < 2 ^ (prefixWord ++ tailWord_3729971).sum := by decide
  have hdescent : baseEnd_3729971 < baseStart_3729971 := by decide
  rcases family_descends (prefixWord ++ tailWord_3729971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3729984 : List Nat := [2, 1, 1, 2, 2, 2, 2, 2, 3, 5]
def baseStart_3729984 : Nat := 118140960795 + 3729984 * 2 ^ 59
def prefixEnd_3729984 : Nat := 4983230072969 + 3 ^ 40 * 3729984 * 2
def baseEnd_3729984 : Nat := 1276849750386693102764081

theorem tailTrace_3729984 : CollatzResearch.WordTrace tailWord_3729984 prefixEnd_3729984 1276849750386693102764081 := by
  unfold tailWord_3729984
  simp only [CollatzResearch.WordTrace]
  refine ⟨68021846459456236697858503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90695795279274982263811337 68021846459456236697858503)
  ·
    refine ⟨102032769689184355046787755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68021846459456236697858503 102032769689184355046787755)
    ·
      refine ⟨153049154533776532570181633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102032769689184355046787755 153049154533776532570181633)
      ·
        refine ⟨114786865900332399427636225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153049154533776532570181633 114786865900332399427636225)
        ·
          refine ⟨86090149425249299570727169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114786865900332399427636225 86090149425249299570727169)
          ·
            refine ⟨64567612068936974678045377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86090149425249299570727169 64567612068936974678045377)
            ·
              refine ⟨48425709051702731008534033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64567612068936974678045377 48425709051702731008534033)
              ·
                refine ⟨36319281788777048256400525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48425709051702731008534033 36319281788777048256400525)
                ·
                  refine ⟨13619730670791393096150197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36319281788777048256400525 13619730670791393096150197)
                  ·
                    refine ⟨1276849750386693102764081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13619730670791393096150197 1276849750386693102764081)
                    ·
                      rfl

theorem cell22_3729984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 2, 3, 5].length) (baseStart_3729984 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3729984 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3729984 prefixEnd_3729984 := by exact prefixLift 3729984
  have htrace : WordTrace (prefixWord ++ tailWord_3729984) baseStart_3729984 baseEnd_3729984 := by
    simpa [prefixWord, tailWord_3729984, baseEnd_3729984] using wordTrace_append hprefix tailTrace_3729984
  have hstable : (prefixWord ++ tailWord_3729984).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3729984).length < 2 ^ (prefixWord ++ tailWord_3729984).sum := by decide
  have hdescent : baseEnd_3729984 < baseStart_3729984 := by decide
  rcases family_descends (prefixWord ++ tailWord_3729984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3729999 : List Nat := [1, 1, 2, 1, 1, 2, 5, 2, 1, 6]
def baseStart_3729999 : Nat := 118140960795 + 3729999 * 2 ^ 59
def prefixEnd_3729999 : Nat := 4983230072969 + 3 ^ 40 * 3729999 * 2
def baseEnd_3729999 : Nat := 1276854885193238063639035

theorem tailTrace_3729999 : CollatzResearch.WordTrace tailWord_3729999 prefixEnd_3729999 1276854885193238063639035 := by
  unfold tailWord_3729999
  simp only [CollatzResearch.WordTrace]
  refine ⟨136044240013858130957513051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90696160009238753971675367 136044240013858130957513051)
  ·
    refine ⟨204066360020787196436269577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136044240013858130957513051 204066360020787196436269577)
    ·
      refine ⟨153049770015590397327202183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 204066360020787196436269577 153049770015590397327202183)
      ·
        refine ⟨229574655023385595990803275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153049770015590397327202183 229574655023385595990803275)
        ·
          refine ⟨344361982535078393986204913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 229574655023385595990803275 344361982535078393986204913)
          ·
            refine ⟨258271486901308795489653685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 344361982535078393986204913 258271486901308795489653685)
            ·
              refine ⟨24212951896997699577155033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 258271486901308795489653685 24212951896997699577155033)
              ·
                refine ⟨18159713922748274682866275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24212951896997699577155033 18159713922748274682866275)
                ·
                  refine ⟨27239570884122412024299413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18159713922748274682866275 27239570884122412024299413)
                  ·
                    refine ⟨1276854885193238063639035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27239570884122412024299413 1276854885193238063639035)
                    ·
                      rfl

theorem cell22_3729999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 2, 1, 6].length) (baseStart_3729999 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3729999 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3729999 prefixEnd_3729999 := by exact prefixLift 3729999
  have htrace : WordTrace (prefixWord ++ tailWord_3729999) baseStart_3729999 baseEnd_3729999 := by
    simpa [prefixWord, tailWord_3729999, baseEnd_3729999] using wordTrace_append hprefix tailTrace_3729999
  have hstable : (prefixWord ++ tailWord_3729999).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3729999).length < 2 ^ (prefixWord ++ tailWord_3729999).sum := by decide
  have hdescent : baseEnd_3729999 < baseStart_3729999 := by decide
  rcases family_descends (prefixWord ++ tailWord_3729999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3730001 : List Nat := [1, 2, 2, 1, 3, 3, 3, 1, 1, 5]
def baseStart_3730001 : Nat := 118140960795 + 3730001 * 2 ^ 59
def prefixEnd_3730001 : Nat := 4983230072969 + 3 ^ 40 * 3730001 * 2
def baseEnd_3730001 : Nat := 1276855569834110725089029

theorem tailTrace_3730001 : CollatzResearch.WordTrace tailWord_3730001 prefixEnd_3730001 1276855569834110725089029 := by
  unfold tailWord_3730001
  simp only [CollatzResearch.WordTrace]
  refine ⟨136044312959850885299085857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90696208639900590199390571 136044312959850885299085857)
  ·
    refine ⟨102033234719888163974314393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136044312959850885299085857 102033234719888163974314393)
    ·
      refine ⟨76524926039916122980735795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102033234719888163974314393 76524926039916122980735795)
      ·
        refine ⟨114787389059874184471103693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76524926039916122980735795 114787389059874184471103693)
        ·
          refine ⟨43045270897452819176663885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 114787389059874184471103693 43045270897452819176663885)
          ·
            refine ⟨16141976586544807191248957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43045270897452819176663885 16141976586544807191248957)
            ·
              refine ⟨6053241219954302696718359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16141976586544807191248957 6053241219954302696718359)
              ·
                refine ⟨9079861829931454045077539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6053241219954302696718359 9079861829931454045077539)
                ·
                  refine ⟨13619792744897181067616309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9079861829931454045077539 13619792744897181067616309)
                  ·
                    refine ⟨1276855569834110725089029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13619792744897181067616309 1276855569834110725089029)
                    ·
                      rfl

theorem cell22_3730001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 3, 1, 1, 5].length) (baseStart_3730001 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3730001 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3730001 prefixEnd_3730001 := by exact prefixLift 3730001
  have htrace : WordTrace (prefixWord ++ tailWord_3730001) baseStart_3730001 baseEnd_3730001 := by
    simpa [prefixWord, tailWord_3730001, baseEnd_3730001] using wordTrace_append hprefix tailTrace_3730001
  have hstable : (prefixWord ++ tailWord_3730001).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3730001).length < 2 ^ (prefixWord ++ tailWord_3730001).sum := by decide
  have hdescent : baseEnd_3730001 < baseStart_3730001 := by decide
  rcases family_descends (prefixWord ++ tailWord_3730001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3730037 : List Nat := [1, 3, 4, 2, 2, 1, 3, 2, 4]
def baseStart_3730037 : Nat := 118140960795 + 3730037 * 2 ^ 59
def prefixEnd_3730037 : Nat := 4983230072969 + 3 ^ 40 * 3730037 * 2
def baseEnd_3730037 : Nat := 425622631123272877062973

theorem tailTrace_3730037 : CollatzResearch.WordTrace tailWord_3730037 prefixEnd_3730037 425622631123272877062973 := by
  unfold tailWord_3730037
  simp only [CollatzResearch.WordTrace]
  refine ⟨136045625987720463447396365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90697083991813642298264243 136045625987720463447396365)
  ·
    refine ⟨51017109745395173792773637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136045625987720463447396365 51017109745395173792773637)
    ·
      refine ⟨9565708077261595086145057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51017109745395173792773637 9565708077261595086145057)
      ·
        refine ⟨7174281057946196314608793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9565708077261595086145057 7174281057946196314608793)
        ·
          refine ⟨5380710793459647235956595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7174281057946196314608793 5380710793459647235956595)
          ·
            refine ⟨8071066190189470853934893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5380710793459647235956595 8071066190189470853934893)
            ·
              refine ⟨3026649821321051570225585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8071066190189470853934893 3026649821321051570225585)
              ·
                refine ⟨2269987365990788677669189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3026649821321051570225585 2269987365990788677669189)
                ·
                  refine ⟨425622631123272877062973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2269987365990788677669189 425622631123272877062973)
                  ·
                    rfl

theorem cell22_3730037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 3, 2, 4].length) (baseStart_3730037 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3730037 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3730037 prefixEnd_3730037 := by exact prefixLift 3730037
  have htrace : WordTrace (prefixWord ++ tailWord_3730037) baseStart_3730037 baseEnd_3730037 := by
    simpa [prefixWord, tailWord_3730037, baseEnd_3730037] using wordTrace_append hprefix tailTrace_3730037
  have hstable : (prefixWord ++ tailWord_3730037).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3730037).length < 2 ^ (prefixWord ++ tailWord_3730037).sum := by decide
  have hdescent : baseEnd_3730037 < baseStart_3730037 := by decide
  rcases family_descends (prefixWord ++ tailWord_3730037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3730052 : List Nat := [2, 3, 2, 1, 3, 3, 2, 1, 2, 3]
def baseStart_3730052 : Nat := 118140960795 + 3730052 * 2 ^ 59
def prefixEnd_3730052 : Nat := 4983230072969 + 3 ^ 40 * 3730052 * 2
def baseEnd_3730052 : Nat := 1276873028176363592063873

theorem tailTrace_3730052 : CollatzResearch.WordTrace tailWord_3730052 prefixEnd_3730052 1276873028176363592063873 := by
  unfold tailWord_3730052
  simp only [CollatzResearch.WordTrace]
  refine ⟨68023086541333060504596205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90697448721777414006128273 68023086541333060504596205)
  ·
    refine ⟨25508657452999897689223577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68023086541333060504596205 25508657452999897689223577)
    ·
      refine ⟨19131493089749923266917683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25508657452999897689223577 19131493089749923266917683)
      ·
        refine ⟨28697239634624884900376525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19131493089749923266917683 28697239634624884900376525)
        ·
          refine ⟨10761464862984331837641197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28697239634624884900376525 10761464862984331837641197)
          ·
            refine ⟨4035549323619124439115449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10761464862984331837641197 4035549323619124439115449)
            ·
              refine ⟨3026661992714343329336587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4035549323619124439115449 3026661992714343329336587)
              ·
                refine ⟨4539992989071514994004881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3026661992714343329336587 4539992989071514994004881)
                ·
                  refine ⟨3404994741803636245503661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4539992989071514994004881 3404994741803636245503661)
                  ·
                    refine ⟨1276873028176363592063873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3404994741803636245503661 1276873028176363592063873)
                    ·
                      rfl

theorem cell22_3730052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 3, 2, 1, 2, 3].length) (baseStart_3730052 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3730052 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3730052 prefixEnd_3730052 := by exact prefixLift 3730052
  have htrace : WordTrace (prefixWord ++ tailWord_3730052) baseStart_3730052 baseEnd_3730052 := by
    simpa [prefixWord, tailWord_3730052, baseEnd_3730052] using wordTrace_append hprefix tailTrace_3730052
  have hstable : (prefixWord ++ tailWord_3730052).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3730052).length < 2 ^ (prefixWord ++ tailWord_3730052).sum := by decide
  have hdescent : baseEnd_3730052 < baseStart_3730052 := by decide
  rcases family_descends (prefixWord ++ tailWord_3730052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3730059 : List Nat := [1, 1, 1, 1, 4, 1, 2, 2, 9]
def baseStart_3730059 : Nat := 118140960795 + 3730059 * 2 ^ 59
def prefixEnd_3730059 : Nat := 4983230072969 + 3 ^ 40 * 3730059 * 2
def baseEnd_3730059 : Nat := 425625141473139302379617

theorem tailTrace_3730059 : CollatzResearch.WordTrace tailWord_3730059 prefixEnd_3730059 425625141473139302379617 := by
  unfold tailWord_3730059
  simp only [CollatzResearch.WordTrace]
  refine ⟨136046428393640761204697231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90697618929093840803131487 136046428393640761204697231)
  ·
    refine ⟨204069642590461141807045847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136046428393640761204697231 204069642590461141807045847)
    ·
      refine ⟨306104463885691712710568771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204069642590461141807045847 306104463885691712710568771)
      ·
        refine ⟨459156695828537569065853157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 306104463885691712710568771 459156695828537569065853157)
        ·
          refine ⟨86091880467850794199847467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 459156695828537569065853157 86091880467850794199847467)
          ·
            refine ⟨129137820701776191299771201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86091880467850794199847467 129137820701776191299771201)
            ·
              refine ⟨96853365526332143474828401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 129137820701776191299771201 96853365526332143474828401)
              ·
                refine ⟨72640024144749107606121301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 96853365526332143474828401 72640024144749107606121301)
                ·
                  refine ⟨425625141473139302379617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 72640024144749107606121301 425625141473139302379617)
                  ·
                    rfl

theorem cell22_3730059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 2, 9].length) (baseStart_3730059 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3730059 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3730059 prefixEnd_3730059 := by exact prefixLift 3730059
  have htrace : WordTrace (prefixWord ++ tailWord_3730059) baseStart_3730059 baseEnd_3730059 := by
    simpa [prefixWord, tailWord_3730059, baseEnd_3730059] using wordTrace_append hprefix tailTrace_3730059
  have hstable : (prefixWord ++ tailWord_3730059).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3730059).length < 2 ^ (prefixWord ++ tailWord_3730059).sum := by decide
  have hdescent : baseEnd_3730059 < baseStart_3730059 := by decide
  rcases family_descends (prefixWord ++ tailWord_3730059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3730093 : List Nat := [1, 5, 2, 1, 1, 2, 1, 4, 5]
def baseStart_3730093 : Nat := 118140960795 + 3730093 * 2 ^ 59
def prefixEnd_3730093 : Nat := 4983230072969 + 3 ^ 40 * 3730093 * 2
def baseEnd_3730093 : Nat := 425629021104751050596249

theorem tailTrace_3730093 : CollatzResearch.WordTrace tailWord_3730093 prefixEnd_3730093 425629021104751050596249 := by
  unfold tailWord_3730093
  simp only [CollatzResearch.WordTrace]
  refine ⟨136047668475517585011434933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90698445650345056674289955 136047668475517585011434933)
  ·
    refine ⟨12754468919579773594822025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 136047668475517585011434933 12754468919579773594822025)
    ·
      refine ⟨9565851689684830196116519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12754468919579773594822025 9565851689684830196116519)
      ·
        refine ⟨14348777534527245294174779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9565851689684830196116519 14348777534527245294174779)
        ·
          refine ⟨21523166301790867941262169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14348777534527245294174779 21523166301790867941262169)
          ·
            refine ⟨16142374726343150955946627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21523166301790867941262169 16142374726343150955946627)
            ·
              refine ⟨24213562089514726433919941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16142374726343150955946627 24213562089514726433919941)
              ·
                refine ⟨4540042891784011206359989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24213562089514726433919941 4540042891784011206359989)
                ·
                  refine ⟨425629021104751050596249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4540042891784011206359989 425629021104751050596249)
                  ·
                    rfl

theorem cell22_3730093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 4, 5].length) (baseStart_3730093 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3730093 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3730093 prefixEnd_3730093 := by exact prefixLift 3730093
  have htrace : WordTrace (prefixWord ++ tailWord_3730093) baseStart_3730093 baseEnd_3730093 := by
    simpa [prefixWord, tailWord_3730093, baseEnd_3730093] using wordTrace_append hprefix tailTrace_3730093
  have hstable : (prefixWord ++ tailWord_3730093).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3730093).length < 2 ^ (prefixWord ++ tailWord_3730093).sum := by decide
  have hdescent : baseEnd_3730093 < baseStart_3730093 := by decide
  rcases family_descends (prefixWord ++ tailWord_3730093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3730106 : List Nat := [3, 1, 1, 1, 2, 3, 1, 1, 5, 4]
def baseStart_3730106 : Nat := 118140960795 + 3730106 * 2 ^ 59
def prefixEnd_3730106 : Nat := 4983230072969 + 3 ^ 40 * 3730106 * 2
def baseEnd_3730106 : Nat := 1276891513479925451213707

theorem tailTrace_3730106 : CollatzResearch.WordTrace tailWord_3730106 prefixEnd_3730106 1276891513479925451213707 := by
  unfold tailWord_3730106
  simp only [CollatzResearch.WordTrace]
  refine ⟨34012035656117622057914543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90698761749646992154438781 34012035656117622057914543)
  ·
    refine ⟨51018053484176433086871815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34012035656117622057914543 51018053484176433086871815)
    ·
      refine ⟨76527080226264649630307723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51018053484176433086871815 76527080226264649630307723)
      ·
        refine ⟨114790620339396974445461585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76527080226264649630307723 114790620339396974445461585)
        ·
          refine ⟨86092965254547730834096189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114790620339396974445461585 86092965254547730834096189)
          ·
            refine ⟨32284861970455399062786071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86092965254547730834096189 32284861970455399062786071)
            ·
              refine ⟨48427292955683098594179107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32284861970455399062786071 48427292955683098594179107)
              ·
                refine ⟨72640939433524647891268661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48427292955683098594179107 72640939433524647891268661)
                ·
                  refine ⟨6810088071892935739806437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 72640939433524647891268661 6810088071892935739806437)
                  ·
                    refine ⟨1276891513479925451213707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6810088071892935739806437 1276891513479925451213707)
                    ·
                      rfl

theorem cell22_3730106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 1, 5, 4].length) (baseStart_3730106 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3730106 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3730106 prefixEnd_3730106 := by exact prefixLift 3730106
  have htrace : WordTrace (prefixWord ++ tailWord_3730106) baseStart_3730106 baseEnd_3730106 := by
    simpa [prefixWord, tailWord_3730106, baseEnd_3730106] using wordTrace_append hprefix tailTrace_3730106
  have hstable : (prefixWord ++ tailWord_3730106).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3730106).length < 2 ^ (prefixWord ++ tailWord_3730106).sum := by decide
  have hdescent : baseEnd_3730106 < baseStart_3730106 := by decide
  rcases family_descends (prefixWord ++ tailWord_3730106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3730183 : List Nat := [1, 1, 4, 4, 1, 2, 1, 8]
def baseStart_3730183 : Nat := 118140960795 + 3730183 * 2 ^ 59
def prefixEnd_3730183 : Nat := 4983230072969 + 3 ^ 40 * 3730183 * 2
def baseEnd_3730183 : Nat := 141879763572613657448719

theorem tailTrace_3730183 : CollatzResearch.WordTrace tailWord_3730183 prefixEnd_3730183 141879763572613657448719 := by
  unfold tailWord_3730183
  simp only [CollatzResearch.WordTrace]
  refine ⟨136050951045191530382211203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90700634030127686921474135 136050951045191530382211203)
  ·
    refine ⟨204076426567787295573316805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136050951045191530382211203 204076426567787295573316805)
    ·
      refine ⟨38264329981460117919996901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 204076426567787295573316805 38264329981460117919996901)
      ·
        refine ⟨7174561871523772109999419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38264329981460117919996901 7174561871523772109999419)
        ·
          refine ⟨10761842807285658164999129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7174561871523772109999419 10761842807285658164999129)
          ·
            refine ⟨8071382105464243623749347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10761842807285658164999129 8071382105464243623749347)
            ·
              refine ⟨12107073158196365435624021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8071382105464243623749347 12107073158196365435624021)
              ·
                refine ⟨141879763572613657448719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12107073158196365435624021 141879763572613657448719)
                ·
                  rfl

theorem cell22_3730183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 1, 8].length) (baseStart_3730183 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3730183 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3730183 prefixEnd_3730183 := by exact prefixLift 3730183
  have htrace : WordTrace (prefixWord ++ tailWord_3730183) baseStart_3730183 baseEnd_3730183 := by
    simpa [prefixWord, tailWord_3730183, baseEnd_3730183] using wordTrace_append hprefix tailTrace_3730183
  have hstable : (prefixWord ++ tailWord_3730183).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3730183).length < 2 ^ (prefixWord ++ tailWord_3730183).sum := by decide
  have hdescent : baseEnd_3730183 < baseStart_3730183 := by decide
  rcases family_descends (prefixWord ++ tailWord_3730183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3730288 : List Nat := [2, 1, 1, 1, 4, 1, 3, 3, 1, 5]
def baseStart_3730288 : Nat := 118140960795 + 3730288 * 2 ^ 59
def prefixEnd_3730288 : Nat := 4983230072969 + 3 ^ 40 * 3730288 * 2
def baseEnd_3730288 : Nat := 1276953815799337643163149

theorem tailTrace_3730288 : CollatzResearch.WordTrace tailWord_3730288 prefixEnd_3730288 1276953815799337643163149 := by
  unfold tailWord_3730288
  simp only [CollatzResearch.WordTrace]
  refine ⟨68027390354905566657391759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90703187139874088876522345 68027390354905566657391759)
  ·
    refine ⟨102041085532358349986087639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68027390354905566657391759 102041085532358349986087639)
    ·
      refine ⟨153061628298537524979131459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102041085532358349986087639 153061628298537524979131459)
      ·
        refine ⟨229592442447806287468697189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153061628298537524979131459 229592442447806287468697189)
        ·
          refine ⟨43048582958963678900380723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 229592442447806287468697189 43048582958963678900380723)
          ·
            refine ⟨64572874438445518350571085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43048582958963678900380723 64572874438445518350571085)
            ·
              refine ⟨24214827914417069381464157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64572874438445518350571085 24214827914417069381464157)
              ·
                refine ⟨9080560467906401018049059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24214827914417069381464157 9080560467906401018049059)
                ·
                  refine ⟨13620840701859601527073589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9080560467906401018049059 13620840701859601527073589)
                  ·
                    refine ⟨1276953815799337643163149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13620840701859601527073589 1276953815799337643163149)
                    ·
                      rfl

theorem cell22_3730288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 3, 1, 5].length) (baseStart_3730288 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3730288 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3730288 prefixEnd_3730288 := by exact prefixLift 3730288
  have htrace : WordTrace (prefixWord ++ tailWord_3730288) baseStart_3730288 baseEnd_3730288 := by
    simpa [prefixWord, tailWord_3730288, baseEnd_3730288] using wordTrace_append hprefix tailTrace_3730288
  have hstable : (prefixWord ++ tailWord_3730288).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3730288).length < 2 ^ (prefixWord ++ tailWord_3730288).sum := by decide
  have hdescent : baseEnd_3730288 < baseStart_3730288 := by decide
  rcases family_descends (prefixWord ++ tailWord_3730288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3730367 : List Nat := [1, 1, 2, 2, 2, 1, 2, 7, 1, 3]
def baseStart_3730367 : Nat := 118140960795 + 3730367 * 2 ^ 59
def prefixEnd_3730367 : Nat := 4983230072969 + 3 ^ 40 * 3730367 * 2
def baseEnd_3730367 : Nat := 1276980859113807770437907

theorem tailTrace_3730367 : CollatzResearch.WordTrace tailWord_3730367 prefixEnd_3730367 1276980859113807770437907 := by
  unfold tailWord_3730367
  simp only [CollatzResearch.WordTrace]
  refine ⟨136057662076524929806909355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90705108051016619871272903 136057662076524929806909355)
  ·
    refine ⟨204086493114787394710364033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136057662076524929806909355 204086493114787394710364033)
    ·
      refine ⟨153064869836090546032773025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 204086493114787394710364033 153064869836090546032773025)
      ·
        refine ⟨114798652377067909524579769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153064869836090546032773025 114798652377067909524579769)
        ·
          refine ⟨86098989282800932143434827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114798652377067909524579769 86098989282800932143434827)
          ·
            refine ⟨129148483924201398215152241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86098989282800932143434827 129148483924201398215152241)
            ·
              refine ⟨96861362943151048661364181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 129148483924201398215152241 96861362943151048661364181)
              ·
                refine ⟨2270188193980102703000723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 96861362943151048661364181 2270188193980102703000723)
                ·
                  refine ⟨3405282290970154054501085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2270188193980102703000723 3405282290970154054501085)
                  ·
                    refine ⟨1276980859113807770437907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3405282290970154054501085 1276980859113807770437907)
                    ·
                      rfl

theorem cell22_3730367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 7, 1, 3].length) (baseStart_3730367 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3730367 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3730367 prefixEnd_3730367 := by exact prefixLift 3730367
  have htrace : WordTrace (prefixWord ++ tailWord_3730367) baseStart_3730367 baseEnd_3730367 := by
    simpa [prefixWord, tailWord_3730367, baseEnd_3730367] using wordTrace_append hprefix tailTrace_3730367
  have hstable : (prefixWord ++ tailWord_3730367).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3730367).length < 2 ^ (prefixWord ++ tailWord_3730367).sum := by decide
  have hdescent : baseEnd_3730367 < baseStart_3730367 := by decide
  rcases family_descends (prefixWord ++ tailWord_3730367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3730380 : List Nat := [2, 2, 1, 4, 1, 1, 2, 4, 5]
def baseStart_3730380 : Nat := 118140960795 + 3730380 * 2 ^ 59
def prefixEnd_3730380 : Nat := 4983230072969 + 3 ^ 40 * 3730380 * 2
def baseEnd_3730380 : Nat := 425661769759826689954289

theorem tailTrace_3730380 : CollatzResearch.WordTrace tailWord_3730380 prefixEnd_3730380 425661769759826689954289 := by
  unfold tailWord_3730380
  simp only [CollatzResearch.WordTrace]
  refine ⟨68029068112738916513566297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90705424150318555351421729 68029068112738916513566297)
  ·
    refine ⟨51021801084554187385174723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68029068112738916513566297 51021801084554187385174723)
    ·
      refine ⟨76532701626831281077762085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51021801084554187385174723 76532701626831281077762085)
      ·
        refine ⟨14349881555030865202080391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 76532701626831281077762085 14349881555030865202080391)
        ·
          refine ⟨21524822332546297803120587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14349881555030865202080391 21524822332546297803120587)
          ·
            refine ⟨32287233498819446704680881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21524822332546297803120587 32287233498819446704680881)
            ·
              refine ⟨24215425124114585028510661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32287233498819446704680881 24215425124114585028510661)
              ·
                refine ⟨4540392210771484692845749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24215425124114585028510661 4540392210771484692845749)
                ·
                  refine ⟨425661769759826689954289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4540392210771484692845749 425661769759826689954289)
                  ·
                    rfl

theorem cell22_3730380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 4, 5].length) (baseStart_3730380 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3730380 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3730380 prefixEnd_3730380 := by exact prefixLift 3730380
  have htrace : WordTrace (prefixWord ++ tailWord_3730380) baseStart_3730380 baseEnd_3730380 := by
    simpa [prefixWord, tailWord_3730380, baseEnd_3730380] using wordTrace_append hprefix tailTrace_3730380
  have hstable : (prefixWord ++ tailWord_3730380).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3730380).length < 2 ^ (prefixWord ++ tailWord_3730380).sum := by decide
  have hdescent : baseEnd_3730380 < baseStart_3730380 := by decide
  rcases family_descends (prefixWord ++ tailWord_3730380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3730397 : List Nat := [1, 4, 3, 1, 2, 2, 1, 3, 5]
def baseStart_3730397 : Nat := 118140960795 + 3730397 * 2 ^ 59
def prefixEnd_3730397 : Nat := 4983230072969 + 3 ^ 40 * 3730397 * 2
def baseEnd_3730397 : Nat := 425663709575632564062605

theorem tailTrace_3730397 : CollatzResearch.WordTrace tailWord_3730397 prefixEnd_3730397 425663709575632564062605 := by
  unfold tailWord_3730397
  simp only [CollatzResearch.WordTrace]
  refine ⟨136058756266416244930501445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90705837510944163287000963 136058756266416244930501445)
  ·
    refine ⟨25511016799953045924469021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 136058756266416244930501445 25511016799953045924469021)
    ·
      refine ⟨9566631299982392221675883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25511016799953045924469021 9566631299982392221675883)
      ·
        refine ⟨14349946949973588332513825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9566631299982392221675883 14349946949973588332513825)
        ·
          refine ⟨10762460212480191249385369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14349946949973588332513825 10762460212480191249385369)
          ·
            refine ⟨8071845159360143437039027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10762460212480191249385369 8071845159360143437039027)
            ·
              refine ⟨12107767739040215155558541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8071845159360143437039027 12107767739040215155558541)
              ·
                refine ⟨4540412902140080683334453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12107767739040215155558541 4540412902140080683334453)
                ·
                  refine ⟨425663709575632564062605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4540412902140080683334453 425663709575632564062605)
                  ·
                    rfl

theorem cell22_3730397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 1, 3, 5].length) (baseStart_3730397 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3730397 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3730397 prefixEnd_3730397 := by exact prefixLift 3730397
  have htrace : WordTrace (prefixWord ++ tailWord_3730397) baseStart_3730397 baseEnd_3730397 := by
    simpa [prefixWord, tailWord_3730397, baseEnd_3730397] using wordTrace_append hprefix tailTrace_3730397
  have hstable : (prefixWord ++ tailWord_3730397).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3730397).length < 2 ^ (prefixWord ++ tailWord_3730397).sum := by decide
  have hdescent : baseEnd_3730397 < baseStart_3730397 := by decide
  rcases family_descends (prefixWord ++ tailWord_3730397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3730457 : List Nat := [1, 2, 1, 2, 1, 1, 6, 3, 2, 3]
def baseStart_3730457 : Nat := 118140960795 + 3730457 * 2 ^ 59
def prefixEnd_3730457 : Nat := 4983230072969 + 3 ^ 40 * 3730457 * 2
def baseEnd_3730457 : Nat := 1277011667953077535687631

theorem tailTrace_3730457 : CollatzResearch.WordTrace tailWord_3730457 prefixEnd_3730457 1277011667953077535687631 := by
  unfold tailWord_3730457
  simp only [CollatzResearch.WordTrace]
  refine ⟨136060944646198875177685625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90707296430799250118457083 136060944646198875177685625)
  ·
    refine ⟨102045708484649156383264219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136060944646198875177685625 102045708484649156383264219)
    ·
      refine ⟨153068562726973734574896329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102045708484649156383264219 153068562726973734574896329)
      ·
        refine ⟨114801422045230300931172247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153068562726973734574896329 114801422045230300931172247)
        ·
          refine ⟨172202133067845451396758371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114801422045230300931172247 172202133067845451396758371)
          ·
            refine ⟨258303199601768177095137557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 172202133067845451396758371 258303199601768177095137557)
            ·
              refine ⟨12107962481332883301334573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 258303199601768177095137557 12107962481332883301334573)
              ·
                refine ⟨4540485930499831238000465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12107962481332883301334573 4540485930499831238000465)
                ·
                  refine ⟨3405364447874873428500349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4540485930499831238000465 3405364447874873428500349)
                  ·
                    refine ⟨1277011667953077535687631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3405364447874873428500349 1277011667953077535687631)
                    ·
                      rfl

theorem cell22_3730457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 6, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 6, 3, 2, 3].length) (baseStart_3730457 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3730457 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3730457 prefixEnd_3730457 := by exact prefixLift 3730457
  have htrace : WordTrace (prefixWord ++ tailWord_3730457) baseStart_3730457 baseEnd_3730457 := by
    simpa [prefixWord, tailWord_3730457, baseEnd_3730457] using wordTrace_append hprefix tailTrace_3730457
  have hstable : (prefixWord ++ tailWord_3730457).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3730457).length < 2 ^ (prefixWord ++ tailWord_3730457).sum := by decide
  have hdescent : baseEnd_3730457 < baseStart_3730457 := by decide
  rcases family_descends (prefixWord ++ tailWord_3730457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3730553 : List Nat := [1, 2, 1, 3, 5, 1, 3, 2, 1, 3]
def baseStart_3730553 : Nat := 118140960795 + 3730553 * 2 ^ 59
def prefixEnd_3730553 : Nat := 4983230072969 + 3 ^ 40 * 3730553 * 2
def baseEnd_3730553 : Nat := 1277044530714965285287337

theorem tailTrace_3730553 : CollatzResearch.WordTrace tailWord_3730553 prefixEnd_3730553 1277044530714965285287337 := by
  unfold tailWord_3730553
  simp only [CollatzResearch.WordTrace]
  refine ⟨136064446053851083573180313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90709630702567389048786875 136064446053851083573180313)
  ·
    refine ⟨102048334540388312679885235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136064446053851083573180313 102048334540388312679885235)
    ·
      refine ⟨153072501810582469019827853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102048334540388312679885235 153072501810582469019827853)
      ·
        refine ⟨57402188178968425882435445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 153072501810582469019827853 57402188178968425882435445)
        ·
          refine ⟨5381455141778289926478323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 57402188178968425882435445 5381455141778289926478323)
          ·
            refine ⟨8072182712667434889717485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5381455141778289926478323 8072182712667434889717485)
            ·
              refine ⟨3027068517250288083644057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8072182712667434889717485 3027068517250288083644057)
              ·
                refine ⟨2270301387937716062733043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3027068517250288083644057 2270301387937716062733043)
                ·
                  refine ⟨3405452081906574094099565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2270301387937716062733043 3405452081906574094099565)
                  ·
                    refine ⟨1277044530714965285287337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3405452081906574094099565 1277044530714965285287337)
                    ·
                      rfl

theorem cell22_3730553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 3, 2, 1, 3].length) (baseStart_3730553 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3730553 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3730553 prefixEnd_3730553 := by exact prefixLift 3730553
  have htrace : WordTrace (prefixWord ++ tailWord_3730553) baseStart_3730553 baseEnd_3730553 := by
    simpa [prefixWord, tailWord_3730553, baseEnd_3730553] using wordTrace_append hprefix tailTrace_3730553
  have hstable : (prefixWord ++ tailWord_3730553).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3730553).length < 2 ^ (prefixWord ++ tailWord_3730553).sum := by decide
  have hdescent : baseEnd_3730553 < baseStart_3730553 := by decide
  rcases family_descends (prefixWord ++ tailWord_3730553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3730592 : List Nat := [2, 1, 1, 4, 2, 1, 3, 2, 1, 5]
def baseStart_3730592 : Nat := 118140960795 + 3730592 * 2 ^ 59
def prefixEnd_3730592 : Nat := 4983230072969 + 3 ^ 40 * 3730592 * 2
def baseEnd_3730592 : Nat := 1277057881211982183562217

theorem tailTrace_3730592 : CollatzResearch.WordTrace tailWord_3730592 prefixEnd_3730592 1277057881211982183562217 := by
  unfold tailWord_3730592
  simp only [CollatzResearch.WordTrace]
  refine ⟨68032934250354896616925015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90710579000473195489233353 68032934250354896616925015)
  ·
    refine ⟨102049401375532344925387523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68032934250354896616925015 102049401375532344925387523)
    ·
      refine ⟨153074102063298517388081285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102049401375532344925387523 153074102063298517388081285)
      ·
        refine ⟨28701394136868472010265241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 153074102063298517388081285 28701394136868472010265241)
        ·
          refine ⟨21526045602651354007698931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28701394136868472010265241 21526045602651354007698931)
          ·
            refine ⟨32289068403977031011548397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21526045602651354007698931 32289068403977031011548397)
            ·
              refine ⟨12108400651491386629330649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32289068403977031011548397 12108400651491386629330649)
              ·
                refine ⟨9081300488618539971997987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12108400651491386629330649 9081300488618539971997987)
                ·
                  refine ⟨13621950732927809957996981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9081300488618539971997987 13621950732927809957996981)
                  ·
                    refine ⟨1277057881211982183562217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13621950732927809957996981 1277057881211982183562217)
                    ·
                      rfl

theorem cell22_3730592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 3, 2, 1, 5].length) (baseStart_3730592 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3730592 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3730592 prefixEnd_3730592 := by exact prefixLift 3730592
  have htrace : WordTrace (prefixWord ++ tailWord_3730592) baseStart_3730592 baseEnd_3730592 := by
    simpa [prefixWord, tailWord_3730592, baseEnd_3730592] using wordTrace_append hprefix tailTrace_3730592
  have hstable : (prefixWord ++ tailWord_3730592).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3730592).length < 2 ^ (prefixWord ++ tailWord_3730592).sum := by decide
  have hdescent : baseEnd_3730592 < baseStart_3730592 := by decide
  rcases family_descends (prefixWord ++ tailWord_3730592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3730596 : List Nat := [2, 3, 1, 2, 3, 2, 3, 1, 1, 4]
def baseStart_3730596 : Nat := 118140960795 + 3730596 * 2 ^ 59
def prefixEnd_3730596 : Nat := 4983230072969 + 3 ^ 40 * 3730596 * 2
def baseEnd_3730596 : Nat := 1277059250493727506462205

theorem tailTrace_3730596 : CollatzResearch.WordTrace tailWord_3730596 prefixEnd_3730596 1277059250493727506462205 := by
  unfold tailWord_3730596
  simp only [CollatzResearch.WordTrace]
  refine ⟨68033007196347650958497821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90710676261796867944663761 68033007196347650958497821)
  ·
    refine ⟨25512377698630369109436683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68033007196347650958497821 25512377698630369109436683)
    ·
      refine ⟨38268566547945553664155025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25512377698630369109436683 38268566547945553664155025)
      ·
        refine ⟨28701424910959165248116269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38268566547945553664155025 28701424910959165248116269)
        ·
          refine ⟨10763034341609686968043601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28701424910959165248116269 10763034341609686968043601)
          ·
            refine ⟨8072275756207265226032701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10763034341609686968043601 8072275756207265226032701)
            ·
              refine ⟨3027103408577724459762263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8072275756207265226032701 3027103408577724459762263)
              ·
                refine ⟨4540655112866586689643395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3027103408577724459762263 4540655112866586689643395)
                ·
                  refine ⟨6810982669299880034465093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4540655112866586689643395 6810982669299880034465093)
                  ·
                    refine ⟨1277059250493727506462205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6810982669299880034465093 1277059250493727506462205)
                    ·
                      rfl

theorem cell22_3730596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 3, 1, 1, 4].length) (baseStart_3730596 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3730596 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3730596 prefixEnd_3730596 := by exact prefixLift 3730596
  have htrace : WordTrace (prefixWord ++ tailWord_3730596) baseStart_3730596 baseEnd_3730596 := by
    simpa [prefixWord, tailWord_3730596, baseEnd_3730596] using wordTrace_append hprefix tailTrace_3730596
  have hstable : (prefixWord ++ tailWord_3730596).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3730596).length < 2 ^ (prefixWord ++ tailWord_3730596).sum := by decide
  have hdescent : baseEnd_3730596 < baseStart_3730596 := by decide
  rcases family_descends (prefixWord ++ tailWord_3730596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3730607 : List Nat := [1, 1, 2, 1, 2, 3, 4, 2, 2, 4]
def baseStart_3730607 : Nat := 118140960795 + 3730607 * 2 ^ 59
def prefixEnd_3730607 : Nat := 4983230072969 + 3 ^ 40 * 3730607 * 2
def baseEnd_3730607 : Nat := 1277063016018527144437171

theorem tailTrace_3730607 : CollatzResearch.WordTrace tailWord_3730607 prefixEnd_3730607 1277063016018527144437171 := by
  unfold tailWord_3730607
  simp only [CollatzResearch.WordTrace]
  refine ⟨136066415595655450795646075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90710943730436967197097383 136066415595655450795646075)
  ·
    refine ⟨204099623393483176193469113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136066415595655450795646075 204099623393483176193469113)
    ·
      refine ⟨153074717545112382145101835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 204099623393483176193469113 153074717545112382145101835)
      ·
        refine ⟨229612076317668573217652753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153074717545112382145101835 229612076317668573217652753)
        ·
          refine ⟨172209057238251429913239565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 229612076317668573217652753 172209057238251429913239565)
          ·
            refine ⟨64578396464344286217464837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 172209057238251429913239565 64578396464344286217464837)
            ·
              refine ⟨12108449337064553665774657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64578396464344286217464837 12108449337064553665774657)
              ·
                refine ⟨9081337002798415249330993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12108449337064553665774657 9081337002798415249330993)
                ·
                  refine ⟨6811002752098811436998245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9081337002798415249330993 6811002752098811436998245)
                  ·
                    refine ⟨1277063016018527144437171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6811002752098811436998245 1277063016018527144437171)
                    ·
                      rfl

theorem cell22_3730607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 4, 2, 2, 4].length) (baseStart_3730607 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3730607 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3730607 prefixEnd_3730607 := by exact prefixLift 3730607
  have htrace : WordTrace (prefixWord ++ tailWord_3730607) baseStart_3730607 baseEnd_3730607 := by
    simpa [prefixWord, tailWord_3730607, baseEnd_3730607] using wordTrace_append hprefix tailTrace_3730607
  have hstable : (prefixWord ++ tailWord_3730607).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3730607).length < 2 ^ (prefixWord ++ tailWord_3730607).sum := by decide
  have hdescent : baseEnd_3730607 < baseStart_3730607 := by decide
  rcases family_descends (prefixWord ++ tailWord_3730607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3730667 : List Nat := [1, 1, 1, 1, 2, 7, 1, 1, 7]
def baseStart_3730667 : Nat := 118140960795 + 3730667 * 2 ^ 59
def prefixEnd_3730667 : Nat := 4983230072969 + 3 ^ 40 * 3730667 * 2
def baseEnd_3730667 : Nat := 425694518414902329312329

theorem tailTrace_3730667 : CollatzResearch.WordTrace tailWord_3730667 prefixEnd_3730667 425694518414902329312329 := by
  unfold tailWord_3730667
  simp only [CollatzResearch.WordTrace]
  refine ⟨136068603975438081042830255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90712402650292054028553503 136068603975438081042830255)
  ·
    refine ⟨204102905963157121564245383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136068603975438081042830255 204102905963157121564245383)
    ·
      refine ⟨306154358944735682346368075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204102905963157121564245383 306154358944735682346368075)
      ·
        refine ⟨459231538417103523519552113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 306154358944735682346368075 459231538417103523519552113)
        ·
          refine ⟨344423653812827642639664085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 459231538417103523519552113 344423653812827642639664085)
          ·
            refine ⟨8072429386238147874367127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 344423653812827642639664085 8072429386238147874367127)
            ·
              refine ⟨12108644079357221811550691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8072429386238147874367127 12108644079357221811550691)
              ·
                refine ⟨18162966119035832717326037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12108644079357221811550691 18162966119035832717326037)
                ·
                  refine ⟨425694518414902329312329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18162966119035832717326037 425694518414902329312329)
                  ·
                    rfl

theorem cell22_3730667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 1, 1, 7].length) (baseStart_3730667 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3730667 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3730667 prefixEnd_3730667 := by exact prefixLift 3730667
  have htrace : WordTrace (prefixWord ++ tailWord_3730667) baseStart_3730667 baseEnd_3730667 := by
    simpa [prefixWord, tailWord_3730667, baseEnd_3730667] using wordTrace_append hprefix tailTrace_3730667
  have hstable : (prefixWord ++ tailWord_3730667).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3730667).length < 2 ^ (prefixWord ++ tailWord_3730667).sum := by decide
  have hdescent : baseEnd_3730667 < baseStart_3730667 := by decide
  rcases family_descends (prefixWord ++ tailWord_3730667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3730671 : List Nat := [1, 1, 2, 1, 7, 1, 2, 1, 3, 3]
def baseStart_3730671 : Nat := 118140960795 + 3730671 * 2 ^ 59
def prefixEnd_3730671 : Nat := 4983230072969 + 3 ^ 40 * 3730671 * 2
def baseEnd_3730671 : Nat := 1277084924526452310836975

theorem tailTrace_3730671 : CollatzResearch.WordTrace tailWord_3730671 prefixEnd_3730671 1277084924526452310836975 := by
  unfold tailWord_3730671
  simp only [CollatzResearch.WordTrace]
  refine ⟨136068749867423589725975867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90712499911615726483983911 136068749867423589725975867)
  ·
    refine ⟨204103124801135384588963801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136068749867423589725975867 204103124801135384588963801)
    ·
      refine ⟨153077343600851538441722851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 204103124801135384588963801 153077343600851538441722851)
      ·
        refine ⟨229616015401277307662584277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153077343600851538441722851 229616015401277307662584277)
        ·
          refine ⟨5381625360967436898341819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 229616015401277307662584277 5381625360967436898341819)
          ·
            refine ⟨8072438041451155347512729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5381625360967436898341819 8072438041451155347512729)
            ·
              refine ⟨6054328531088366510634547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8072438041451155347512729 6054328531088366510634547)
              ·
                refine ⟨9081492796632549765951821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6054328531088366510634547 9081492796632549765951821)
                ·
                  refine ⟨3405559798737206162231933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9081492796632549765951821 3405559798737206162231933)
                  ·
                    refine ⟨1277084924526452310836975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3405559798737206162231933 1277084924526452310836975)
                    ·
                      rfl

theorem cell22_3730671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 2, 1, 3, 3].length) (baseStart_3730671 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3730671 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3730671 prefixEnd_3730671 := by exact prefixLift 3730671
  have htrace : WordTrace (prefixWord ++ tailWord_3730671) baseStart_3730671 baseEnd_3730671 := by
    simpa [prefixWord, tailWord_3730671, baseEnd_3730671] using wordTrace_append hprefix tailTrace_3730671
  have hstable : (prefixWord ++ tailWord_3730671).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3730671).length < 2 ^ (prefixWord ++ tailWord_3730671).sum := by decide
  have hdescent : baseEnd_3730671 < baseStart_3730671 := by decide
  rcases family_descends (prefixWord ++ tailWord_3730671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3730682 : List Nat := [3, 1, 1, 1, 1, 4, 1, 3, 2, 5]
def baseStart_3730682 : Nat := 118140960795 + 3730682 * 2 ^ 59
def prefixEnd_3730682 : Nat := 4983230072969 + 3 ^ 40 * 3730682 * 2
def baseEnd_3730682 : Nat := 1277088690051251948811941

theorem tailTrace_3730682 : CollatzResearch.WordTrace tailWord_3730682 prefixEnd_3730682 1277088690051251948811941 := by
  unfold tailWord_3730682
  simp only [CollatzResearch.WordTrace]
  refine ⟨34017287767595934651156575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90712767380255825736417533 34017287767595934651156575)
  ·
    refine ⟨51025931651393901976734863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34017287767595934651156575 51025931651393901976734863)
    ·
      refine ⟨76538897477090852965102295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51025931651393901976734863 76538897477090852965102295)
      ·
        refine ⟨114808346215636279447653443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76538897477090852965102295 114808346215636279447653443)
        ·
          refine ⟨172212519323454419171480165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114808346215636279447653443 172212519323454419171480165)
          ·
            refine ⟨32289847373147703594652531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 172212519323454419171480165 32289847373147703594652531)
            ·
              refine ⟨48434771059721555391978797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32289847373147703594652531 48434771059721555391978797)
              ·
                refine ⟨18163039147395583271992049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48434771059721555391978797 18163039147395583271992049)
                ·
                  refine ⟨13622279360546687453994037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18163039147395583271992049 13622279360546687453994037)
                  ·
                    refine ⟨1277088690051251948811941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13622279360546687453994037 1277088690051251948811941)
                    ·
                      rfl

theorem cell22_3730682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 3, 2, 5].length) (baseStart_3730682 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3730682 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3730682 prefixEnd_3730682 := by exact prefixLift 3730682
  have htrace : WordTrace (prefixWord ++ tailWord_3730682) baseStart_3730682 baseEnd_3730682 := by
    simpa [prefixWord, tailWord_3730682, baseEnd_3730682] using wordTrace_append hprefix tailTrace_3730682
  have hstable : (prefixWord ++ tailWord_3730682).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3730682).length < 2 ^ (prefixWord ++ tailWord_3730682).sum := by decide
  have hdescent : baseEnd_3730682 < baseStart_3730682 := by decide
  rcases family_descends (prefixWord ++ tailWord_3730682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3730759 : List Nat := [1, 1, 4, 1, 2, 3, 1, 3, 2, 4]
def baseStart_3730759 : Nat := 118140960795 + 3730759 * 2 ^ 59
def prefixEnd_3730759 : Nat := 4983230072969 + 3 ^ 40 * 3730759 * 2
def baseEnd_3730759 : Nat := 1277115048724849414636705

theorem tailTrace_3730759 : CollatzResearch.WordTrace tailWord_3730759 prefixEnd_3730759 1277115048724849414636705 := by
  unfold tailWord_3730759
  simp only [CollatzResearch.WordTrace]
  refine ⟨136071959491104780755179331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90714639660736520503452887 136071959491104780755179331)
  ·
    refine ⟨204107939236657171132768997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136071959491104780755179331 204107939236657171132768997)
    ·
      refine ⟨38270238606873219587394187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 204107939236657171132768997 38270238606873219587394187)
      ·
        refine ⟨57405357910309829381091281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38270238606873219587394187 57405357910309829381091281)
        ·
          refine ⟨43054018432732372035818461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57405357910309829381091281 43054018432732372035818461)
          ·
            refine ⟨16145256912274639513431923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43054018432732372035818461 16145256912274639513431923)
            ·
              refine ⟨24217885368411959270147885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16145256912274639513431923 24217885368411959270147885)
              ·
                refine ⟨9081707013154484726305457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24217885368411959270147885 9081707013154484726305457)
                ·
                  refine ⟨6811280259865863544729093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9081707013154484726305457 6811280259865863544729093)
                  ·
                    refine ⟨1277115048724849414636705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6811280259865863544729093 1277115048724849414636705)
                    ·
                      rfl

theorem cell22_3730759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 3, 2, 4].length) (baseStart_3730759 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3730759 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3730759 prefixEnd_3730759 := by exact prefixLift 3730759
  have htrace : WordTrace (prefixWord ++ tailWord_3730759) baseStart_3730759 baseEnd_3730759 := by
    simpa [prefixWord, tailWord_3730759, baseEnd_3730759] using wordTrace_append hprefix tailTrace_3730759
  have hstable : (prefixWord ++ tailWord_3730759).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3730759).length < 2 ^ (prefixWord ++ tailWord_3730759).sum := by decide
  have hdescent : baseEnd_3730759 < baseStart_3730759 := by decide
  rcases family_descends (prefixWord ++ tailWord_3730759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3730791 : List Nat := [1, 1, 5, 1, 4, 2, 1, 7]
def baseStart_3730791 : Nat := 118140960795 + 3730791 * 2 ^ 59
def prefixEnd_3730791 : Nat := 4983230072969 + 3 ^ 40 * 3730791 * 2
def baseEnd_3730791 : Nat := 141902889219867999759623

theorem tailTrace_3730791 : CollatzResearch.WordTrace tailWord_3730791 prefixEnd_3730791 141902889219867999759623 := by
  unfold tailWord_3730791
  simp only [CollatzResearch.WordTrace]
  refine ⟨136073126626988850220344227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90715417751325900146896151 136073126626988850220344227)
  ·
    refine ⟨204109689940483275330516341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136073126626988850220344227 204109689940483275330516341)
    ·
      refine ⟨19135283431920307062235907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 204109689940483275330516341 19135283431920307062235907)
      ·
        refine ⟨28702925147880460593353861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19135283431920307062235907 28702925147880460593353861)
        ·
          refine ⟨5381798465227586361253849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28702925147880460593353861 5381798465227586361253849)
          ·
            refine ⟨4036348848920689770940387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5381798465227586361253849 4036348848920689770940387)
            ·
              refine ⟨6054523273381034656410581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4036348848920689770940387 6054523273381034656410581)
              ·
                refine ⟨141902889219867999759623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6054523273381034656410581 141902889219867999759623)
                ·
                  rfl

theorem cell22_3730791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 2, 1, 7].length) (baseStart_3730791 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3730791 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3730791 prefixEnd_3730791 := by exact prefixLift 3730791
  have htrace : WordTrace (prefixWord ++ tailWord_3730791) baseStart_3730791 baseEnd_3730791 := by
    simpa [prefixWord, tailWord_3730791, baseEnd_3730791] using wordTrace_append hprefix tailTrace_3730791
  have hstable : (prefixWord ++ tailWord_3730791).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3730791).length < 2 ^ (prefixWord ++ tailWord_3730791).sum := by decide
  have hdescent : baseEnd_3730791 < baseStart_3730791 := by decide
  rcases family_descends (prefixWord ++ tailWord_3730791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3730823 : List Nat := [1, 1, 4, 2, 2, 2, 1, 5, 1, 3]
def baseStart_3730823 : Nat := 118140960795 + 3730823 * 2 ^ 59
def prefixEnd_3730823 : Nat := 4983230072969 + 3 ^ 40 * 3730823 * 2
def baseEnd_3730823 : Nat := 1277136957232774581036509

theorem tailTrace_3730823 : CollatzResearch.WordTrace tailWord_3730823 prefixEnd_3730823 1277136957232774581036509 := by
  unfold tailWord_3730823
  simp only [CollatzResearch.WordTrace]
  refine ⟨136074293762872919685509123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90716195841915279790339415 136074293762872919685509123)
  ·
    refine ⟨204111440644309379528263685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136074293762872919685509123 204111440644309379528263685)
    ·
      refine ⟨38270895120808008661549441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 204111440644309379528263685 38270895120808008661549441)
      ·
        refine ⟨28703171340606006496162081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38270895120808008661549441 28703171340606006496162081)
        ·
          refine ⟨21527378505454504872121561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28703171340606006496162081 21527378505454504872121561)
          ·
            refine ⟨16145533879090878654091171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21527378505454504872121561 16145533879090878654091171)
            ·
              refine ⟨24218300818636317981136757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16145533879090878654091171 24218300818636317981136757)
              ·
                refine ⟨2270465701747154810731571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24218300818636317981136757 2270465701747154810731571)
                ·
                  refine ⟨3405698552620732216097357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2270465701747154810731571 3405698552620732216097357)
                  ·
                    refine ⟨1277136957232774581036509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3405698552620732216097357 1277136957232774581036509)
                    ·
                      rfl

theorem cell22_3730823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 5, 1, 3].length) (baseStart_3730823 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3730823 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3730823 prefixEnd_3730823 := by exact prefixLift 3730823
  have htrace : WordTrace (prefixWord ++ tailWord_3730823) baseStart_3730823 baseEnd_3730823 := by
    simpa [prefixWord, tailWord_3730823, baseEnd_3730823] using wordTrace_append hprefix tailTrace_3730823
  have hstable : (prefixWord ++ tailWord_3730823).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3730823).length < 2 ^ (prefixWord ++ tailWord_3730823).sum := by decide
  have hdescent : baseEnd_3730823 < baseStart_3730823 := by decide
  rcases family_descends (prefixWord ++ tailWord_3730823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3730836 : List Nat := [2, 4, 2, 1, 2, 2, 1, 1, 7]
def baseStart_3730836 : Nat := 118140960795 + 3730836 * 2 ^ 59
def prefixEnd_3730836 : Nat := 4983230072969 + 3 ^ 40 * 3730836 * 2
def baseEnd_3730836 : Nat := 425713802466148960153823

theorem tailTrace_3730836 : CollatzResearch.WordTrace tailWord_3730836 prefixEnd_3730836 425713802466148960153823 := by
  unfold tailWord_3730836
  simp only [CollatzResearch.WordTrace]
  refine ⟨68037383955912911452866181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90716511941217215270488241 68037383955912911452866181)
  ·
    refine ⟨12757009491733670897412409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 68037383955912911452866181 12757009491733670897412409)
    ·
      refine ⟨9567757118800253173059307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12757009491733670897412409 9567757118800253173059307)
      ·
        refine ⟨14351635678200379759588961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9567757118800253173059307 14351635678200379759588961)
        ·
          refine ⟨10763726758650284819691721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14351635678200379759588961 10763726758650284819691721)
          ·
            refine ⟨8072795068987713614768791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10763726758650284819691721 8072795068987713614768791)
            ·
              refine ⟨12109192603481570422153187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8072795068987713614768791 12109192603481570422153187)
              ·
                refine ⟨18163788905222355633229781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12109192603481570422153187 18163788905222355633229781)
                ·
                  refine ⟨425713802466148960153823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18163788905222355633229781 425713802466148960153823)
                  ·
                    rfl

theorem cell22_3730836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 1, 1, 7].length) (baseStart_3730836 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3730836 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3730836 prefixEnd_3730836 := by exact prefixLift 3730836
  have htrace : WordTrace (prefixWord ++ tailWord_3730836) baseStart_3730836 baseEnd_3730836 := by
    simpa [prefixWord, tailWord_3730836, baseEnd_3730836] using wordTrace_append hprefix tailTrace_3730836
  have hstable : (prefixWord ++ tailWord_3730836).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3730836).length < 2 ^ (prefixWord ++ tailWord_3730836).sum := by decide
  have hdescent : baseEnd_3730836 < baseStart_3730836 := by decide
  rcases family_descends (prefixWord ++ tailWord_3730836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3730879 : List Nat := [1, 1, 2, 2, 2, 1, 1, 6, 1, 5]
def baseStart_3730879 : Nat := 118140960795 + 3730879 * 2 ^ 59
def prefixEnd_3730879 : Nat := 4983230072969 + 3 ^ 40 * 3730879 * 2
def baseEnd_3730879 : Nat := 1277156127177209101636337

theorem tailTrace_3730879 : CollatzResearch.WordTrace tailWord_3730879 prefixEnd_3730879 1277156127177209101636337 := by
  unfold tailWord_3730879
  simp only [CollatzResearch.WordTrace]
  refine ⟨136076336250670041249547691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90717557500446694166365127 136076336250670041249547691)
  ·
    refine ⟨204114504376005061874321537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136076336250670041249547691 204114504376005061874321537)
    ·
      refine ⟨153085878282003796405741153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 204114504376005061874321537 153085878282003796405741153)
      ·
        refine ⟨114814408711502847304305865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153085878282003796405741153 114814408711502847304305865)
        ·
          refine ⟨86110806533627135478229399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114814408711502847304305865 86110806533627135478229399)
          ·
            refine ⟨129166209800440703217344099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86110806533627135478229399 129166209800440703217344099)
            ·
              refine ⟨193749314700661054826016149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129166209800440703217344099 193749314700661054826016149)
              ·
                refine ⟨9081999126593486944969507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 193749314700661054826016149 9081999126593486944969507)
                ·
                  refine ⟨13622998689890230417454261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9081999126593486944969507 13622998689890230417454261)
                  ·
                    refine ⟨1277156127177209101636337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13622998689890230417454261 1277156127177209101636337)
                    ·
                      rfl

theorem cell22_3730879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 6, 1, 5].length) (baseStart_3730879 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3730879 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3730879 prefixEnd_3730879 := by exact prefixLift 3730879
  have htrace : WordTrace (prefixWord ++ tailWord_3730879) baseStart_3730879 baseEnd_3730879 := by
    simpa [prefixWord, tailWord_3730879, baseEnd_3730879] using wordTrace_append hprefix tailTrace_3730879
  have hstable : (prefixWord ++ tailWord_3730879).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3730879).length < 2 ^ (prefixWord ++ tailWord_3730879).sum := by decide
  have hdescent : baseEnd_3730879 < baseStart_3730879 := by decide
  rcases family_descends (prefixWord ++ tailWord_3730879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3730913 : List Nat := [1, 2, 3, 1, 2, 4, 1, 3, 2, 3]
def baseStart_3730913 : Nat := 118140960795 + 3730913 * 2 ^ 59
def prefixEnd_3730913 : Nat := 4983230072969 + 3 ^ 40 * 3730913 * 2
def baseEnd_3730913 : Nat := 1277167766072044346286233

theorem tailTrace_3730913 : CollatzResearch.WordTrace tailWord_3730913 prefixEnd_3730913 1277167766072044346286233 := by
  unfold tailWord_3730913
  simp only [CollatzResearch.WordTrace]
  refine ⟨136077576332546865056285393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90718384221697910037523595 136077576332546865056285393)
  ·
    refine ⟨102058182249410148792214045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136077576332546865056285393 102058182249410148792214045)
    ·
      refine ⟨38271818343528805797080267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102058182249410148792214045 38271818343528805797080267)
      ·
        refine ⟨57407727515293208695620401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38271818343528805797080267 57407727515293208695620401)
        ·
          refine ⟨43055795636469906521715301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57407727515293208695620401 43055795636469906521715301)
          ·
            refine ⟨8072961681838107472821619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43055795636469906521715301 8072961681838107472821619)
            ·
              refine ⟨12109442522757161209232429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8072961681838107472821619 12109442522757161209232429)
              ·
                refine ⟨4541040946033935453462161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12109442522757161209232429 4541040946033935453462161)
                ·
                  refine ⟨3405780709525451590096621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4541040946033935453462161 3405780709525451590096621)
                  ·
                    refine ⟨1277167766072044346286233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3405780709525451590096621 1277167766072044346286233)
                    ·
                      rfl

theorem cell22_3730913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 1, 3, 2, 3].length) (baseStart_3730913 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3730913 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3730913 prefixEnd_3730913 := by exact prefixLift 3730913
  have htrace : WordTrace (prefixWord ++ tailWord_3730913) baseStart_3730913 baseEnd_3730913 := by
    simpa [prefixWord, tailWord_3730913, baseEnd_3730913] using wordTrace_append hprefix tailTrace_3730913
  have hstable : (prefixWord ++ tailWord_3730913).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3730913).length < 2 ^ (prefixWord ++ tailWord_3730913).sum := by decide
  have hdescent : baseEnd_3730913 < baseStart_3730913 := by decide
  rcases family_descends (prefixWord ++ tailWord_3730913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3730986 : List Nat := [3, 1, 4, 1, 1, 1, 1, 2, 1, 7]
def baseStart_3730986 : Nat := 118140960795 + 3730986 * 2 ^ 59
def prefixEnd_3730986 : Nat := 4983230072969 + 3 ^ 40 * 3730986 * 2
def baseEnd_3730986 : Nat := 1277192755463896489211009

theorem tailTrace_3730986 : CollatzResearch.WordTrace tailWord_3730986 prefixEnd_3730986 1277192755463896489211009 := by
  unfold tailWord_3730986
  simp only [CollatzResearch.WordTrace]
  refine ⟨34020059715320599630923203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90720159240854932349128541 34020059715320599630923203)
  ·
    refine ⟨51030089572980899446384805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34020059715320599630923203 51030089572980899446384805)
    ·
      refine ⟨9568141794933918646197151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51030089572980899446384805 9568141794933918646197151)
      ·
        refine ⟨14352212692400877969295727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9568141794933918646197151 14352212692400877969295727)
        ·
          refine ⟨21528319038601316953943591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14352212692400877969295727 21528319038601316953943591)
          ·
            refine ⟨32292478557901975430915387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21528319038601316953943591 32292478557901975430915387)
            ·
              refine ⟨48438717836852963146373081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32292478557901975430915387 48438717836852963146373081)
              ·
                refine ⟨36329038377639722359779811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48438717836852963146373081 36329038377639722359779811)
                ·
                  refine ⟨54493557566459583539669717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36329038377639722359779811 54493557566459583539669717)
                  ·
                    refine ⟨1277192755463896489211009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 54493557566459583539669717 1277192755463896489211009)
                    ·
                      rfl

theorem cell22_3730986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 2, 1, 7].length) (baseStart_3730986 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3730986 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3730986 prefixEnd_3730986 := by exact prefixLift 3730986
  have htrace : WordTrace (prefixWord ++ tailWord_3730986) baseStart_3730986 baseEnd_3730986 := by
    simpa [prefixWord, tailWord_3730986, baseEnd_3730986] using wordTrace_append hprefix tailTrace_3730986
  have hstable : (prefixWord ++ tailWord_3730986).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3730986).length < 2 ^ (prefixWord ++ tailWord_3730986).sum := by decide
  have hdescent : baseEnd_3730986 < baseStart_3730986 := by decide
  rcases family_descends (prefixWord ++ tailWord_3730986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3731005 : List Nat := [1, 4, 1, 3, 3, 2, 1, 2, 5]
def baseStart_3731005 : Nat := 118140960795 + 3731005 * 2 ^ 59
def prefixEnd_3731005 : Nat := 4983230072969 + 3 ^ 40 * 3731005 * 2
def baseEnd_3731005 : Nat := 425733086517395590995317

theorem tailTrace_3731005 : CollatzResearch.WordTrace tailWord_3731005 prefixEnd_3731005 425733086517395590995317 := by
  unfold tailWord_3731005
  simp only [CollatzResearch.WordTrace]
  refine ⟨136080931848213564768634469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90720621232142376512422979 136080931848213564768634469)
  ·
    refine ⟨25515174721540043394118963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 136080931848213564768634469 25515174721540043394118963)
    ·
      refine ⟨38272762082310065091178445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25515174721540043394118963 38272762082310065091178445)
      ·
        refine ⟨14352285780866274409191917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38272762082310065091178445 14352285780866274409191917)
        ·
          refine ⟨5382107167824852903446969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14352285780866274409191917 5382107167824852903446969)
          ·
            refine ⟨4036580375868639677585227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5382107167824852903446969 4036580375868639677585227)
            ·
              refine ⟨6054870563802959516377841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4036580375868639677585227 6054870563802959516377841)
              ·
                refine ⟨4541152922852219637283381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6054870563802959516377841 4541152922852219637283381)
                ·
                  refine ⟨425733086517395590995317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4541152922852219637283381 425733086517395590995317)
                  ·
                    rfl

theorem cell22_3731005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 2, 1, 2, 5].length) (baseStart_3731005 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3731005 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3731005 prefixEnd_3731005 := by exact prefixLift 3731005
  have htrace : WordTrace (prefixWord ++ tailWord_3731005) baseStart_3731005 baseEnd_3731005 := by
    simpa [prefixWord, tailWord_3731005, baseEnd_3731005] using wordTrace_append hprefix tailTrace_3731005
  have hstable : (prefixWord ++ tailWord_3731005).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3731005).length < 2 ^ (prefixWord ++ tailWord_3731005).sum := by decide
  have hdescent : baseEnd_3731005 < baseStart_3731005 := by decide
  rcases family_descends (prefixWord ++ tailWord_3731005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3731050 : List Nat := [3, 1, 3, 2, 1, 2, 3, 3, 4]
def baseStart_3731050 : Nat := 118140960795 + 3731050 * 2 ^ 59
def prefixEnd_3731050 : Nat := 4983230072969 + 3 ^ 40 * 3731050 * 2
def baseEnd_3731050 : Nat := 425738221323940551870271

theorem tailTrace_3731050 : CollatzResearch.WordTrace tailWord_3731050 prefixEnd_3731050 425738221323940551870271 := by
  unfold tailWord_3731050
  simp only [CollatzResearch.WordTrace]
  refine ⟨34020643283262634363505651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90721715422033691636015069 34020643283262634363505651)
  ·
    refine ⟨51030964924893951545258477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34020643283262634363505651 51030964924893951545258477)
    ·
      refine ⟨19136611846835231829471929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51030964924893951545258477 19136611846835231829471929)
      ·
        refine ⟨14352458885126423872103947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19136611846835231829471929 14352458885126423872103947)
        ·
          refine ⟨21528688327689635808155921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14352458885126423872103947 21528688327689635808155921)
          ·
            refine ⟨16146516245767226856116941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21528688327689635808155921 16146516245767226856116941)
            ·
              refine ⟨6054943592162710071043853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16146516245767226856116941 6054943592162710071043853)
              ·
                refine ⟨2270603847061016276641445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6054943592162710071043853 2270603847061016276641445)
                ·
                  refine ⟨425738221323940551870271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2270603847061016276641445 425738221323940551870271)
                  ·
                    rfl

theorem cell22_3731050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 3, 3, 4].length) (baseStart_3731050 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3731050 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3731050 prefixEnd_3731050 := by exact prefixLift 3731050
  have htrace : WordTrace (prefixWord ++ tailWord_3731050) baseStart_3731050 baseEnd_3731050 := by
    simpa [prefixWord, tailWord_3731050, baseEnd_3731050] using wordTrace_append hprefix tailTrace_3731050
  have hstable : (prefixWord ++ tailWord_3731050).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3731050).length < 2 ^ (prefixWord ++ tailWord_3731050).sum := by decide
  have hdescent : baseEnd_3731050 < baseStart_3731050 := by decide
  rcases family_descends (prefixWord ++ tailWord_3731050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3731082 : List Nat := [3, 1, 2, 3, 2, 1, 4, 1, 2, 3]
def baseStart_3731082 : Nat := 118140960795 + 3731082 * 2 ^ 59
def prefixEnd_3731082 : Nat := 4983230072969 + 3 ^ 40 * 3731082 * 2
def baseEnd_3731082 : Nat := 1277225618225784238810715

theorem tailTrace_3731082 : CollatzResearch.WordTrace tailWord_3731082 prefixEnd_3731082 1277225618225784238810715 := by
  unfold tailWord_3731082
  simp only [CollatzResearch.WordTrace]
  refine ⟨34020935067233651729796875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90722493512623071279458333 34020935067233651729796875)
  ·
    refine ⟨51031402600850477594695313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34020935067233651729796875 51031402600850477594695313)
    ·
      refine ⟨38273551950637858196021485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51031402600850477594695313 38273551950637858196021485)
      ·
        refine ⟨14352581981489196823508057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38273551950637858196021485 14352581981489196823508057)
        ·
          refine ⟨10764436486116897617631043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14352581981489196823508057 10764436486116897617631043)
          ·
            refine ⟨16146654729175346426446565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10764436486116897617631043 16146654729175346426446565)
            ·
              refine ⟨3027497761720377454958731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16146654729175346426446565 3027497761720377454958731)
              ·
                refine ⟨4541246642580566182438097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3027497761720377454958731 4541246642580566182438097)
                ·
                  refine ⟨3405934981935424636828573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4541246642580566182438097 3405934981935424636828573)
                  ·
                    refine ⟨1277225618225784238810715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3405934981935424636828573 1277225618225784238810715)
                    ·
                      rfl

theorem cell22_3731082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 4, 1, 2, 3].length) (baseStart_3731082 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3731082 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3731082 prefixEnd_3731082 := by exact prefixLift 3731082
  have htrace : WordTrace (prefixWord ++ tailWord_3731082) baseStart_3731082 baseEnd_3731082 := by
    simpa [prefixWord, tailWord_3731082, baseEnd_3731082] using wordTrace_append hprefix tailTrace_3731082
  have hstable : (prefixWord ++ tailWord_3731082).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3731082).length < 2 ^ (prefixWord ++ tailWord_3731082).sum := by decide
  have hdescent : baseEnd_3731082 < baseStart_3731082 := by decide
  rcases family_descends (prefixWord ++ tailWord_3731082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3731093 : List Nat := [1, 3, 2, 1, 1, 1, 1, 6, 3, 3]
def baseStart_3731093 : Nat := 118140960795 + 3731093 * 2 ^ 59
def prefixEnd_3731093 : Nat := 4983230072969 + 3 ^ 40 * 3731093 * 2
def baseEnd_3731093 : Nat := 1277229383750583876785681

theorem tailTrace_3731093 : CollatzResearch.WordTrace tailWord_3731093 prefixEnd_3731093 1277229383750583876785681 := by
  unfold tailWord_3731093
  simp only [CollatzResearch.WordTrace]
  refine ⟨136084141471894755797837933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90722760981263170531891955 136084141471894755797837933)
  ·
    refine ⟨51031553051960533424189225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136084141471894755797837933 51031553051960533424189225)
    ·
      refine ⟨38273664788970400068141919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51031553051960533424189225 38273664788970400068141919)
      ·
        refine ⟨57410497183455600102212879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38273664788970400068141919 57410497183455600102212879)
        ·
          refine ⟨86115745775183400153319319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57410497183455600102212879 86115745775183400153319319)
          ·
            refine ⟨129173618662775100229978979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86115745775183400153319319 129173618662775100229978979)
            ·
              refine ⟨193760427994162650344968469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129173618662775100229978979 193760427994162650344968469)
              ·
                refine ⟨9082520062226374234920397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 193760427994162650344968469 9082520062226374234920397)
                ·
                  refine ⟨3405945023334890338095149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9082520062226374234920397 3405945023334890338095149)
                  ·
                    refine ⟨1277229383750583876785681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3405945023334890338095149 1277229383750583876785681)
                    ·
                      rfl

theorem cell22_3731093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 6, 3, 3].length) (baseStart_3731093 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3731093 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3731093 prefixEnd_3731093 := by exact prefixLift 3731093
  have htrace : WordTrace (prefixWord ++ tailWord_3731093) baseStart_3731093 baseEnd_3731093 := by
    simpa [prefixWord, tailWord_3731093, baseEnd_3731093] using wordTrace_append hprefix tailTrace_3731093
  have hstable : (prefixWord ++ tailWord_3731093).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3731093).length < 2 ^ (prefixWord ++ tailWord_3731093).sum := by decide
  have hdescent : baseEnd_3731093 < baseStart_3731093 := by decide
  rcases family_descends (prefixWord ++ tailWord_3731093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3731112 : List Nat := [2, 1, 7, 1, 2, 9]
def baseStart_3731112 : Nat := 118140960795 + 3731112 * 2 ^ 59
def prefixEnd_3731112 : Nat := 4983230072969 + 3 ^ 40 * 3731112 * 2
def baseEnd_3731112 : Nat := 15768344294307088401983

theorem tailTrace_3731112 : CollatzResearch.WordTrace tailWord_3731112 prefixEnd_3731112 15768344294307088401983 := by
  unfold tailWord_3731112
  simp only [CollatzResearch.WordTrace]
  refine ⟨68042417229412961021389795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90723222972550614695186393 68042417229412961021389795)
  ·
    refine ⟨102063625844119441532084693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68042417229412961021389795 102063625844119441532084693)
    ·
      refine ⟨2392116230721549410908235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 102063625844119441532084693 2392116230721549410908235)
      ·
        refine ⟨3588174346082324116362353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2392116230721549410908235 3588174346082324116362353)
        ·
          refine ⟨2691130759561743087271765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3588174346082324116362353 2691130759561743087271765)
          ·
            refine ⟨15768344294307088401983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2691130759561743087271765 15768344294307088401983)
            ·
              rfl

theorem cell22_3731112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 2, 9].length) (baseStart_3731112 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3731112 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3731112 prefixEnd_3731112 := by exact prefixLift 3731112
  have htrace : WordTrace (prefixWord ++ tailWord_3731112) baseStart_3731112 baseEnd_3731112 := by
    simpa [prefixWord, tailWord_3731112, baseEnd_3731112] using wordTrace_append hprefix tailTrace_3731112
  have hstable : (prefixWord ++ tailWord_3731112).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3731112).length < 2 ^ (prefixWord ++ tailWord_3731112).sum := by decide
  have hdescent : baseEnd_3731112 < baseStart_3731112 := by decide
  rcases family_descends (prefixWord ++ tailWord_3731112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3731123 : List Nat := [1, 1, 1, 2, 3, 3, 4, 2, 5]
def baseStart_3731123 : Nat := 118140960795 + 3731123 * 2 ^ 59
def prefixEnd_3731123 : Nat := 4983230072969 + 3 ^ 40 * 3731123 * 2
def baseEnd_3731123 : Nat := 425746551121224599511863

theorem tailTrace_3731123 : CollatzResearch.WordTrace tailWord_3731123 prefixEnd_3731123 425746551121224599511863 := by
  unfold tailWord_3731123
  simp only [CollatzResearch.WordTrace]
  refine ⟨136085235661786070921430023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90723490441190713947620015 136085235661786070921430023)
  ·
    refine ⟨204127853492679106382145035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136085235661786070921430023 204127853492679106382145035)
    ·
      refine ⟨306191780239018659573217553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204127853492679106382145035 306191780239018659573217553)
      ·
        refine ⟨229643835179263994679913165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 306191780239018659573217553 229643835179263994679913165)
        ·
          refine ⟨86116438192223998004967437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 229643835179263994679913165 86116438192223998004967437)
          ·
            refine ⟨32293664322083999251862789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86116438192223998004967437 32293664322083999251862789)
            ·
              refine ⟨6055062060390749859724273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32293664322083999251862789 6055062060390749859724273)
              ·
                refine ⟨4541296545293062394793205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6055062060390749859724273 4541296545293062394793205)
                ·
                  refine ⟨425746551121224599511863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4541296545293062394793205 425746551121224599511863)
                  ·
                    rfl

theorem cell22_3731123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 4, 2, 5].length) (baseStart_3731123 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3731123 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3731123 prefixEnd_3731123 := by exact prefixLift 3731123
  have htrace : WordTrace (prefixWord ++ tailWord_3731123) baseStart_3731123 baseEnd_3731123 := by
    simpa [prefixWord, tailWord_3731123, baseEnd_3731123] using wordTrace_append hprefix tailTrace_3731123
  have hstable : (prefixWord ++ tailWord_3731123).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3731123).length < 2 ^ (prefixWord ++ tailWord_3731123).sum := by decide
  have hdescent : baseEnd_3731123 < baseStart_3731123 := by decide
  rcases family_descends (prefixWord ++ tailWord_3731123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3731127 : List Nat := [1, 1, 3, 1, 5, 2, 1, 4, 1, 3]
def baseStart_3731127 : Nat := 118140960795 + 3731127 * 2 ^ 59
def prefixEnd_3731127 : Nat := 4983230072969 + 3 ^ 40 * 3731127 * 2
def baseEnd_3731127 : Nat := 1277241022645419121435577

theorem tailTrace_3731127 : CollatzResearch.WordTrace tailWord_3731127 prefixEnd_3731127 1277241022645419121435577 := by
  unfold tailWord_3731127
  simp only [CollatzResearch.WordTrace]
  refine ⟨136085381553771579604575635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90723587702514386403050423 136085381553771579604575635)
  ·
    refine ⟨204128072330657369406863453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136085381553771579604575635 204128072330657369406863453)
    ·
      refine ⟨76548027123996513527573795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 204128072330657369406863453 76548027123996513527573795)
      ·
        refine ⟨114822040685994770291360693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76548027123996513527573795 114822040685994770291360693)
        ·
          refine ⟨10764566314312009714815065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 114822040685994770291360693 10764566314312009714815065)
          ·
            refine ⟨8073424735734007286111299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10764566314312009714815065 8073424735734007286111299)
            ·
              refine ⟨12110137103601010929166949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8073424735734007286111299 12110137103601010929166949)
              ·
                refine ⟨2270650706925189549218803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12110137103601010929166949 2270650706925189549218803)
                ·
                  refine ⟨3405976060387784323828205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2270650706925189549218803 3405976060387784323828205)
                  ·
                    refine ⟨1277241022645419121435577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3405976060387784323828205 1277241022645419121435577)
                    ·
                      rfl

theorem cell22_3731127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 1, 4, 1, 3].length) (baseStart_3731127 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3731127 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3731127 prefixEnd_3731127 := by exact prefixLift 3731127
  have htrace : WordTrace (prefixWord ++ tailWord_3731127) baseStart_3731127 baseEnd_3731127 := by
    simpa [prefixWord, tailWord_3731127, baseEnd_3731127] using wordTrace_append hprefix tailTrace_3731127
  have hstable : (prefixWord ++ tailWord_3731127).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3731127).length < 2 ^ (prefixWord ++ tailWord_3731127).sum := by decide
  have hdescent : baseEnd_3731127 < baseStart_3731127 := by decide
  rcases family_descends (prefixWord ++ tailWord_3731127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3731153 : List Nat := [1, 2, 2, 1, 2, 4, 2, 1, 3, 4]
def baseStart_3731153 : Nat := 118140960795 + 3731153 * 2 ^ 59
def prefixEnd_3731153 : Nat := 4983230072969 + 3 ^ 40 * 3731153 * 2
def baseEnd_3731153 : Nat := 1277249922976763720285497

theorem tailTrace_3731153 : CollatzResearch.WordTrace tailWord_3731153 prefixEnd_3731153 1277249922976763720285497 := by
  unfold tailWord_3731153
  simp only [CollatzResearch.WordTrace]
  refine ⟨136086329851677386045022113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90724219901118257363348075 136086329851677386045022113)
  ·
    refine ⟨102064747388758039533766585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136086329851677386045022113 102064747388758039533766585)
    ·
      refine ⟨76548560541568529650324939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102064747388758039533766585 76548560541568529650324939)
      ·
        refine ⟨114822840812352794475487409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76548560541568529650324939 114822840812352794475487409)
        ·
          refine ⟨86117130609264595856615557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114822840812352794475487409 86117130609264595856615557)
          ·
            refine ⟨16146961989237111723115417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 86117130609264595856615557 16146961989237111723115417)
            ·
              refine ⟨12110221491927833792336563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16146961989237111723115417 12110221491927833792336563)
              ·
                refine ⟨18165332237891750688504845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12110221491927833792336563 18165332237891750688504845)
                ·
                  refine ⟨6811999589209406508189317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18165332237891750688504845 6811999589209406508189317)
                  ·
                    refine ⟨1277249922976763720285497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6811999589209406508189317 1277249922976763720285497)
                    ·
                      rfl

theorem cell22_3731153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 2, 1, 3, 4].length) (baseStart_3731153 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3731153 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3731153 prefixEnd_3731153 := by exact prefixLift 3731153
  have htrace : WordTrace (prefixWord ++ tailWord_3731153) baseStart_3731153 baseEnd_3731153 := by
    simpa [prefixWord, tailWord_3731153, baseEnd_3731153] using wordTrace_append hprefix tailTrace_3731153
  have hstable : (prefixWord ++ tailWord_3731153).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3731153).length < 2 ^ (prefixWord ++ tailWord_3731153).sum := by decide
  have hdescent : baseEnd_3731153 < baseStart_3731153 := by decide
  rcases family_descends (prefixWord ++ tailWord_3731153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3731185 : List Nat := [1, 2, 2, 2, 2, 3, 2, 4, 4]
def baseStart_3731185 : Nat := 118140960795 + 3731185 * 2 ^ 59
def prefixEnd_3731185 : Nat := 4983230072969 + 3 ^ 40 * 3731185 * 2
def baseEnd_3731185 : Nat := 425753625743575434495133

theorem tailTrace_3731185 : CollatzResearch.WordTrace tailWord_3731185 prefixEnd_3731185 425753625743575434495133 := by
  unfold tailWord_3731185
  simp only [CollatzResearch.WordTrace]
  refine ⟨136087496987561455510187009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90724997991707637006791339 136087496987561455510187009)
  ·
    refine ⟨102065622740671091632640257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136087496987561455510187009 102065622740671091632640257)
    ·
      refine ⟨76549217055503318724480193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102065622740671091632640257 76549217055503318724480193)
      ·
        refine ⟨57411912791627489043360145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76549217055503318724480193 57411912791627489043360145)
        ·
          refine ⟨43058934593720616782520109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57411912791627489043360145 43058934593720616782520109)
          ·
            refine ⟨16147100472645231293445041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43058934593720616782520109 16147100472645231293445041)
            ·
              refine ⟨12110325354483923470083781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16147100472645231293445041 12110325354483923470083781)
              ·
                refine ⟨2270686003965735650640709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12110325354483923470083781 2270686003965735650640709)
                ·
                  refine ⟨425753625743575434495133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2270686003965735650640709 425753625743575434495133)
                  ·
                    rfl

theorem cell22_3731185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 2, 4, 4].length) (baseStart_3731185 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3731185 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3731185 prefixEnd_3731185 := by exact prefixLift 3731185
  have htrace : WordTrace (prefixWord ++ tailWord_3731185) baseStart_3731185 baseEnd_3731185 := by
    simpa [prefixWord, tailWord_3731185, baseEnd_3731185] using wordTrace_append hprefix tailTrace_3731185
  have hstable : (prefixWord ++ tailWord_3731185).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3731185).length < 2 ^ (prefixWord ++ tailWord_3731185).sum := by decide
  have hdescent : baseEnd_3731185 < baseStart_3731185 := by decide
  rcases family_descends (prefixWord ++ tailWord_3731185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3731251 : List Nat := [1, 1, 1, 2, 8, 1, 2, 1, 2, 3]
def baseStart_3731251 : Nat := 118140960795 + 3731251 * 2 ^ 59
def prefixEnd_3731251 : Nat := 4983230072969 + 3 ^ 40 * 3731251 * 2
def baseEnd_3731251 : Nat := 1277283470379524131335197

theorem tailTrace_3731251 : CollatzResearch.WordTrace tailWord_3731251 prefixEnd_3731251 1277283470379524131335197 := by
  unfold tailWord_3731251
  simp only [CollatzResearch.WordTrace]
  refine ⟨136089904205322348782089607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90726602803548232521393071 136089904205322348782089607)
  ·
    refine ⟨204134856307983523173134411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136089904205322348782089607 204134856307983523173134411)
    ·
      refine ⟨306202284461975284759701617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204134856307983523173134411 306202284461975284759701617)
      ·
        refine ⟨229651713346481463569776213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 306202284461975284759701617 229651713346481463569776213)
        ·
          refine ⟨2691231015779079651208315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 229651713346481463569776213 2691231015779079651208315)
          ·
            refine ⟨4036846523668619476812473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2691231015779079651208315 4036846523668619476812473)
            ·
              refine ⟨3027634892751464607609355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4036846523668619476812473 3027634892751464607609355)
              ·
                refine ⟨4541452339127196911414033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3027634892751464607609355 4541452339127196911414033)
                ·
                  refine ⟨3406089254345397683560525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4541452339127196911414033 3406089254345397683560525)
                  ·
                    refine ⟨1277283470379524131335197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3406089254345397683560525 1277283470379524131335197)
                    ·
                      rfl

theorem cell22_3731251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 8, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 8, 1, 2, 1, 2, 3].length) (baseStart_3731251 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3731251 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3731251 prefixEnd_3731251 := by exact prefixLift 3731251
  have htrace : WordTrace (prefixWord ++ tailWord_3731251) baseStart_3731251 baseEnd_3731251 := by
    simpa [prefixWord, tailWord_3731251, baseEnd_3731251] using wordTrace_append hprefix tailTrace_3731251
  have hstable : (prefixWord ++ tailWord_3731251).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3731251).length < 2 ^ (prefixWord ++ tailWord_3731251).sum := by decide
  have hdescent : baseEnd_3731251 < baseStart_3731251 := by decide
  rcases family_descends (prefixWord ++ tailWord_3731251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3731296 : List Nat := [2, 1, 1, 3, 3, 4, 2, 2, 1, 3]
def baseStart_3731296 : Nat := 118140960795 + 3731296 * 2 ^ 59
def prefixEnd_3731296 : Nat := 4983230072969 + 3 ^ 40 * 3731296 * 2
def baseEnd_3731296 : Nat := 1277298874799159013960059

theorem tailTrace_3731296 : CollatzResearch.WordTrace tailWord_3731296 prefixEnd_3731296 1277298874799159013960059 := by
  unfold tailWord_3731296
  simp only [CollatzResearch.WordTrace]
  refine ⟨68045772745079660733738871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90727696993439547644985161 68045772745079660733738871)
  ·
    refine ⟨102068659117619491100608307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68045772745079660733738871 102068659117619491100608307)
    ·
      refine ⟨153102988676429236650912461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102068659117619491100608307 153102988676429236650912461)
      ·
        refine ⟨57413620753660963744092173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 153102988676429236650912461 57413620753660963744092173)
        ·
          refine ⟨21530107782622861404034565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57413620753660963744092173 21530107782622861404034565)
          ·
            refine ⟨4036895209241786513256481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21530107782622861404034565 4036895209241786513256481)
            ·
              refine ⟨3027671406931339884942361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4036895209241786513256481 3027671406931339884942361)
              ·
                refine ⟨2270753555198504913706771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3027671406931339884942361 2270753555198504913706771)
                ·
                  refine ⟨3406130332797757370560157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2270753555198504913706771 3406130332797757370560157)
                  ·
                    refine ⟨1277298874799159013960059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3406130332797757370560157 1277298874799159013960059)
                    ·
                      rfl

theorem cell22_3731296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 4, 2, 2, 1, 3].length) (baseStart_3731296 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3731296 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3731296 prefixEnd_3731296 := by exact prefixLift 3731296
  have htrace : WordTrace (prefixWord ++ tailWord_3731296) baseStart_3731296 baseEnd_3731296 := by
    simpa [prefixWord, tailWord_3731296, baseEnd_3731296] using wordTrace_append hprefix tailTrace_3731296
  have hstable : (prefixWord ++ tailWord_3731296).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3731296).length < 2 ^ (prefixWord ++ tailWord_3731296).sum := by decide
  have hdescent : baseEnd_3731296 < baseStart_3731296 := by decide
  rcases family_descends (prefixWord ++ tailWord_3731296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3731337 : List Nat := [1, 2, 1, 1, 5, 1, 4, 3, 4]
def baseStart_3731337 : Nat := 118140960795 + 3731337 * 2 ^ 59
def prefixEnd_3731337 : Nat := 4983230072969 + 3 ^ 40 * 3731337 * 2
def baseEnd_3731337 : Nat := 425770969979016191228311

theorem tailTrace_3731337 : CollatzResearch.WordTrace tailWord_3731337 prefixEnd_3731337 425770969979016191228311 := by
  unfold tailWord_3731337
  simp only [CollatzResearch.WordTrace]
  refine ⟨136093040883010785469720265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90728693922007190313146843 136093040883010785469720265)
  ·
    refine ⟨102069780662258089102290199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136093040883010785469720265 102069780662258089102290199)
    ·
      refine ⟨153104670993387133653435299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102069780662258089102290199 153104670993387133653435299)
      ·
        refine ⟨229657006490080700480152949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153104670993387133653435299 229657006490080700480152949)
        ·
          refine ⟨21530344358445065670014339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 229657006490080700480152949 21530344358445065670014339)
          ·
            refine ⟨32295516537667598505021509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21530344358445065670014339 32295516537667598505021509)
            ·
              refine ⟨6055409350812674719691533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32295516537667598505021509 6055409350812674719691533)
              ·
                refine ⟨2270778506554753019884325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6055409350812674719691533 2270778506554753019884325)
                ·
                  refine ⟨425770969979016191228311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2270778506554753019884325 425770969979016191228311)
                  ·
                    rfl

theorem cell22_3731337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 4, 3, 4].length) (baseStart_3731337 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3731337 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3731337 prefixEnd_3731337 := by exact prefixLift 3731337
  have htrace : WordTrace (prefixWord ++ tailWord_3731337) baseStart_3731337 baseEnd_3731337 := by
    simpa [prefixWord, tailWord_3731337, baseEnd_3731337] using wordTrace_append hprefix tailTrace_3731337
  have hstable : (prefixWord ++ tailWord_3731337).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3731337).length < 2 ^ (prefixWord ++ tailWord_3731337).sum := by decide
  have hdescent : baseEnd_3731337 < baseStart_3731337 := by decide
  rcases family_descends (prefixWord ++ tailWord_3731337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3731388 : List Nat := [2, 2, 2, 5, 2, 1, 1, 3, 4]
def baseStart_3731388 : Nat := 118140960795 + 3731388 * 2 ^ 59
def prefixEnd_3731388 : Nat := 4983230072969 + 3 ^ 40 * 3731388 * 2
def baseEnd_3731388 : Nat := 425776789426433813553259

theorem tailTrace_3731388 : CollatzResearch.WordTrace tailWord_3731388 prefixEnd_3731388 425776789426433813553259 := by
  unfold tailWord_3731388
  simp only [CollatzResearch.WordTrace]
  refine ⟨68047450502913010589913409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90729934003884014119884545 68047450502913010589913409)
  ·
    refine ⟨51035587877184757942435057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68047450502913010589913409 51035587877184757942435057)
    ·
      refine ⟨38276690907888568456826293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51035587877184757942435057 38276690907888568456826293)
      ·
        refine ⟨3588439772614553292827465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 38276690907888568456826293 3588439772614553292827465)
        ·
          refine ⟨2691329829460914969620599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3588439772614553292827465 2691329829460914969620599)
          ·
            refine ⟨4036994744191372454430899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2691329829460914969620599 4036994744191372454430899)
            ·
              refine ⟨6055492116287058681646349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4036994744191372454430899 6055492116287058681646349)
              ·
                refine ⟨2270809543607647005617381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6055492116287058681646349 2270809543607647005617381)
                ·
                  refine ⟨425776789426433813553259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2270809543607647005617381 425776789426433813553259)
                  ·
                    rfl

theorem cell22_3731388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 2, 1, 1, 3, 4].length) (baseStart_3731388 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3731388 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3731388 prefixEnd_3731388 := by exact prefixLift 3731388
  have htrace : WordTrace (prefixWord ++ tailWord_3731388) baseStart_3731388 baseEnd_3731388 := by
    simpa [prefixWord, tailWord_3731388, baseEnd_3731388] using wordTrace_append hprefix tailTrace_3731388
  have hstable : (prefixWord ++ tailWord_3731388).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3731388).length < 2 ^ (prefixWord ++ tailWord_3731388).sum := by decide
  have hdescent : baseEnd_3731388 < baseStart_3731388 := by decide
  rcases family_descends (prefixWord ++ tailWord_3731388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3731425 : List Nat := [1, 2, 3, 1, 2, 1, 2, 3, 2, 5]
def baseStart_3731425 : Nat := 118140960795 + 3731425 * 2 ^ 59
def prefixEnd_3731425 : Nat := 4983230072969 + 3 ^ 40 * 3731425 * 2
def baseEnd_3731425 : Nat := 1277343034135445677484663

theorem tailTrace_3731425 : CollatzResearch.WordTrace tailWord_3731425 prefixEnd_3731425 1277343034135445677484663 := by
  unfold tailWord_3731425
  simp only [CollatzResearch.WordTrace]
  refine ⟨136096250506691976498923729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90730833671127984332615819 136096250506691976498923729)
  ·
    refine ⟨102072187880018982374192797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136096250506691976498923729 102072187880018982374192797)
    ·
      refine ⟨38277070455007118390322299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102072187880018982374192797 38277070455007118390322299)
      ·
        refine ⟨57415605682510677585483449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38277070455007118390322299 57415605682510677585483449)
        ·
          refine ⟨43061704261883008189112587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57415605682510677585483449 43061704261883008189112587)
          ·
            refine ⟨64592556392824512283668881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43061704261883008189112587 64592556392824512283668881)
            ·
              refine ⟨48444417294618384212751661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64592556392824512283668881 48444417294618384212751661)
              ·
                refine ⟨18166656485481894079781873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48444417294618384212751661 18166656485481894079781873)
                ·
                  refine ⟨13624992364111420559836405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18166656485481894079781873 13624992364111420559836405)
                  ·
                    refine ⟨1277343034135445677484663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13624992364111420559836405 1277343034135445677484663)
                    ·
                      rfl

theorem cell22_3731425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 3, 2, 5].length) (baseStart_3731425 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3731425 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3731425 prefixEnd_3731425 := by exact prefixLift 3731425
  have htrace : WordTrace (prefixWord ++ tailWord_3731425) baseStart_3731425 baseEnd_3731425 := by
    simpa [prefixWord, tailWord_3731425, baseEnd_3731425] using wordTrace_append hprefix tailTrace_3731425
  have hstable : (prefixWord ++ tailWord_3731425).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3731425).length < 2 ^ (prefixWord ++ tailWord_3731425).sum := by decide
  have hdescent : baseEnd_3731425 < baseStart_3731425 := by decide
  rcases family_descends (prefixWord ++ tailWord_3731425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3731427 : List Nat := [1, 1, 1, 6, 1, 3, 1, 3, 5]
def baseStart_3731427 : Nat := 118140960795 + 3731427 * 2 ^ 59
def prefixEnd_3731427 : Nat := 4983230072969 + 3 ^ 40 * 3731427 * 2
def baseEnd_3731427 : Nat := 425781239592106112978219

theorem tailTrace_3731427 : CollatzResearch.WordTrace tailWord_3731427 prefixEnd_3731427 425781239592106112978219 := by
  unfold tailWord_3731427
  simp only [CollatzResearch.WordTrace]
  refine ⟨136096323452684730840496535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90730882301789820560331023 136096323452684730840496535)
  ·
    refine ⟨204144485179027096260744803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136096323452684730840496535 204144485179027096260744803)
    ·
      refine ⟨306216727768540644391117205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204144485179027096260744803 306216727768540644391117205)
      ·
        refine ⟨14353909114150342705833619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 306216727768540644391117205 14353909114150342705833619)
        ·
          refine ⟨21530863671225514058750429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14353909114150342705833619 21530863671225514058750429)
          ·
            refine ⟨8074073876709567772031411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21530863671225514058750429 8074073876709567772031411)
            ·
              refine ⟨12111110815064351658047117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8074073876709567772031411 12111110815064351658047117)
              ·
                refine ⟨4541666555649131871767669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12111110815064351658047117 4541666555649131871767669)
                ·
                  refine ⟨425781239592106112978219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4541666555649131871767669 425781239592106112978219)
                  ·
                    rfl

theorem cell22_3731427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 1, 3, 5].length) (baseStart_3731427 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3731427 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3731427 prefixEnd_3731427 := by exact prefixLift 3731427
  have htrace : WordTrace (prefixWord ++ tailWord_3731427) baseStart_3731427 baseEnd_3731427 := by
    simpa [prefixWord, tailWord_3731427, baseEnd_3731427] using wordTrace_append hprefix tailTrace_3731427
  have hstable : (prefixWord ++ tailWord_3731427).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3731427).length < 2 ^ (prefixWord ++ tailWord_3731427).sum := by decide
  have hdescent : baseEnd_3731427 < baseStart_3731427 := by decide
  rcases family_descends (prefixWord ++ tailWord_3731427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3731472 : List Nat := [2, 1, 1, 1, 1, 1, 1, 10, 4]
def baseStart_3731472 : Nat := 118140960795 + 3731472 * 2 ^ 59
def prefixEnd_3731472 : Nat := 4983230072969 + 3 ^ 40 * 3731472 * 2
def baseEnd_3731472 : Nat := 425786374398651073853173

theorem tailTrace_3731472 : CollatzResearch.WordTrace tailWord_3731472 prefixEnd_3731472 425786374398651073853173 := by
  unfold tailWord_3731472
  simp only [CollatzResearch.WordTrace]
  refine ⟨68048982368760851762942335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90731976491681135683923113 68048982368760851762942335)
  ·
    refine ⟨102073473553141277644413503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68048982368760851762942335 102073473553141277644413503)
    ·
      refine ⟨153110210329711916466620255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102073473553141277644413503 153110210329711916466620255)
      ·
        refine ⟨229665315494567874699930383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153110210329711916466620255 229665315494567874699930383)
        ·
          refine ⟨344497973241851812049895575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 229665315494567874699930383 344497973241851812049895575)
          ·
            refine ⟨516746959862777718074843363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 344497973241851812049895575 516746959862777718074843363)
            ·
              refine ⟨775120439794166577112265045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 516746959862777718074843363 775120439794166577112265045)
              ·
                refine ⟨2270860663459472393883589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 775120439794166577112265045 2270860663459472393883589)
                ·
                  refine ⟨425786374398651073853173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2270860663459472393883589 425786374398651073853173)
                  ·
                    rfl

theorem cell22_3731472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 10, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 10, 4].length) (baseStart_3731472 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3731472 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3731472 prefixEnd_3731472 := by exact prefixLift 3731472
  have htrace : WordTrace (prefixWord ++ tailWord_3731472) baseStart_3731472 baseEnd_3731472 := by
    simpa [prefixWord, tailWord_3731472, baseEnd_3731472] using wordTrace_append hprefix tailTrace_3731472
  have hstable : (prefixWord ++ tailWord_3731472).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3731472).length < 2 ^ (prefixWord ++ tailWord_3731472).sum := by decide
  have hdescent : baseEnd_3731472 < baseStart_3731472 := by decide
  rcases family_descends (prefixWord ++ tailWord_3731472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3731476 : List Nat := [2, 4, 3, 2, 1, 1, 1, 1, 2, 5]
def baseStart_3731476 : Nat := 118140960795 + 3731476 * 2 ^ 59
def prefixEnd_3731476 : Nat := 4983230072969 + 3 ^ 40 * 3731476 * 2
def baseEnd_3731476 : Nat := 1277360492477698544459507

theorem tailTrace_3731476 : CollatzResearch.WordTrace tailWord_3731476 prefixEnd_3731476 1277360492477698544459507 := by
  unfold tailWord_3731476
  simp only [CollatzResearch.WordTrace]
  refine ⟨68049055314753606104515141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90732073753004808139353521 68049055314753606104515141)
  ·
    refine ⟨12759197871516301144596589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 68049055314753606104515141 12759197871516301144596589)
    ·
      refine ⟨4784699201818612929223721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12759197871516301144596589 4784699201818612929223721)
      ·
        refine ⟨3588524401363959696917791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4784699201818612929223721 3588524401363959696917791)
        ·
          refine ⟨5382786602045939545376687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3588524401363959696917791 5382786602045939545376687)
          ·
            refine ⟨8074179903068909318065031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5382786602045939545376687 8074179903068909318065031)
            ·
              refine ⟨12111269854603363977097547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8074179903068909318065031 12111269854603363977097547)
              ·
                refine ⟨18166904781905045965646321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12111269854603363977097547 18166904781905045965646321)
                ·
                  refine ⟨13625178586428784474234741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18166904781905045965646321 13625178586428784474234741)
                  ·
                    refine ⟨1277360492477698544459507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13625178586428784474234741 1277360492477698544459507)
                    ·
                      rfl

theorem cell22_3731476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 1, 1, 2, 5].length) (baseStart_3731476 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3731476 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3731476 prefixEnd_3731476 := by exact prefixLift 3731476
  have htrace : WordTrace (prefixWord ++ tailWord_3731476) baseStart_3731476 baseEnd_3731476 := by
    simpa [prefixWord, tailWord_3731476, baseEnd_3731476] using wordTrace_append hprefix tailTrace_3731476
  have hstable : (prefixWord ++ tailWord_3731476).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3731476).length < 2 ^ (prefixWord ++ tailWord_3731476).sum := by decide
  have hdescent : baseEnd_3731476 < baseStart_3731476 := by decide
  rcases family_descends (prefixWord ++ tailWord_3731476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3731487 : List Nat := [1, 1, 2, 4, 1, 2, 4, 1, 1, 5]
def baseStart_3731487 : Nat := 118140960795 + 3731487 * 2 ^ 59
def prefixEnd_3731487 : Nat := 4983230072969 + 3 ^ 40 * 3731487 * 2
def baseEnd_3731487 : Nat := 1277364258002498182434473

theorem tailTrace_3731487 : CollatzResearch.WordTrace tailWord_3731487 prefixEnd_3731487 1277364258002498182434473 := by
  unfold tailWord_3731487
  simp only [CollatzResearch.WordTrace]
  refine ⟨136098511832467361087680715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90732341221644907391787143 136098511832467361087680715)
  ·
    refine ⟨204147767748701041631521073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136098511832467361087680715 204147767748701041631521073)
    ·
      refine ⟨153110825811525781223640805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 204147767748701041631521073 153110825811525781223640805)
      ·
        refine ⟨28708279839661083979432651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 153110825811525781223640805 28708279839661083979432651)
        ·
          refine ⟨43062419759491625969148977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28708279839661083979432651 43062419759491625969148977)
          ·
            refine ⟨32296814819618719476861733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43062419759491625969148977 32296814819618719476861733)
            ·
              refine ⟨6055652778678509901911575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32296814819618719476861733 6055652778678509901911575)
              ·
                refine ⟨9083479168017764852867363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6055652778678509901911575 9083479168017764852867363)
                ·
                  refine ⟨13625218752026647279301045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9083479168017764852867363 13625218752026647279301045)
                  ·
                    refine ⟨1277364258002498182434473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13625218752026647279301045 1277364258002498182434473)
                    ·
                      rfl

theorem cell22_3731487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 4, 1, 1, 5].length) (baseStart_3731487 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3731487 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3731487 prefixEnd_3731487 := by exact prefixLift 3731487
  have htrace : WordTrace (prefixWord ++ tailWord_3731487) baseStart_3731487 baseEnd_3731487 := by
    simpa [prefixWord, tailWord_3731487, baseEnd_3731487] using wordTrace_append hprefix tailTrace_3731487
  have hstable : (prefixWord ++ tailWord_3731487).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3731487).length < 2 ^ (prefixWord ++ tailWord_3731487).sum := by decide
  have hdescent : baseEnd_3731487 < baseStart_3731487 := by decide
  rcases family_descends (prefixWord ++ tailWord_3731487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3731521 : List Nat := [1, 2, 5, 1, 2, 1, 3, 2, 2, 3]
def baseStart_3731521 : Nat := 118140960795 + 3731521 * 2 ^ 59
def prefixEnd_3731521 : Nat := 4983230072969 + 3 ^ 40 * 3731521 * 2
def baseEnd_3731521 : Nat := 1277375896897333427084369

theorem tailTrace_3731521 : CollatzResearch.WordTrace tailWord_3731521 prefixEnd_3731521 1277375896897333427084369 := by
  unfold tailWord_3731521
  simp only [CollatzResearch.WordTrace]
  refine ⟨136099751914344184894418417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90733167942896123262945611 136099751914344184894418417)
  ·
    refine ⟨102074813935758138670813813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136099751914344184894418417 102074813935758138670813813)
    ·
      refine ⟨9569513806477325500388795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 102074813935758138670813813 9569513806477325500388795)
      ·
        refine ⟨14354270709715988250583193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9569513806477325500388795 14354270709715988250583193)
        ·
          refine ⟨10765703032286991187937395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14354270709715988250583193 10765703032286991187937395)
          ·
            refine ⟨16148554548430486781906093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10765703032286991187937395 16148554548430486781906093)
            ·
              refine ⟨6055707955661432543214785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16148554548430486781906093 6055707955661432543214785)
              ·
                refine ⟨4541780966746074407411089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6055707955661432543214785 4541780966746074407411089)
                ·
                  refine ⟨3406335725059555805558317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4541780966746074407411089 3406335725059555805558317)
                  ·
                    refine ⟨1277375896897333427084369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3406335725059555805558317 1277375896897333427084369)
                    ·
                      rfl

theorem cell22_3731521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 3, 2, 2, 3].length) (baseStart_3731521 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3731521 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3731521 prefixEnd_3731521 := by exact prefixLift 3731521
  have htrace : WordTrace (prefixWord ++ tailWord_3731521) baseStart_3731521 baseEnd_3731521 := by
    simpa [prefixWord, tailWord_3731521, baseEnd_3731521] using wordTrace_append hprefix tailTrace_3731521
  have hstable : (prefixWord ++ tailWord_3731521).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3731521).length < 2 ^ (prefixWord ++ tailWord_3731521).sum := by decide
  have hdescent : baseEnd_3731521 < baseStart_3731521 := by decide
  rcases family_descends (prefixWord ++ tailWord_3731521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3731538 : List Nat := [3, 2, 2, 1, 4, 1, 3, 1, 2, 3]
def baseStart_3731538 : Nat := 118140960795 + 3731538 * 2 ^ 59
def prefixEnd_3731538 : Nat := 4983230072969 + 3 ^ 40 * 3731538 * 2
def baseEnd_3731538 : Nat := 1277381716344751049409317

theorem tailTrace_3731538 : CollatzResearch.WordTrace tailWord_3731538 prefixEnd_3731538 1277381716344751049409317 := by
  unfold tailWord_3731538
  simp only [CollatzResearch.WordTrace]
  refine ⟨34025092988820649199446817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90733581303521731198524845 34025092988820649199446817)
  ·
    refine ⟨25518819741615486899585113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34025092988820649199446817 25518819741615486899585113)
    ·
      refine ⟨19139114806211615174688835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25518819741615486899585113 19139114806211615174688835)
      ·
        refine ⟨28708672209317422762033253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19139114806211615174688835 28708672209317422762033253)
        ·
          refine ⟨5382876039247016767881235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28708672209317422762033253 5382876039247016767881235)
          ·
            refine ⟨8074314058870525151821853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5382876039247016767881235 8074314058870525151821853)
            ·
              refine ⟨3027867772076446931933195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8074314058870525151821853 3027867772076446931933195)
              ·
                refine ⟨4541801658114670397899793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3027867772076446931933195 4541801658114670397899793)
                ·
                  refine ⟨3406351243586002798424845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4541801658114670397899793 3406351243586002798424845)
                  ·
                    refine ⟨1277381716344751049409317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3406351243586002798424845 1277381716344751049409317)
                    ·
                      rfl

theorem cell22_3731538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 3, 1, 2, 3].length) (baseStart_3731538 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3731538 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3731538 prefixEnd_3731538 := by exact prefixLift 3731538
  have htrace : WordTrace (prefixWord ++ tailWord_3731538) baseStart_3731538 baseEnd_3731538 := by
    simpa [prefixWord, tailWord_3731538, baseEnd_3731538] using wordTrace_append hprefix tailTrace_3731538
  have hstable : (prefixWord ++ tailWord_3731538).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3731538).length < 2 ^ (prefixWord ++ tailWord_3731538).sum := by decide
  have hdescent : baseEnd_3731538 < baseStart_3731538 := by decide
  rcases family_descends (prefixWord ++ tailWord_3731538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3731684 : List Nat := [2, 3, 1, 1, 1, 2, 1, 1, 7, 3]
def baseStart_3731684 : Nat := 118140960795 + 3731684 * 2 ^ 59
def prefixEnd_3731684 : Nat := 4983230072969 + 3 ^ 40 * 3731684 * 2
def baseEnd_3731684 : Nat := 1277431695128455335258869

theorem tailTrace_3731684 : CollatzResearch.WordTrace tailWord_3731684 prefixEnd_3731684 1277431695128455335258869 := by
  unfold tailWord_3731684
  simp only [CollatzResearch.WordTrace]
  refine ⟨68052848506376831866301053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90737131341835775821734737 68052848506376831866301053)
  ·
    refine ⟨25519818189891311949862895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68052848506376831866301053 25519818189891311949862895)
    ·
      refine ⟨38279727284836967924794343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25519818189891311949862895 38279727284836967924794343)
      ·
        refine ⟨57419590927255451887191515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38279727284836967924794343 57419590927255451887191515)
        ·
          refine ⟨86129386390883177830787273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57419590927255451887191515 86129386390883177830787273)
          ·
            refine ⟨64597039793162383373090455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86129386390883177830787273 64597039793162383373090455)
            ·
              refine ⟨96895559689743575059635683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64597039793162383373090455 96895559689743575059635683)
              ·
                refine ⟨145343339534615362589453525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96895559689743575059635683 145343339534615362589453525)
                ·
                  refine ⟨3406484520342547560690317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 145343339534615362589453525 3406484520342547560690317)
                  ·
                    refine ⟨1277431695128455335258869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3406484520342547560690317 1277431695128455335258869)
                    ·
                      rfl

theorem cell22_3731684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 1, 7, 3].length) (baseStart_3731684 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3731684 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3731684 prefixEnd_3731684 := by exact prefixLift 3731684
  have htrace : WordTrace (prefixWord ++ tailWord_3731684) baseStart_3731684 baseEnd_3731684 := by
    simpa [prefixWord, tailWord_3731684, baseEnd_3731684] using wordTrace_append hprefix tailTrace_3731684
  have hstable : (prefixWord ++ tailWord_3731684).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3731684).length < 2 ^ (prefixWord ++ tailWord_3731684).sum := by decide
  have hdescent : baseEnd_3731684 < baseStart_3731684 := by decide
  rcases family_descends (prefixWord ++ tailWord_3731684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3731727 : List Nat := [1, 1, 2, 1, 1, 1, 3, 2, 2, 8]
def baseStart_3731727 : Nat := 118140960795 + 3731727 * 2 ^ 59
def prefixEnd_3731727 : Nat := 4983230072969 + 3 ^ 40 * 3731727 * 2
def baseEnd_3731727 : Nat := 1277446414907217556433737

theorem tailTrace_3731727 : CollatzResearch.WordTrace tailWord_3731727 prefixEnd_3731727 1277446414907217556433737 := by
  unfold tailWord_3731727
  simp only [CollatzResearch.WordTrace]
  refine ⟨136107265351597882076417435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90738176901065254717611623 136107265351597882076417435)
  ·
    refine ⟨204160898027396823114626153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136107265351597882076417435 204160898027396823114626153)
    ·
      refine ⟨153120673520547617335969615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 204160898027396823114626153 153120673520547617335969615)
      ·
        refine ⟨229681010280821426003954423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153120673520547617335969615 229681010280821426003954423)
        ·
          refine ⟨344521515421232139005931635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 229681010280821426003954423 344521515421232139005931635)
          ·
            refine ⟨516782273131848208508897453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 344521515421232139005931635 516782273131848208508897453)
            ·
              refine ⟨193793352424443078190836545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 516782273131848208508897453 193793352424443078190836545)
              ·
                refine ⟨145345014318332308643127409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 193793352424443078190836545 145345014318332308643127409)
                ·
                  refine ⟨109008760738749231482345557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 145345014318332308643127409 109008760738749231482345557)
                  ·
                    refine ⟨1277446414907217556433737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 109008760738749231482345557 1277446414907217556433737)
                    ·
                      rfl

theorem cell22_3731727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 2, 2, 8].length) (baseStart_3731727 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3731727 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3731727 prefixEnd_3731727 := by exact prefixLift 3731727
  have htrace : WordTrace (prefixWord ++ tailWord_3731727) baseStart_3731727 baseEnd_3731727 := by
    simpa [prefixWord, tailWord_3731727, baseEnd_3731727] using wordTrace_append hprefix tailTrace_3731727
  have hstable : (prefixWord ++ tailWord_3731727).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3731727).length < 2 ^ (prefixWord ++ tailWord_3731727).sum := by decide
  have hdescent : baseEnd_3731727 < baseStart_3731727 := by decide
  rcases family_descends (prefixWord ++ tailWord_3731727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3731735 : List Nat := [1, 1, 3, 4, 1, 4, 1, 3, 1, 3]
def baseStart_3731735 : Nat := 118140960795 + 3731735 * 2 ^ 59
def prefixEnd_3731735 : Nat := 4983230072969 + 3 ^ 40 * 3731735 * 2
def baseEnd_3731735 : Nat := 1277449153470708202233713

theorem tailTrace_3731735 : CollatzResearch.WordTrace tailWord_3731735 prefixEnd_3731735 1277449153470708202233713 := by
  unfold tailWord_3731735
  simp only [CollatzResearch.WordTrace]
  refine ⟨136107557135568899442708659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90738371423712599628472439 136107557135568899442708659)
  ·
    refine ⟨204161335703353349164062989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136107557135568899442708659 204161335703353349164062989)
    ·
      refine ⟨76560500888757505936523621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 204161335703353349164062989 76560500888757505936523621)
      ·
        refine ⟨14355093916642032363098179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 76560500888757505936523621 14355093916642032363098179)
        ·
          refine ⟨21532640874963048544647269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14355093916642032363098179 21532640874963048544647269)
          ·
            refine ⟨4037370164055571602121363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21532640874963048544647269 4037370164055571602121363)
            ·
              refine ⟨6056055246083357403182045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4037370164055571602121363 6056055246083357403182045)
              ·
                refine ⟨2271020717281259026193267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6056055246083357403182045 2271020717281259026193267)
                ·
                  refine ⟨3406531075921888539289901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2271020717281259026193267 3406531075921888539289901)
                  ·
                    refine ⟨1277449153470708202233713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3406531075921888539289901 1277449153470708202233713)
                    ·
                      rfl

theorem cell22_3731735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 4, 1, 3, 1, 3].length) (baseStart_3731735 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3731735 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3731735 prefixEnd_3731735 := by exact prefixLift 3731735
  have htrace : WordTrace (prefixWord ++ tailWord_3731735) baseStart_3731735 baseEnd_3731735 := by
    simpa [prefixWord, tailWord_3731735, baseEnd_3731735] using wordTrace_append hprefix tailTrace_3731735
  have hstable : (prefixWord ++ tailWord_3731735).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3731735).length < 2 ^ (prefixWord ++ tailWord_3731735).sum := by decide
  have hdescent : baseEnd_3731735 < baseStart_3731735 := by decide
  rcases family_descends (prefixWord ++ tailWord_3731735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3731752 : List Nat := [2, 1, 5, 1, 3, 1, 3, 2, 1, 3]
def baseStart_3731752 : Nat := 118140960795 + 3731752 * 2 ^ 59
def prefixEnd_3731752 : Nat := 4983230072969 + 3 ^ 40 * 3731752 * 2
def baseEnd_3731752 : Nat := 1277454972918125824558661

theorem tailTrace_3731752 : CollatzResearch.WordTrace tailWord_3731752 prefixEnd_3731752 1277454972918125824558661 := by
  unfold tailWord_3731752
  simp only [CollatzResearch.WordTrace]
  refine ⟨68054088588253655673038755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90738784784338207564051673 68054088588253655673038755)
  ·
    refine ⟨102081132882380483509558133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68054088588253655673038755 102081132882380483509558133)
    ·
      refine ⟨9570106207723170329021075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 102081132882380483509558133 9570106207723170329021075)
      ·
        refine ⟨14355159311584755493531613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9570106207723170329021075 14355159311584755493531613)
        ·
          refine ⟨5383184741844283310074355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14355159311584755493531613 5383184741844283310074355)
          ·
            refine ⟨8074777112766424965111533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5383184741844283310074355 8074777112766424965111533)
            ·
              refine ⟨3028041417287409361916825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8074777112766424965111533 3028041417287409361916825)
              ·
                refine ⟨2271031062965557021437619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3028041417287409361916825 2271031062965557021437619)
                ·
                  refine ⟨3406546594448335532156429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2271031062965557021437619 3406546594448335532156429)
                  ·
                    refine ⟨1277454972918125824558661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3406546594448335532156429 1277454972918125824558661)
                    ·
                      rfl

theorem cell22_3731752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 3, 2, 1, 3].length) (baseStart_3731752 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3731752 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3731752 prefixEnd_3731752 := by exact prefixLift 3731752
  have htrace : WordTrace (prefixWord ++ tailWord_3731752) baseStart_3731752 baseEnd_3731752 := by
    simpa [prefixWord, tailWord_3731752, baseEnd_3731752] using wordTrace_append hprefix tailTrace_3731752
  have hstable : (prefixWord ++ tailWord_3731752).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3731752).length < 2 ^ (prefixWord ++ tailWord_3731752).sum := by decide
  have hdescent : baseEnd_3731752 < baseStart_3731752 := by decide
  rcases family_descends (prefixWord ++ tailWord_3731752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3731759 : List Nat := [1, 1, 2, 1, 2, 1, 7, 1, 6]
def baseStart_3731759 : Nat := 118140960795 + 3731759 * 2 ^ 59
def prefixEnd_3731759 : Nat := 4983230072969 + 3 ^ 40 * 3731759 * 2
def baseEnd_3731759 : Nat := 425819123053726713211213

theorem tailTrace_3731759 : CollatzResearch.WordTrace tailWord_3731759 prefixEnd_3731759 425819123053726713211213 := by
  unfold tailWord_3731759
  simp only [CollatzResearch.WordTrace]
  refine ⟨136108432487481951541582331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90738954991654634361054887 136108432487481951541582331)
  ·
    refine ⟨204162648731222927312373497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136108432487481951541582331 204162648731222927312373497)
    ·
      refine ⟨153121986548417195484280123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 204162648731222927312373497 153121986548417195484280123)
      ·
        refine ⟨229682979822625793226420185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153121986548417195484280123 229682979822625793226420185)
        ·
          refine ⟨172262234866969344919815139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 229682979822625793226420185 172262234866969344919815139)
          ·
            refine ⟨258393352300454017379722709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 172262234866969344919815139 258393352300454017379722709)
            ·
              refine ⟨6056094194541891032337251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 258393352300454017379722709 6056094194541891032337251)
              ·
                refine ⟨9084141291812836548505877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6056094194541891032337251 9084141291812836548505877)
                ·
                  refine ⟨425819123053726713211213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9084141291812836548505877 425819123053726713211213)
                  ·
                    rfl

theorem cell22_3731759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 7, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 7, 1, 6].length) (baseStart_3731759 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3731759 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3731759 prefixEnd_3731759 := by exact prefixLift 3731759
  have htrace : WordTrace (prefixWord ++ tailWord_3731759) baseStart_3731759 baseEnd_3731759 := by
    simpa [prefixWord, tailWord_3731759, baseEnd_3731759] using wordTrace_append hprefix tailTrace_3731759
  have hstable : (prefixWord ++ tailWord_3731759).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3731759).length < 2 ^ (prefixWord ++ tailWord_3731759).sum := by decide
  have hdescent : baseEnd_3731759 < baseStart_3731759 := by decide
  rcases family_descends (prefixWord ++ tailWord_3731759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3731810 : List Nat := [3, 3, 2, 1, 1, 2, 4, 2, 4]
def baseStart_3731810 : Nat := 118140960795 + 3731810 * 2 ^ 59
def prefixEnd_3731810 : Nat := 4983230072969 + 3 ^ 40 * 3731810 * 2
def baseEnd_3731810 : Nat := 425824942501144335536161

theorem tailTrace_3731810 : CollatzResearch.WordTrace tailWord_3731810 prefixEnd_3731810 425824942501144335536161 := by
  unfold tailWord_3731810
  simp only [CollatzResearch.WordTrace]
  refine ⟨34027573152574296812922221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90740195073531458167792589 34027573152574296812922221)
  ·
    refine ⟨12760339932215361304845833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34027573152574296812922221 12760339932215361304845833)
    ·
      refine ⟨9570254949161520978634375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12760339932215361304845833 9570254949161520978634375)
      ·
        refine ⟨14355382423742281467951563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9570254949161520978634375 14355382423742281467951563)
        ·
          refine ⟨21533073635613422201927345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14355382423742281467951563 21533073635613422201927345)
          ·
            refine ⟨16149805226710066651445509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21533073635613422201927345 16149805226710066651445509)
            ·
              refine ⟨3028088480008137497146033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16149805226710066651445509 3028088480008137497146033)
              ·
                refine ⟨2271066360006103122859525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3028088480008137497146033 2271066360006103122859525)
                ·
                  refine ⟨425824942501144335536161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2271066360006103122859525 425824942501144335536161)
                  ·
                    rfl

theorem cell22_3731810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 4, 2, 4].length) (baseStart_3731810 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3731810 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3731810 prefixEnd_3731810 := by exact prefixLift 3731810
  have htrace : WordTrace (prefixWord ++ tailWord_3731810) baseStart_3731810 baseEnd_3731810 := by
    simpa [prefixWord, tailWord_3731810, baseEnd_3731810] using wordTrace_append hprefix tailTrace_3731810
  have hstable : (prefixWord ++ tailWord_3731810).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3731810).length < 2 ^ (prefixWord ++ tailWord_3731810).sum := by decide
  have hdescent : baseEnd_3731810 < baseStart_3731810 := by decide
  rcases family_descends (prefixWord ++ tailWord_3731810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3731866 : List Nat := [3, 1, 1, 4, 1, 3, 1, 1, 7]
def baseStart_3731866 : Nat := 118140960795 + 3731866 * 2 ^ 59
def prefixEnd_3731866 : Nat := 4983230072969 + 3 ^ 40 * 3731866 * 2
def baseEnd_3731866 : Nat := 425831332482622509069437

theorem tailTrace_3731866 : CollatzResearch.WordTrace tailWord_3731866 prefixEnd_3731866 425831332482622509069437 := by
  unfold tailWord_3731866
  simp only [CollatzResearch.WordTrace]
  refine ⟨34028083774523577203931863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90741556732062872543818301 34028083774523577203931863)
  ·
    refine ⟨51042125661785365805897795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34028083774523577203931863 51042125661785365805897795)
    ·
      refine ⟨76563188492678048708846693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51042125661785365805897795 76563188492678048708846693)
      ·
        refine ⟨14355597842377134132908755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 76563188492678048708846693 14355597842377134132908755)
        ·
          refine ⟨21533396763565701199363133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14355597842377134132908755 21533396763565701199363133)
          ·
            refine ⟨8075023786337137949761175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21533396763565701199363133 8075023786337137949761175)
            ·
              refine ⟨12112535679505706924641763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8075023786337137949761175 12112535679505706924641763)
              ·
                refine ⟨18168803519258560386962645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12112535679505706924641763 18168803519258560386962645)
                ·
                  refine ⟨425831332482622509069437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18168803519258560386962645 425831332482622509069437)
                  ·
                    rfl

theorem cell22_3731866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 1, 1, 7].length) (baseStart_3731866 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3731866 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3731866 prefixEnd_3731866 := by exact prefixLift 3731866
  have htrace : WordTrace (prefixWord ++ tailWord_3731866) baseStart_3731866 baseEnd_3731866 := by
    simpa [prefixWord, tailWord_3731866, baseEnd_3731866] using wordTrace_append hprefix tailTrace_3731866
  have hstable : (prefixWord ++ tailWord_3731866).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3731866).length < 2 ^ (prefixWord ++ tailWord_3731866).sum := by decide
  have hdescent : baseEnd_3731866 < baseStart_3731866 := by decide
  rcases family_descends (prefixWord ++ tailWord_3731866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3731870 : List Nat := [4, 3, 1, 2, 1, 1, 1, 3, 3, 3]
def baseStart_3731870 : Nat := 118140960795 + 3731870 * 2 ^ 59
def prefixEnd_3731870 : Nat := 4983230072969 + 3 ^ 40 * 3731870 * 2
def baseEnd_3731870 : Nat := 1277495366729612850108299

theorem tailTrace_3731870 : CollatzResearch.WordTrace tailWord_3731870 prefixEnd_3731870 1277495366729612850108299 := by
  unfold tailWord_3731870
  simp only [CollatzResearch.WordTrace]
  refine ⟨17014060123759977187359133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 90741653993386544999248709 17014060123759977187359133)
  ·
    refine ⟨6380272546409991445259675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17014060123759977187359133 6380272546409991445259675)
    ·
      refine ⟨9570408819614987167889513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6380272546409991445259675 9570408819614987167889513)
      ·
        refine ⟨7177806614711240375917135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9570408819614987167889513 7177806614711240375917135)
        ·
          refine ⟨10766709922066860563875703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7177806614711240375917135 10766709922066860563875703)
          ·
            refine ⟨16150064883100290845813555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10766709922066860563875703 16150064883100290845813555)
            ·
              refine ⟨24225097324650436268720333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16150064883100290845813555 24225097324650436268720333)
              ·
                refine ⟨9084411496743913600770125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24225097324650436268720333 9084411496743913600770125)
                ·
                  refine ⟨3406654311278967600288797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9084411496743913600770125 3406654311278967600288797)
                  ·
                    refine ⟨1277495366729612850108299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3406654311278967600288797 1277495366729612850108299)
                    ·
                      rfl

theorem cell22_3731870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 3, 3, 3].length) (baseStart_3731870 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3731870 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3731870 prefixEnd_3731870 := by exact prefixLift 3731870
  have htrace : WordTrace (prefixWord ++ tailWord_3731870) baseStart_3731870 baseEnd_3731870 := by
    simpa [prefixWord, tailWord_3731870, baseEnd_3731870] using wordTrace_append hprefix tailTrace_3731870
  have hstable : (prefixWord ++ tailWord_3731870).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3731870).length < 2 ^ (prefixWord ++ tailWord_3731870).sum := by decide
  have hdescent : baseEnd_3731870 < baseStart_3731870 := by decide
  rcases family_descends (prefixWord ++ tailWord_3731870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3732007 : List Nat := [1, 1, 7, 2, 1, 1, 3, 6]
def baseStart_3732007 : Nat := 118140960795 + 3732007 * 2 ^ 59
def prefixEnd_3732007 : Nat := 4983230072969 + 3 ^ 40 * 3732007 * 2
def baseEnd_3732007 : Nat := 141949140514376684381431

theorem tailTrace_3732007 : CollatzResearch.WordTrace tailWord_3732007 prefixEnd_3732007 141949140514376684381431 := by
  unfold tailWord_3732007
  simp only [CollatzResearch.WordTrace]
  refine ⟨136117477790583489896610275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90744985193722326597740183 136117477790583489896610275)
  ·
    refine ⟨204176216685875234844915413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136117477790583489896610275 204176216685875234844915413)
    ·
      refine ⟨4785380078575200816677705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 204176216685875234844915413 4785380078575200816677705)
      ·
        refine ⟨3589035058931400612508279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4785380078575200816677705 3589035058931400612508279)
        ·
          refine ⟨5383552588397100918762419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3589035058931400612508279 5383552588397100918762419)
          ·
            refine ⟨8075328882595651378143629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5383552588397100918762419 8075328882595651378143629)
            ·
              refine ⟨3028248330973369266803861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8075328882595651378143629 3028248330973369266803861)
              ·
                refine ⟨141949140514376684381431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3028248330973369266803861 141949140514376684381431)
                ·
                  rfl

theorem cell22_3732007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 3, 6].length) (baseStart_3732007 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3732007 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3732007 prefixEnd_3732007 := by exact prefixLift 3732007
  have htrace : WordTrace (prefixWord ++ tailWord_3732007) baseStart_3732007 baseEnd_3732007 := by
    simpa [prefixWord, tailWord_3732007, baseEnd_3732007] using wordTrace_append hprefix tailTrace_3732007
  have hstable : (prefixWord ++ tailWord_3732007).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3732007).length < 2 ^ (prefixWord ++ tailWord_3732007).sum := by decide
  have hdescent : baseEnd_3732007 < baseStart_3732007 := by decide
  rcases family_descends (prefixWord ++ tailWord_3732007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3732033 : List Nat := [1, 2, 5, 1, 1, 2, 1, 2, 2, 5]
def baseStart_3732033 : Nat := 118140960795 + 3732033 * 2 ^ 59
def prefixEnd_3732033 : Nat := 4983230072969 + 3 ^ 40 * 3732033 * 2
def baseEnd_3732033 : Nat := 1277551164960734758282799

theorem tailTrace_3732033 : CollatzResearch.WordTrace tailWord_3732033 prefixEnd_3732033 1277551164960734758282799 := by
  unfold tailWord_3732033
  simp only [CollatzResearch.WordTrace]
  refine ⟨136118426088489296337056753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90745617392326197558037835 136118426088489296337056753)
  ·
    refine ⟨102088819566366972252792565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136118426088489296337056753 102088819566366972252792565)
    ·
      refine ⟨9570826834346903648699303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 102088819566366972252792565 9570826834346903648699303)
      ·
        refine ⟨14356240251520355473048955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9570826834346903648699303 14356240251520355473048955)
        ·
          refine ⟨21534360377280533209573433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14356240251520355473048955 21534360377280533209573433)
          ·
            refine ⟨16150770282960399907180075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21534360377280533209573433 16150770282960399907180075)
            ·
              refine ⟨24226155424440599860770113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16150770282960399907180075 24226155424440599860770113)
              ·
                refine ⟨18169616568330449895577585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24226155424440599860770113 18169616568330449895577585)
                ·
                  refine ⟨13627212426247837421683189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18169616568330449895577585 13627212426247837421683189)
                  ·
                    refine ⟨1277551164960734758282799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13627212426247837421683189 1277551164960734758282799)
                    ·
                      rfl

theorem cell22_3732033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 2, 2, 5].length) (baseStart_3732033 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3732033 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3732033 prefixEnd_3732033 := by exact prefixLift 3732033
  have htrace : WordTrace (prefixWord ++ tailWord_3732033) baseStart_3732033 baseEnd_3732033 := by
    simpa [prefixWord, tailWord_3732033, baseEnd_3732033] using wordTrace_append hprefix tailTrace_3732033
  have hstable : (prefixWord ++ tailWord_3732033).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3732033).length < 2 ^ (prefixWord ++ tailWord_3732033).sum := by decide
  have hdescent : baseEnd_3732033 < baseStart_3732033 := by decide
  rcases family_descends (prefixWord ++ tailWord_3732033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3732065 : List Nat := [1, 2, 3, 1, 1, 5, 2, 2, 1, 4]
def baseStart_3732065 : Nat := 118140960795 + 3732065 * 2 ^ 59
def prefixEnd_3732065 : Nat := 4983230072969 + 3 ^ 40 * 3732065 * 2
def baseEnd_3732065 : Nat := 1277562119214697341482701

theorem tailTrace_3732065 : CollatzResearch.WordTrace tailWord_3732065 prefixEnd_3732065 1277562119214697341482701 := by
  unfold tailWord_3732065
  simp only [CollatzResearch.WordTrace]
  refine ⟨136119593224373365802221649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90746395482915577201481099 136119593224373365802221649)
  ·
    refine ⟨102089694918280024351666237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136119593224373365802221649 102089694918280024351666237)
    ·
      refine ⟨38283635594355009131874839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102089694918280024351666237 38283635594355009131874839)
      ·
        refine ⟨57425453391532513697812259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38283635594355009131874839 57425453391532513697812259)
        ·
          refine ⟨86138180087298770546718389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57425453391532513697812259 86138180087298770546718389)
          ·
            refine ⟨8075454383184259738754849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 86138180087298770546718389 8075454383184259738754849)
            ·
              refine ⟨6056590787388194804066137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8075454383184259738754849 6056590787388194804066137)
              ·
                refine ⟨4542443090541146103049603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6056590787388194804066137 4542443090541146103049603)
                ·
                  refine ⟨6813664635811719154574405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4542443090541146103049603 6813664635811719154574405)
                  ·
                    refine ⟨1277562119214697341482701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6813664635811719154574405 1277562119214697341482701)
                    ·
                      rfl

theorem cell22_3732065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 2, 2, 1, 4].length) (baseStart_3732065 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3732065 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3732065 prefixEnd_3732065 := by exact prefixLift 3732065
  have htrace : WordTrace (prefixWord ++ tailWord_3732065) baseStart_3732065 baseEnd_3732065 := by
    simpa [prefixWord, tailWord_3732065, baseEnd_3732065] using wordTrace_append hprefix tailTrace_3732065
  have hstable : (prefixWord ++ tailWord_3732065).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3732065).length < 2 ^ (prefixWord ++ tailWord_3732065).sum := by decide
  have hdescent : baseEnd_3732065 < baseStart_3732065 := by decide
  rcases family_descends (prefixWord ++ tailWord_3732065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3732097 : List Nat := [1, 2, 4, 2, 1, 1, 5, 2, 4]
def baseStart_3732097 : Nat := 118140960795 + 3732097 * 2 ^ 59
def prefixEnd_3732097 : Nat := 4983230072969 + 3 ^ 40 * 3732097 * 2
def baseEnd_3732097 : Nat := 425857691156219974894201

theorem tailTrace_3732097 : CollatzResearch.WordTrace tailWord_3732097 prefixEnd_3732097 425857691156219974894201 := by
  unfold tailWord_3732097
  simp only [CollatzResearch.WordTrace]
  refine ⟨136120760360257435267386545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90747173573504956844924363 136120760360257435267386545)
  ·
    refine ⟨102090570270193076450539909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136120760360257435267386545 102090570270193076450539909)
    ·
      refine ⟨19141981925661201834476233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 102090570270193076450539909 19141981925661201834476233)
      ·
        refine ⟨14356486444245901375857175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19141981925661201834476233 14356486444245901375857175)
        ·
          refine ⟨21534729666368852063785763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14356486444245901375857175 21534729666368852063785763)
          ·
            refine ⟨32302094499553278095678645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21534729666368852063785763 32302094499553278095678645)
            ·
              refine ⟨3028321359333119821469873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 32302094499553278095678645 3028321359333119821469873)
              ·
                refine ⟨2271241019499839866102405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3028321359333119821469873 2271241019499839866102405)
                ·
                  refine ⟨425857691156219974894201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2271241019499839866102405 425857691156219974894201)
                  ·
                    rfl

theorem cell22_3732097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 5, 2, 4].length) (baseStart_3732097 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3732097 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3732097 prefixEnd_3732097 := by exact prefixLift 3732097
  have htrace : WordTrace (prefixWord ++ tailWord_3732097) baseStart_3732097 baseEnd_3732097 := by
    simpa [prefixWord, tailWord_3732097, baseEnd_3732097] using wordTrace_append hprefix tailTrace_3732097
  have hstable : (prefixWord ++ tailWord_3732097).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3732097).length < 2 ^ (prefixWord ++ tailWord_3732097).sum := by decide
  have hdescent : baseEnd_3732097 < baseStart_3732097 := by decide
  rcases family_descends (prefixWord ++ tailWord_3732097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3732123 : List Nat := [1, 1, 1, 1, 1, 1, 2, 2, 9, 3]
def baseStart_3732123 : Nat := 118140960795 + 3732123 * 2 ^ 59
def prefixEnd_3732123 : Nat := 4983230072969 + 3 ^ 40 * 3732123 * 2
def baseEnd_3732123 : Nat := 1277581973800004523532523

theorem tailTrace_3732123 : CollatzResearch.WordTrace tailWord_3732123 prefixEnd_3732123 1277581973800004523532523 := by
  unfold tailWord_3732123
  simp only [CollatzResearch.WordTrace]
  refine ⟨136121708658163241707833023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90747805772108827805222015 136121708658163241707833023)
  ·
    refine ⟨204182562987244862561749535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136121708658163241707833023 204182562987244862561749535)
    ·
      refine ⟨306273844480867293842624303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204182562987244862561749535 306273844480867293842624303)
      ·
        refine ⟨459410766721300940763936455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 306273844480867293842624303 459410766721300940763936455)
        ·
          refine ⟨689116150081951411145904683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 459410766721300940763936455 689116150081951411145904683)
          ·
            refine ⟨1033674225122927116718857025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 689116150081951411145904683 1033674225122927116718857025)
            ·
              refine ⟨775255668842195337539142769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1033674225122927116718857025 775255668842195337539142769)
              ·
                refine ⟨581441751631646503154357077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 775255668842195337539142769 581441751631646503154357077)
                ·
                  refine ⟨3406885263466678729420061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 581441751631646503154357077 3406885263466678729420061)
                  ·
                    refine ⟨1277581973800004523532523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3406885263466678729420061 1277581973800004523532523)
                    ·
                      rfl

theorem cell22_3732123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 9, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 9, 3].length) (baseStart_3732123 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3732123 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3732123 prefixEnd_3732123 := by exact prefixLift 3732123
  have htrace : WordTrace (prefixWord ++ tailWord_3732123) baseStart_3732123 baseEnd_3732123 := by
    simpa [prefixWord, tailWord_3732123, baseEnd_3732123] using wordTrace_append hprefix tailTrace_3732123
  have hstable : (prefixWord ++ tailWord_3732123).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3732123).length < 2 ^ (prefixWord ++ tailWord_3732123).sum := by decide
  have hdescent : baseEnd_3732123 < baseStart_3732123 := by decide
  rcases family_descends (prefixWord ++ tailWord_3732123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3732168 : List Nat := [2, 1, 3, 1, 2, 3, 1, 1, 1, 7]
def baseStart_3732168 : Nat := 118140960795 + 3732168 * 2 ^ 59
def prefixEnd_3732168 : Nat := 4983230072969 + 3 ^ 40 * 3732168 * 2
def baseEnd_3732168 : Nat := 1277597378219639406157385

theorem tailTrace_3732168 : CollatzResearch.WordTrace tailWord_3732168 prefixEnd_3732168 1277597378219639406157385 := by
  unfold tailWord_3732168
  simp only [CollatzResearch.WordTrace]
  refine ⟨68061674971500107196610579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90748899962000142928814105 68061674971500107196610579)
  ·
    refine ⟨102092512457250160794915869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68061674971500107196610579 102092512457250160794915869)
    ·
      refine ⟨38284692171468810298093451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102092512457250160794915869 38284692171468810298093451)
      ·
        refine ⟨57427038257203215447140177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38284692171468810298093451 57427038257203215447140177)
        ·
          refine ⟨43070278692902411585355133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57427038257203215447140177 43070278692902411585355133)
          ·
            refine ⟨16151354509838404344508175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43070278692902411585355133 16151354509838404344508175)
            ·
              refine ⟨24227031764757606516762263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16151354509838404344508175 24227031764757606516762263)
              ·
                refine ⟨36340547647136409775143395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24227031764757606516762263 36340547647136409775143395)
                ·
                  refine ⟨54510821470704614662715093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36340547647136409775143395 54510821470704614662715093)
                  ·
                    refine ⟨1277597378219639406157385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 54510821470704614662715093 1277597378219639406157385)
                    ·
                      rfl

theorem cell22_3732168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 1, 1, 7].length) (baseStart_3732168 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3732168 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3732168 prefixEnd_3732168 := by exact prefixLift 3732168
  have htrace : WordTrace (prefixWord ++ tailWord_3732168) baseStart_3732168 baseEnd_3732168 := by
    simpa [prefixWord, tailWord_3732168, baseEnd_3732168] using wordTrace_append hprefix tailTrace_3732168
  have hstable : (prefixWord ++ tailWord_3732168).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3732168).length < 2 ^ (prefixWord ++ tailWord_3732168).sum := by decide
  have hdescent : baseEnd_3732168 < baseStart_3732168 := by decide
  rcases family_descends (prefixWord ++ tailWord_3732168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3732170 : List Nat := [3, 1, 2, 1, 4, 1, 2, 3, 5]
def baseStart_3732170 : Nat := 118140960795 + 3732170 * 2 ^ 59
def prefixEnd_3732170 : Nat := 4983230072969 + 3 ^ 40 * 3732170 * 2
def baseEnd_3732170 : Nat := 425866020953504022535793

theorem tailTrace_3732170 : CollatzResearch.WordTrace tailWord_3732170 prefixEnd_3732170 425866020953504022535793 := by
  unfold tailWord_3732170
  simp only [CollatzResearch.WordTrace]
  refine ⟨34030855722248242183698491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90748948592661979156529309 34030855722248242183698491)
  ·
    refine ⟨51046283583372363275547737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34030855722248242183698491 51046283583372363275547737)
    ·
      refine ⟨38284712687529272456660803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51046283583372363275547737 38284712687529272456660803)
      ·
        refine ⟨57427069031293908684991205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38284712687529272456660803 57427069031293908684991205)
        ·
          refine ⟨10767575443367607878435851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57427069031293908684991205 10767575443367607878435851)
          ·
            refine ⟨16151363165051411817653777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10767575443367607878435851 16151363165051411817653777)
            ·
              refine ⟨12113522373788558863240333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16151363165051411817653777 12113522373788558863240333)
              ·
                refine ⟨4542570890170709573715125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12113522373788558863240333 4542570890170709573715125)
                ·
                  refine ⟨425866020953504022535793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4542570890170709573715125 425866020953504022535793)
                  ·
                    rfl

theorem cell22_3732170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 2, 3, 5].length) (baseStart_3732170 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3732170 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3732170 prefixEnd_3732170 := by exact prefixLift 3732170
  have htrace : WordTrace (prefixWord ++ tailWord_3732170) baseStart_3732170 baseEnd_3732170 := by
    simpa [prefixWord, tailWord_3732170, baseEnd_3732170] using wordTrace_append hprefix tailTrace_3732170
  have hstable : (prefixWord ++ tailWord_3732170).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3732170).length < 2 ^ (prefixWord ++ tailWord_3732170).sum := by decide
  have hdescent : baseEnd_3732170 < baseStart_3732170 := by decide
  rcases family_descends (prefixWord ++ tailWord_3732170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3732243 : List Nat := [1, 1, 1, 2, 1, 3, 5, 8]
def baseStart_3732243 : Nat := 118140960795 + 3732243 * 2 ^ 59
def prefixEnd_3732243 : Nat := 4983230072969 + 3 ^ 40 * 3732243 * 2
def baseEnd_3732243 : Nat := 141958116916929356725795

theorem tailTrace_3732243 : CollatzResearch.WordTrace tailWord_3732243 prefixEnd_3732243 141958116916929356725795 := by
  unfold tailWord_3732243
  simp only [CollatzResearch.WordTrace]
  refine ⟨136126085417728502202201383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90750723611819001468134255 136126085417728502202201383)
  ·
    refine ⟨204189128126592753303302075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136126085417728502202201383 204189128126592753303302075)
    ·
      refine ⟨306283692189889129954953113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204189128126592753303302075 306283692189889129954953113)
      ·
        refine ⟨229712769142416847466214835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 306283692189889129954953113 229712769142416847466214835)
        ·
          refine ⟨344569153713625271199322253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 229712769142416847466214835 344569153713625271199322253)
          ·
            refine ⟨129213432642609476699745845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 344569153713625271199322253 129213432642609476699745845)
            ·
              refine ⟨12113759310244638440601173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 129213432642609476699745845 12113759310244638440601173)
              ·
                refine ⟨141958116916929356725795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12113759310244638440601173 141958116916929356725795)
                ·
                  rfl

theorem cell22_3732243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 5, 8].length) (baseStart_3732243 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3732243 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3732243 prefixEnd_3732243 := by exact prefixLift 3732243
  have htrace : WordTrace (prefixWord ++ tailWord_3732243) baseStart_3732243 baseEnd_3732243 := by
    simpa [prefixWord, tailWord_3732243, baseEnd_3732243] using wordTrace_append hprefix tailTrace_3732243
  have hstable : (prefixWord ++ tailWord_3732243).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3732243).length < 2 ^ (prefixWord ++ tailWord_3732243).sum := by decide
  have hdescent : baseEnd_3732243 < baseStart_3732243 := by decide
  rcases family_descends (prefixWord ++ tailWord_3732243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3732245 : List Nat := [1, 3, 2, 1, 2, 2, 2, 3, 2, 4]
def baseStart_3732245 : Nat := 118140960795 + 3732245 * 2 ^ 59
def prefixEnd_3732245 : Nat := 4983230072969 + 3 ^ 40 * 3732245 * 2
def baseEnd_3732245 : Nat := 1277623736893236871982149

theorem tailTrace_3732245 : CollatzResearch.WordTrace tailWord_3732245 prefixEnd_3732245 1277623736893236871982149 := by
  unfold tailWord_3732245
  simp only [CollatzResearch.WordTrace]
  refine ⟨136126158363721256543774189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90750772242480837695849459 136126158363721256543774189)
  ·
    refine ⟨51047309386395471203915321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136126158363721256543774189 51047309386395471203915321)
    ·
      refine ⟨38285482039796603402936491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51047309386395471203915321 38285482039796603402936491)
      ·
        refine ⟨57428223059694905104404737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38285482039796603402936491 57428223059694905104404737)
        ·
          refine ⟨43071167294771178828303553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57428223059694905104404737 43071167294771178828303553)
          ·
            refine ⟨32303375471078384121227665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43071167294771178828303553 32303375471078384121227665)
            ·
              refine ⟨24227531603308788090920749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32303375471078384121227665 24227531603308788090920749)
              ·
                refine ⟨9085324351240795534095281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24227531603308788090920749 9085324351240795534095281)
                ·
                  refine ⟨6813993263430596650571461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9085324351240795534095281 6813993263430596650571461)
                  ·
                    refine ⟨1277623736893236871982149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6813993263430596650571461 1277623736893236871982149)
                    ·
                      rfl

theorem cell22_3732245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 3, 2, 4].length) (baseStart_3732245 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3732245 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3732245 prefixEnd_3732245 := by exact prefixLift 3732245
  have htrace : WordTrace (prefixWord ++ tailWord_3732245) baseStart_3732245 baseEnd_3732245 := by
    simpa [prefixWord, tailWord_3732245, baseEnd_3732245] using wordTrace_append hprefix tailTrace_3732245
  have hstable : (prefixWord ++ tailWord_3732245).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3732245).length < 2 ^ (prefixWord ++ tailWord_3732245).sum := by decide
  have hdescent : baseEnd_3732245 < baseStart_3732245 := by decide
  rcases family_descends (prefixWord ++ tailWord_3732245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3732266 : List Nat := [3, 1, 4, 3, 2, 1, 1, 1, 6]
def baseStart_3732266 : Nat := 118140960795 + 3732266 * 2 ^ 59
def prefixEnd_3732266 : Nat := 4983230072969 + 3 ^ 40 * 3732266 * 2
def baseEnd_3732266 : Nat := 425876975207466605735695

theorem tailTrace_3732266 : CollatzResearch.WordTrace tailWord_3732266 prefixEnd_3732266 425876975207466605735695 := by
  unfold tailWord_3732266
  simp only [CollatzResearch.WordTrace]
  refine ⟨34031731074161294282572163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90751282864430118086859101 34031731074161294282572163)
  ·
    refine ⟨51047596611241941423858245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34031731074161294282572163 51047596611241941423858245)
    ·
      refine ⟨9571424364607864016973421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51047596611241941423858245 9571424364607864016973421)
      ·
        refine ⟨3589284136727949006365033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9571424364607864016973421 3589284136727949006365033)
        ·
          refine ⟨2691963102545961754773775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3589284136727949006365033 2691963102545961754773775)
          ·
            refine ⟨4037944653818942632160663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2691963102545961754773775 4037944653818942632160663)
            ·
              refine ⟨6056916980728413948240995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4037944653818942632160663 6056916980728413948240995)
              ·
                refine ⟨9085375471092620922361493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6056916980728413948240995 9085375471092620922361493)
                ·
                  refine ⟨425876975207466605735695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9085375471092620922361493 425876975207466605735695)
                  ·
                    rfl

theorem cell22_3732266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 2, 1, 1, 1, 6].length) (baseStart_3732266 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3732266 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3732266 prefixEnd_3732266 := by exact prefixLift 3732266
  have htrace : WordTrace (prefixWord ++ tailWord_3732266) baseStart_3732266 baseEnd_3732266 := by
    simpa [prefixWord, tailWord_3732266, baseEnd_3732266] using wordTrace_append hprefix tailTrace_3732266
  have hstable : (prefixWord ++ tailWord_3732266).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3732266).length < 2 ^ (prefixWord ++ tailWord_3732266).sum := by decide
  have hdescent : baseEnd_3732266 < baseStart_3732266 := by decide
  rcases family_descends (prefixWord ++ tailWord_3732266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3732309 : List Nat := [1, 3, 2, 2, 2, 1, 2, 5, 1, 3]
def baseStart_3732309 : Nat := 118140960795 + 3732309 * 2 ^ 59
def prefixEnd_3732309 : Nat := 4983230072969 + 3 ^ 40 * 3732309 * 2
def baseEnd_3732309 : Nat := 1277645645401162038381953

theorem tailTrace_3732309 : CollatzResearch.WordTrace tailWord_3732309 prefixEnd_3732309 1277645645401162038381953 := by
  unfold tailWord_3732309
  simp only [CollatzResearch.WordTrace]
  refine ⟨136128492635489395474103981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90752328423659596982735987 136128492635489395474103981)
  ·
    refine ⟨51048184738308523302788993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136128492635489395474103981 51048184738308523302788993)
    ·
      refine ⟨38286138553731392477091745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51048184738308523302788993 38286138553731392477091745)
      ·
        refine ⟨28714603915298544357818809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38286138553731392477091745 28714603915298544357818809)
        ·
          refine ⟨21535952936473908268364107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28714603915298544357818809 21535952936473908268364107)
          ·
            refine ⟨32303929404710862402546161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21535952936473908268364107 32303929404710862402546161)
            ·
              refine ⟨24227947053533146801909621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32303929404710862402546161 24227947053533146801909621)
              ·
                refine ⟨2271370036268732512679027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24227947053533146801909621 2271370036268732512679027)
                ·
                  refine ⟨3407055054403098769018541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2271370036268732512679027 3407055054403098769018541)
                  ·
                    refine ⟨1277645645401162038381953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3407055054403098769018541 1277645645401162038381953)
                    ·
                      rfl

theorem cell22_3732309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 5, 1, 3].length) (baseStart_3732309 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3732309 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3732309 prefixEnd_3732309 := by exact prefixLift 3732309
  have htrace : WordTrace (prefixWord ++ tailWord_3732309) baseStart_3732309 baseEnd_3732309 := by
    simpa [prefixWord, tailWord_3732309, baseEnd_3732309] using wordTrace_append hprefix tailTrace_3732309
  have hstable : (prefixWord ++ tailWord_3732309).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3732309).length < 2 ^ (prefixWord ++ tailWord_3732309).sum := by decide
  have hdescent : baseEnd_3732309 < baseStart_3732309 := by decide
  rcases family_descends (prefixWord ++ tailWord_3732309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3732320 : List Nat := [2, 1, 1, 3, 3, 1, 2, 2, 2, 5]
def baseStart_3732320 : Nat := 118140960795 + 3732320 * 2 ^ 59
def prefixEnd_3732320 : Nat := 4983230072969 + 3 ^ 40 * 3732320 * 2
def baseEnd_3732320 : Nat := 1277649410925961676356919

theorem tailTrace_3732320 : CollatzResearch.WordTrace tailWord_3732320 prefixEnd_3732320 1277649410925961676356919 := by
  unfold tailWord_3732320
  simp only [CollatzResearch.WordTrace]
  refine ⟨68064446919224772176377207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90752595892299696235169609 68064446919224772176377207)
  ·
    refine ⟨102096670378837158264565811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68064446919224772176377207 102096670378837158264565811)
    ·
      refine ⟨153145005568255737396848717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102096670378837158264565811 153145005568255737396848717)
      ·
        refine ⟨57429377088095901523818269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 153145005568255737396848717 57429377088095901523818269)
        ·
          refine ⟨21536016408035963071431851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57429377088095901523818269 21536016408035963071431851)
          ·
            refine ⟨32304024612053944607147777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21536016408035963071431851 32304024612053944607147777)
            ·
              refine ⟨24228018459040458455360833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32304024612053944607147777 24228018459040458455360833)
              ·
                refine ⟨18171013844280343841520625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24228018459040458455360833 18171013844280343841520625)
                ·
                  refine ⟨13628260383210257881140469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18171013844280343841520625 13628260383210257881140469)
                  ·
                    refine ⟨1277649410925961676356919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13628260383210257881140469 1277649410925961676356919)
                    ·
                      rfl

theorem cell22_3732320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 2, 2, 5].length) (baseStart_3732320 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3732320 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3732320 prefixEnd_3732320 := by exact prefixLift 3732320
  have htrace : WordTrace (prefixWord ++ tailWord_3732320) baseStart_3732320 baseEnd_3732320 := by
    simpa [prefixWord, tailWord_3732320, baseEnd_3732320] using wordTrace_append hprefix tailTrace_3732320
  have hstable : (prefixWord ++ tailWord_3732320).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3732320).length < 2 ^ (prefixWord ++ tailWord_3732320).sum := by decide
  have hdescent : baseEnd_3732320 < baseStart_3732320 := by decide
  rcases family_descends (prefixWord ++ tailWord_3732320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3732410 : List Nat := [3, 1, 1, 1, 2, 1, 3, 1, 2, 7]
def baseStart_3732410 : Nat := 118140960795 + 3732410 * 2 ^ 59
def prefixEnd_3732410 : Nat := 4983230072969 + 3 ^ 40 * 3732410 * 2
def baseEnd_3732410 : Nat := 1277680219765231441606643

theorem tailTrace_3732410 : CollatzResearch.WordTrace tailWord_3732410 prefixEnd_3732410 1277680219765231441606643 := by
  unfold tailWord_3732410
  simp only [CollatzResearch.WordTrace]
  refine ⟨34033044102030872430882671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90754784272082326482353789 34033044102030872430882671)
  ·
    refine ⟨51049566153046308646324007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34033044102030872430882671 51049566153046308646324007)
    ·
      refine ⟨76574349229569462969486011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51049566153046308646324007 76574349229569462969486011)
      ·
        refine ⟨114861523844354194454229017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76574349229569462969486011 114861523844354194454229017)
        ·
          refine ⟨86146142883265645840671763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114861523844354194454229017 86146142883265645840671763)
          ·
            refine ⟨129219214324898468761007645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86146142883265645840671763 129219214324898468761007645)
            ·
              refine ⟨48457205371836925785377867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 129219214324898468761007645 48457205371836925785377867)
              ·
                refine ⟨72685808057755388678066801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48457205371836925785377867 72685808057755388678066801)
                ·
                  refine ⟨54514356043316541508550101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72685808057755388678066801 54514356043316541508550101)
                  ·
                    refine ⟨1277680219765231441606643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 54514356043316541508550101 1277680219765231441606643)
                    ·
                      rfl

theorem cell22_3732410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 1, 2, 7].length) (baseStart_3732410 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3732410 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3732410 prefixEnd_3732410 := by exact prefixLift 3732410
  have htrace : WordTrace (prefixWord ++ tailWord_3732410) baseStart_3732410 baseEnd_3732410 := by
    simpa [prefixWord, tailWord_3732410, baseEnd_3732410] using wordTrace_append hprefix tailTrace_3732410
  have hstable : (prefixWord ++ tailWord_3732410).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3732410).length < 2 ^ (prefixWord ++ tailWord_3732410).sum := by decide
  have hdescent : baseEnd_3732410 < baseStart_3732410 := by decide
  rcases family_descends (prefixWord ++ tailWord_3732410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3732450 : List Nat := [3, 3, 3, 1, 1, 3, 2, 1, 2, 3]
def baseStart_3732450 : Nat := 118140960795 + 3732450 * 2 ^ 59
def prefixEnd_3732450 : Nat := 4983230072969 + 3 ^ 40 * 3732450 * 2
def baseEnd_3732450 : Nat := 1277693912582684670606521

theorem tailTrace_3732450 : CollatzResearch.WordTrace tailWord_3732450 prefixEnd_3732450 1277693912582684670606521 := by
  unfold tailWord_3732450
  simp only [CollatzResearch.WordTrace]
  refine ⟨34033408831994644138746701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90755756885319051036657869 34033408831994644138746701)
  ·
    refine ⟨12762528311997991552030013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34033408831994644138746701 12762528311997991552030013)
    ·
      refine ⟨4785948116999246832011255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12762528311997991552030013 4785948116999246832011255)
      ·
        refine ⟨7178922175498870248016883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4785948116999246832011255 7178922175498870248016883)
        ·
          refine ⟨10768383263248305372025325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7178922175498870248016883 10768383263248305372025325)
          ·
            refine ⟨4038143723718114514509497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10768383263248305372025325 4038143723718114514509497)
            ·
              refine ⟨3028607792788585885882123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4038143723718114514509497 3028607792788585885882123)
              ·
                refine ⟨4542911689182878828823185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3028607792788585885882123 4542911689182878828823185)
                ·
                  refine ⟨3407183766887159121617389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4542911689182878828823185 3407183766887159121617389)
                  ·
                    refine ⟨1277693912582684670606521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3407183766887159121617389 1277693912582684670606521)
                    ·
                      rfl

theorem cell22_3732450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 3, 2, 1, 2, 3].length) (baseStart_3732450 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3732450 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3732450 prefixEnd_3732450 := by exact prefixLift 3732450
  have htrace : WordTrace (prefixWord ++ tailWord_3732450) baseStart_3732450 baseEnd_3732450 := by
    simpa [prefixWord, tailWord_3732450, baseEnd_3732450] using wordTrace_append hprefix tailTrace_3732450
  have hstable : (prefixWord ++ tailWord_3732450).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3732450).length < 2 ^ (prefixWord ++ tailWord_3732450).sum := by decide
  have hdescent : baseEnd_3732450 < baseStart_3732450 := by decide
  rcases family_descends (prefixWord ++ tailWord_3732450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3732519 : List Nat := [1, 1, 7, 1, 1, 1, 1, 1, 8]
def baseStart_3732519 : Nat := 118140960795 + 3732519 * 2 ^ 59
def prefixEnd_3732519 : Nat := 4983230072969 + 3 ^ 40 * 3732519 * 2
def baseEnd_3732519 : Nat := 425905844230930496877103

theorem tailTrace_3732519 : CollatzResearch.WordTrace tailWord_3732519 prefixEnd_3732519 425905844230930496877103 := by
  unfold tailWord_3732519
  simp only [CollatzResearch.WordTrace]
  refine ⟨136136151964728601339248611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90757434643152400892832407 136136151964728601339248611)
  ·
    refine ⟨204204227947092902008872917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136136151964728601339248611 204204227947092902008872917)
    ·
      refine ⟨4786036592509989890832959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 204204227947092902008872917 4786036592509989890832959)
      ·
        refine ⟨7179054888764984836249439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4786036592509989890832959 7179054888764984836249439)
        ·
          refine ⟨10768582333147477254374159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7179054888764984836249439 10768582333147477254374159)
          ·
            refine ⟨16152873499721215881561239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10768582333147477254374159 16152873499721215881561239)
            ·
              refine ⟨24229310249581823822341859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16152873499721215881561239 24229310249581823822341859)
              ·
                refine ⟨36343965374372735733512789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24229310249581823822341859 36343965374372735733512789)
                ·
                  refine ⟨425905844230930496877103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 36343965374372735733512789 425905844230930496877103)
                  ·
                    rfl

theorem cell22_3732519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 1, 8].length) (baseStart_3732519 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3732519 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3732519 prefixEnd_3732519 := by exact prefixLift 3732519
  have htrace : WordTrace (prefixWord ++ tailWord_3732519) baseStart_3732519 baseEnd_3732519 := by
    simpa [prefixWord, tailWord_3732519, baseEnd_3732519] using wordTrace_append hprefix tailTrace_3732519
  have hstable : (prefixWord ++ tailWord_3732519).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3732519).length < 2 ^ (prefixWord ++ tailWord_3732519).sum := by decide
  have hdescent : baseEnd_3732519 < baseStart_3732519 := by decide
  rcases family_descends (prefixWord ++ tailWord_3732519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3732536 : List Nat := [2, 1, 2, 1, 5, 2, 2, 3, 4]
def baseStart_3732536 : Nat := 118140960795 + 3732536 * 2 ^ 59
def prefixEnd_3732536 : Nat := 4983230072969 + 3 ^ 40 * 3732536 * 2
def baseEnd_3732536 : Nat := 425907784046736370985419

theorem tailTrace_3732536 : CollatzResearch.WordTrace tailWord_3732536 prefixEnd_3732536 425907784046736370985419 := by
  unfold tailWord_3732536
  simp only [CollatzResearch.WordTrace]
  refine ⟨68068386002833506621308731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90757848003778008828411641 68068386002833506621308731)
  ·
    refine ⟨102102579004250259931963097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68068386002833506621308731 102102579004250259931963097)
    ·
      refine ⟨76576934253187694948972323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102102579004250259931963097 76576934253187694948972323)
      ·
        refine ⟨114865401379781542423458485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76576934253187694948972323 114865401379781542423458485)
        ·
          refine ⟨10768631379354519602199233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 114865401379781542423458485 10768631379354519602199233)
          ·
            refine ⟨8076473534515889701649425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10768631379354519602199233 8076473534515889701649425)
            ·
              refine ⟨6057355150886917276237069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8076473534515889701649425 6057355150886917276237069)
              ·
                refine ⟨2271508181582593978588901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6057355150886917276237069 2271508181582593978588901)
                ·
                  refine ⟨425907784046736370985419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2271508181582593978588901 425907784046736370985419)
                  ·
                    rfl

theorem cell22_3732536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 2, 3, 4].length) (baseStart_3732536 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3732536 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3732536 prefixEnd_3732536 := by exact prefixLift 3732536
  have htrace : WordTrace (prefixWord ++ tailWord_3732536) baseStart_3732536 baseEnd_3732536 := by
    simpa [prefixWord, tailWord_3732536, baseEnd_3732536] using wordTrace_append hprefix tailTrace_3732536
  have hstable : (prefixWord ++ tailWord_3732536).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3732536).length < 2 ^ (prefixWord ++ tailWord_3732536).sum := by decide
  have hdescent : baseEnd_3732536 < baseStart_3732536 := by decide
  rcases family_descends (prefixWord ++ tailWord_3732536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3732551 : List Nat := [1, 1, 4, 1, 3, 2, 3, 2, 2, 3]
def baseStart_3732551 : Nat := 118140960795 + 3732551 * 2 ^ 59
def prefixEnd_3732551 : Nat := 4983230072969 + 3 ^ 40 * 3732551 * 2
def baseEnd_3732551 : Nat := 1277728486946754073831211

theorem tailTrace_3732551 : CollatzResearch.WordTrace tailWord_3732551 prefixEnd_3732551 1277728486946754073831211 := by
  unfold tailWord_3732551
  simp only [CollatzResearch.WordTrace]
  refine ⟨136137319100612670804413507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90758212733741780536275671 136137319100612670804413507)
  ·
    refine ⟨204205978650919006206620261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136137319100612670804413507 204205978650919006206620261)
    ·
      refine ⟨38288620997047313663741299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 204205978650919006206620261 38288620997047313663741299)
      ·
        refine ⟨57432931495570970495611949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38288620997047313663741299 57432931495570970495611949)
        ·
          refine ⟨21537349310839113935854481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57432931495570970495611949 21537349310839113935854481)
          ·
            refine ⟨16153011983129335451890861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21537349310839113935854481 16153011983129335451890861)
            ·
              refine ⟨6057379493673500794459073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16153011983129335451890861 6057379493673500794459073)
              ·
                refine ⟨4543034620255125595844305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6057379493673500794459073 4543034620255125595844305)
                ·
                  refine ⟨3407275965191344196883229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4543034620255125595844305 3407275965191344196883229)
                  ·
                    refine ⟨1277728486946754073831211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3407275965191344196883229 1277728486946754073831211)
                    ·
                      rfl

theorem cell22_3732551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 3, 2, 2, 3].length) (baseStart_3732551 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3732551 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3732551 prefixEnd_3732551 := by exact prefixLift 3732551
  have htrace : WordTrace (prefixWord ++ tailWord_3732551) baseStart_3732551 baseEnd_3732551 := by
    simpa [prefixWord, tailWord_3732551, baseEnd_3732551] using wordTrace_append hprefix tailTrace_3732551
  have hstable : (prefixWord ++ tailWord_3732551).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3732551).length < 2 ^ (prefixWord ++ tailWord_3732551).sum := by decide
  have hdescent : baseEnd_3732551 < baseStart_3732551 := by decide
  rcases family_descends (prefixWord ++ tailWord_3732551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3732577 : List Nat := [1, 2, 3, 1, 1, 2, 2, 2, 2, 6]
def baseStart_3732577 : Nat := 118140960795 + 3732577 * 2 ^ 59
def prefixEnd_3732577 : Nat := 4983230072969 + 3 ^ 40 * 3732577 * 2
def baseEnd_3732577 : Nat := 1277737387278098672681131

theorem tailTrace_3732577 : CollatzResearch.WordTrace tailWord_3732577 prefixEnd_3732577 1277737387278098672681131 := by
  unfold tailWord_3732577
  simp only [CollatzResearch.WordTrace]
  refine ⟨136138267398518477244859985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90758844932345651496573323 136138267398518477244859985)
  ·
    refine ⟨102103700548888857933644989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136138267398518477244859985 102103700548888857933644989)
    ·
      refine ⟨38288887705833321725116871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102103700548888857933644989 38288887705833321725116871)
      ·
        refine ⟨57433331558749982587675307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38288887705833321725116871 57433331558749982587675307)
        ·
          refine ⟨86149997338124973881512961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57433331558749982587675307 86149997338124973881512961)
          ·
            refine ⟨64612498003593730411134721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86149997338124973881512961 64612498003593730411134721)
            ·
              refine ⟨48459373502695297808351041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64612498003593730411134721 48459373502695297808351041)
              ·
                refine ⟨36344530127021473356263281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48459373502695297808351041 36344530127021473356263281)
                ·
                  refine ⟨27258397595266105017197461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36344530127021473356263281 27258397595266105017197461)
                  ·
                    refine ⟨1277737387278098672681131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27258397595266105017197461 1277737387278098672681131)
                    ·
                      rfl

theorem cell22_3732577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 2, 2, 6].length) (baseStart_3732577 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3732577 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3732577 prefixEnd_3732577 := by exact prefixLift 3732577
  have htrace : WordTrace (prefixWord ++ tailWord_3732577) baseStart_3732577 baseEnd_3732577 := by
    simpa [prefixWord, tailWord_3732577, baseEnd_3732577] using wordTrace_append hprefix tailTrace_3732577
  have hstable : (prefixWord ++ tailWord_3732577).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3732577).length < 2 ^ (prefixWord ++ tailWord_3732577).sum := by decide
  have hdescent : baseEnd_3732577 < baseStart_3732577 := by decide
  rcases family_descends (prefixWord ++ tailWord_3732577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3732592 : List Nat := [2, 1, 1, 1, 5, 1, 1, 1, 9]
def baseStart_3732592 : Nat := 118140960795 + 3732592 * 2 ^ 59
def prefixEnd_3732592 : Nat := 4983230072969 + 3 ^ 40 * 3732592 * 2
def baseEnd_3732592 : Nat := 425914174028214544518695

theorem tailTrace_3732592 : CollatzResearch.WordTrace tailWord_3732592 prefixEnd_3732592 425914174028214544518695 := by
  unfold tailWord_3732592
  simp only [CollatzResearch.WordTrace]
  refine ⟨68069407246732067403328015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90759209662309423204437353 68069407246732067403328015)
  ·
    refine ⟨102104110870098101104992023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68069407246732067403328015 102104110870098101104992023)
    ·
      refine ⟨153156166305147151657488035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102104110870098101104992023 153156166305147151657488035)
      ·
        refine ⟨229734249457720727486232053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153156166305147151657488035 229734249457720727486232053)
        ·
          refine ⟨21537585886661318201834255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 229734249457720727486232053 21537585886661318201834255)
          ·
            refine ⟨32306378829991977302751383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21537585886661318201834255 32306378829991977302751383)
            ·
              refine ⟨48459568244987965954127075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32306378829991977302751383 48459568244987965954127075)
              ·
                refine ⟨72689352367481948931190613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48459568244987965954127075 72689352367481948931190613)
                ·
                  refine ⟨425914174028214544518695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 72689352367481948931190613 425914174028214544518695)
                  ·
                    rfl

theorem cell22_3732592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 1, 9].length) (baseStart_3732592 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3732592 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3732592 prefixEnd_3732592 := by exact prefixLift 3732592
  have htrace : WordTrace (prefixWord ++ tailWord_3732592) baseStart_3732592 baseEnd_3732592 := by
    simpa [prefixWord, tailWord_3732592, baseEnd_3732592] using wordTrace_append hprefix tailTrace_3732592
  have hstable : (prefixWord ++ tailWord_3732592).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3732592).length < 2 ^ (prefixWord ++ tailWord_3732592).sum := by decide
  have hdescent : baseEnd_3732592 < baseStart_3732592 := by decide
  rcases family_descends (prefixWord ++ tailWord_3732592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3732609 : List Nat := [1, 2, 4, 2, 2, 1, 2, 1, 7]
def baseStart_3732609 : Nat := 118140960795 + 3732609 * 2 ^ 59
def prefixEnd_3732609 : Nat := 4983230072969 + 3 ^ 40 * 3732609 * 2
def baseEnd_3732609 : Nat := 425916113844020418627011

theorem tailTrace_3732609 : CollatzResearch.WordTrace tailWord_3732609 prefixEnd_3732609 425916113844020418627011 := by
  unfold tailWord_3732609
  simp only [CollatzResearch.WordTrace]
  refine ⟨136139434534402546710024881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90759623022935031140016587 136139434534402546710024881)
  ·
    refine ⟨102104575900801910032518661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136139434534402546710024881 102104575900801910032518661)
    ·
      refine ⟨19144607981400358131097249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 102104575900801910032518661 19144607981400358131097249)
      ·
        refine ⟨14358455986050268598322937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19144607981400358131097249 14358455986050268598322937)
        ·
          refine ⟨10768841989537701448742203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14358455986050268598322937 10768841989537701448742203)
          ·
            refine ⟨16153262984306552173113305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10768841989537701448742203 16153262984306552173113305)
            ·
              refine ⟨12114947238229914129834979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16153262984306552173113305 12114947238229914129834979)
              ·
                refine ⟨18172420857344871194752469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12114947238229914129834979 18172420857344871194752469)
                ·
                  refine ⟨425916113844020418627011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18172420857344871194752469 425916113844020418627011)
                  ·
                    rfl

theorem cell22_3732609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 2, 1, 7].length) (baseStart_3732609 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3732609 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3732609 prefixEnd_3732609 := by exact prefixLift 3732609
  have htrace : WordTrace (prefixWord ++ tailWord_3732609) baseStart_3732609 baseEnd_3732609 := by
    simpa [prefixWord, tailWord_3732609, baseEnd_3732609] using wordTrace_append hprefix tailTrace_3732609
  have hstable : (prefixWord ++ tailWord_3732609).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3732609).length < 2 ^ (prefixWord ++ tailWord_3732609).sum := by decide
  have hdescent : baseEnd_3732609 < baseStart_3732609 := by decide
  rcases family_descends (prefixWord ++ tailWord_3732609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3732613 : List Nat := [1, 3, 1, 1, 6, 2, 1, 1, 3, 3]
def baseStart_3732613 : Nat := 118140960795 + 3732613 * 2 ^ 59
def prefixEnd_3732613 : Nat := 4983230072969 + 3 ^ 40 * 3732613 * 2
def baseEnd_3732613 : Nat := 1277749710813806578781021

theorem tailTrace_3732613 : CollatzResearch.WordTrace tailWord_3732613 prefixEnd_3732613 1277749710813806578781021 := by
  unfold tailWord_3732613
  simp only [CollatzResearch.WordTrace]
  refine ⟨136139580426388055393170493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90759720284258703595446995 136139580426388055393170493)
  ·
    refine ⟨51052342659895520772438935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136139580426388055393170493 51052342659895520772438935)
    ·
      refine ⟨76578513989843281158658403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51052342659895520772438935 76578513989843281158658403)
      ·
        refine ⟨114867770984764921737987605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76578513989843281158658403 114867770984764921737987605)
        ·
          refine ⟨5384426764910855706468169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 114867770984764921737987605 5384426764910855706468169)
          ·
            refine ⟨4038320073683141779851127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5384426764910855706468169 4038320073683141779851127)
            ·
              refine ⟨6057480110524712669776691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4038320073683141779851127 6057480110524712669776691)
              ·
                refine ⟨9086220165787069004665037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6057480110524712669776691 9086220165787069004665037)
                ·
                  refine ⟨3407332562170150876749389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9086220165787069004665037 3407332562170150876749389)
                  ·
                    refine ⟨1277749710813806578781021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3407332562170150876749389 1277749710813806578781021)
                    ·
                      rfl

theorem cell22_3732613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 2, 1, 1, 3, 3].length) (baseStart_3732613 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3732613 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3732613 prefixEnd_3732613 := by exact prefixLift 3732613
  have htrace : WordTrace (prefixWord ++ tailWord_3732613) baseStart_3732613 baseEnd_3732613 := by
    simpa [prefixWord, tailWord_3732613, baseEnd_3732613] using wordTrace_append hprefix tailTrace_3732613
  have hstable : (prefixWord ++ tailWord_3732613).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3732613).length < 2 ^ (prefixWord ++ tailWord_3732613).sum := by decide
  have hdescent : baseEnd_3732613 < baseStart_3732613 := by decide
  rcases family_descends (prefixWord ++ tailWord_3732613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3732626 : List Nat := [3, 2, 3, 1, 1, 3, 1, 3, 5]
def baseStart_3732626 : Nat := 118140960795 + 3732626 * 2 ^ 59
def prefixEnd_3732626 : Nat := 4983230072969 + 3 ^ 40 * 3732626 * 2
def baseEnd_3732626 : Nat := 425918053659826292735327

theorem tailTrace_3732626 : CollatzResearch.WordTrace tailWord_3732626 prefixEnd_3732626 425918053659826292735327 := by
  unfold tailWord_3732626
  simp only [CollatzResearch.WordTrace]
  refine ⟨34035013643835239653348433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90760036383560639075595821 34035013643835239653348433)
  ·
    refine ⟨25526260232876429740011325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34035013643835239653348433 25526260232876429740011325)
    ·
      refine ⟨9572347587328661152504247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25526260232876429740011325 9572347587328661152504247)
      ·
        refine ⟨14358521380992991728756371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9572347587328661152504247 14358521380992991728756371)
        ·
          refine ⟨21537782071489487593134557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14358521380992991728756371 21537782071489487593134557)
          ·
            refine ⟨8076668276808557847425459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21537782071489487593134557 8076668276808557847425459)
            ·
              refine ⟨12115002415212836771138189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8076668276808557847425459 12115002415212836771138189)
              ·
                refine ⟨4543125905704813789176821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12115002415212836771138189 4543125905704813789176821)
                ·
                  refine ⟨425918053659826292735327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4543125905704813789176821 425918053659826292735327)
                  ·
                    rfl

theorem cell22_3732626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 1, 3, 5].length) (baseStart_3732626 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3732626 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3732626 prefixEnd_3732626 := by exact prefixLift 3732626
  have htrace : WordTrace (prefixWord ++ tailWord_3732626) baseStart_3732626 baseEnd_3732626 := by
    simpa [prefixWord, tailWord_3732626, baseEnd_3732626] using wordTrace_append hprefix tailTrace_3732626
  have hstable : (prefixWord ++ tailWord_3732626).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3732626).length < 2 ^ (prefixWord ++ tailWord_3732626).sum := by decide
  have hdescent : baseEnd_3732626 < baseStart_3732626 := by decide
  rcases family_descends (prefixWord ++ tailWord_3732626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3732821 : List Nat := [1, 3, 2, 2, 3, 1, 1, 1, 3, 5]
def baseStart_3732821 : Nat := 118140960795 + 3732821 * 2 ^ 59
def prefixEnd_3732821 : Nat := 4983230072969 + 3 ^ 40 * 3732821 * 2
def baseEnd_3732821 : Nat := 1277820913464563369580383

theorem tailTrace_3732821 : CollatzResearch.WordTrace tailWord_3732821 prefixEnd_3732821 1277820913464563369580383 := by
  unfold tailWord_3732821
  simp only [CollatzResearch.WordTrace]
  refine ⟨136147166809634506916742317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90764777873089671277828211 136147166809634506916742317)
  ·
    refine ⟨51055187553612940093778369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136147166809634506916742317 51055187553612940093778369)
    ·
      refine ⟨38291390665209705070333777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51055187553612940093778369 38291390665209705070333777)
      ·
        refine ⟨28718542998907278802750333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38291390665209705070333777 28718542998907278802750333)
        ·
          refine ⟨10769453624590229551031375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28718542998907278802750333 10769453624590229551031375)
          ·
            refine ⟨16154180436885344326547063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10769453624590229551031375 16154180436885344326547063)
            ·
              refine ⟨24231270655328016489820595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16154180436885344326547063 24231270655328016489820595)
              ·
                refine ⟨36346905982992024734730893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24231270655328016489820595 36346905982992024734730893)
                ·
                  refine ⟨13630089743622009275524085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36346905982992024734730893 13630089743622009275524085)
                  ·
                    refine ⟨1277820913464563369580383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13630089743622009275524085 1277820913464563369580383)
                    ·
                      rfl

theorem cell22_3732821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 1, 3, 5].length) (baseStart_3732821 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3732821 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3732821 prefixEnd_3732821 := by exact prefixLift 3732821
  have htrace : WordTrace (prefixWord ++ tailWord_3732821) baseStart_3732821 baseEnd_3732821 := by
    simpa [prefixWord, tailWord_3732821, baseEnd_3732821] using wordTrace_append hprefix tailTrace_3732821
  have hstable : (prefixWord ++ tailWord_3732821).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3732821).length < 2 ^ (prefixWord ++ tailWord_3732821).sum := by decide
  have hdescent : baseEnd_3732821 < baseStart_3732821 := by decide
  rcases family_descends (prefixWord ++ tailWord_3732821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3732840 : List Nat := [2, 1, 4, 2, 3, 1, 1, 4, 4]
def baseStart_3732840 : Nat := 118140960795 + 3732840 * 2 ^ 59
def prefixEnd_3732840 : Nat := 4983230072969 + 3 ^ 40 * 3732840 * 2
def baseEnd_3732840 : Nat := 425942472517617884451775

theorem tailTrace_3732840 : CollatzResearch.WordTrace tailWord_3732840 prefixEnd_3732840 425942472517617884451775 := by
  unfold tailWord_3732840
  simp only [CollatzResearch.WordTrace]
  refine ⟨68073929898282836580841987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90765239864377115441122649 68073929898282836580841987)
  ·
    refine ⟨102110894847424254871262981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68073929898282836580841987 102110894847424254871262981)
    ·
      refine ⟨19145792783892047788361809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 102110894847424254871262981 19145792783892047788361809)
      ·
        refine ⟨14359344587919035841271357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19145792783892047788361809 14359344587919035841271357)
        ·
          refine ⟨5384754220469638440476759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14359344587919035841271357 5384754220469638440476759)
          ·
            refine ⟨8077131330704457660715139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5384754220469638440476759 8077131330704457660715139)
            ·
              refine ⟨12115696996056686491072709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8077131330704457660715139 12115696996056686491072709)
              ·
                refine ⟨2271693186760628717076133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12115696996056686491072709 2271693186760628717076133)
                ·
                  refine ⟨425942472517617884451775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2271693186760628717076133 425942472517617884451775)
                  ·
                    rfl

theorem cell22_3732840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 1, 4, 4].length) (baseStart_3732840 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3732840 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3732840 prefixEnd_3732840 := by exact prefixLift 3732840
  have htrace : WordTrace (prefixWord ++ tailWord_3732840) baseStart_3732840 baseEnd_3732840 := by
    simpa [prefixWord, tailWord_3732840, baseEnd_3732840] using wordTrace_append hprefix tailTrace_3732840
  have hstable : (prefixWord ++ tailWord_3732840).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3732840).length < 2 ^ (prefixWord ++ tailWord_3732840).sum := by decide
  have hdescent : baseEnd_3732840 < baseStart_3732840 := by decide
  rcases family_descends (prefixWord ++ tailWord_3732840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3732868 : List Nat := [2, 3, 2, 1, 1, 4, 3, 6]
def baseStart_3732868 : Nat := 118140960795 + 3732868 * 2 ^ 59
def prefixEnd_3732868 : Nat := 4983230072969 + 3 ^ 40 * 3732868 * 2
def baseEnd_3732868 : Nat := 141981889169452323739471

theorem tailTrace_3732868 : CollatzResearch.WordTrace tailWord_3732868 prefixEnd_3732868 141981889169452323739471 := by
  unfold tailWord_3732868
  simp only [CollatzResearch.WordTrace]
  refine ⟨68074440520232116971851629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90765920693642822629135505 68074440520232116971851629)
  ·
    refine ⟨25527915195087043864444361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68074440520232116971851629 25527915195087043864444361)
    ·
      refine ⟨19145936396315282898333271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25527915195087043864444361 19145936396315282898333271)
      ·
        refine ⟨28718904594472924347499907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19145936396315282898333271 28718904594472924347499907)
        ·
          refine ⟨43078356891709386521249861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28718904594472924347499907 43078356891709386521249861)
          ·
            refine ⟨8077191917195509972734349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43078356891709386521249861 8077191917195509972734349)
            ·
              refine ⟨3028946968948316239775381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8077191917195509972734349 3028946968948316239775381)
              ·
                refine ⟨141981889169452323739471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3028946968948316239775381 141981889169452323739471)
                ·
                  rfl

theorem cell22_3732868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 3, 6].length) (baseStart_3732868 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3732868 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3732868 prefixEnd_3732868 := by exact prefixLift 3732868
  have htrace : WordTrace (prefixWord ++ tailWord_3732868) baseStart_3732868 baseEnd_3732868 := by
    simpa [prefixWord, tailWord_3732868, baseEnd_3732868] using wordTrace_append hprefix tailTrace_3732868
  have hstable : (prefixWord ++ tailWord_3732868).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3732868).length < 2 ^ (prefixWord ++ tailWord_3732868).sum := by decide
  have hdescent : baseEnd_3732868 < baseStart_3732868 := by decide
  rcases family_descends (prefixWord ++ tailWord_3732868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3732896 : List Nat := [2, 1, 1, 4, 1, 2, 3, 1, 7]
def baseStart_3732896 : Nat := 118140960795 + 3732896 * 2 ^ 59
def prefixEnd_3732896 : Nat := 4983230072969 + 3 ^ 40 * 3732896 * 2
def baseEnd_3732896 : Nat := 425948862499096057985051

theorem tailTrace_3732896 : CollatzResearch.WordTrace tailWord_3732896 prefixEnd_3732896 425948862499096057985051 := by
  unfold tailWord_3732896
  simp only [CollatzResearch.WordTrace]
  refine ⟨68074951142181397362861271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90766601522908529817148361 68074951142181397362861271)
  ·
    refine ⟨102112426713272096044291907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68074951142181397362861271 102112426713272096044291907)
    ·
      refine ⟨153168640069908144066437861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102112426713272096044291907 153168640069908144066437861)
      ·
        refine ⟨28719120013107777012457099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 153168640069908144066437861 28719120013107777012457099)
        ·
          refine ⟨43078680019661665518685649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28719120013107777012457099 43078680019661665518685649)
          ·
            refine ⟨32309010014746249139014237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43078680019661665518685649 32309010014746249139014237)
            ·
              refine ⟨12115878755529843427130339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32309010014746249139014237 12115878755529843427130339)
              ·
                refine ⟨18173818133294765140695509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12115878755529843427130339 18173818133294765140695509)
                ·
                  refine ⟨425948862499096057985051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18173818133294765140695509 425948862499096057985051)
                  ·
                    rfl

theorem cell22_3732896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 3, 1, 7].length) (baseStart_3732896 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3732896 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3732896 prefixEnd_3732896 := by exact prefixLift 3732896
  have htrace : WordTrace (prefixWord ++ tailWord_3732896) baseStart_3732896 baseEnd_3732896 := by
    simpa [prefixWord, tailWord_3732896, baseEnd_3732896] using wordTrace_append hprefix tailTrace_3732896
  have hstable : (prefixWord ++ tailWord_3732896).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3732896).length < 2 ^ (prefixWord ++ tailWord_3732896).sum := by decide
  have hdescent : baseEnd_3732896 < baseStart_3732896 := by decide
  rcases family_descends (prefixWord ++ tailWord_3732896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3732943 : List Nat := [1, 1, 2, 1, 1, 4, 4, 3, 1, 4]
def baseStart_3732943 : Nat := 118140960795 + 3732943 * 2 ^ 59
def prefixEnd_3732943 : Nat := 4983230072969 + 3 ^ 40 * 3732943 * 2
def baseEnd_3732943 : Nat := 1277862676557795718030009

theorem tailTrace_3732943 : CollatzResearch.WordTrace tailWord_3732943 prefixEnd_3732943 1277862676557795718030009 := by
  unfold tailWord_3732943
  simp only [CollatzResearch.WordTrace]
  refine ⟨136151616515192521752683483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90767744343461681168455655 136151616515192521752683483)
  ·
    refine ⟨204227424772788782629025225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136151616515192521752683483 204227424772788782629025225)
    ·
      refine ⟨153170568579591586971768919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 204227424772788782629025225 153170568579591586971768919)
      ·
        refine ⟨229755852869387380457653379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153170568579591586971768919 229755852869387380457653379)
        ·
          refine ⟨344633779304081070686480069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 229755852869387380457653379 344633779304081070686480069)
          ·
            refine ⟨64618833619515200753715013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 344633779304081070686480069 64618833619515200753715013)
            ·
              refine ⟨12116031303659100141321565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64618833619515200753715013 12116031303659100141321565)
              ·
                refine ⟨4543511738872162552995587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12116031303659100141321565 4543511738872162552995587)
                ·
                  refine ⟨6815267608308243829493381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4543511738872162552995587 6815267608308243829493381)
                  ·
                    refine ⟨1277862676557795718030009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6815267608308243829493381 1277862676557795718030009)
                    ·
                      rfl

theorem cell22_3732943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 4, 3, 1, 4].length) (baseStart_3732943 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3732943 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3732943 prefixEnd_3732943 := by exact prefixLift 3732943
  have htrace : WordTrace (prefixWord ++ tailWord_3732943) baseStart_3732943 baseEnd_3732943 := by
    simpa [prefixWord, tailWord_3732943, baseEnd_3732943] using wordTrace_append hprefix tailTrace_3732943
  have hstable : (prefixWord ++ tailWord_3732943).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3732943).length < 2 ^ (prefixWord ++ tailWord_3732943).sum := by decide
  have hdescent : baseEnd_3732943 < baseStart_3732943 := by decide
  rcases family_descends (prefixWord ++ tailWord_3732943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3732971 : List Nat := [1, 1, 1, 1, 2, 3, 2, 4, 1, 6]
def baseStart_3732971 : Nat := 118140960795 + 3732971 * 2 ^ 59
def prefixEnd_3732971 : Nat := 4983230072969 + 3 ^ 40 * 3732971 * 2
def baseEnd_3732971 : Nat := 1277872261530012978329923

theorem tailTrace_3732971 : CollatzResearch.WordTrace tailWord_3732971 prefixEnd_3732971 1277872261530012978329923 := by
  unfold tailWord_3732971
  simp only [CollatzResearch.WordTrace]
  refine ⟨136152637759091082534702767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90768425172727388356468511 136152637759091082534702767)
  ·
    refine ⟨204228956638636623802054151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136152637759091082534702767 204228956638636623802054151)
    ·
      refine ⟨306343434957954935703081227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204228956638636623802054151 306343434957954935703081227)
      ·
        refine ⟨459515152436932403554621841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 306343434957954935703081227 459515152436932403554621841)
        ·
          refine ⟨344636364327699302665966381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 459515152436932403554621841 344636364327699302665966381)
          ·
            refine ⟨129238636622887238499737393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 344636364327699302665966381 129238636622887238499737393)
            ·
              refine ⟨96928977467165428874803045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 129238636622887238499737393 96928977467165428874803045)
              ·
                refine ⟨18174183275093517914025571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 96928977467165428874803045 18174183275093517914025571)
                ·
                  refine ⟨27261274912640276871038357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18174183275093517914025571 27261274912640276871038357)
                  ·
                    refine ⟨1277872261530012978329923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27261274912640276871038357 1277872261530012978329923)
                    ·
                      rfl

theorem cell22_3732971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 4, 1, 6].length) (baseStart_3732971 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3732971 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3732971 prefixEnd_3732971 := by exact prefixLift 3732971
  have htrace : WordTrace (prefixWord ++ tailWord_3732971) baseStart_3732971 baseEnd_3732971 := by
    simpa [prefixWord, tailWord_3732971, baseEnd_3732971] using wordTrace_append hprefix tailTrace_3732971
  have hstable : (prefixWord ++ tailWord_3732971).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3732971).length < 2 ^ (prefixWord ++ tailWord_3732971).sum := by decide
  have hdescent : baseEnd_3732971 < baseStart_3732971 := by decide
  rcases family_descends (prefixWord ++ tailWord_3732971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3732986 : List Nat := [3, 1, 1, 1, 1, 2, 3, 10]
def baseStart_3732986 : Nat := 118140960795 + 3732986 * 2 ^ 59
def prefixEnd_3732986 : Nat := 4983230072969 + 3 ^ 40 * 3732986 * 2
def baseEnd_3732986 : Nat := 141986377370728659911653

theorem tailTrace_3732986 : CollatzResearch.WordTrace tailWord_3732986 prefixEnd_3732986 141986377370728659911653 := by
  unfold tailWord_3732986
  simp only [CollatzResearch.WordTrace]
  refine ⟨34038296213509185024124703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90768789902691160064332541 34038296213509185024124703)
  ·
    refine ⟨51057444320263777536187055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34038296213509185024124703 51057444320263777536187055)
    ·
      refine ⟨76586166480395666304280583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51057444320263777536187055 76586166480395666304280583)
      ·
        refine ⟨114879249720593499456420875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76586166480395666304280583 114879249720593499456420875)
        ·
          refine ⟨172318874580890249184631313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114879249720593499456420875 172318874580890249184631313)
          ·
            refine ⟨129239155935667686888473485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 172318874580890249184631313 129239155935667686888473485)
            ·
              refine ⟨48464683475875382583177557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 129239155935667686888473485 48464683475875382583177557)
              ·
                refine ⟨141986377370728659911653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 48464683475875382583177557 141986377370728659911653)
                ·
                  rfl

theorem cell22_3732986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 10].length) (baseStart_3732986 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3732986 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3732986 prefixEnd_3732986 := by exact prefixLift 3732986
  have htrace : WordTrace (prefixWord ++ tailWord_3732986) baseStart_3732986 baseEnd_3732986 := by
    simpa [prefixWord, tailWord_3732986, baseEnd_3732986] using wordTrace_append hprefix tailTrace_3732986
  have hstable : (prefixWord ++ tailWord_3732986).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3732986).length < 2 ^ (prefixWord ++ tailWord_3732986).sum := by decide
  have hdescent : baseEnd_3732986 < baseStart_3732986 := by decide
  rcases family_descends (prefixWord ++ tailWord_3732986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3732988 : List Nat := [2, 2, 2, 1, 2, 1, 3, 3, 2, 4]
def baseStart_3732988 : Nat := 118140960795 + 3732988 * 2 ^ 59
def prefixEnd_3732988 : Nat := 4983230072969 + 3 ^ 40 * 3732988 * 2
def baseEnd_3732988 : Nat := 1277878080977430600654871

theorem tailTrace_3732988 : CollatzResearch.WordTrace tailWord_3732988 prefixEnd_3732988 1277878080977430600654871 := by
  unfold tailWord_3732988
  simp only [CollatzResearch.WordTrace]
  refine ⟨68076628900014747219035809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90768838533352996292047745 68076628900014747219035809)
  ·
    refine ⟨51057471675011060414276857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68076628900014747219035809 51057471675011060414276857)
    ·
      refine ⟨38293103756258295310707643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51057471675011060414276857 38293103756258295310707643)
      ·
        refine ⟨57439655634387442966061465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38293103756258295310707643 57439655634387442966061465)
        ·
          refine ⟨43079741725790582224546099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57439655634387442966061465 43079741725790582224546099)
          ·
            refine ⟨64619612588685873336819149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43079741725790582224546099 64619612588685873336819149)
            ·
              refine ⟨24232354720757202501307181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64619612588685873336819149 24232354720757202501307181)
              ·
                refine ⟨9087133020283950937990193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24232354720757202501307181 9087133020283950937990193)
                ·
                  refine ⟨6815349765212963203492645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9087133020283950937990193 6815349765212963203492645)
                  ·
                    refine ⟨1277878080977430600654871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6815349765212963203492645 1277878080977430600654871)
                    ·
                      rfl

theorem cell22_3732988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 3, 2, 4].length) (baseStart_3732988 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3732988 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3732988 prefixEnd_3732988 := by exact prefixLift 3732988
  have htrace : WordTrace (prefixWord ++ tailWord_3732988) baseStart_3732988 baseEnd_3732988 := by
    simpa [prefixWord, tailWord_3732988, baseEnd_3732988] using wordTrace_append hprefix tailTrace_3732988
  have hstable : (prefixWord ++ tailWord_3732988).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3732988).length < 2 ^ (prefixWord ++ tailWord_3732988).sum := by decide
  have hdescent : baseEnd_3732988 < baseStart_3732988 := by decide
  rcases family_descends (prefixWord ++ tailWord_3732988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3732994 : List Nat := [3, 4, 1, 2, 1, 2, 3, 1, 1, 4]
def baseStart_3732994 : Nat := 118140960795 + 3732994 * 2 ^ 59
def prefixEnd_3732994 : Nat := 4983230072969 + 3 ^ 40 * 3732994 * 2
def baseEnd_3732994 : Nat := 1277880134900048585004853

theorem tailTrace_3732994 : CollatzResearch.WordTrace tailWord_3732994 prefixEnd_3732994 1277880134900048585004853 := by
  unfold tailWord_3732994
  simp only [CollatzResearch.WordTrace]
  refine ⟨34038369159501939365697509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90768984425338504975193357 34038369159501939365697509)
  ·
    refine ⟨6382194217406613631068283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34038369159501939365697509 6382194217406613631068283)
    ·
      refine ⟨9573291326109920446602425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6382194217406613631068283 9573291326109920446602425)
      ·
        refine ⟨7179968494582440334951819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9573291326109920446602425 7179968494582440334951819)
        ·
          refine ⟨10769952741873660502427729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7179968494582440334951819 10769952741873660502427729)
          ·
            refine ⟨8077464556405245376820797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10769952741873660502427729 8077464556405245376820797)
            ·
              refine ⟨3029049208651967016307799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8077464556405245376820797 3029049208651967016307799)
              ·
                refine ⟨4543573812977950524461699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3029049208651967016307799 4543573812977950524461699)
                ·
                  refine ⟨6815360719466925786692549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4543573812977950524461699 6815360719466925786692549)
                  ·
                    refine ⟨1277880134900048585004853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6815360719466925786692549 1277880134900048585004853)
                    ·
                      rfl

theorem cell22_3732994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 3, 1, 1, 4].length) (baseStart_3732994 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3732994 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3732994 prefixEnd_3732994 := by exact prefixLift 3732994
  have htrace : WordTrace (prefixWord ++ tailWord_3732994) baseStart_3732994 baseEnd_3732994 := by
    simpa [prefixWord, tailWord_3732994, baseEnd_3732994] using wordTrace_append hprefix tailTrace_3732994
  have hstable : (prefixWord ++ tailWord_3732994).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3732994).length < 2 ^ (prefixWord ++ tailWord_3732994).sum := by decide
  have hdescent : baseEnd_3732994 < baseStart_3732994 := by decide
  rcases family_descends (prefixWord ++ tailWord_3732994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3733003 : List Nat := [1, 1, 1, 1, 9, 9]
def baseStart_3733003 : Nat := 118140960795 + 3733003 * 2 ^ 59
def prefixEnd_3733003 : Nat := 4983230072969 + 3 ^ 40 * 3733003 * 2
def baseEnd_3733003 : Nat := 15776335997333031623825

theorem tailTrace_3733003 : CollatzResearch.WordTrace tailWord_3733003 prefixEnd_3733003 15776335997333031623825 := by
  unfold tailWord_3733003
  simp only [CollatzResearch.WordTrace]
  refine ⟨136153804894975151999867663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90769203263316767999911775 136153804894975151999867663)
  ·
    refine ⟨204230707342462727999801495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136153804894975151999867663 204230707342462727999801495)
    ·
      refine ⟨306346061013694091999702243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204230707342462727999801495 306346061013694091999702243)
      ·
        refine ⟨459519091520541137999553365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 306346061013694091999702243 459519091520541137999553365)
        ·
          refine ⟨2692494676878170730466133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 459519091520541137999553365 2692494676878170730466133)
          ·
            refine ⟨15776335997333031623825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2692494676878170730466133 15776335997333031623825)
            ·
              rfl

theorem cell22_3733003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 9, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 9, 9].length) (baseStart_3733003 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3733003 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3733003 prefixEnd_3733003 := by exact prefixLift 3733003
  have htrace : WordTrace (prefixWord ++ tailWord_3733003) baseStart_3733003 baseEnd_3733003 := by
    simpa [prefixWord, tailWord_3733003, baseEnd_3733003] using wordTrace_append hprefix tailTrace_3733003
  have hstable : (prefixWord ++ tailWord_3733003).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3733003).length < 2 ^ (prefixWord ++ tailWord_3733003).sum := by decide
  have hdescent : baseEnd_3733003 < baseStart_3733003 := by decide
  rcases family_descends (prefixWord ++ tailWord_3733003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3733069 : List Nat := [1, 6, 1, 1, 3, 1, 2, 1, 3, 3]
def baseStart_3733069 : Nat := 118140960795 + 3733069 * 2 ^ 59
def prefixEnd_3733069 : Nat := 4983230072969 + 3 ^ 40 * 3733069 * 2
def baseEnd_3733069 : Nat := 1277905808932773389379623

theorem tailTrace_3733069 : CollatzResearch.WordTrace tailWord_3733069 prefixEnd_3733069 1277905808932773389379623 := by
  unfold tailWord_3733069
  simp only [CollatzResearch.WordTrace]
  refine ⟨136156212112736045271770261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90770808075157363514513507 136156212112736045271770261)
  ·
    refine ⟨6382322442784502122114231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 136156212112736045271770261 6382322442784502122114231)
    ·
      refine ⟨9573483664176753183171347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6382322442784502122114231 9573483664176753183171347)
      ·
        refine ⟨14360225496265129774757021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9573483664176753183171347 14360225496265129774757021)
        ·
          refine ⟨5385084561099423665533883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14360225496265129774757021 5385084561099423665533883)
          ·
            refine ⟨8077626841649135498300825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5385084561099423665533883 8077626841649135498300825)
            ·
              refine ⟨6058220131236851623725619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8077626841649135498300825 6058220131236851623725619)
              ·
                refine ⟨9087330196855277435588429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6058220131236851623725619 9087330196855277435588429)
                ·
                  refine ⟨3407748823820729038345661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9087330196855277435588429 3407748823820729038345661)
                  ·
                    refine ⟨1277905808932773389379623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3407748823820729038345661 1277905808932773389379623)
                    ·
                      rfl

theorem cell22_3733069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 2, 1, 3, 3].length) (baseStart_3733069 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3733069 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3733069 prefixEnd_3733069 := by exact prefixLift 3733069
  have htrace : WordTrace (prefixWord ++ tailWord_3733069) baseStart_3733069 baseEnd_3733069 := by
    simpa [prefixWord, tailWord_3733069, baseEnd_3733069] using wordTrace_append hprefix tailTrace_3733069
  have hstable : (prefixWord ++ tailWord_3733069).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3733069).length < 2 ^ (prefixWord ++ tailWord_3733069).sum := by decide
  have hdescent : baseEnd_3733069 < baseStart_3733069 := by decide
  rcases family_descends (prefixWord ++ tailWord_3733069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3733095 : List Nat := [1, 1, 5, 1, 1, 1, 3, 4, 1, 4]
def baseStart_3733095 : Nat := 118140960795 + 3733095 * 2 ^ 59
def prefixEnd_3733095 : Nat := 4983230072969 + 3 ^ 40 * 3733095 * 2
def baseEnd_3733095 : Nat := 1277914709264117988229543

theorem tailTrace_3733095 : CollatzResearch.WordTrace tailWord_3733095 prefixEnd_3733095 1277914709264117988229543 := by
  unfold tailWord_3733095
  simp only [CollatzResearch.WordTrace]
  refine ⟨136157160410641851712216739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90771440273761234474811159 136157160410641851712216739)
  ·
    refine ⟨204235740615962777568325109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136157160410641851712216739 204235740615962777568325109)
    ·
      refine ⟨19147100682746510397030479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 204235740615962777568325109 19147100682746510397030479)
      ·
        refine ⟨28720651024119765595545719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19147100682746510397030479 28720651024119765595545719)
        ·
          refine ⟨43080976536179648393318579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28720651024119765595545719 43080976536179648393318579)
          ·
            refine ⟨64621464804269472589977869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43080976536179648393318579 64621464804269472589977869)
            ·
              refine ⟨24233049301601052221241701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64621464804269472589977869 24233049301601052221241701)
              ·
                refine ⟨4543696744050197291482819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24233049301601052221241701 4543696744050197291482819)
                ·
                  refine ⟨6815545116075295937224229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4543696744050197291482819 6815545116075295937224229)
                  ·
                    refine ⟨1277914709264117988229543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6815545116075295937224229 1277914709264117988229543)
                    ·
                      rfl

theorem cell22_3733095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 4, 1, 4].length) (baseStart_3733095 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3733095 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3733095 prefixEnd_3733095 := by exact prefixLift 3733095
  have htrace : WordTrace (prefixWord ++ tailWord_3733095) baseStart_3733095 baseEnd_3733095 := by
    simpa [prefixWord, tailWord_3733095, baseEnd_3733095] using wordTrace_append hprefix tailTrace_3733095
  have hstable : (prefixWord ++ tailWord_3733095).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3733095).length < 2 ^ (prefixWord ++ tailWord_3733095).sum := by decide
  have hdescent : baseEnd_3733095 < baseStart_3733095 := by decide
  rcases family_descends (prefixWord ++ tailWord_3733095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3733125 : List Nat := [1, 3, 1, 1, 4, 1, 1, 3, 4, 3]
def baseStart_3733125 : Nat := 118140960795 + 3733125 * 2 ^ 59
def prefixEnd_3733125 : Nat := 4983230072969 + 3 ^ 40 * 3733125 * 2
def baseEnd_3733125 : Nat := 1277924978877207909979451

theorem tailTrace_3733125 : CollatzResearch.WordTrace tailWord_3733125 prefixEnd_3733125 1277924978877207909979451 := by
  unfold tailWord_3733125
  simp only [CollatzResearch.WordTrace]
  refine ⟨136158254600533166835808829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90772169733688777890539219 136158254600533166835808829)
  ·
    refine ⟨51059345475199937563428311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136158254600533166835808829 51059345475199937563428311)
    ·
      refine ⟨76589018212799906345142467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51059345475199937563428311 76589018212799906345142467)
      ·
        refine ⟨114883527319199859517713701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76589018212799906345142467 114883527319199859517713701)
        ·
          refine ⟨21540661372349973659571319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 114883527319199859517713701 21540661372349973659571319)
          ·
            refine ⟨32310992058524960489356979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21540661372349973659571319 32310992058524960489356979)
            ·
              refine ⟨48466488087787440734035469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32310992058524960489356979 48466488087787440734035469)
              ·
                refine ⟨18174933032920290275263301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48466488087787440734035469 18174933032920290275263301)
                ·
                  refine ⟨3407799943672554426611869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18174933032920290275263301 3407799943672554426611869)
                  ·
                    refine ⟨1277924978877207909979451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3407799943672554426611869 1277924978877207909979451)
                    ·
                      rfl

theorem cell22_3733125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 3, 4, 3].length) (baseStart_3733125 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3733125 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3733125 prefixEnd_3733125 := by exact prefixLift 3733125
  have htrace : WordTrace (prefixWord ++ tailWord_3733125) baseStart_3733125 baseEnd_3733125 := by
    simpa [prefixWord, tailWord_3733125, baseEnd_3733125] using wordTrace_append hprefix tailTrace_3733125
  have hstable : (prefixWord ++ tailWord_3733125).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3733125).length < 2 ^ (prefixWord ++ tailWord_3733125).sum := by decide
  have hdescent : baseEnd_3733125 < baseStart_3733125 := by decide
  rcases family_descends (prefixWord ++ tailWord_3733125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3733174 : List Nat := [5, 1, 3, 1, 1, 1, 2, 2, 2, 4]
def baseStart_3733174 : Nat := 118140960795 + 3733174 * 2 ^ 59
def prefixEnd_3733174 : Nat := 4983230072969 + 3 ^ 40 * 3733174 * 2
def baseEnd_3733174 : Nat := 1277941752578588115504301

theorem tailTrace_3733174 : CollatzResearch.WordTrace tailWord_3733174 prefixEnd_3733174 1277941752578588115504301 := by
  unfold tailWord_3733174
  simp only [CollatzResearch.WordTrace]
  refine ⟨8510002611084728012771411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 90773361184903765469561717 8510002611084728012771411)
  ·
    refine ⟨12765003916627092019157117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8510002611084728012771411 12765003916627092019157117)
    ·
      refine ⟨4786876468735159507183919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12765003916627092019157117 4786876468735159507183919)
      ·
        refine ⟨7180314703102739260775879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4786876468735159507183919 7180314703102739260775879)
        ·
          refine ⟨10770472054654108891163819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7180314703102739260775879 10770472054654108891163819)
          ·
            refine ⟨16155708081981163336745729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10770472054654108891163819 16155708081981163336745729)
            ·
              refine ⟨12116781061485872502559297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16155708081981163336745729 12116781061485872502559297)
              ·
                refine ⟨9087585796114404376919473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12116781061485872502559297 9087585796114404376919473)
                ·
                  refine ⟨6815689347085803282689605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9087585796114404376919473 6815689347085803282689605)
                  ·
                    refine ⟨1277941752578588115504301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6815689347085803282689605 1277941752578588115504301)
                    ·
                      rfl

theorem cell22_3733174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 2, 2, 2, 4].length) (baseStart_3733174 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3733174 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3733174 prefixEnd_3733174 := by exact prefixLift 3733174
  have htrace : WordTrace (prefixWord ++ tailWord_3733174) baseStart_3733174 baseEnd_3733174 := by
    simpa [prefixWord, tailWord_3733174, baseEnd_3733174] using wordTrace_append hprefix tailTrace_3733174
  have hstable : (prefixWord ++ tailWord_3733174).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3733174).length < 2 ^ (prefixWord ++ tailWord_3733174).sum := by decide
  have hdescent : baseEnd_3733174 < baseStart_3733174 := by decide
  rcases family_descends (prefixWord ++ tailWord_3733174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3733204 : List Nat := [2, 4, 1, 3, 1, 2, 1, 2, 3, 3]
def baseStart_3733204 : Nat := 118140960795 + 3733204 * 2 ^ 59
def prefixEnd_3733204 : Nat := 4983230072969 + 3 ^ 40 * 3733204 * 2
def baseEnd_3733204 : Nat := 1277952022191678037254209

theorem tailTrace_3733204 : CollatzResearch.WordTrace tailWord_3733204 prefixEnd_3733204 1277952022191678037254209 := by
  unfold tailWord_3733204
  simp only [CollatzResearch.WordTrace]
  refine ⟨68080567983623481663967333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90774090644831308885289777 68080567983623481663967333)
  ·
    refine ⟨12765106496929402811993875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 68080567983623481663967333 12765106496929402811993875)
    ·
      refine ⟨19147659745394104217990813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12765106496929402811993875 19147659745394104217990813)
      ·
        refine ⟨7180372404522789081746555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19147659745394104217990813 7180372404522789081746555)
        ·
          refine ⟨10770558606784183622619833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7180372404522789081746555 10770558606784183622619833)
          ·
            refine ⟨8077918955088137716964875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10770558606784183622619833 8077918955088137716964875)
            ·
              refine ⟨12116878432632206575447313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8077918955088137716964875 12116878432632206575447313)
              ·
                refine ⟨9087658824474154931585485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12116878432632206575447313 9087658824474154931585485)
                ·
                  refine ⟨3407872059177808099344557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9087658824474154931585485 3407872059177808099344557)
                  ·
                    refine ⟨1277952022191678037254209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3407872059177808099344557 1277952022191678037254209)
                    ·
                      rfl

theorem cell22_3733204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 1, 2, 3, 3].length) (baseStart_3733204 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3733204 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3733204 prefixEnd_3733204 := by exact prefixLift 3733204
  have htrace : WordTrace (prefixWord ++ tailWord_3733204) baseStart_3733204 baseEnd_3733204 := by
    simpa [prefixWord, tailWord_3733204, baseEnd_3733204] using wordTrace_append hprefix tailTrace_3733204
  have hstable : (prefixWord ++ tailWord_3733204).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3733204).length < 2 ^ (prefixWord ++ tailWord_3733204).sum := by decide
  have hdescent : baseEnd_3733204 < baseStart_3733204 := by decide
  rcases family_descends (prefixWord ++ tailWord_3733204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3733206 : List Nat := [5, 2, 1, 3, 1, 1, 3, 6]
def baseStart_3733206 : Nat := 118140960795 + 3733206 * 2 ^ 59
def prefixEnd_3733206 : Nat := 4983230072969 + 3 ^ 40 * 3733206 * 2
def baseEnd_3733206 : Nat := 141994745203616744300467

theorem tailTrace_3733206 : CollatzResearch.WordTrace tailWord_3733206 prefixEnd_3733206 141994745203616744300467 := by
  unfold tailWord_3733206
  simp only [CollatzResearch.WordTrace]
  refine ⟨8510075557077482354344217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 90774139275493145113004981 8510075557077482354344217)
  ·
    refine ⟨6382556667808111765758163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8510075557077482354344217 6382556667808111765758163)
    ·
      refine ⟨9573835001712167648637245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6382556667808111765758163 9573835001712167648637245)
      ·
        refine ⟨3590188125642062868238967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9573835001712167648637245 3590188125642062868238967)
        ·
          refine ⟨5385282188463094302358451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3590188125642062868238967 5385282188463094302358451)
          ·
            refine ⟨8077923282694641453537677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5385282188463094302358451 8077923282694641453537677)
            ·
              refine ⟨3029221231010490545076629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8077923282694641453537677 3029221231010490545076629)
              ·
                refine ⟨141994745203616744300467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3029221231010490545076629 141994745203616744300467)
                ·
                  rfl

theorem cell22_3733206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 3, 6].length) (baseStart_3733206 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3733206 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3733206 prefixEnd_3733206 := by exact prefixLift 3733206
  have htrace : WordTrace (prefixWord ++ tailWord_3733206) baseStart_3733206 baseEnd_3733206 := by
    simpa [prefixWord, tailWord_3733206, baseEnd_3733206] using wordTrace_append hprefix tailTrace_3733206
  have hstable : (prefixWord ++ tailWord_3733206).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3733206).length < 2 ^ (prefixWord ++ tailWord_3733206).sum := by decide
  have hdescent : baseEnd_3733206 < baseStart_3733206 := by decide
  rcases family_descends (prefixWord ++ tailWord_3733206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3733292 : List Nat := [2, 2, 1, 1, 1, 6, 1, 2, 2, 4]
def baseStart_3733292 : Nat := 118140960795 + 3733292 * 2 ^ 59
def prefixEnd_3733292 : Nat := 4983230072969 + 3 ^ 40 * 3733292 * 2
def baseEnd_3733292 : Nat := 1277982146390075141053939

theorem tailTrace_3733292 : CollatzResearch.WordTrace tailWord_3733292 prefixEnd_3733292 1277982146390075141053939 := by
  unfold tailWord_3733292
  simp only [CollatzResearch.WordTrace]
  refine ⟨68082172795464077178569065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90776230393952102904758753 68082172795464077178569065)
  ·
    refine ⟨51061629596598057883926799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68082172795464077178569065 51061629596598057883926799)
    ·
      refine ⟨76592444394897086825890199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51061629596598057883926799 76592444394897086825890199)
      ·
        refine ⟨114888666592345630238835299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76592444394897086825890199 114888666592345630238835299)
        ·
          refine ⟨172332999888518445358252949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114888666592345630238835299 172332999888518445358252949)
          ·
            refine ⟨8078109369774302126168107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 172332999888518445358252949 8078109369774302126168107)
            ·
              refine ⟨12117164054661453189252161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8078109369774302126168107 12117164054661453189252161)
              ·
                refine ⟨9087873040996089891939121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12117164054661453189252161 9087873040996089891939121)
                ·
                  refine ⟨6815904780747067418954341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9087873040996089891939121 6815904780747067418954341)
                  ·
                    refine ⟨1277982146390075141053939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6815904780747067418954341 1277982146390075141053939)
                    ·
                      rfl

theorem cell22_3733292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 4].length) (baseStart_3733292 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3733292 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3733292 prefixEnd_3733292 := by exact prefixLift 3733292
  have htrace : WordTrace (prefixWord ++ tailWord_3733292) baseStart_3733292 baseEnd_3733292 := by
    simpa [prefixWord, tailWord_3733292, baseEnd_3733292] using wordTrace_append hprefix tailTrace_3733292
  have hstable : (prefixWord ++ tailWord_3733292).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3733292).length < 2 ^ (prefixWord ++ tailWord_3733292).sum := by decide
  have hdescent : baseEnd_3733292 < baseStart_3733292 := by decide
  rcases family_descends (prefixWord ++ tailWord_3733292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3733322 : List Nat := [3, 1, 2, 1, 1, 1, 4, 1, 5, 3]
def baseStart_3733322 : Nat := 118140960795 + 3733322 * 2 ^ 59
def prefixEnd_3733322 : Nat := 4983230072969 + 3 ^ 40 * 3733322 * 2
def baseEnd_3733322 : Nat := 1277992416003165062803847

theorem tailTrace_3733322 : CollatzResearch.WordTrace tailWord_3733322 prefixEnd_3733322 1277992416003165062803847 := by
  unfold tailWord_3733322
  simp only [CollatzResearch.WordTrace]
  refine ⟨34041359945204867370182555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90776959853879646320486813 34041359945204867370182555)
  ·
    refine ⟨51062039917807301055273833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34041359945204867370182555 51062039917807301055273833)
    ·
      refine ⟨38296529938355475791455375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51062039917807301055273833 38296529938355475791455375)
      ·
        refine ⟨57444794907533213687183063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38296529938355475791455375 57444794907533213687183063)
        ·
          refine ⟨86167192361299820530774595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57444794907533213687183063 86167192361299820530774595)
          ·
            refine ⟨129250788541949730796161893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86167192361299820530774595 129250788541949730796161893)
            ·
              refine ⟨24234522851615574524280355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 129250788541949730796161893 24234522851615574524280355)
              ·
                refine ⟨36351784277423361786420533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24234522851615574524280355 36351784277423361786420533)
                ·
                  refine ⟨3407979776008440167476925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 36351784277423361786420533 3407979776008440167476925)
                  ·
                    refine ⟨1277992416003165062803847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3407979776008440167476925 1277992416003165062803847)
                    ·
                      rfl

theorem cell22_3733322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 1, 5, 3].length) (baseStart_3733322 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3733322 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3733322 prefixEnd_3733322 := by exact prefixLift 3733322
  have htrace : WordTrace (prefixWord ++ tailWord_3733322) baseStart_3733322 baseEnd_3733322 := by
    simpa [prefixWord, tailWord_3733322, baseEnd_3733322] using wordTrace_append hprefix tailTrace_3733322
  have hstable : (prefixWord ++ tailWord_3733322).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3733322).length < 2 ^ (prefixWord ++ tailWord_3733322).sum := by decide
  have hdescent : baseEnd_3733322 < baseStart_3733322 := by decide
  rcases family_descends (prefixWord ++ tailWord_3733322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3733356 : List Nat := [2, 2, 1, 1, 4, 3, 1, 4, 1, 3]
def baseStart_3733356 : Nat := 118140960795 + 3733356 * 2 ^ 59
def prefixEnd_3733356 : Nat := 4983230072969 + 3 ^ 40 * 3733356 * 2
def baseEnd_3733356 : Nat := 1278004054898000307453743

theorem tailTrace_3733356 : CollatzResearch.WordTrace tailWord_3733356 prefixEnd_3733356 1278004054898000307453743 := by
  unfold tailWord_3733356
  simp only [CollatzResearch.WordTrace]
  refine ⟨68083339931348146643733961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90777786575130862191645281 68083339931348146643733961)
  ·
    refine ⟨51062504948511109982800471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68083339931348146643733961 51062504948511109982800471)
    ·
      refine ⟨76593757422766664974200707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51062504948511109982800471 76593757422766664974200707)
      ·
        refine ⟨114890636134149997461301061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76593757422766664974200707 114890636134149997461301061)
        ·
          refine ⟨21541994275153124523993949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 114890636134149997461301061 21541994275153124523993949)
          ·
            refine ⟨8078247853182421696497731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21541994275153124523993949 8078247853182421696497731)
            ·
              refine ⟨12117371779773632544746597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8078247853182421696497731 12117371779773632544746597)
              ·
                refine ⟨2272007208707556102139987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12117371779773632544746597 2272007208707556102139987)
                ·
                  refine ⟨3408010813061334153209981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2272007208707556102139987 3408010813061334153209981)
                  ·
                    refine ⟨1278004054898000307453743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3408010813061334153209981 1278004054898000307453743)
                    ·
                      rfl

theorem cell22_3733356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 1, 4, 1, 3].length) (baseStart_3733356 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3733356 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3733356 prefixEnd_3733356 := by exact prefixLift 3733356
  have htrace : WordTrace (prefixWord ++ tailWord_3733356) baseStart_3733356 baseEnd_3733356 := by
    simpa [prefixWord, tailWord_3733356, baseEnd_3733356] using wordTrace_append hprefix tailTrace_3733356
  have hstable : (prefixWord ++ tailWord_3733356).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3733356).length < 2 ^ (prefixWord ++ tailWord_3733356).sum := by decide
  have hdescent : baseEnd_3733356 < baseStart_3733356 := by decide
  rcases family_descends (prefixWord ++ tailWord_3733356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3733390 : List Nat := [4, 1, 1, 5, 1, 1, 2, 3, 1, 3]
def baseStart_3733390 : Nat := 118140960795 + 3733390 * 2 ^ 59
def prefixEnd_3733390 : Nat := 4983230072969 + 3 ^ 40 * 3733390 * 2
def baseEnd_3733390 : Nat := 1278015693792835552103639

theorem tailTrace_3733390 : CollatzResearch.WordTrace tailWord_3733390 prefixEnd_3733390 1278015693792835552103639 := by
  unfold tailWord_3733390
  simp only [CollatzResearch.WordTrace]
  refine ⟨17020989993071639636775703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 90778613296382078062803749 17020989993071639636775703)
  ·
    refine ⟨25531484989607459455163555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17020989993071639636775703 25531484989607459455163555)
    ·
      refine ⟨38297227484411189182745333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25531484989607459455163555 38297227484411189182745333)
      ·
        refine ⟨3590365076663548985882375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 38297227484411189182745333 3590365076663548985882375)
        ·
          refine ⟨5385547614995323478823563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3590365076663548985882375 5385547614995323478823563)
          ·
            refine ⟨8078321422492985218235345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5385547614995323478823563 8078321422492985218235345)
            ·
              refine ⟨6058741066869738913676509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8078321422492985218235345 6058741066869738913676509)
              ·
                refine ⟨2272027900076152092628691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6058741066869738913676509 2272027900076152092628691)
                ·
                  refine ⟨3408041850114228138943037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2272027900076152092628691 3408041850114228138943037)
                  ·
                    refine ⟨1278015693792835552103639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3408041850114228138943037 1278015693792835552103639)
                    ·
                      rfl

theorem cell22_3733390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 2, 3, 1, 3].length) (baseStart_3733390 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3733390 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3733390 prefixEnd_3733390 := by exact prefixLift 3733390
  have htrace : WordTrace (prefixWord ++ tailWord_3733390) baseStart_3733390 baseEnd_3733390 := by
    simpa [prefixWord, tailWord_3733390, baseEnd_3733390] using wordTrace_append hprefix tailTrace_3733390
  have hstable : (prefixWord ++ tailWord_3733390).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3733390).length < 2 ^ (prefixWord ++ tailWord_3733390).sum := by decide
  have hdescent : baseEnd_3733390 < baseStart_3733390 := by decide
  rcases family_descends (prefixWord ++ tailWord_3733390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3733395 : List Nat := [1, 1, 1, 2, 1, 2, 1, 2, 2, 9]
def baseStart_3733395 : Nat := 118140960795 + 3733395 * 2 ^ 59
def prefixEnd_3733395 : Nat := 4983230072969 + 3 ^ 40 * 3733395 * 2
def baseEnd_3733395 : Nat := 1278017405395017205728623

theorem tailTrace_3733395 : CollatzResearch.WordTrace tailWord_3733395 prefixEnd_3733395 1278017405395017205728623 := by
  unfold tailWord_3733395
  simp only [CollatzResearch.WordTrace]
  refine ⟨136168102309555002948137639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90778734873036668632091759 136168102309555002948137639)
  ·
    refine ⟨204252153464332504422206459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136168102309555002948137639 204252153464332504422206459)
    ·
      refine ⟨306378230196498756633309689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204252153464332504422206459 306378230196498756633309689)
      ·
        refine ⟨229783672647374067474982267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 306378230196498756633309689 229783672647374067474982267)
        ·
          refine ⟨344675508971061101212473401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 229783672647374067474982267 344675508971061101212473401)
          ·
            refine ⟨258506631728295825909355051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 344675508971061101212473401 258506631728295825909355051)
            ·
              refine ⟨387759947592443738864032577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 258506631728295825909355051 387759947592443738864032577)
              ·
                refine ⟨290819960694332804148024433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 387759947592443738864032577 290819960694332804148024433)
                ·
                  refine ⟨218114970520749603111018325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 290819960694332804148024433 218114970520749603111018325)
                  ·
                    refine ⟨1278017405395017205728623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 218114970520749603111018325 1278017405395017205728623)
                    ·
                      rfl

theorem cell22_3733395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 2, 2, 9].length) (baseStart_3733395 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3733395 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3733395 prefixEnd_3733395 := by exact prefixLift 3733395
  have htrace : WordTrace (prefixWord ++ tailWord_3733395) baseStart_3733395 baseEnd_3733395 := by
    simpa [prefixWord, tailWord_3733395, baseEnd_3733395] using wordTrace_append hprefix tailTrace_3733395
  have hstable : (prefixWord ++ tailWord_3733395).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3733395).length < 2 ^ (prefixWord ++ tailWord_3733395).sum := by decide
  have hdescent : baseEnd_3733395 < baseStart_3733395 := by decide
  rcases family_descends (prefixWord ++ tailWord_3733395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3733399 : List Nat := [1, 1, 3, 3, 1, 4, 1, 3, 1, 4]
def baseStart_3733399 : Nat := 118140960795 + 3733399 * 2 ^ 59
def prefixEnd_3733399 : Nat := 4983230072969 + 3 ^ 40 * 3733399 * 2
def baseEnd_3733399 : Nat := 1278018774676762528628611

theorem tailTrace_3733399 : CollatzResearch.WordTrace tailWord_3733399 prefixEnd_3733399 1278018774676762528628611 := by
  unfold tailWord_3733399
  simp only [CollatzResearch.WordTrace]
  refine ⟨136168248201540511631283251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90778832134360341087522167 136168248201540511631283251)
  ·
    refine ⟨204252372302310767446924877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136168248201540511631283251 204252372302310767446924877)
    ·
      refine ⟨76594639613366537792596829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 204252372302310767446924877 76594639613366537792596829)
      ·
        refine ⟨28722989855012451672223811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76594639613366537792596829 28722989855012451672223811)
        ·
          refine ⟨43084484782518677508335717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28722989855012451672223811 43084484782518677508335717)
          ·
            refine ⟨8078340896722252032812947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43084484782518677508335717 8078340896722252032812947)
            ·
              refine ⟨12117511345083378049219421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8078340896722252032812947 12117511345083378049219421)
              ·
                refine ⟨4544066754406266768457283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12117511345083378049219421 4544066754406266768457283)
                ·
                  refine ⟨6816100131609400152685925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4544066754406266768457283 6816100131609400152685925)
                  ·
                    refine ⟨1278018774676762528628611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6816100131609400152685925 1278018774676762528628611)
                    ·
                      rfl

theorem cell22_3733399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 1, 3, 1, 4].length) (baseStart_3733399 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3733399 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3733399 prefixEnd_3733399 := by exact prefixLift 3733399
  have htrace : WordTrace (prefixWord ++ tailWord_3733399) baseStart_3733399 baseEnd_3733399 := by
    simpa [prefixWord, tailWord_3733399, baseEnd_3733399] using wordTrace_append hprefix tailTrace_3733399
  have hstable : (prefixWord ++ tailWord_3733399).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3733399).length < 2 ^ (prefixWord ++ tailWord_3733399).sum := by decide
  have hdescent : baseEnd_3733399 < baseStart_3733399 := by decide
  rcases family_descends (prefixWord ++ tailWord_3733399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3733429 : List Nat := [1, 3, 3, 2, 1, 2, 3, 1, 1, 5]
def baseStart_3733429 : Nat := 118140960795 + 3733429 * 2 ^ 59
def prefixEnd_3733429 : Nat := 4983230072969 + 3 ^ 40 * 3733429 * 2
def baseEnd_3733429 : Nat := 1278029044289852450378519

theorem tailTrace_3733429 : CollatzResearch.WordTrace tailWord_3733429 prefixEnd_3733429 1278029044289852450378519 := by
  unfold tailWord_3733429
  simp only [CollatzResearch.WordTrace]
  refine ⟨136169342391431826754875341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90779561594287884503250227 136169342391431826754875341)
  ·
    refine ⟨51063503396786935033078253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136169342391431826754875341 51063503396786935033078253)
    ·
      refine ⟨19148813773795100637404345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51063503396786935033078253 19148813773795100637404345)
      ·
        refine ⟨14361610330346325478053259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19148813773795100637404345 14361610330346325478053259)
        ·
          refine ⟨21542415495519488217079889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14361610330346325478053259 21542415495519488217079889)
          ·
            refine ⟨16156811621639616162809917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21542415495519488217079889 16156811621639616162809917)
            ·
              refine ⟨6058804358114856061053719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16156811621639616162809917 6058804358114856061053719)
              ·
                refine ⟨9088206537172284091580579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6058804358114856061053719 9088206537172284091580579)
                ·
                  refine ⟨13632309805758426137370869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9088206537172284091580579 13632309805758426137370869)
                  ·
                    refine ⟨1278029044289852450378519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13632309805758426137370869 1278029044289852450378519)
                    ·
                      rfl

theorem cell22_3733429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 3, 1, 1, 5].length) (baseStart_3733429 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3733429 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3733429 prefixEnd_3733429 := by exact prefixLift 3733429
  have htrace : WordTrace (prefixWord ++ tailWord_3733429) baseStart_3733429 baseEnd_3733429 := by
    simpa [prefixWord, tailWord_3733429, baseEnd_3733429] using wordTrace_append hprefix tailTrace_3733429
  have hstable : (prefixWord ++ tailWord_3733429).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3733429).length < 2 ^ (prefixWord ++ tailWord_3733429).sum := by decide
  have hdescent : baseEnd_3733429 < baseStart_3733429 := by decide
  rcases family_descends (prefixWord ++ tailWord_3733429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3733510 : List Nat := [6, 2, 1, 2, 2, 9]
def baseStart_3733510 : Nat := 118140960795 + 3733510 * 2 ^ 59
def prefixEnd_3733510 : Nat := 4983230072969 + 3 ^ 40 * 3733510 * 2
def baseEnd_3733510 : Nat := 15778478669693768383991

theorem tailTrace_3733510 : CollatzResearch.WordTrace tailWord_3733510 prefixEnd_3733510 15778478669693768383991 := by
  unfold tailWord_3733510
  simp only [CollatzResearch.WordTrace]
  refine ⟨4255384272004324299642937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 90781531136092251725715989 4255384272004324299642937)
  ·
    refine ⟨3191538204003243224732203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4255384272004324299642937 3191538204003243224732203)
    ·
      refine ⟨4787307306004864837098305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3191538204003243224732203 4787307306004864837098305)
      ·
        refine ⟨3590480479503648627823729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4787307306004864837098305 3590480479503648627823729)
        ·
          refine ⟨2692860359627736470867797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3590480479503648627823729 2692860359627736470867797)
          ·
            refine ⟨15778478669693768383991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2692860359627736470867797 15778478669693768383991)
            ·
              rfl

theorem cell22_3733510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 2, 9].length) (baseStart_3733510 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3733510 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3733510 prefixEnd_3733510 := by exact prefixLift 3733510
  have htrace : WordTrace (prefixWord ++ tailWord_3733510) baseStart_3733510 baseEnd_3733510 := by
    simpa [prefixWord, tailWord_3733510, baseEnd_3733510] using wordTrace_append hprefix tailTrace_3733510
  have hstable : (prefixWord ++ tailWord_3733510).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3733510).length < 2 ^ (prefixWord ++ tailWord_3733510).sum := by decide
  have hdescent : baseEnd_3733510 < baseStart_3733510 := by decide
  rcases family_descends (prefixWord ++ tailWord_3733510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3733564 : List Nat := [2, 2, 2, 2, 2, 1, 1, 4, 1, 5]
def baseStart_3733564 : Nat := 118140960795 + 3733564 * 2 ^ 59
def prefixEnd_3733564 : Nat := 4983230072969 + 3 ^ 40 * 3733564 * 2
def baseEnd_3733564 : Nat := 1278075257548757098253105

theorem tailTrace_3733564 : CollatzResearch.WordTrace tailWord_3733564 prefixEnd_3733564 1278075257548757098253105 := by
  unfold tailWord_3733564
  simp only [CollatzResearch.WordTrace]
  refine ⟨68087133122971372405519873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90782844163961829874026497 68087133122971372405519873)
  ·
    refine ⟨51065349842228529304139905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68087133122971372405519873 51065349842228529304139905)
    ·
      refine ⟨38299012381671396978104929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51065349842228529304139905 38299012381671396978104929)
      ·
        refine ⟨28724259286253547733578697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38299012381671396978104929 28724259286253547733578697)
        ·
          refine ⟨21543194464690160800184023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28724259286253547733578697 21543194464690160800184023)
          ·
            refine ⟨32314791697035241200276035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21543194464690160800184023 32314791697035241200276035)
            ·
              refine ⟨48472187545552861800414053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32314791697035241200276035 48472187545552861800414053)
              ·
                refine ⟨9088535164791161587577635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48472187545552861800414053 9088535164791161587577635)
                ·
                  refine ⟨13632802747186742381366453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9088535164791161587577635 13632802747186742381366453)
                  ·
                    refine ⟨1278075257548757098253105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13632802747186742381366453 1278075257548757098253105)
                    ·
                      rfl

theorem cell22_3733564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 4, 1, 5].length) (baseStart_3733564 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3733564 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3733564 prefixEnd_3733564 := by exact prefixLift 3733564
  have htrace : WordTrace (prefixWord ++ tailWord_3733564) baseStart_3733564 baseEnd_3733564 := by
    simpa [prefixWord, tailWord_3733564, baseEnd_3733564] using wordTrace_append hprefix tailTrace_3733564
  have hstable : (prefixWord ++ tailWord_3733564).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3733564).length < 2 ^ (prefixWord ++ tailWord_3733564).sum := by decide
  have hdescent : baseEnd_3733564 < baseStart_3733564 := by decide
  rcases family_descends (prefixWord ++ tailWord_3733564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3733568 : List Nat := [2, 1, 1, 2, 2, 6, 2, 1, 1, 4]
def baseStart_3733568 : Nat := 118140960795 + 3733568 * 2 ^ 59
def prefixEnd_3733568 : Nat := 4983230072969 + 3 ^ 40 * 3733568 * 2
def baseEnd_3733568 : Nat := 1278076626830502421153093

theorem tailTrace_3733568 : CollatzResearch.WordTrace tailWord_3733568 prefixEnd_3733568 1278076626830502421153093 := by
  unfold tailWord_3733568
  simp only [CollatzResearch.WordTrace]
  refine ⟨68087206068964126747092679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90782941425285502329456905 68087206068964126747092679)
  ·
    refine ⟨102130809103446190120639019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68087206068964126747092679 102130809103446190120639019)
    ·
      refine ⟨153196213655169285180958529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102130809103446190120639019 153196213655169285180958529)
      ·
        refine ⟨114897160241376963885718897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153196213655169285180958529 114897160241376963885718897)
        ·
          refine ⟨86172870181032722914289173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114897160241376963885718897 86172870181032722914289173)
          ·
            refine ⟨4039353289735908886607305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 86172870181032722914289173 4039353289735908886607305)
            ·
              refine ⟨3029514967301931664955479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4039353289735908886607305 3029514967301931664955479)
              ·
                refine ⟨4544272450952897497433219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3029514967301931664955479 4544272450952897497433219)
                ·
                  refine ⟨6816408676429346246149829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4544272450952897497433219 6816408676429346246149829)
                  ·
                    refine ⟨1278076626830502421153093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6816408676429346246149829 1278076626830502421153093)
                    ·
                      rfl

theorem cell22_3733568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 6, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 6, 2, 1, 1, 4].length) (baseStart_3733568 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3733568 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3733568 prefixEnd_3733568 := by exact prefixLift 3733568
  have htrace : WordTrace (prefixWord ++ tailWord_3733568) baseStart_3733568 baseEnd_3733568 := by
    simpa [prefixWord, tailWord_3733568, baseEnd_3733568] using wordTrace_append hprefix tailTrace_3733568
  have hstable : (prefixWord ++ tailWord_3733568).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3733568).length < 2 ^ (prefixWord ++ tailWord_3733568).sum := by decide
  have hdescent : baseEnd_3733568 < baseStart_3733568 := by decide
  rcases family_descends (prefixWord ++ tailWord_3733568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3733577 : List Nat := [1, 2, 1, 1, 2, 2, 13]
def baseStart_3733577 : Nat := 118140960795 + 3733577 * 2 ^ 59
def prefixEnd_3733577 : Nat := 4983230072969 + 3 ^ 40 * 3733577 * 2
def baseEnd_3733577 : Nat := 47336285470904792506595

theorem tailTrace_3733577 : CollatzResearch.WordTrace tailWord_3733577 prefixEnd_3733577 47336285470904792506595 := by
  unfold tailWord_3733577
  simp only [CollatzResearch.WordTrace]
  refine ⟨136174740394895648031262985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90783160263263765354175323 136174740394895648031262985)
  ·
    refine ⟨102131055296171736023447239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136174740394895648031262985 102131055296171736023447239)
    ·
      refine ⟨153196582944257604035170859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102131055296171736023447239 153196582944257604035170859)
      ·
        refine ⟨229794874416386406052756289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153196582944257604035170859 229794874416386406052756289)
        ·
          refine ⟨172346155812289804539567217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 229794874416386406052756289 172346155812289804539567217)
          ·
            refine ⟨129259616859217353404675413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 172346155812289804539567217 129259616859217353404675413)
            ·
              refine ⟨47336285470904792506595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 129259616859217353404675413 47336285470904792506595)
              ·
                rfl

theorem cell22_3733577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 13].length) (baseStart_3733577 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3733577 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3733577 prefixEnd_3733577 := by exact prefixLift 3733577
  have htrace : WordTrace (prefixWord ++ tailWord_3733577) baseStart_3733577 baseEnd_3733577 := by
    simpa [prefixWord, tailWord_3733577, baseEnd_3733577] using wordTrace_append hprefix tailTrace_3733577
  have hstable : (prefixWord ++ tailWord_3733577).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3733577).length < 2 ^ (prefixWord ++ tailWord_3733577).sum := by decide
  have hdescent : baseEnd_3733577 < baseStart_3733577 := by decide
  rcases family_descends (prefixWord ++ tailWord_3733577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3733639 : List Nat := [1, 1, 4, 2, 1, 1, 4, 1, 7]
def baseStart_3733639 : Nat := 118140960795 + 3733639 * 2 ^ 59
def prefixEnd_3733639 : Nat := 4983230072969 + 3 ^ 40 * 3733639 * 2
def baseEnd_3733639 : Nat := 426033643860493967542625

theorem tailTrace_3733639 : CollatzResearch.WordTrace tailWord_3733639 prefixEnd_3733639 426033643860493967542625 := by
  unfold tailWord_3733639
  simp only [CollatzResearch.WordTrace]
  refine ⟨136177001720671032620019971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90784667813780688413346647 136177001720671032620019971)
  ·
    refine ⟨204265502581006548930029957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136177001720671032620019971 204265502581006548930029957)
    ·
      refine ⟨38299781733938727924380617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 204265502581006548930029957 38299781733938727924380617)
      ·
        refine ⟨28724836300454045943285463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38299781733938727924380617 28724836300454045943285463)
        ·
          refine ⟨43087254450681068914928195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28724836300454045943285463 43087254450681068914928195)
          ·
            refine ⟨64630881676021603372392293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43087254450681068914928195 64630881676021603372392293)
            ·
              refine ⟨12118290314254050632323555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64630881676021603372392293 12118290314254050632323555)
              ·
                refine ⟨18177435471381075948485333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12118290314254050632323555 18177435471381075948485333)
                ·
                  refine ⟨426033643860493967542625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18177435471381075948485333 426033643860493967542625)
                  ·
                    rfl

theorem cell22_3733639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 4, 1, 7].length) (baseStart_3733639 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3733639 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3733639 prefixEnd_3733639 := by exact prefixLift 3733639
  have htrace : WordTrace (prefixWord ++ tailWord_3733639) baseStart_3733639 baseEnd_3733639 := by
    simpa [prefixWord, tailWord_3733639, baseEnd_3733639] using wordTrace_append hprefix tailTrace_3733639
  have hstable : (prefixWord ++ tailWord_3733639).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3733639).length < 2 ^ (prefixWord ++ tailWord_3733639).sum := by decide
  have hdescent : baseEnd_3733639 < baseStart_3733639 := by decide
  rcases family_descends (prefixWord ++ tailWord_3733639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3733694 : List Nat := [4, 2, 1, 1, 4, 2, 2, 2, 1, 3]
def baseStart_3733694 : Nat := 118140960795 + 3733694 * 2 ^ 59
def prefixEnd_3733694 : Nat := 4983230072969 + 3 ^ 40 * 3733694 * 2
def baseEnd_3733694 : Nat := 1278119759205480092502707

theorem tailTrace_3733694 : CollatzResearch.WordTrace tailWord_3733694 prefixEnd_3733694 1278119759205480092502707 := by
  unfold tailWord_3733694
  simp only [CollatzResearch.WordTrace]
  refine ⟨17022375966933972126659017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 90786005156981184675514757 17022375966933972126659017)
  ·
    refine ⟨12766781975200479094994263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17022375966933972126659017 12766781975200479094994263)
    ·
      refine ⟨19150172962800718642491395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12766781975200479094994263 19150172962800718642491395)
      ·
        refine ⟨28725259444201077963737093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19150172962800718642491395 28725259444201077963737093)
        ·
          refine ⟨5385986145787702118200705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28725259444201077963737093 5385986145787702118200705)
          ·
            refine ⟨4039489609340776588650529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5385986145787702118200705 4039489609340776588650529)
            ·
              refine ⟨3029617207005582441487897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4039489609340776588650529 3029617207005582441487897)
              ·
                refine ⟨2272212905254186831115923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3029617207005582441487897 2272212905254186831115923)
                ·
                  refine ⟨3408319357881280246673885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2272212905254186831115923 3408319357881280246673885)
                  ·
                    refine ⟨1278119759205480092502707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3408319357881280246673885 1278119759205480092502707)
                    ·
                      rfl

theorem cell22_3733694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 2, 2, 2, 1, 3].length) (baseStart_3733694 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3733694 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3733694 prefixEnd_3733694 := by exact prefixLift 3733694
  have htrace : WordTrace (prefixWord ++ tailWord_3733694) baseStart_3733694 baseEnd_3733694 := by
    simpa [prefixWord, tailWord_3733694, baseEnd_3733694] using wordTrace_append hprefix tailTrace_3733694
  have hstable : (prefixWord ++ tailWord_3733694).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3733694).length < 2 ^ (prefixWord ++ tailWord_3733694).sum := by decide
  have hdescent : baseEnd_3733694 < baseStart_3733694 := by decide
  rcases family_descends (prefixWord ++ tailWord_3733694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3733718 : List Nat := [5, 2, 1, 2, 1, 1, 1, 1, 8]
def baseStart_3733718 : Nat := 118140960795 + 3733718 * 2 ^ 59
def prefixEnd_3733718 : Nat := 4983230072969 + 3 ^ 40 * 3733718 * 2
def baseEnd_3733718 : Nat := 426042658298650676634211

theorem tailTrace_3733718 : CollatzResearch.WordTrace tailWord_3733718 prefixEnd_3733718 426042658298650676634211 := by
  unfold tailWord_3733718
  simp only [CollatzResearch.WordTrace]
  refine ⟨8511242692961551819509113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 90786588724923219408097205 8511242692961551819509113)
  ·
    refine ⟨6383432019721163864631835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8511242692961551819509113 6383432019721163864631835)
    ·
      refine ⟨9575148029581745796947753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6383432019721163864631835 9575148029581745796947753)
      ·
        refine ⟨7181361022186309347710815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9575148029581745796947753 7181361022186309347710815)
        ·
          refine ⟨10772041533279464021566223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7181361022186309347710815 10772041533279464021566223)
          ·
            refine ⟨16158062299919196032349335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10772041533279464021566223 16158062299919196032349335)
            ·
              refine ⟨24237093449878794048524003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16158062299919196032349335 24237093449878794048524003)
              ·
                refine ⟨36355640174818191072786005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24237093449878794048524003 36355640174818191072786005)
                ·
                  refine ⟨426042658298650676634211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 36355640174818191072786005 426042658298650676634211)
                  ·
                    rfl

theorem cell22_3733718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 1, 8].length) (baseStart_3733718 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3733718 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3733718 prefixEnd_3733718 := by exact prefixLift 3733718
  have htrace : WordTrace (prefixWord ++ tailWord_3733718) baseStart_3733718 baseEnd_3733718 := by
    simpa [prefixWord, tailWord_3733718, baseEnd_3733718] using wordTrace_append hprefix tailTrace_3733718
  have hstable : (prefixWord ++ tailWord_3733718).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3733718).length < 2 ^ (prefixWord ++ tailWord_3733718).sum := by decide
  have hdescent : baseEnd_3733718 < baseStart_3733718 := by decide
  rcases family_descends (prefixWord ++ tailWord_3733718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3733735 : List Nat := [1, 1, 5, 3, 1, 2, 2, 3, 4]
def baseStart_3733735 : Nat := 118140960795 + 3733735 * 2 ^ 59
def prefixEnd_3733735 : Nat := 4983230072969 + 3 ^ 40 * 3733735 * 2
def baseEnd_3733735 : Nat := 426044598114456550742527

theorem tailTrace_3733735 : CollatzResearch.WordTrace tailWord_3733735 prefixEnd_3733735 426044598114456550742527 := by
  unfold tailWord_3733735
  simp only [CollatzResearch.WordTrace]
  refine ⟨136180503128323241015514659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90787002085548827343676439 136180503128323241015514659)
  ·
    refine ⟨204270754692484861523271989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136180503128323241015514659 204270754692484861523271989)
    ·
      refine ⟨19150383252420455767806749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 204270754692484861523271989 19150383252420455767806749)
      ·
        refine ⟨7181393719657670912927531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19150383252420455767806749 7181393719657670912927531)
        ·
          refine ⟨10772090579486506369391297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7181393719657670912927531 10772090579486506369391297)
          ·
            refine ⟨8079067934614879777043473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10772090579486506369391297 8079067934614879777043473)
            ·
              refine ⟨6059300950961159832782605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8079067934614879777043473 6059300950961159832782605)
              ·
                refine ⟨2272237856610434937293477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6059300950961159832782605 2272237856610434937293477)
                ·
                  refine ⟨426044598114456550742527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2272237856610434937293477 426044598114456550742527)
                  ·
                    rfl

theorem cell22_3733735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 2, 3, 4].length) (baseStart_3733735 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3733735 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3733735 prefixEnd_3733735 := by exact prefixLift 3733735
  have htrace : WordTrace (prefixWord ++ tailWord_3733735) baseStart_3733735 baseEnd_3733735 := by
    simpa [prefixWord, tailWord_3733735, baseEnd_3733735] using wordTrace_append hprefix tailTrace_3733735
  have hstable : (prefixWord ++ tailWord_3733735).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3733735).length < 2 ^ (prefixWord ++ tailWord_3733735).sum := by decide
  have hdescent : baseEnd_3733735 < baseStart_3733735 := by decide
  rcases family_descends (prefixWord ++ tailWord_3733735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3733744 : List Nat := [2, 1, 1, 1, 3, 1, 1, 2, 1, 9]
def baseStart_3733744 : Nat := 118140960795 + 3733744 * 2 ^ 59
def prefixEnd_3733744 : Nat := 4983230072969 + 3 ^ 40 * 3733744 * 2
def baseEnd_3733744 : Nat := 1278136875227296628752553

theorem tailTrace_3733744 : CollatzResearch.WordTrace tailWord_3733744 prefixEnd_3733744 1278136875227296628752553 := by
  unfold tailWord_3733744
  simp only [CollatzResearch.WordTrace]
  refine ⟨68090415692645317776296143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90787220923527090368394857 68090415692645317776296143)
  ·
    refine ⟨102135623538967976664444215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68090415692645317776296143 102135623538967976664444215)
    ·
      refine ⟨153203435308451964996666323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102135623538967976664444215 153203435308451964996666323)
      ·
        refine ⟨229805152962677947494999485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153203435308451964996666323 229805152962677947494999485)
        ·
          refine ⟨86176932361004230310624807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 229805152962677947494999485 86176932361004230310624807)
          ·
            refine ⟨129265398541506345465937211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86176932361004230310624807 129265398541506345465937211)
            ·
              refine ⟨193898097812259518198905817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129265398541506345465937211 193898097812259518198905817)
              ·
                refine ⟨145423573359194638649179363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 193898097812259518198905817 145423573359194638649179363)
                ·
                  refine ⟨218135360038791957973769045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 145423573359194638649179363 218135360038791957973769045)
                  ·
                    refine ⟨1278136875227296628752553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 218135360038791957973769045 1278136875227296628752553)
                    ·
                      rfl

theorem cell22_3733744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 2, 1, 9].length) (baseStart_3733744 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3733744 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3733744 prefixEnd_3733744 := by exact prefixLift 3733744
  have htrace : WordTrace (prefixWord ++ tailWord_3733744) baseStart_3733744 baseEnd_3733744 := by
    simpa [prefixWord, tailWord_3733744, baseEnd_3733744] using wordTrace_append hprefix tailTrace_3733744
  have hstable : (prefixWord ++ tailWord_3733744).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3733744).length < 2 ^ (prefixWord ++ tailWord_3733744).sum := by decide
  have hdescent : baseEnd_3733744 < baseStart_3733744 := by decide
  rcases family_descends (prefixWord ++ tailWord_3733744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3733746 : List Nat := [3, 2, 1, 3, 2, 2, 9]
def baseStart_3733746 : Nat := 118140960795 + 3733746 * 2 ^ 59
def prefixEnd_3733746 : Nat := 4983230072969 + 3 ^ 40 * 3733746 * 2
def baseEnd_3733746 : Nat := 47338428143265529266761

theorem tailTrace_3733746 : CollatzResearch.WordTrace tailWord_3733746 prefixEnd_3733746 47338428143265529266761 := by
  unfold tailWord_3733746
  simp only [CollatzResearch.WordTrace]
  refine ⟨34045226082820847473541273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90787269554188926596110061 34045226082820847473541273)
  ·
    refine ⟨25533919562115635605155955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34045226082820847473541273 25533919562115635605155955)
    ·
      refine ⟨38300879343173453407733933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25533919562115635605155955 38300879343173453407733933)
      ·
        refine ⟨14362829753690045027900225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38300879343173453407733933 14362829753690045027900225)
        ·
          refine ⟨10772122315267533770925169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14362829753690045027900225 10772122315267533770925169)
          ·
            refine ⟨8079091736450650328193877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10772122315267533770925169 8079091736450650328193877)
            ·
              refine ⟨47338428143265529266761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8079091736450650328193877 47338428143265529266761)
              ·
                rfl

theorem cell22_3733746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 9].length) (baseStart_3733746 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3733746 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3733746 prefixEnd_3733746 := by exact prefixLift 3733746
  have htrace : WordTrace (prefixWord ++ tailWord_3733746) baseStart_3733746 baseEnd_3733746 := by
    simpa [prefixWord, tailWord_3733746, baseEnd_3733746] using wordTrace_append hprefix tailTrace_3733746
  have hstable : (prefixWord ++ tailWord_3733746).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3733746).length < 2 ^ (prefixWord ++ tailWord_3733746).sum := by decide
  have hdescent : baseEnd_3733746 < baseStart_3733746 := by decide
  rcases family_descends (prefixWord ++ tailWord_3733746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3733750 : List Nat := [5, 1, 1, 1, 1, 1, 5, 2, 2, 3]
def baseStart_3733750 : Nat := 118140960795 + 3733750 * 2 ^ 59
def prefixEnd_3733750 : Nat := 4983230072969 + 3 ^ 40 * 3733750 * 2
def baseEnd_3733750 : Nat := 1278138929149914613102535

theorem tailTrace_3733750 : CollatzResearch.WordTrace tailWord_3733750 prefixEnd_3733750 1278138929149914613102535 := by
  unfold tailWord_3733750
  simp only [CollatzResearch.WordTrace]
  refine ⟨8511315638954306161081919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 90787366815512599051540469 8511315638954306161081919)
  ·
    refine ⟨12766973458431459241622879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8511315638954306161081919 12766973458431459241622879)
    ·
      refine ⟨19150460187647188862434319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12766973458431459241622879 19150460187647188862434319)
      ·
        refine ⟨28725690281470783293651479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19150460187647188862434319 28725690281470783293651479)
        ·
          refine ⟨43088535422206174940477219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28725690281470783293651479 43088535422206174940477219)
          ·
            refine ⟨64632803133309262410715829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43088535422206174940477219 64632803133309262410715829)
            ·
              refine ⟨6059325293747743351004609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 64632803133309262410715829 6059325293747743351004609)
              ·
                refine ⟨4544493970310807513253457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6059325293747743351004609 4544493970310807513253457)
                ·
                  refine ⟨3408370477733105634940093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4544493970310807513253457 3408370477733105634940093)
                  ·
                    refine ⟨1278138929149914613102535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3408370477733105634940093 1278138929149914613102535)
                    ·
                      rfl

theorem cell22_3733750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 5, 2, 2, 3].length) (baseStart_3733750 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3733750 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3733750 prefixEnd_3733750 := by exact prefixLift 3733750
  have htrace : WordTrace (prefixWord ++ tailWord_3733750) baseStart_3733750 baseEnd_3733750 := by
    simpa [prefixWord, tailWord_3733750, baseEnd_3733750] using wordTrace_append hprefix tailTrace_3733750
  have hstable : (prefixWord ++ tailWord_3733750).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3733750).length < 2 ^ (prefixWord ++ tailWord_3733750).sum := by decide
  have hdescent : baseEnd_3733750 < baseStart_3733750 := by decide
  rcases family_descends (prefixWord ++ tailWord_3733750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3733767 : List Nat := [1, 1, 4, 5, 2, 1, 1, 1, 1, 5]
def baseStart_3733767 : Nat := 118140960795 + 3733767 * 2 ^ 59
def prefixEnd_3733767 : Nat := 4983230072969 + 3 ^ 40 * 3733767 * 2
def baseEnd_3733767 : Nat := 1278144748597332235427483

theorem tailTrace_3733767 : CollatzResearch.WordTrace tailWord_3733767 prefixEnd_3733767 1278144748597332235427483 := by
  unfold tailWord_3733767
  simp only [CollatzResearch.WordTrace]
  refine ⟨136181670264207310480679555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90787780176138206987119703 136181670264207310480679555)
  ·
    refine ⟨204272505396310965721019333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136181670264207310480679555 204272505396310965721019333)
    ·
      refine ⟨38301094761808306072691125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 204272505396310965721019333 38301094761808306072691125)
      ·
        refine ⟨3590727633919528694314793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 38301094761808306072691125 3590727633919528694314793)
        ·
          refine ⟨2693045725439646520736095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3590727633919528694314793 2693045725439646520736095)
          ·
            refine ⟨4039568588159469781104143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2693045725439646520736095 4039568588159469781104143)
            ·
              refine ⟨6059352882239204671656215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4039568588159469781104143 6059352882239204671656215)
              ·
                refine ⟨9089029323358807007484323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6059352882239204671656215 9089029323358807007484323)
                ·
                  refine ⟨13633543985038210511226485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9089029323358807007484323 13633543985038210511226485)
                  ·
                    refine ⟨1278144748597332235427483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13633543985038210511226485 1278144748597332235427483)
                    ·
                      rfl

theorem cell22_3733767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 2, 1, 1, 1, 1, 5].length) (baseStart_3733767 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3733767 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3733767 prefixEnd_3733767 := by exact prefixLift 3733767
  have htrace : WordTrace (prefixWord ++ tailWord_3733767) baseStart_3733767 baseEnd_3733767 := by
    simpa [prefixWord, tailWord_3733767, baseEnd_3733767] using wordTrace_append hprefix tailTrace_3733767
  have hstable : (prefixWord ++ tailWord_3733767).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3733767).length < 2 ^ (prefixWord ++ tailWord_3733767).sum := by decide
  have hdescent : baseEnd_3733767 < baseStart_3733767 := by decide
  rcases family_descends (prefixWord ++ tailWord_3733767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3733791 : List Nat := [1, 1, 2, 4, 3, 1, 1, 2, 7]
def baseStart_3733791 : Nat := 118140960795 + 3733791 * 2 ^ 59
def prefixEnd_3733791 : Nat := 4983230072969 + 3 ^ 40 * 3733791 * 2
def baseEnd_3733791 : Nat := 426050988095934724275803

theorem tailTrace_3733791 : CollatzResearch.WordTrace tailWord_3733791 prefixEnd_3733791 426050988095934724275803 := by
  unfold tailWord_3733791
  simp only [CollatzResearch.WordTrace]
  refine ⟨136182545616120362579553227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90788363744080241719702151 136182545616120362579553227)
  ·
    refine ⟨204273818424180543869329841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136182545616120362579553227 204273818424180543869329841)
    ·
      refine ⟨153205363818135407901997381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 204273818424180543869329841 153205363818135407901997381)
      ·
        refine ⟨28726005715900388981624509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 153205363818135407901997381 28726005715900388981624509)
        ·
          refine ⟨10772252143462645868109191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28726005715900388981624509 10772252143462645868109191)
          ·
            refine ⟨16158378215193968802163787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10772252143462645868109191 16158378215193968802163787)
            ·
              refine ⟨24237567322790953203245681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16158378215193968802163787 24237567322790953203245681)
              ·
                refine ⟨18178175492093214902434261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24237567322790953203245681 18178175492093214902434261)
                ·
                  refine ⟨426050988095934724275803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18178175492093214902434261 426050988095934724275803)
                  ·
                    rfl

theorem cell22_3733791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 2, 7].length) (baseStart_3733791 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3733791 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3733791 prefixEnd_3733791 := by exact prefixLift 3733791
  have htrace : WordTrace (prefixWord ++ tailWord_3733791) baseStart_3733791 baseEnd_3733791 := by
    simpa [prefixWord, tailWord_3733791, baseEnd_3733791] using wordTrace_append hprefix tailTrace_3733791
  have hstable : (prefixWord ++ tailWord_3733791).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3733791).length < 2 ^ (prefixWord ++ tailWord_3733791).sum := by decide
  have hdescent : baseEnd_3733791 < baseStart_3733791 := by decide
  rcases family_descends (prefixWord ++ tailWord_3733791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3733812 : List Nat := [2, 5, 1, 1, 1, 4, 1, 1, 3, 3]
def baseStart_3733812 : Nat := 118140960795 + 3733812 * 2 ^ 59
def prefixEnd_3733812 : Nat := 4983230072969 + 3 ^ 40 * 3733812 * 2
def baseEnd_3733812 : Nat := 1278160153016967118052345

theorem tailTrace_3733812 : CollatzResearch.WordTrace tailWord_3733812 prefixEnd_3733812 1278160153016967118052345 := by
  unfold tailWord_3733812
  simp only [CollatzResearch.WordTrace]
  refine ⟨68091655774522141583033845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90788874366029522110711793 68091655774522141583033845)
  ·
    refine ⟨6383592728861450773409423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 68091655774522141583033845 6383592728861450773409423)
    ·
      refine ⟨9575389093292176160114135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6383592728861450773409423 9575389093292176160114135)
      ·
        refine ⟨14363083639938264240171203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9575389093292176160114135 14363083639938264240171203)
        ·
          refine ⟨21544625459907396360256805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14363083639938264240171203 21544625459907396360256805)
          ·
            refine ⟨4039617273732636817548151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21544625459907396360256805 4039617273732636817548151)
            ·
              refine ⟨6059425910598955226322227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4039617273732636817548151 6059425910598955226322227)
              ·
                refine ⟨9089138865898432839483341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6059425910598955226322227 9089138865898432839483341)
                ·
                  refine ⟨3408427074711912314806253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9089138865898432839483341 3408427074711912314806253)
                  ·
                    refine ⟨1278160153016967118052345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3408427074711912314806253 1278160153016967118052345)
                    ·
                      rfl

theorem cell22_3733812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 4, 1, 1, 3, 3].length) (baseStart_3733812 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3733812 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3733812 prefixEnd_3733812 := by exact prefixLift 3733812
  have htrace : WordTrace (prefixWord ++ tailWord_3733812) baseStart_3733812 baseEnd_3733812 := by
    simpa [prefixWord, tailWord_3733812, baseEnd_3733812] using wordTrace_append hprefix tailTrace_3733812
  have hstable : (prefixWord ++ tailWord_3733812).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3733812).length < 2 ^ (prefixWord ++ tailWord_3733812).sum := by decide
  have hdescent : baseEnd_3733812 < baseStart_3733812 := by decide
  rcases family_descends (prefixWord ++ tailWord_3733812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3733825 : List Nat := [1, 2, 5, 2, 2, 1, 1, 3, 5]
def baseStart_3733825 : Nat := 118140960795 + 3733825 * 2 ^ 59
def prefixEnd_3733825 : Nat := 4983230072969 + 3 ^ 40 * 3733825 * 2
def baseEnd_3733825 : Nat := 426054867727546472492435

theorem tailTrace_3733825 : CollatzResearch.WordTrace tailWord_3733825 prefixEnd_3733825 426054867727546472492435 := by
  unfold tailWord_3733825
  simp only [CollatzResearch.WordTrace]
  refine ⟨136183785697997186386290929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90789190465331457590860619 136183785697997186386290929)
  ·
    refine ⟨102137839273497889789718197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136183785697997186386290929 102137839273497889789718197)
    ·
      refine ⟨9575422431890427167786081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 102137839273497889789718197 9575422431890427167786081)
      ·
        refine ⟨7181566823917820375839561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9575422431890427167786081 7181566823917820375839561)
        ·
          refine ⟨5386175117938365281879671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7181566823917820375839561 5386175117938365281879671)
          ·
            refine ⟨8079262676907547922819507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5386175117938365281879671 8079262676907547922819507)
            ·
              refine ⟨12118894015361321884229261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8079262676907547922819507 12118894015361321884229261)
              ·
                refine ⟨4544585255760495706585973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12118894015361321884229261 4544585255760495706585973)
                ·
                  refine ⟨426054867727546472492435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4544585255760495706585973 426054867727546472492435)
                  ·
                    rfl

theorem cell22_3733825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 1, 3, 5].length) (baseStart_3733825 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3733825 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3733825 prefixEnd_3733825 := by exact prefixLift 3733825
  have htrace : WordTrace (prefixWord ++ tailWord_3733825) baseStart_3733825 baseEnd_3733825 := by
    simpa [prefixWord, tailWord_3733825, baseEnd_3733825] using wordTrace_append hprefix tailTrace_3733825
  have hstable : (prefixWord ++ tailWord_3733825).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3733825).length < 2 ^ (prefixWord ++ tailWord_3733825).sum := by decide
  have hdescent : baseEnd_3733825 < baseStart_3733825 := by decide
  rcases family_descends (prefixWord ++ tailWord_3733825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3733836 : List Nat := [2, 2, 1, 3, 2, 1, 2, 1, 8]
def baseStart_3733836 : Nat := 118140960795 + 3733836 * 2 ^ 59
def prefixEnd_3733836 : Nat := 4983230072969 + 3 ^ 40 * 3733836 * 2
def baseEnd_3733836 : Nat := 426056122902479685150757

theorem tailTrace_3733836 : CollatzResearch.WordTrace tailWord_3733836 prefixEnd_3733836 426056122902479685150757 := by
  unfold tailWord_3733836
  simp only [CollatzResearch.WordTrace]
  refine ⟨68092093450478667632470681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90789457933971556843294241 68092093450478667632470681)
  ·
    refine ⟨51069070087859000724353011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68092093450478667632470681 51069070087859000724353011)
    ·
      refine ⟨76603605131788501086529517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51069070087859000724353011 76603605131788501086529517)
      ·
        refine ⟨28726351924420687907448569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76603605131788501086529517 28726351924420687907448569)
        ·
          refine ⟨21544763943315515930586427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28726351924420687907448569 21544763943315515930586427)
          ·
            refine ⟨32317145914973273895879641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21544763943315515930586427 32317145914973273895879641)
            ·
              refine ⟨24237859436229955421909731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32317145914973273895879641 24237859436229955421909731)
              ·
                refine ⟨36356789154344933132864597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24237859436229955421909731 36356789154344933132864597)
                ·
                  refine ⟨426056122902479685150757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 36356789154344933132864597 426056122902479685150757)
                  ·
                    rfl

theorem cell22_3733836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 1, 8].length) (baseStart_3733836 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3733836 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3733836 prefixEnd_3733836 := by exact prefixLift 3733836
  have htrace : WordTrace (prefixWord ++ tailWord_3733836) baseStart_3733836 baseEnd_3733836 := by
    simpa [prefixWord, tailWord_3733836, baseEnd_3733836] using wordTrace_append hprefix tailTrace_3733836
  have hstable : (prefixWord ++ tailWord_3733836).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3733836).length < 2 ^ (prefixWord ++ tailWord_3733836).sum := by decide
  have hdescent : baseEnd_3733836 < baseStart_3733836 := by decide
  rcases family_descends (prefixWord ++ tailWord_3733836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3733838 : List Nat := [4, 1, 1, 1, 1, 1, 2, 6, 1, 4]
def baseStart_3733838 : Nat := 118140960795 + 3733838 * 2 ^ 59
def prefixEnd_3733838 : Nat := 4983230072969 + 3 ^ 40 * 3733838 * 2
def baseEnd_3733838 : Nat := 1278169053348311716902265

theorem tailTrace_3733838 : CollatzResearch.WordTrace tailWord_3733838 prefixEnd_3733838 1278169053348311716902265 := by
  unfold tailWord_3733838
  simp only [CollatzResearch.WordTrace]
  refine ⟨17023032480868761200814271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 90789506564633393071009445 17023032480868761200814271)
  ·
    refine ⟨25534548721303141801221407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17023032480868761200814271 25534548721303141801221407)
    ·
      refine ⟨38301823081954712701832111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25534548721303141801221407 38301823081954712701832111)
      ·
        refine ⟨57452734622932069052748167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38301823081954712701832111 57452734622932069052748167)
        ·
          refine ⟨86179101934398103579122251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57452734622932069052748167 86179101934398103579122251)
          ·
            refine ⟨129268652901597155368683377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86179101934398103579122251 129268652901597155368683377)
            ·
              refine ⟨96951489676197866526512533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 129268652901597155368683377 96951489676197866526512533)
              ·
                refine ⟨4544601078571774993430275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 96951489676197866526512533 4544601078571774993430275)
                ·
                  refine ⟨6816901617857662490145413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4544601078571774993430275 6816901617857662490145413)
                  ·
                    refine ⟨1278169053348311716902265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6816901617857662490145413 1278169053348311716902265)
                    ·
                      rfl

theorem cell22_3733838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 6, 1, 4].length) (baseStart_3733838 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3733838 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3733838 prefixEnd_3733838 := by exact prefixLift 3733838
  have htrace : WordTrace (prefixWord ++ tailWord_3733838) baseStart_3733838 baseEnd_3733838 := by
    simpa [prefixWord, tailWord_3733838, baseEnd_3733838] using wordTrace_append hprefix tailTrace_3733838
  have hstable : (prefixWord ++ tailWord_3733838).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3733838).length < 2 ^ (prefixWord ++ tailWord_3733838).sum := by decide
  have hdescent : baseEnd_3733838 < baseStart_3733838 := by decide
  rcases family_descends (prefixWord ++ tailWord_3733838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3733885 : List Nat := [1, 4, 1, 1, 2, 3, 2, 3, 2, 3]
def baseStart_3733885 : Nat := 118140960795 + 3733885 * 2 ^ 59
def prefixEnd_3733885 : Nat := 4983230072969 + 3 ^ 40 * 3733885 * 2
def baseEnd_3733885 : Nat := 1278185142408819260977121

theorem tailTrace_3733885 : CollatzResearch.WordTrace tailWord_3733885 prefixEnd_3733885 1278185142408819260977121 := by
  unfold tailWord_3733885
  simp only [CollatzResearch.WordTrace]
  refine ⟨136185974077779816633475109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90790649385186544422316739 136185974077779816633475109)
  ·
    refine ⟨25534870139583715618776583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 136185974077779816633475109 25534870139583715618776583)
    ·
      refine ⟨38302305209375573428164875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25534870139583715618776583 38302305209375573428164875)
      ·
        refine ⟨57453457814063360142247313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38302305209375573428164875 57453457814063360142247313)
        ·
          refine ⟨43090093360547520106685485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57453457814063360142247313 43090093360547520106685485)
          ·
            refine ⟨16158785010205320040007057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43090093360547520106685485 16158785010205320040007057)
            ·
              refine ⟨12119088757653990030005293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16158785010205320040007057 12119088757653990030005293)
              ·
                refine ⟨4544658284120246261251985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12119088757653990030005293 4544658284120246261251985)
                ·
                  refine ⟨3408493713090184695938989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4544658284120246261251985 3408493713090184695938989)
                  ·
                    refine ⟨1278185142408819260977121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3408493713090184695938989 1278185142408819260977121)
                    ·
                      rfl

theorem cell22_3733885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 2, 3, 2, 3].length) (baseStart_3733885 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3733885 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3733885 prefixEnd_3733885 := by exact prefixLift 3733885
  have htrace : WordTrace (prefixWord ++ tailWord_3733885) baseStart_3733885 baseEnd_3733885 := by
    simpa [prefixWord, tailWord_3733885, baseEnd_3733885] using wordTrace_append hprefix tailTrace_3733885
  have hstable : (prefixWord ++ tailWord_3733885).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3733885).length < 2 ^ (prefixWord ++ tailWord_3733885).sum := by decide
  have hdescent : baseEnd_3733885 < baseStart_3733885 := by decide
  rcases family_descends (prefixWord ++ tailWord_3733885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3733900 : List Nat := [2, 2, 1, 2, 1, 6, 1, 1, 2, 4]
def baseStart_3733900 : Nat := 118140960795 + 3733900 * 2 ^ 59
def prefixEnd_3733900 : Nat := 4983230072969 + 3 ^ 40 * 3733900 * 2
def baseEnd_3733900 : Nat := 1278190277215364221852075

theorem tailTrace_3733900 : CollatzResearch.WordTrace tailWord_3733900 prefixEnd_3733900 1278190277215364221852075 := by
  unfold tailWord_3733900
  simp only [CollatzResearch.WordTrace]
  refine ⟨68093260586362737097635577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90791014115150316130180769 68093260586362737097635577)
  ·
    refine ⟨51069945439772052823226683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68093260586362737097635577 51069945439772052823226683)
    ·
      refine ⟨76604918159658079234840025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51069945439772052823226683 76604918159658079234840025)
      ·
        refine ⟨57453688619743559426130019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76604918159658079234840025 57453688619743559426130019)
        ·
          refine ⟨86180532929615339139195029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57453688619743559426130019 86180532929615339139195029)
          ·
            refine ⟨4039712481075719022149767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 86180532929615339139195029 4039712481075719022149767)
            ·
              refine ⟨6059568721613578533224651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4039712481075719022149767 6059568721613578533224651)
              ·
                refine ⟨9089353082420367799836977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6059568721613578533224651 9089353082420367799836977)
                ·
                  refine ⟨6817014811815275849877733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9089353082420367799836977 6817014811815275849877733)
                  ·
                    refine ⟨1278190277215364221852075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6817014811815275849877733 1278190277215364221852075)
                    ·
                      rfl

theorem cell22_3733900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 6, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 6, 1, 1, 2, 4].length) (baseStart_3733900 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3733900 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3733900 prefixEnd_3733900 := by exact prefixLift 3733900
  have htrace : WordTrace (prefixWord ++ tailWord_3733900) baseStart_3733900 baseEnd_3733900 := by
    simpa [prefixWord, tailWord_3733900, baseEnd_3733900] using wordTrace_append hprefix tailTrace_3733900
  have hstable : (prefixWord ++ tailWord_3733900).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3733900).length < 2 ^ (prefixWord ++ tailWord_3733900).sum := by decide
  have hdescent : baseEnd_3733900 < baseStart_3733900 := by decide
  rcases family_descends (prefixWord ++ tailWord_3733900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3733913 : List Nat := [1, 2, 1, 2, 1, 4, 1, 2, 5, 3]
def baseStart_3733913 : Nat := 118140960795 + 3733913 * 2 ^ 59
def prefixEnd_3733913 : Nat := 4983230072969 + 3 ^ 40 * 3733913 * 2
def baseEnd_3733913 : Nat := 1278194727381036521277035

theorem tailTrace_3733913 : CollatzResearch.WordTrace tailWord_3733913 prefixEnd_3733913 1278194727381036521277035 := by
  unfold tailWord_3733913
  simp only [CollatzResearch.WordTrace]
  refine ⟨136186995321678377415494393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90791330214452251610329595 136186995321678377415494393)
  ·
    refine ⟨102140246491258783061620795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136186995321678377415494393 102140246491258783061620795)
    ·
      refine ⟨153210369736888174592431193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102140246491258783061620795 153210369736888174592431193)
      ·
        refine ⟨114907777302666130944323395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153210369736888174592431193 114907777302666130944323395)
        ·
          refine ⟨172361665953999196416485093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114907777302666130944323395 172361665953999196416485093)
          ·
            refine ⟨32317812366374849328090955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 172361665953999196416485093 32317812366374849328090955)
            ·
              refine ⟨48476718549562273992136433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32317812366374849328090955 48476718549562273992136433)
              ·
                refine ⟨36357538912171705494102325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48476718549562273992136433 36357538912171705494102325)
                ·
                  refine ⟨3408519273016097390072093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 36357538912171705494102325 3408519273016097390072093)
                  ·
                    refine ⟨1278194727381036521277035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3408519273016097390072093 1278194727381036521277035)
                    ·
                      rfl

theorem cell22_3733913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 2, 5, 3].length) (baseStart_3733913 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3733913 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3733913 prefixEnd_3733913 := by exact prefixLift 3733913
  have htrace : WordTrace (prefixWord ++ tailWord_3733913) baseStart_3733913 baseEnd_3733913 := by
    simpa [prefixWord, tailWord_3733913, baseEnd_3733913] using wordTrace_append hprefix tailTrace_3733913
  have hstable : (prefixWord ++ tailWord_3733913).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3733913).length < 2 ^ (prefixWord ++ tailWord_3733913).sum := by decide
  have hdescent : baseEnd_3733913 < baseStart_3733913 := by decide
  rcases family_descends (prefixWord ++ tailWord_3733913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3734003 : List Nat := [1, 1, 1, 2, 2, 2, 4, 3, 1, 5]
def baseStart_3734003 : Nat := 118140960795 + 3734003 * 2 ^ 59
def prefixEnd_3734003 : Nat := 4983230072969 + 3 ^ 40 * 3734003 * 2
def baseEnd_3734003 : Nat := 1278225536220306286526759

theorem tailTrace_3734003 : CollatzResearch.WordTrace tailWord_3734003 prefixEnd_3734003 1278225536220306286526759 := by
  unfold tailWord_3734003
  simp only [CollatzResearch.WordTrace]
  refine ⟨136190277891352322786270663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90793518594234881857513775 136190277891352322786270663)
  ·
    refine ⟨204285416837028484179405995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136190277891352322786270663 204285416837028484179405995)
    ·
      refine ⟨306428125255542726269108993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204285416837028484179405995 306428125255542726269108993)
      ·
        refine ⟨229821093941657044701831745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 306428125255542726269108993 229821093941657044701831745)
        ·
          refine ⟨172365820456242783526373809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 229821093941657044701831745 172365820456242783526373809)
          ·
            refine ⟨129274365342182087644780357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 172365820456242783526373809 129274365342182087644780357)
            ·
              refine ⟨24238943501659141433396317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 129274365342182087644780357 24238943501659141433396317)
              ·
                refine ⟨9089603813122178037523619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24238943501659141433396317 9089603813122178037523619)
                ·
                  refine ⟨13634405719683267056285429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9089603813122178037523619 13634405719683267056285429)
                  ·
                    refine ⟨1278225536220306286526759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13634405719683267056285429 1278225536220306286526759)
                    ·
                      rfl

theorem cell22_3734003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 3, 1, 5].length) (baseStart_3734003 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3734003 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3734003 prefixEnd_3734003 := by exact prefixLift 3734003
  have htrace : WordTrace (prefixWord ++ tailWord_3734003) baseStart_3734003 baseEnd_3734003 := by
    simpa [prefixWord, tailWord_3734003, baseEnd_3734003] using wordTrace_append hprefix tailTrace_3734003
  have hstable : (prefixWord ++ tailWord_3734003).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3734003).length < 2 ^ (prefixWord ++ tailWord_3734003).sum := by decide
  have hdescent : baseEnd_3734003 < baseStart_3734003 := by decide
  rcases family_descends (prefixWord ++ tailWord_3734003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3734020 : List Nat := [2, 3, 2, 3, 1, 1, 1, 1, 3, 5]
def baseStart_3734020 : Nat := 118140960795 + 3734020 * 2 ^ 59
def prefixEnd_3734020 : Nat := 4983230072969 + 3 ^ 40 * 3734020 * 2
def baseEnd_3734020 : Nat := 1278231355667723908851707

theorem tailTrace_3734020 : CollatzResearch.WordTrace tailWord_3734020 prefixEnd_3734020 1278231355667723908851707 := by
  unfold tailWord_3734020
  simp only [CollatzResearch.WordTrace]
  refine ⟨68095448966145367344819757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90793931954860489793093009 68095448966145367344819757)
  ·
    refine ⟨25535793362304512754307409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68095448966145367344819757 25535793362304512754307409)
    ·
      refine ⟨19151845021728384565730557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25535793362304512754307409 19151845021728384565730557)
      ·
        refine ⟨7181941883148144212148959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19151845021728384565730557 7181941883148144212148959)
        ·
          refine ⟨10772912824722216318223439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7181941883148144212148959 10772912824722216318223439)
          ·
            refine ⟨16159369237083324477335159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10772912824722216318223439 16159369237083324477335159)
            ·
              refine ⟨24239053855624986716002739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16159369237083324477335159 24239053855624986716002739)
              ·
                refine ⟨36358580783437480074004109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24239053855624986716002739 36358580783437480074004109)
                ·
                  refine ⟨13634467793789055027751541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36358580783437480074004109 13634467793789055027751541)
                  ·
                    refine ⟨1278231355667723908851707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13634467793789055027751541 1278231355667723908851707)
                    ·
                      rfl

theorem cell22_3734020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 1, 3, 5].length) (baseStart_3734020 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3734020 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3734020 prefixEnd_3734020 := by exact prefixLift 3734020
  have htrace : WordTrace (prefixWord ++ tailWord_3734020) baseStart_3734020 baseEnd_3734020 := by
    simpa [prefixWord, tailWord_3734020, baseEnd_3734020] using wordTrace_append hprefix tailTrace_3734020
  have hstable : (prefixWord ++ tailWord_3734020).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3734020).length < 2 ^ (prefixWord ++ tailWord_3734020).sum := by decide
  have hdescent : baseEnd_3734020 < baseStart_3734020 := by decide
  rcases family_descends (prefixWord ++ tailWord_3734020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3734037 : List Nat := [1, 3, 2, 1, 3, 1, 4, 2, 2, 3]
def baseStart_3734037 : Nat := 118140960795 + 3734037 * 2 ^ 59
def prefixEnd_3734037 : Nat := 4983230072969 + 3 ^ 40 * 3734037 * 2
def baseEnd_3734037 : Nat := 1278237175115141531176655

theorem tailTrace_3734037 : CollatzResearch.WordTrace tailWord_3734037 prefixEnd_3734037 1278237175115141531176655 := by
  unfold tailWord_3734037
  simp only [CollatzResearch.WordTrace]
  refine ⟨136191517973229146593008365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90794345315486097728672243 136191517973229146593008365)
  ·
    refine ⟨51071819239960929972378137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136191517973229146593008365 51071819239960929972378137)
    ·
      refine ⟨38303864429970697479283603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51071819239960929972378137 38303864429970697479283603)
      ·
        refine ⟨57455796644956046218925405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38303864429970697479283603 57455796644956046218925405)
        ·
          refine ⟨21545923741858517332097027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57455796644956046218925405 21545923741858517332097027)
          ·
            refine ⟨32318885612787775998145541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21545923741858517332097027 32318885612787775998145541)
            ·
              refine ⟨6059791052397707999652289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32318885612787775998145541 6059791052397707999652289)
              ·
                refine ⟨4544843289298280999739217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6059791052397707999652289 4544843289298280999739217)
                ·
                  refine ⟨3408632466973710749804413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4544843289298280999739217 3408632466973710749804413)
                  ·
                    refine ⟨1278237175115141531176655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3408632466973710749804413 1278237175115141531176655)
                    ·
                      rfl

theorem cell22_3734037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 4, 2, 2, 3].length) (baseStart_3734037 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3734037 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3734037 prefixEnd_3734037 := by exact prefixLift 3734037
  have htrace : WordTrace (prefixWord ++ tailWord_3734037) baseStart_3734037 baseEnd_3734037 := by
    simpa [prefixWord, tailWord_3734037, baseEnd_3734037] using wordTrace_append hprefix tailTrace_3734037
  have hstable : (prefixWord ++ tailWord_3734037).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3734037).length < 2 ^ (prefixWord ++ tailWord_3734037).sum := by decide
  have hdescent : baseEnd_3734037 < baseStart_3734037 := by decide
  rcases family_descends (prefixWord ++ tailWord_3734037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3734039 : List Nat := [1, 1, 3, 6, 1, 1, 1, 4, 4]
def baseStart_3734039 : Nat := 118140960795 + 3734039 * 2 ^ 59
def prefixEnd_3734039 : Nat := 4983230072969 + 3 ^ 40 * 3734039 * 2
def baseEnd_3734039 : Nat := 426079286585338064208883

theorem tailTrace_3734039 : CollatzResearch.WordTrace tailWord_3734039 prefixEnd_3734039 426079286585338064208883 := by
  unfold tailWord_3734039
  simp only [CollatzResearch.WordTrace]
  refine ⟨136191590919221900934581171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90794393946147933956387447 136191590919221900934581171)
  ·
    refine ⟨204287386378832851401871757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136191590919221900934581171 204287386378832851401871757)
    ·
      refine ⟨76607769892062319275701909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 204287386378832851401871757 76607769892062319275701909)
      ·
        refine ⟨3590989213690421216048527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 76607769892062319275701909 3590989213690421216048527)
        ·
          refine ⟨5386483820535631824072791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3590989213690421216048527 5386483820535631824072791)
          ·
            refine ⟨8079725730803447736109187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5386483820535631824072791 8079725730803447736109187)
            ·
              refine ⟨12119588596205171604163781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8079725730803447736109187 12119588596205171604163781)
              ·
                refine ⟨2272422861788469675780709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12119588596205171604163781 2272422861788469675780709)
                ·
                  refine ⟨426079286585338064208883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2272422861788469675780709 426079286585338064208883)
                  ·
                    rfl

theorem cell22_3734039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 1, 4, 4].length) (baseStart_3734039 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3734039 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3734039 prefixEnd_3734039 := by exact prefixLift 3734039
  have htrace : WordTrace (prefixWord ++ tailWord_3734039) baseStart_3734039 baseEnd_3734039 := by
    simpa [prefixWord, tailWord_3734039, baseEnd_3734039] using wordTrace_append hprefix tailTrace_3734039
  have hstable : (prefixWord ++ tailWord_3734039).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3734039).length < 2 ^ (prefixWord ++ tailWord_3734039).sum := by decide
  have hdescent : baseEnd_3734039 < baseStart_3734039 := by decide
  rcases family_descends (prefixWord ++ tailWord_3734039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3734065 : List Nat := [1, 2, 2, 3, 1, 1, 3, 1, 5, 3]
def baseStart_3734065 : Nat := 118140960795 + 3734065 * 2 ^ 59
def prefixEnd_3734065 : Nat := 4983230072969 + 3 ^ 40 * 3734065 * 2
def baseEnd_3734065 : Nat := 1278246760087358791476569

theorem tailTrace_3734065 : CollatzResearch.WordTrace tailWord_3734065 prefixEnd_3734065 1278246760087358791476569 := by
  unfold tailWord_3734065
  simp only [CollatzResearch.WordTrace]
  refine ⟨136192539217127707375027649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90795026144751804916685099 136192539217127707375027649)
  ·
    refine ⟨102144404412845780531270737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136192539217127707375027649 102144404412845780531270737)
    ·
      refine ⟨76608303309634335398453053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102144404412845780531270737 76608303309634335398453053)
      ·
        refine ⟨28728113741112875774419895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76608303309634335398453053 28728113741112875774419895)
        ·
          refine ⟨43092170611669313661629843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28728113741112875774419895 43092170611669313661629843)
          ·
            refine ⟨64638255917503970492444765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43092170611669313661629843 64638255917503970492444765)
            ·
              refine ⟨24239345969063988934666787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64638255917503970492444765 24239345969063988934666787)
              ·
                refine ⟨36359018953595983402000181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24239345969063988934666787 36359018953595983402000181)
                ·
                  refine ⟨3408658026899623443937517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 36359018953595983402000181 3408658026899623443937517)
                  ·
                    refine ⟨1278246760087358791476569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3408658026899623443937517 1278246760087358791476569)
                    ·
                      rfl

theorem cell22_3734065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 1, 5, 3].length) (baseStart_3734065 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3734065 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3734065 prefixEnd_3734065 := by exact prefixLift 3734065
  have htrace : WordTrace (prefixWord ++ tailWord_3734065) baseStart_3734065 baseEnd_3734065 := by
    simpa [prefixWord, tailWord_3734065, baseEnd_3734065] using wordTrace_append hprefix tailTrace_3734065
  have hstable : (prefixWord ++ tailWord_3734065).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3734065).length < 2 ^ (prefixWord ++ tailWord_3734065).sum := by decide
  have hdescent : baseEnd_3734065 < baseStart_3734065 := by decide
  rcases family_descends (prefixWord ++ tailWord_3734065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3734084 : List Nat := [2, 3, 5, 1, 1, 1, 9]
def baseStart_3734084 : Nat := 118140960795 + 3734084 * 2 ^ 59
def prefixEnd_3734084 : Nat := 4983230072969 + 3 ^ 40 * 3734084 * 2
def baseEnd_3734084 : Nat := 47342713487987002787093

theorem tailTrace_3734084 : CollatzResearch.WordTrace tailWord_3734084 prefixEnd_3734084 47342713487987002787093 := by
  unfold tailWord_3734084
  simp only [CollatzResearch.WordTrace]
  refine ⟨68096616102029436809984653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90795488136039249079979537 68096616102029436809984653)
  ·
    refine ⟨25536231038261038803744245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68096616102029436809984653 25536231038261038803744245)
    ·
      refine ⟨2394021659836972387851023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 25536231038261038803744245 2394021659836972387851023)
      ·
        refine ⟨3591032489755458581776535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2394021659836972387851023 3591032489755458581776535)
        ·
          refine ⟨5386548734633187872664803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3591032489755458581776535 5386548734633187872664803)
          ·
            refine ⟨8079823101949781808997205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5386548734633187872664803 8079823101949781808997205)
            ·
              refine ⟨47342713487987002787093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8079823101949781808997205 47342713487987002787093)
              ·
                rfl

theorem cell22_3734084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 9].length) (baseStart_3734084 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3734084 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3734084 prefixEnd_3734084 := by exact prefixLift 3734084
  have htrace : WordTrace (prefixWord ++ tailWord_3734084) baseStart_3734084 baseEnd_3734084 := by
    simpa [prefixWord, tailWord_3734084, baseEnd_3734084] using wordTrace_append hprefix tailTrace_3734084
  have hstable : (prefixWord ++ tailWord_3734084).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3734084).length < 2 ^ (prefixWord ++ tailWord_3734084).sum := by decide
  have hdescent : baseEnd_3734084 < baseStart_3734084 := by decide
  rcases family_descends (prefixWord ++ tailWord_3734084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3734095 : List Nat := [1, 1, 2, 1, 1, 2, 7, 2, 5]
def baseStart_3734095 : Nat := 118140960795 + 3734095 * 2 ^ 59
def prefixEnd_3734095 : Nat := 4983230072969 + 3 ^ 40 * 3734095 * 2
def baseEnd_3734095 : Nat := 426085676566816237742159

theorem tailTrace_3734095 : CollatzResearch.WordTrace tailWord_3734095 prefixEnd_3734095 426085676566816237742159 := by
  unfold tailWord_3734095
  simp only [CollatzResearch.WordTrace]
  refine ⟨136193633407019022498619739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90795755604679348332413159 136193633407019022498619739)
  ·
    refine ⟨204290450110528533747929609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136193633407019022498619739 204290450110528533747929609)
    ·
      refine ⟨153217837582896400310947207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 204290450110528533747929609 153217837582896400310947207)
      ·
        refine ⟨229826756374344600466420811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153217837582896400310947207 229826756374344600466420811)
        ·
          refine ⟨344740134561516900699631217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 229826756374344600466420811 344740134561516900699631217)
          ·
            refine ⟨258555100921137675524723413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 344740134561516900699631217 258555100921137675524723413)
            ·
              refine ⟨6059885177839164270110705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 258555100921137675524723413 6059885177839164270110705)
              ·
                refine ⟨4544913883379373202583029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6059885177839164270110705 4544913883379373202583029)
                ·
                  refine ⟨426085676566816237742159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4544913883379373202583029 426085676566816237742159)
                  ·
                    rfl

theorem cell22_3734095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 7, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 7, 2, 5].length) (baseStart_3734095 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3734095 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3734095 prefixEnd_3734095 := by exact prefixLift 3734095
  have htrace : WordTrace (prefixWord ++ tailWord_3734095) baseStart_3734095 baseEnd_3734095 := by
    simpa [prefixWord, tailWord_3734095, baseEnd_3734095] using wordTrace_append hprefix tailTrace_3734095
  have hstable : (prefixWord ++ tailWord_3734095).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3734095).length < 2 ^ (prefixWord ++ tailWord_3734095).sum := by decide
  have hdescent : baseEnd_3734095 < baseStart_3734095 := by decide
  rcases family_descends (prefixWord ++ tailWord_3734095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3734123 : List Nat := [1, 1, 1, 1, 2, 2, 1, 5, 8]
def baseStart_3734123 : Nat := 118140960795 + 3734123 * 2 ^ 59
def prefixEnd_3734123 : Nat := 4983230072969 + 3 ^ 40 * 3734123 * 2
def baseEnd_3734123 : Nat := 426088871557555324508797

theorem tailTrace_3734123 : CollatzResearch.WordTrace tailWord_3734123 prefixEnd_3734123 426088871557555324508797 := by
  unfold tailWord_3734123
  simp only [CollatzResearch.WordTrace]
  refine ⟨136194654650917583280639023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90796436433945055520426015 136194654650917583280639023)
  ·
    refine ⟨204291981976376374920958535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136194654650917583280639023 204291981976376374920958535)
    ·
      refine ⟨306437972964564562381437803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204291981976376374920958535 306437972964564562381437803)
      ·
        refine ⟨459656959446846843572156705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 306437972964564562381437803 459656959446846843572156705)
        ·
          refine ⟨344742719585135132679117529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 459656959446846843572156705 344742719585135132679117529)
          ·
            refine ⟨258557039688851349509338147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 344742719585135132679117529 258557039688851349509338147)
            ·
              refine ⟨387835559533277024264007221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 258557039688851349509338147 387835559533277024264007221)
              ·
                refine ⟨36359583706244721024750677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 387835559533277024264007221 36359583706244721024750677)
                ·
                  refine ⟨426088871557555324508797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 36359583706244721024750677 426088871557555324508797)
                  ·
                    rfl

theorem cell22_3734123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 5, 8].length) (baseStart_3734123 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3734123 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3734123 prefixEnd_3734123 := by exact prefixLift 3734123
  have htrace : WordTrace (prefixWord ++ tailWord_3734123) baseStart_3734123 baseEnd_3734123 := by
    simpa [prefixWord, tailWord_3734123, baseEnd_3734123] using wordTrace_append hprefix tailTrace_3734123
  have hstable : (prefixWord ++ tailWord_3734123).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3734123).length < 2 ^ (prefixWord ++ tailWord_3734123).sum := by decide
  have hdescent : baseEnd_3734123 < baseStart_3734123 := by decide
  rcases family_descends (prefixWord ++ tailWord_3734123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3734133 : List Nat := [1, 3, 4, 2, 2, 2, 1, 3, 1, 3]
def baseStart_3734133 : Nat := 118140960795 + 3734133 * 2 ^ 59
def prefixEnd_3734133 : Nat := 4983230072969 + 3 ^ 40 * 3734133 * 2
def baseEnd_3734133 : Nat := 1278270037877029280776361

theorem tailTrace_3734133 : CollatzResearch.WordTrace tailWord_3734133 prefixEnd_3734133 1278270037877029280776361 := by
  unfold tailWord_3734133
  simp only [CollatzResearch.WordTrace]
  refine ⟨136195019380881354988503053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90796679587254236659002035 136195019380881354988503053)
  ·
    refine ⟨51073132267830508120688645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136195019380881354988503053 51073132267830508120688645)
    ·
      refine ⟨9576212300218220272629121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51073132267830508120688645 9576212300218220272629121)
      ·
        refine ⟨7182159225163665204471841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9576212300218220272629121 7182159225163665204471841)
        ·
          refine ⟨5386619418872748903353881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7182159225163665204471841 5386619418872748903353881)
          ·
            refine ⟨4039964564154561677515411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5386619418872748903353881 4039964564154561677515411)
            ·
              refine ⟨6059946846231842516273117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4039964564154561677515411 6059946846231842516273117)
              ·
                refine ⟨2272480067336940943602419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6059946846231842516273117 2272480067336940943602419)
                ·
                  refine ⟨3408720101005411415403629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2272480067336940943602419 3408720101005411415403629)
                  ·
                    refine ⟨1278270037877029280776361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3408720101005411415403629 1278270037877029280776361)
                    ·
                      rfl

theorem cell22_3734133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 2, 1, 3, 1, 3].length) (baseStart_3734133 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3734133 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3734133 prefixEnd_3734133 := by exact prefixLift 3734133
  have htrace : WordTrace (prefixWord ++ tailWord_3734133) baseStart_3734133 baseEnd_3734133 := by
    simpa [prefixWord, tailWord_3734133, baseEnd_3734133] using wordTrace_append hprefix tailTrace_3734133
  have hstable : (prefixWord ++ tailWord_3734133).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3734133).length < 2 ^ (prefixWord ++ tailWord_3734133).sum := by decide
  have hdescent : baseEnd_3734133 < baseStart_3734133 := by decide
  rcases family_descends (prefixWord ++ tailWord_3734133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3734176 : List Nat := [2, 1, 1, 4, 5, 1, 1, 2, 1, 4]
def baseStart_3734176 : Nat := 118140960795 + 3734176 * 2 ^ 59
def prefixEnd_3734176 : Nat := 4983230072969 + 3 ^ 40 * 3734176 * 2
def baseEnd_3734176 : Nat := 1278284757655791501951229

theorem tailTrace_3734176 : CollatzResearch.WordTrace tailWord_3734176 prefixEnd_3734176 1278284757655791501951229 := by
  unfold tailWord_3734176
  simp only [CollatzResearch.WordTrace]
  refine ⟨68098293859862786666159191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90797725146483715554878921 68098293859862786666159191)
  ·
    refine ⟨102147440789794179999238787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68098293859862786666159191 102147440789794179999238787)
    ·
      refine ⟨153221161184691269998858181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102147440789794179999238787 153221161184691269998858181)
      ·
        refine ⟨28728967722129613124785909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 153221161184691269998858181 28728967722129613124785909)
        ·
          refine ⟨2693340723949651230448679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 28728967722129613124785909 2693340723949651230448679)
          ·
            refine ⟨4040011085924476845673019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2693340723949651230448679 4040011085924476845673019)
            ·
              refine ⟨6060016628886715268509529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4040011085924476845673019 6060016628886715268509529)
              ·
                refine ⟨4545012471665036451382147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6060016628886715268509529 4545012471665036451382147)
                ·
                  refine ⟨6817518707497554677073221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4545012471665036451382147 6817518707497554677073221)
                  ·
                    refine ⟨1278284757655791501951229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6817518707497554677073221 1278284757655791501951229)
                    ·
                      rfl

theorem cell22_3734176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 5, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 5, 1, 1, 2, 1, 4].length) (baseStart_3734176 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3734176 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3734176 prefixEnd_3734176 := by exact prefixLift 3734176
  have htrace : WordTrace (prefixWord ++ tailWord_3734176) baseStart_3734176 baseEnd_3734176 := by
    simpa [prefixWord, tailWord_3734176, baseEnd_3734176] using wordTrace_append hprefix tailTrace_3734176
  have hstable : (prefixWord ++ tailWord_3734176).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3734176).length < 2 ^ (prefixWord ++ tailWord_3734176).sum := by decide
  have hdescent : baseEnd_3734176 < baseStart_3734176 := by decide
  rcases family_descends (prefixWord ++ tailWord_3734176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3734262 : List Nat := [5, 1, 1, 1, 1, 2, 1, 1, 4, 5]
def baseStart_3734262 : Nat := 118140960795 + 3734262 * 2 ^ 59
def prefixEnd_3734262 : Nat := 4983230072969 + 3 ^ 40 * 3734262 * 2
def baseEnd_3734262 : Nat := 1278314197213315944300965

theorem tailTrace_3734262 : CollatzResearch.WordTrace tailWord_3734262 prefixEnd_3734262 1278314197213315944300965 := by
  unfold tailWord_3734262
  simp only [CollatzResearch.WordTrace]
  refine ⟨8512482774838375626246815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 90799816264942673346632693 8512482774838375626246815)
  ·
    refine ⟨12768724162257563439370223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8512482774838375626246815 12768724162257563439370223)
    ·
      refine ⟨19153086243386345159055335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12768724162257563439370223 19153086243386345159055335)
      ·
        refine ⟨28729629365079517738583003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19153086243386345159055335 28729629365079517738583003)
        ·
          refine ⟨43094444047619276607874505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28729629365079517738583003 43094444047619276607874505)
          ·
            refine ⟨32320833035714457455905879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43094444047619276607874505 32320833035714457455905879)
            ·
              refine ⟨48481249553571686183858819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32320833035714457455905879 48481249553571686183858819)
              ·
                refine ⟨72721874330357529275788229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48481249553571686183858819 72721874330357529275788229)
                ·
                  refine ⟨13635351436942036739210293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 72721874330357529275788229 13635351436942036739210293)
                  ·
                    refine ⟨1278314197213315944300965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13635351436942036739210293 1278314197213315944300965)
                    ·
                      rfl

theorem cell22_3734262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 1, 4, 5].length) (baseStart_3734262 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3734262 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3734262 prefixEnd_3734262 := by exact prefixLift 3734262
  have htrace : WordTrace (prefixWord ++ tailWord_3734262) baseStart_3734262 baseEnd_3734262 := by
    simpa [prefixWord, tailWord_3734262, baseEnd_3734262] using wordTrace_append hprefix tailTrace_3734262
  have hstable : (prefixWord ++ tailWord_3734262).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3734262).length < 2 ^ (prefixWord ++ tailWord_3734262).sum := by decide
  have hdescent : baseEnd_3734262 < baseStart_3734262 := by decide
  rcases family_descends (prefixWord ++ tailWord_3734262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3734356 : List Nat := [2, 4, 1, 1, 4, 1, 2, 1, 2, 4]
def baseStart_3734356 : Nat := 118140960795 + 3734356 * 2 ^ 59
def prefixEnd_3734356 : Nat := 4983230072969 + 3 ^ 40 * 3734356 * 2
def baseEnd_3734356 : Nat := 1278346375334331032450677

theorem tailTrace_3734356 : CollatzResearch.WordTrace tailWord_3734356 prefixEnd_3734356 1278346375334331032450677 := by
  unfold tailWord_3734356
  simp only [CollatzResearch.WordTrace]
  refine ⟨68101576429536732036935461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90802101906048976049247281 68101576429536732036935461)
  ·
    refine ⟨12769045580538137256925399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 68101576429536732036935461 12769045580538137256925399)
    ·
      refine ⟨19153568370807205885388099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12769045580538137256925399 19153568370807205885388099)
      ·
        refine ⟨28730352556210808828082149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19153568370807205885388099 28730352556210808828082149)
        ·
          refine ⟨5386941104289526655265403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28730352556210808828082149 5386941104289526655265403)
          ·
            refine ⟨8080411656434289982898105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5386941104289526655265403 8080411656434289982898105)
            ·
              refine ⟨6060308742325717487173579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8080411656434289982898105 6060308742325717487173579)
              ·
                refine ⟨9090463113488576230760369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6060308742325717487173579 9090463113488576230760369)
                ·
                  refine ⟨6817847335116432173070277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9090463113488576230760369 6817847335116432173070277)
                  ·
                    refine ⟨1278346375334331032450677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6817847335116432173070277 1278346375334331032450677)
                    ·
                      rfl

theorem cell22_3734356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 2, 1, 2, 4].length) (baseStart_3734356 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3734356 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3734356 prefixEnd_3734356 := by exact prefixLift 3734356
  have htrace : WordTrace (prefixWord ++ tailWord_3734356) baseStart_3734356 baseEnd_3734356 := by
    simpa [prefixWord, tailWord_3734356, baseEnd_3734356] using wordTrace_append hprefix tailTrace_3734356
  have hstable : (prefixWord ++ tailWord_3734356).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3734356).length < 2 ^ (prefixWord ++ tailWord_3734356).sum := by decide
  have hdescent : baseEnd_3734356 < baseStart_3734356 := by decide
  rcases family_descends (prefixWord ++ tailWord_3734356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3734397 : List Nat := [1, 4, 1, 1, 2, 1, 3, 1, 1, 7]
def baseStart_3734397 : Nat := 118140960795 + 3734397 * 2 ^ 59
def prefixEnd_3734397 : Nat := 4983230072969 + 3 ^ 40 * 3734397 * 2
def baseEnd_3734397 : Nat := 1278360410472220592175551

theorem tailTrace_3734397 : CollatzResearch.WordTrace tailWord_3734397 prefixEnd_3734397 1278360410472220592175551 := by
  unfold tailWord_3734397
  simp only [CollatzResearch.WordTrace]
  refine ⟨136204648251924928076113445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90803098834616618717408963 136204648251924928076113445)
  ·
    refine ⟨25538371547235924014271271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 136204648251924928076113445 25538371547235924014271271)
    ·
      refine ⟨38307557320853886021406907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25538371547235924014271271 38307557320853886021406907)
      ·
        refine ⟨57461335981280829032110361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38307557320853886021406907 57461335981280829032110361)
        ·
          refine ⟨43096001985960621774082771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57461335981280829032110361 43096001985960621774082771)
          ·
            refine ⟨64644002978940932661124157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43096001985960621774082771 64644002978940932661124157)
            ·
              refine ⟨24241501117102849747921559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64644002978940932661124157 24241501117102849747921559)
              ·
                refine ⟨36362251675654274621882339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24241501117102849747921559 36362251675654274621882339)
                ·
                  refine ⟨54543377513481411932823509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36362251675654274621882339 54543377513481411932823509)
                  ·
                    refine ⟨1278360410472220592175551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 54543377513481411932823509 1278360410472220592175551)
                    ·
                      rfl

theorem cell22_3734397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 1, 1, 7].length) (baseStart_3734397 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3734397 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3734397 prefixEnd_3734397 := by exact prefixLift 3734397
  have htrace : WordTrace (prefixWord ++ tailWord_3734397) baseStart_3734397 baseEnd_3734397 := by
    simpa [prefixWord, tailWord_3734397, baseEnd_3734397] using wordTrace_append hprefix tailTrace_3734397
  have hstable : (prefixWord ++ tailWord_3734397).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3734397).length < 2 ^ (prefixWord ++ tailWord_3734397).sum := by decide
  have hdescent : baseEnd_3734397 < baseStart_3734397 := by decide
  rcases family_descends (prefixWord ++ tailWord_3734397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3734474 : List Nat := [3, 1, 2, 1, 2, 1, 1, 5, 2, 4]
def baseStart_3734474 : Nat := 118140960795 + 3734474 * 2 ^ 59
def prefixEnd_3734474 : Nat := 4983230072969 + 3 ^ 40 * 3734474 * 2
def baseEnd_3734474 : Nat := 1278386769145818058000315

theorem tailTrace_3734474 : CollatzResearch.WordTrace tailWord_3734474 prefixEnd_3734474 1278386769145818058000315 := by
  unfold tailWord_3734474
  simp only [CollatzResearch.WordTrace]
  refine ⟨34051864168161492556666619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90804971115097313484444317 34051864168161492556666619)
  ·
    refine ⟨51077796252242238834999929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34051864168161492556666619 51077796252242238834999929)
    ·
      refine ⟨38308347189181679126249947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51077796252242238834999929 38308347189181679126249947)
      ·
        refine ⟨57462520783772518689374921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38308347189181679126249947 57462520783772518689374921)
        ·
          refine ⟨43096890587829389017031191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57462520783772518689374921 43096890587829389017031191)
          ·
            refine ⟨64645335881744083525546787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43096890587829389017031191 64645335881744083525546787)
            ·
              refine ⟨96968003822616125288320181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64645335881744083525546787 96968003822616125288320181)
              ·
                refine ⟨9090750358370261745780017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 96968003822616125288320181 9090750358370261745780017)
                ·
                  refine ⟨6818062768777696309335013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9090750358370261745780017 6818062768777696309335013)
                  ·
                    refine ⟨1278386769145818058000315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6818062768777696309335013 1278386769145818058000315)
                    ·
                      rfl

theorem cell22_3734474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 5, 2, 4].length) (baseStart_3734474 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3734474 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3734474 prefixEnd_3734474 := by exact prefixLift 3734474
  have htrace : WordTrace (prefixWord ++ tailWord_3734474) baseStart_3734474 baseEnd_3734474 := by
    simpa [prefixWord, tailWord_3734474, baseEnd_3734474] using wordTrace_append hprefix tailTrace_3734474
  have hstable : (prefixWord ++ tailWord_3734474).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3734474).length < 2 ^ (prefixWord ++ tailWord_3734474).sum := by decide
  have hdescent : baseEnd_3734474 < baseStart_3734474 := by decide
  rcases family_descends (prefixWord ++ tailWord_3734474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3734478 : List Nat := [4, 1, 1, 1, 2, 5, 1, 3, 4]
def baseStart_3734478 : Nat := 118140960795 + 3734478 * 2 ^ 59
def prefixEnd_3734478 : Nat := 4983230072969 + 3 ^ 40 * 3734478 * 2
def baseEnd_3734478 : Nat := 426129379475854460300101

theorem tailTrace_3734478 : CollatzResearch.WordTrace tailWord_3734478 prefixEnd_3734478 426129379475854460300101 := by
  unfold tailWord_3734478
  simp only [CollatzResearch.WordTrace]
  refine ⟨17025950320578934863726511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 90805068376420985939874725 17025950320578934863726511)
  ·
    refine ⟨25538925480868402295589767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17025950320578934863726511 25538925480868402295589767)
    ·
      refine ⟨38308388221302603443384651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25538925480868402295589767 38308388221302603443384651)
      ·
        refine ⟨57462582331953905165076977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38308388221302603443384651 57462582331953905165076977)
        ·
          refine ⟨43096936748965428873807733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57462582331953905165076977 43096936748965428873807733)
          ·
            refine ⟨4040337820215508956919475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 43096936748965428873807733 4040337820215508956919475)
            ·
              refine ⟨6060506730323263435379213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4040337820215508956919475 6060506730323263435379213)
              ·
                refine ⟨2272690023871223788267205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6060506730323263435379213 2272690023871223788267205)
                ·
                  refine ⟨426129379475854460300101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2272690023871223788267205 426129379475854460300101)
                  ·
                    rfl

theorem cell22_3734478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 5, 1, 3, 4].length) (baseStart_3734478 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3734478 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3734478 prefixEnd_3734478 := by exact prefixLift 3734478
  have htrace : WordTrace (prefixWord ++ tailWord_3734478) baseStart_3734478 baseEnd_3734478 := by
    simpa [prefixWord, tailWord_3734478, baseEnd_3734478] using wordTrace_append hprefix tailTrace_3734478
  have hstable : (prefixWord ++ tailWord_3734478).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3734478).length < 2 ^ (prefixWord ++ tailWord_3734478).sum := by decide
  have hdescent : baseEnd_3734478 < baseStart_3734478 := by decide
  rcases family_descends (prefixWord ++ tailWord_3734478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3734489 : List Nat := [1, 2, 1, 2, 5, 3, 8]
def baseStart_3734489 : Nat := 118140960795 + 3734489 * 2 ^ 59
def prefixEnd_3734489 : Nat := 4983230072969 + 3 ^ 40 * 3734489 * 2
def baseEnd_3734489 : Nat := 47347848294531963662047

theorem tailTrace_3734489 : CollatzResearch.WordTrace tailWord_3734489 prefixEnd_3734489 47347848294531963662047 := by
  unfold tailWord_3734489
  simp only [CollatzResearch.WordTrace]
  refine ⟨136208003767591627788462521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90805335845061085192308347 136208003767591627788462521)
  ·
    refine ⟨102156002825693720841346891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136208003767591627788462521 102156002825693720841346891)
    ·
      refine ⟨153234004238540581262020337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102156002825693720841346891 153234004238540581262020337)
      ·
        refine ⟨114925503178905435946515253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153234004238540581262020337 114925503178905435946515253)
        ·
          refine ⟨10774265923022384619985805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 114925503178905435946515253 10774265923022384619985805)
          ·
            refine ⟨4040349721133394232494677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10774265923022384619985805 4040349721133394232494677)
            ·
              refine ⟨47347848294531963662047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4040349721133394232494677 47347848294531963662047)
              ·
                rfl

theorem cell22_3734489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 3, 8].length) (baseStart_3734489 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3734489 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3734489 prefixEnd_3734489 := by exact prefixLift 3734489
  have htrace : WordTrace (prefixWord ++ tailWord_3734489) baseStart_3734489 baseEnd_3734489 := by
    simpa [prefixWord, tailWord_3734489, baseEnd_3734489] using wordTrace_append hprefix tailTrace_3734489
  have hstable : (prefixWord ++ tailWord_3734489).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3734489).length < 2 ^ (prefixWord ++ tailWord_3734489).sum := by decide
  have hdescent : baseEnd_3734489 < baseStart_3734489 := by decide
  rcases family_descends (prefixWord ++ tailWord_3734489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3734546 : List Nat := [3, 2, 5, 1, 2, 1, 2, 2, 4]
def baseStart_3734546 : Nat := 118140960795 + 3734546 * 2 ^ 59
def prefixEnd_3734546 : Nat := 4983230072969 + 3 ^ 40 * 3734546 * 2
def baseEnd_3734546 : Nat := 426137138739077956733365

theorem tailTrace_3734546 : CollatzResearch.WordTrace tailWord_3734546 prefixEnd_3734546 426137138739077956733365 := by
  unfold tailWord_3734546
  simp only [CollatzResearch.WordTrace]
  refine ⟨34052520682096281630821873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90806721818923417682191661 34052520682096281630821873)
  ·
    refine ⟨25539390511572211223116405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34052520682096281630821873 25539390511572211223116405)
    ·
      refine ⟨2394317860459894802167163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 25539390511572211223116405 2394317860459894802167163)
      ·
        refine ⟨3591476790689842203250745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2394317860459894802167163 3591476790689842203250745)
        ·
          refine ⟨2693607593017381652438059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3591476790689842203250745 2693607593017381652438059)
          ·
            refine ⟨4040411389526072478657089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2693607593017381652438059 4040411389526072478657089)
            ·
              refine ⟨3030308542144554358992817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4040411389526072478657089 3030308542144554358992817)
              ·
                refine ⟨2272731406608415769244613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3030308542144554358992817 2272731406608415769244613)
                ·
                  refine ⟨426137138739077956733365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2272731406608415769244613 426137138739077956733365)
                  ·
                    rfl

theorem cell22_3734546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 2, 1, 2, 2, 4].length) (baseStart_3734546 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3734546 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3734546 prefixEnd_3734546 := by exact prefixLift 3734546
  have htrace : WordTrace (prefixWord ++ tailWord_3734546) baseStart_3734546 baseEnd_3734546 := by
    simpa [prefixWord, tailWord_3734546, baseEnd_3734546] using wordTrace_append hprefix tailTrace_3734546
  have hstable : (prefixWord ++ tailWord_3734546).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3734546).length < 2 ^ (prefixWord ++ tailWord_3734546).sum := by decide
  have hdescent : baseEnd_3734546 < baseStart_3734546 := by decide
  rcases family_descends (prefixWord ++ tailWord_3734546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3734551 : List Nat := [1, 1, 3, 5, 1, 1, 1, 4, 5]
def baseStart_3734551 : Nat := 118140960795 + 3734551 * 2 ^ 59
def prefixEnd_3734551 : Nat := 4983230072969 + 3 ^ 40 * 3734551 * 2
def baseEnd_3734551 : Nat := 426137709273138507941693

theorem tailTrace_3734551 : CollatzResearch.WordTrace tailWord_3734551 prefixEnd_3734551 426137709273138507941693 := by
  unfold tailWord_3734551
  simp only [CollatzResearch.WordTrace]
  refine ⟨136210265093367012377219507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90806843395578008251479671 136210265093367012377219507)
  ·
    refine ⟨204315397640050518565829261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136210265093367012377219507 204315397640050518565829261)
    ·
      refine ⟨76618274115018944462185973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 204315397640050518565829261 76618274115018944462185973)
      ·
        refine ⟨7182963198283026043329935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 76618274115018944462185973 7182963198283026043329935)
        ·
          refine ⟨10774444797424539064994903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7182963198283026043329935 10774444797424539064994903)
          ·
            refine ⟨16161667196136808597492355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10774444797424539064994903 16161667196136808597492355)
            ·
              refine ⟨24242500794205212896238533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16161667196136808597492355 24242500794205212896238533)
              ·
                refine ⟨4545468898913477418044725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24242500794205212896238533 4545468898913477418044725)
                ·
                  refine ⟨426137709273138507941693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4545468898913477418044725 426137709273138507941693)
                  ·
                    rfl

theorem cell22_3734551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 4, 5].length) (baseStart_3734551 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3734551 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3734551 prefixEnd_3734551 := by exact prefixLift 3734551
  have htrace : WordTrace (prefixWord ++ tailWord_3734551) baseStart_3734551 baseEnd_3734551 := by
    simpa [prefixWord, tailWord_3734551, baseEnd_3734551] using wordTrace_append hprefix tailTrace_3734551
  have hstable : (prefixWord ++ tailWord_3734551).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3734551).length < 2 ^ (prefixWord ++ tailWord_3734551).sum := by decide
  have hdescent : baseEnd_3734551 < baseStart_3734551 := by decide
  rcases family_descends (prefixWord ++ tailWord_3734551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3734581 : List Nat := [1, 3, 3, 1, 1, 1, 1, 6, 1, 4]
def baseStart_3734581 : Nat := 118140960795 + 3734581 * 2 ^ 59
def prefixEnd_3734581 : Nat := 4983230072969 + 3 ^ 40 * 3734581 * 2
def baseEnd_3734581 : Nat := 1278423397432505445574987

theorem tailTrace_3734581 : CollatzResearch.WordTrace tailWord_3734581 prefixEnd_3734581 1278423397432505445574987 := by
  unfold tailWord_3734581
  simp only [CollatzResearch.WordTrace]
  refine ⟨136211359283258327500811597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90807572855505551667207731 136211359283258327500811597)
  ·
    refine ⟨51079259731221872812804349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136211359283258327500811597 51079259731221872812804349)
    ·
      refine ⟨19154722399208202304801631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51079259731221872812804349 19154722399208202304801631)
      ·
        refine ⟨28732083598812303457202447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19154722399208202304801631 28732083598812303457202447)
        ·
          refine ⟨43098125398218455185803671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28732083598812303457202447 43098125398218455185803671)
          ·
            refine ⟨64647188097327682778705507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43098125398218455185803671 64647188097327682778705507)
            ·
              refine ⟨96970782145991524168058261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64647188097327682778705507 96970782145991524168058261)
              ·
                refine ⟨4545505413093352695377731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 96970782145991524168058261 4545505413093352695377731)
                ·
                  refine ⟨6818258119640029043066597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4545505413093352695377731 6818258119640029043066597)
                  ·
                    refine ⟨1278423397432505445574987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6818258119640029043066597 1278423397432505445574987)
                    ·
                      rfl

theorem cell22_3734581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 6, 1, 4].length) (baseStart_3734581 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3734581 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3734581 prefixEnd_3734581 := by exact prefixLift 3734581
  have htrace : WordTrace (prefixWord ++ tailWord_3734581) baseStart_3734581 baseEnd_3734581 := by
    simpa [prefixWord, tailWord_3734581, baseEnd_3734581] using wordTrace_append hprefix tailTrace_3734581
  have hstable : (prefixWord ++ tailWord_3734581).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3734581).length < 2 ^ (prefixWord ++ tailWord_3734581).sum := by decide
  have hdescent : baseEnd_3734581 < baseStart_3734581 := by decide
  rcases family_descends (prefixWord ++ tailWord_3734581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3734624 : List Nat := [2, 1, 1, 3, 2, 2, 2, 9]
def baseStart_3734624 : Nat := 118140960795 + 3734624 * 2 ^ 59
def prefixEnd_3734624 : Nat := 4983230072969 + 3 ^ 40 * 3734624 * 2
def baseEnd_3734624 : Nat := 142048679690140851861095

theorem tailTrace_3734624 : CollatzResearch.WordTrace tailWord_3734624 prefixEnd_3734624 142048679690140851861095 := by
  unfold tailWord_3734624
  simp only [CollatzResearch.WordTrace]
  refine ⟨68106463811051272922313463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90808618414735030563084617 68106463811051272922313463)
  ·
    refine ⟨102159695716576909383470195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68106463811051272922313463 102159695716576909383470195)
    ·
      refine ⟨153239543574865364075205293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102159695716576909383470195 153239543574865364075205293)
      ·
        refine ⟨57464828840574511528201985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 153239543574865364075205293 57464828840574511528201985)
        ·
          refine ⟨43098621630430883646151489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57464828840574511528201985 43098621630430883646151489)
          ·
            refine ⟨32323966222823162734613617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43098621630430883646151489 32323966222823162734613617)
            ·
              refine ⟨24242974667117372050960213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32323966222823162734613617 24242974667117372050960213)
              ·
                refine ⟨142048679690140851861095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 24242974667117372050960213 142048679690140851861095)
                ·
                  rfl

theorem cell22_3734624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 9].length) (baseStart_3734624 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3734624 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3734624 prefixEnd_3734624 := by exact prefixLift 3734624
  have htrace : WordTrace (prefixWord ++ tailWord_3734624) baseStart_3734624 baseEnd_3734624 := by
    simpa [prefixWord, tailWord_3734624, baseEnd_3734624] using wordTrace_append hprefix tailTrace_3734624
  have hstable : (prefixWord ++ tailWord_3734624).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3734624).length < 2 ^ (prefixWord ++ tailWord_3734624).sum := by decide
  have hdescent : baseEnd_3734624 < baseStart_3734624 := by decide
  rcases family_descends (prefixWord ++ tailWord_3734624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3734639 : List Nat := [1, 1, 2, 1, 3, 3, 1, 1, 2, 7]
def baseStart_3734639 : Nat := 118140960795 + 3734639 * 2 ^ 59
def prefixEnd_3734639 : Nat := 4983230072969 + 3 ^ 40 * 3734639 * 2
def baseEnd_3734639 : Nat := 1278443252017812627624809

theorem tailTrace_3734639 : CollatzResearch.WordTrace tailWord_3734639 prefixEnd_3734639 1278443252017812627624809 := by
  unfold tailWord_3734639
  simp only [CollatzResearch.WordTrace]
  refine ⟨136213474717048203406422971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90808983144698802270948647 136213474717048203406422971)
  ·
    refine ⟨204320212075572305109634457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136213474717048203406422971 204320212075572305109634457)
    ·
      refine ⟨153240159056679228832225843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 204320212075572305109634457 153240159056679228832225843)
      ·
        refine ⟨229860238585018843248338765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153240159056679228832225843 229860238585018843248338765)
        ·
          refine ⟨86197589469382066218127037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 229860238585018843248338765 86197589469382066218127037)
          ·
            refine ⟨32324096051018274831797639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86197589469382066218127037 32324096051018274831797639)
            ·
              refine ⟨48486144076527412247696459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32324096051018274831797639 48486144076527412247696459)
              ·
                refine ⟨72729216114791118371544689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48486144076527412247696459 72729216114791118371544689)
                ·
                  refine ⟨54546912086093338778658517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72729216114791118371544689 54546912086093338778658517)
                  ·
                    refine ⟨1278443252017812627624809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 54546912086093338778658517 1278443252017812627624809)
                    ·
                      rfl

theorem cell22_3734639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 1, 2, 7].length) (baseStart_3734639 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3734639 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3734639 prefixEnd_3734639 := by exact prefixLift 3734639
  have htrace : WordTrace (prefixWord ++ tailWord_3734639) baseStart_3734639 baseEnd_3734639 := by
    simpa [prefixWord, tailWord_3734639, baseEnd_3734639] using wordTrace_append hprefix tailTrace_3734639
  have hstable : (prefixWord ++ tailWord_3734639).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3734639).length < 2 ^ (prefixWord ++ tailWord_3734639).sum := by decide
  have hdescent : baseEnd_3734639 < baseStart_3734639 := by decide
  rcases family_descends (prefixWord ++ tailWord_3734639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3734656 : List Nat := [2, 1, 1, 2, 1, 3, 2, 2, 5, 3]
def baseStart_3734656 : Nat := 118140960795 + 3734656 * 2 ^ 59
def prefixEnd_3734656 : Nat := 4983230072969 + 3 ^ 40 * 3734656 * 2
def baseEnd_3734656 : Nat := 1278449071465230249949757

theorem tailTrace_3734656 : CollatzResearch.WordTrace tailWord_3734656 prefixEnd_3734656 1278449071465230249949757 := by
  unfold tailWord_3734656
  simp only [CollatzResearch.WordTrace]
  refine ⟨68107047378993307654895911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90809396505324410206527881 68107047378993307654895911)
  ·
    refine ⟨102160571068489961482343867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68107047378993307654895911 102160571068489961482343867)
    ·
      refine ⟨153240856602734942223515801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102160571068489961482343867 153240856602734942223515801)
      ·
        refine ⟨114930642452051206667636851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153240856602734942223515801 114930642452051206667636851)
        ·
          refine ⟨172395963678076810001455277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114930642452051206667636851 172395963678076810001455277)
          ·
            refine ⟨64648486379278803750545729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 172395963678076810001455277 64648486379278803750545729)
            ·
              refine ⟨48486364784459102812909297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64648486379278803750545729 48486364784459102812909297)
              ·
                refine ⟨36364773588344327109681973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48486364784459102812909297 36364773588344327109681973)
                ·
                  refine ⟨3409197523907280666532685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 36364773588344327109681973 3409197523907280666532685)
                  ·
                    refine ⟨1278449071465230249949757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3409197523907280666532685 1278449071465230249949757)
                    ·
                      rfl

theorem cell22_3734656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 2, 5, 3].length) (baseStart_3734656 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3734656 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3734656 prefixEnd_3734656 := by exact prefixLift 3734656
  have htrace : WordTrace (prefixWord ++ tailWord_3734656) baseStart_3734656 baseEnd_3734656 := by
    simpa [prefixWord, tailWord_3734656, baseEnd_3734656] using wordTrace_append hprefix tailTrace_3734656
  have hstable : (prefixWord ++ tailWord_3734656).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3734656).length < 2 ^ (prefixWord ++ tailWord_3734656).sum := by decide
  have hdescent : baseEnd_3734656 < baseStart_3734656 := by decide
  rcases family_descends (prefixWord ++ tailWord_3734656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3734765 : List Nat := [1, 5, 1, 2, 2, 1, 1, 5, 4]
def baseStart_3734765 : Nat := 118140960795 + 3734765 * 2 ^ 59
def prefixEnd_3734765 : Nat := 4983230072969 + 3 ^ 40 * 3734765 * 2
def baseEnd_3734765 : Nat := 426162128130930099658141

theorem tailTrace_3734765 : CollatzResearch.WordTrace tailWord_3734765 prefixEnd_3734765 426162128130930099658141 := by
  unfold tailWord_3734765
  simp only [CollatzResearch.WordTrace]
  refine ⟨136218070314591726925509749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90812046876394484617006499 136218070314591726925509749)
  ·
    refine ⟨12770444091992974399266539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 136218070314591726925509749 12770444091992974399266539)
    ·
      refine ⟨19155666137989461598899809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12770444091992974399266539 19155666137989461598899809)
      ·
        refine ⟨14366749603492096199174857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19155666137989461598899809 14366749603492096199174857)
        ·
          refine ⟨10775062202619072149381143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14366749603492096199174857 10775062202619072149381143)
          ·
            refine ⟨16162593303928608224071715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10775062202619072149381143 16162593303928608224071715)
            ·
              refine ⟨24243889955892912336107573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16162593303928608224071715 24243889955892912336107573)
              ·
                refine ⟨2272864683364960531510085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24243889955892912336107573 2272864683364960531510085)
                ·
                  refine ⟨426162128130930099658141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2272864683364960531510085 426162128130930099658141)
                  ·
                    rfl

theorem cell22_3734765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 5, 4].length) (baseStart_3734765 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3734765 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3734765 prefixEnd_3734765 := by exact prefixLift 3734765
  have htrace : WordTrace (prefixWord ++ tailWord_3734765) baseStart_3734765 baseEnd_3734765 := by
    simpa [prefixWord, tailWord_3734765, baseEnd_3734765] using wordTrace_append hprefix tailTrace_3734765
  have hstable : (prefixWord ++ tailWord_3734765).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3734765).length < 2 ^ (prefixWord ++ tailWord_3734765).sum := by decide
  have hdescent : baseEnd_3734765 < baseStart_3734765 := by decide
  rcases family_descends (prefixWord ++ tailWord_3734765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3734767 : List Nat := [1, 1, 2, 1, 7, 2, 2, 1, 1, 4]
def baseStart_3734767 : Nat := 118140960795 + 3734767 * 2 ^ 59
def prefixEnd_3734767 : Nat := 4983230072969 + 3 ^ 40 * 3734767 * 2
def baseEnd_3734767 : Nat := 1278487069033662960424417

theorem tailTrace_3734767 : CollatzResearch.WordTrace tailWord_3734767 prefixEnd_3734767 1278487069033662960424417 := by
  unfold tailWord_3734767
  simp only [CollatzResearch.WordTrace]
  refine ⟨136218143260584481267082555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90812095507056320844721703 136218143260584481267082555)
  ·
    refine ⟨204327214890876721900623833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136218143260584481267082555 204327214890876721900623833)
    ·
      refine ⟨153245411168157541425467875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 204327214890876721900623833 153245411168157541425467875)
      ·
        refine ⟨229868116752236312138201813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153245411168157541425467875 229868116752236312138201813)
        ·
          refine ⟨5387533986380538565739105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 229868116752236312138201813 5387533986380538565739105)
          ·
            refine ⟨4040650489785403924304329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5387533986380538565739105 4040650489785403924304329)
            ·
              refine ⟨3030487867339052943228247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4040650489785403924304329 3030487867339052943228247)
              ·
                refine ⟨4545731801008579414842371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3030487867339052943228247 4545731801008579414842371)
                ·
                  refine ⟨6818597701512869122263557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4545731801008579414842371 6818597701512869122263557)
                  ·
                    refine ⟨1278487069033662960424417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6818597701512869122263557 1278487069033662960424417)
                    ·
                      rfl

theorem cell22_3734767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 2, 2, 1, 1, 4].length) (baseStart_3734767 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3734767 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3734767 prefixEnd_3734767 := by exact prefixLift 3734767
  have htrace : WordTrace (prefixWord ++ tailWord_3734767) baseStart_3734767 baseEnd_3734767 := by
    simpa [prefixWord, tailWord_3734767, baseEnd_3734767] using wordTrace_append hprefix tailTrace_3734767
  have hstable : (prefixWord ++ tailWord_3734767).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3734767).length < 2 ^ (prefixWord ++ tailWord_3734767).sum := by decide
  have hdescent : baseEnd_3734767 < baseStart_3734767 := by decide
  rcases family_descends (prefixWord ++ tailWord_3734767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3734780 : List Nat := [2, 2, 2, 1, 5, 1, 1, 1, 4, 3]
def baseStart_3734780 : Nat := 118140960795 + 3734780 * 2 ^ 59
def prefixEnd_3734780 : Nat := 4983230072969 + 3 ^ 40 * 3734780 * 2
def baseEnd_3734780 : Nat := 1278491519199335259849377

theorem tailTrace_3734780 : CollatzResearch.WordTrace tailWord_3734780 prefixEnd_3734780 1278491519199335259849377 := by
  unfold tailWord_3734780
  simp only [CollatzResearch.WordTrace]
  refine ⟨68109308704768692243652897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90812411606358256324870529 68109308704768692243652897)
  ·
    refine ⟨51081981528576519182739673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68109308704768692243652897 51081981528576519182739673)
    ·
      refine ⟨38311486146432389387054755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51081981528576519182739673 38311486146432389387054755)
      ·
        refine ⟨57467229219648584080582133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38311486146432389387054755 57467229219648584080582133)
        ·
          refine ⟨5387552739342054757554575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 57467229219648584080582133 5387552739342054757554575)
          ·
            refine ⟨8081329109013082136331863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5387552739342054757554575 8081329109013082136331863)
            ·
              refine ⟨12121993663519623204497795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8081329109013082136331863 12121993663519623204497795)
              ·
                refine ⟨18182990495279434806746693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12121993663519623204497795 18182990495279434806746693)
                ·
                  refine ⟨3409310717864894026265005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18182990495279434806746693 3409310717864894026265005)
                  ·
                    refine ⟨1278491519199335259849377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3409310717864894026265005 1278491519199335259849377)
                    ·
                      rfl

theorem cell22_3734780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 1, 1, 4, 3].length) (baseStart_3734780 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3734780 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3734780 prefixEnd_3734780 := by exact prefixLift 3734780
  have htrace : WordTrace (prefixWord ++ tailWord_3734780) baseStart_3734780 baseEnd_3734780 := by
    simpa [prefixWord, tailWord_3734780, baseEnd_3734780] using wordTrace_append hprefix tailTrace_3734780
  have hstable : (prefixWord ++ tailWord_3734780).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3734780).length < 2 ^ (prefixWord ++ tailWord_3734780).sum := by decide
  have hdescent : baseEnd_3734780 < baseStart_3734780 := by decide
  rcases family_descends (prefixWord ++ tailWord_3734780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3734810 : List Nat := [3, 1, 1, 3, 3, 3, 2, 6]
def baseStart_3734810 : Nat := 118140960795 + 3734810 * 2 ^ 59
def prefixEnd_3734810 : Nat := 4983230072969 + 3 ^ 40 * 3734810 * 2
def baseEnd_3734810 : Nat := 142055754312491686844365

theorem tailTrace_3734810 : CollatzResearch.WordTrace tailWord_3734810 prefixEnd_3734810 142055754312491686844365 := by
  unfold tailWord_3734810
  simp only [CollatzResearch.WordTrace]
  refine ⟨34054927899857174902724471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90813141066285799740598589 34054927899857174902724471)
  ·
    refine ⟨51082391849785762354086707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34054927899857174902724471 51082391849785762354086707)
    ·
      refine ⟨76623587774678643531130061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51082391849785762354086707 76623587774678643531130061)
      ·
        refine ⟨28733845415504491324173773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76623587774678643531130061 28733845415504491324173773)
        ·
          refine ⟨10775192030814184246565165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28733845415504491324173773 10775192030814184246565165)
          ·
            refine ⟨4040697011555319092461937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10775192030814184246565165 4040697011555319092461937)
            ·
              refine ⟨3030522758666489319346453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4040697011555319092461937 3030522758666489319346453)
              ·
                refine ⟨142055754312491686844365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3030522758666489319346453 142055754312491686844365)
                ·
                  rfl

theorem cell22_3734810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 3, 2, 6].length) (baseStart_3734810 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3734810 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3734810 prefixEnd_3734810 := by exact prefixLift 3734810
  have htrace : WordTrace (prefixWord ++ tailWord_3734810) baseStart_3734810 baseEnd_3734810 := by
    simpa [prefixWord, tailWord_3734810, baseEnd_3734810] using wordTrace_append hprefix tailTrace_3734810
  have hstable : (prefixWord ++ tailWord_3734810).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3734810).length < 2 ^ (prefixWord ++ tailWord_3734810).sum := by decide
  have hdescent : baseEnd_3734810 < baseStart_3734810 := by decide
  rcases family_descends (prefixWord ++ tailWord_3734810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3734851 : List Nat := [1, 1, 1, 3, 1, 3, 1, 1, 2, 8]
def baseStart_3734851 : Nat := 118140960795 + 3734851 * 2 ^ 59
def prefixEnd_3734851 : Nat := 4983230072969 + 3 ^ 40 * 3734851 * 2
def baseEnd_3734851 : Nat := 1278515823950314741324159

theorem tailTrace_3734851 : CollatzResearch.WordTrace tailWord_3734851 prefixEnd_3734851 1278515823950314741324159 := by
  unfold tailWord_3734851
  simp only [CollatzResearch.WordTrace]
  refine ⟨136221206992280163613140407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90814137994853442408760271 136221206992280163613140407)
  ·
    refine ⟨204331810488420245419710611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136221206992280163613140407 204331810488420245419710611)
    ·
      refine ⟨306497715732630368129565917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204331810488420245419710611 306497715732630368129565917)
      ·
        refine ⟨114936643399736388048587219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 306497715732630368129565917 114936643399736388048587219)
        ·
          refine ⟨172404965099604582072880829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114936643399736388048587219 172404965099604582072880829)
          ·
            refine ⟨64651861912351718277330311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 172404965099604582072880829 64651861912351718277330311)
            ·
              refine ⟨96977792868527577415995467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64651861912351718277330311 96977792868527577415995467)
              ·
                refine ⟨145466689302791366123993201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96977792868527577415995467 145466689302791366123993201)
                ·
                  refine ⟨109100016977093524592994901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 145466689302791366123993201 109100016977093524592994901)
                  ·
                    refine ⟨1278515823950314741324159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 109100016977093524592994901 1278515823950314741324159)
                    ·
                      rfl

theorem cell22_3734851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 1, 2, 8].length) (baseStart_3734851 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3734851 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3734851 prefixEnd_3734851 := by exact prefixLift 3734851
  have htrace : WordTrace (prefixWord ++ tailWord_3734851) baseStart_3734851 baseEnd_3734851 := by
    simpa [prefixWord, tailWord_3734851, baseEnd_3734851] using wordTrace_append hprefix tailTrace_3734851
  have hstable : (prefixWord ++ tailWord_3734851).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3734851).length < 2 ^ (prefixWord ++ tailWord_3734851).sum := by decide
  have hdescent : baseEnd_3734851 < baseStart_3734851 := by decide
  rcases family_descends (prefixWord ++ tailWord_3734851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3734855 : List Nat := [1, 1, 4, 1, 2, 3, 4, 1, 5]
def baseStart_3734855 : Nat := 118140960795 + 3734855 * 2 ^ 59
def prefixEnd_3734855 : Nat := 4983230072969 + 3 ^ 40 * 3734855 * 2
def baseEnd_3734855 : Nat := 426172397744020021408049

theorem tailTrace_3734855 : CollatzResearch.WordTrace tailWord_3734855 prefixEnd_3734855 426172397744020021408049 := by
  unfold tailWord_3734855
  simp only [CollatzResearch.WordTrace]
  refine ⟨136221352884265672296286019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90814235256177114864190679 136221352884265672296286019)
  ·
    refine ⟨204332029326398508444429029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136221352884265672296286019 204332029326398508444429029)
    ·
      refine ⟨38312255498699720333330443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 204332029326398508444429029 38312255498699720333330443)
      ·
        refine ⟨57468383248049580499995665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38312255498699720333330443 57468383248049580499995665)
        ·
          refine ⟨43101287436037185374996749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57468383248049580499995665 43101287436037185374996749)
          ·
            refine ⟨16162982788513944515623781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43101287436037185374996749 16162982788513944515623781)
            ·
              refine ⟨3030559272846364596679459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16162982788513944515623781 3030559272846364596679459)
              ·
                refine ⟨4545838909269546895019189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3030559272846364596679459 4545838909269546895019189)
                ·
                  refine ⟨426172397744020021408049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4545838909269546895019189 426172397744020021408049)
                  ·
                    rfl

theorem cell22_3734855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 4, 1, 5].length) (baseStart_3734855 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3734855 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3734855 prefixEnd_3734855 := by exact prefixLift 3734855
  have htrace : WordTrace (prefixWord ++ tailWord_3734855) baseStart_3734855 baseEnd_3734855 := by
    simpa [prefixWord, tailWord_3734855, baseEnd_3734855] using wordTrace_append hprefix tailTrace_3734855
  have hstable : (prefixWord ++ tailWord_3734855).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3734855).length < 2 ^ (prefixWord ++ tailWord_3734855).sum := by decide
  have hdescent : baseEnd_3734855 < baseStart_3734855 := by decide
  rcases family_descends (prefixWord ++ tailWord_3734855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3734898 : List Nat := [3, 2, 1, 2, 1, 2, 1, 2, 3, 5]
def baseStart_3734898 : Nat := 118140960795 + 3734898 * 2 ^ 59
def prefixEnd_3734898 : Nat := 4983230072969 + 3 ^ 40 * 3734898 * 2
def baseEnd_3734898 : Nat := 1278531913010822285399015

theorem tailTrace_3734898 : CollatzResearch.WordTrace tailWord_3734898 prefixEnd_3734898 1278531913010822285399015 := by
  unfold tailWord_3734898
  simp only [CollatzResearch.WordTrace]
  refine ⟨34055730305777472660025337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90815280815406593760067565 34055730305777472660025337)
  ·
    refine ⟨25541797729333104495019003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34055730305777472660025337 25541797729333104495019003)
    ·
      refine ⟨38312696593999656742528505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25541797729333104495019003 38312696593999656742528505)
      ·
        refine ⟨28734522445499742556896379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38312696593999656742528505 28734522445499742556896379)
        ·
          refine ⟨43101783668249613835344569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28734522445499742556896379 43101783668249613835344569)
          ·
            refine ⟨32326337751187210376508427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43101783668249613835344569 32326337751187210376508427)
            ·
              refine ⟨48489506626780815564762641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32326337751187210376508427 48489506626780815564762641)
              ·
                refine ⟨36367129970085611673571981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48489506626780815564762641 36367129970085611673571981)
                ·
                  refine ⟨13637673738782104377589493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36367129970085611673571981 13637673738782104377589493)
                  ·
                    refine ⟨1278531913010822285399015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13637673738782104377589493 1278531913010822285399015)
                    ·
                      rfl

theorem cell22_3734898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 2, 3, 5].length) (baseStart_3734898 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3734898 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3734898 prefixEnd_3734898 := by exact prefixLift 3734898
  have htrace : WordTrace (prefixWord ++ tailWord_3734898) baseStart_3734898 baseEnd_3734898 := by
    simpa [prefixWord, tailWord_3734898, baseEnd_3734898] using wordTrace_append hprefix tailTrace_3734898
  have hstable : (prefixWord ++ tailWord_3734898).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3734898).length < 2 ^ (prefixWord ++ tailWord_3734898).sum := by decide
  have hdescent : baseEnd_3734898 < baseStart_3734898 := by decide
  rcases family_descends (prefixWord ++ tailWord_3734898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3734915 : List Nat := [1, 1, 1, 3, 5, 2, 2, 1, 1, 5]
def baseStart_3734915 : Nat := 118140960795 + 3734915 * 2 ^ 59
def prefixEnd_3734915 : Nat := 4983230072969 + 3 ^ 40 * 3734915 * 2
def baseEnd_3734915 : Nat := 1278537732458239907723963

theorem tailTrace_3734915 : CollatzResearch.WordTrace tailWord_3734915 prefixEnd_3734915 1278537732458239907723963 := by
  unfold tailWord_3734915
  simp only [CollatzResearch.WordTrace]
  refine ⟨136223541264048302543470199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90815694176032201695646799 136223541264048302543470199)
  ·
    refine ⟨204335311896072453815205299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136223541264048302543470199 204335311896072453815205299)
    ·
      refine ⟨306502967844108680722807949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204335311896072453815205299 306502967844108680722807949)
      ·
        refine ⟨114938612941540755271052981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 306502967844108680722807949 114938612941540755271052981)
        ·
          refine ⟨10775494963269445806661217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 114938612941540755271052981 10775494963269445806661217)
          ·
            refine ⟨8081621222452084354995913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10775494963269445806661217 8081621222452084354995913)
            ·
              refine ⟨6061215916839063266246935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8081621222452084354995913 6061215916839063266246935)
              ·
                refine ⟨9091823875258594899370403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6061215916839063266246935 9091823875258594899370403)
                ·
                  refine ⟨13637735812887892349055605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9091823875258594899370403 13637735812887892349055605)
                  ·
                    refine ⟨1278537732458239907723963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13637735812887892349055605 1278537732458239907723963)
                    ·
                      rfl

theorem cell22_3734915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 2, 1, 1, 5].length) (baseStart_3734915 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3734915 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3734915 prefixEnd_3734915 := by exact prefixLift 3734915
  have htrace : WordTrace (prefixWord ++ tailWord_3734915) baseStart_3734915 baseEnd_3734915 := by
    simpa [prefixWord, tailWord_3734915, baseEnd_3734915] using wordTrace_append hprefix tailTrace_3734915
  have hstable : (prefixWord ++ tailWord_3734915).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3734915).length < 2 ^ (prefixWord ++ tailWord_3734915).sum := by decide
  have hdescent : baseEnd_3734915 < baseStart_3734915 := by decide
  rcases family_descends (prefixWord ++ tailWord_3734915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3734936 : List Nat := [2, 1, 2, 5, 3, 1, 2, 1, 1, 4]
def baseStart_3734936 : Nat := 118140960795 + 3734936 * 2 ^ 59
def prefixEnd_3734936 : Nat := 4983230072969 + 3 ^ 40 * 3734936 * 2
def baseEnd_3734936 : Nat := 1278544921187402852948899

theorem tailTrace_3734936 : CollatzResearch.WordTrace tailWord_3734936 prefixEnd_3734936 1278544921187402852948899 := by
  unfold tailWord_3734936
  simp only [CollatzResearch.WordTrace]
  refine ⟨68112153598486111564992331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90816204797981482086656441 68112153598486111564992331)
  ·
    refine ⟨102168230397729167347488497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68112153598486111564992331 102168230397729167347488497)
    ·
      refine ⟨76626172798296875510616373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102168230397729167347488497 76626172798296875510616373)
      ·
        refine ⟨7183703699840332079120285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 76626172798296875510616373 7183703699840332079120285)
        ·
          refine ⟨2693888887440124529670107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7183703699840332079120285 2693888887440124529670107)
          ·
            refine ⟨4040833331160186794505161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2693888887440124529670107 4040833331160186794505161)
            ·
              refine ⟨3030624998370140095878871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4040833331160186794505161 3030624998370140095878871)
              ·
                refine ⟨4545937497555210143818307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3030624998370140095878871 4545937497555210143818307)
                ·
                  refine ⟨6818906246332815215727461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4545937497555210143818307 6818906246332815215727461)
                  ·
                    refine ⟨1278544921187402852948899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6818906246332815215727461 1278544921187402852948899)
                    ·
                      rfl

theorem cell22_3734936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 3, 1, 2, 1, 1, 4].length) (baseStart_3734936 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3734936 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3734936 prefixEnd_3734936 := by exact prefixLift 3734936
  have htrace : WordTrace (prefixWord ++ tailWord_3734936) baseStart_3734936 baseEnd_3734936 := by
    simpa [prefixWord, tailWord_3734936, baseEnd_3734936] using wordTrace_append hprefix tailTrace_3734936
  have hstable : (prefixWord ++ tailWord_3734936).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3734936).length < 2 ^ (prefixWord ++ tailWord_3734936).sum := by decide
  have hdescent : baseEnd_3734936 < baseStart_3734936 := by decide
  rcases family_descends (prefixWord ++ tailWord_3734936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3735011 : List Nat := [1, 1, 1, 6, 2, 2, 3, 2, 1, 3]
def baseStart_3735011 : Nat := 118140960795 + 3735011 * 2 ^ 59
def prefixEnd_3735011 : Nat := 4983230072969 + 3 ^ 40 * 3735011 * 2
def baseEnd_3735011 : Nat := 1278570595220127657323669

theorem tailTrace_3735011 : CollatzResearch.WordTrace tailWord_3735011 prefixEnd_3735011 1278570595220127657323669 := by
  unfold tailWord_3735011
  simp only [CollatzResearch.WordTrace]
  refine ⟨136227042671700510938964887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90818028447800340625976591 136227042671700510938964887)
  ·
    refine ⟨204340564007550766408447331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136227042671700510938964887 204340564007550766408447331)
    ·
      refine ⟨306510846011326149612670997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204340564007550766408447331 306510846011326149612670997)
      ·
        refine ⟨14367695906780913263093953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 306510846011326149612670997 14367695906780913263093953)
        ·
          refine ⟨10775771930085684947320465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14367695906780913263093953 10775771930085684947320465)
          ·
            refine ⟨8081828947564263710490349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10775771930085684947320465 8081828947564263710490349)
            ·
              refine ⟨3030685855336598891433881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8081828947564263710490349 3030685855336598891433881)
              ·
                refine ⟨2273014391502449168575411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3030685855336598891433881 2273014391502449168575411)
                ·
                  refine ⟨3409521587253673752863117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2273014391502449168575411 3409521587253673752863117)
                  ·
                    refine ⟨1278570595220127657323669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3409521587253673752863117 1278570595220127657323669)
                    ·
                      rfl

theorem cell22_3735011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 3, 2, 1, 3].length) (baseStart_3735011 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3735011 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3735011 prefixEnd_3735011 := by exact prefixLift 3735011
  have htrace : WordTrace (prefixWord ++ tailWord_3735011) baseStart_3735011 baseEnd_3735011 := by
    simpa [prefixWord, tailWord_3735011, baseEnd_3735011] using wordTrace_append hprefix tailTrace_3735011
  have hstable : (prefixWord ++ tailWord_3735011).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3735011).length < 2 ^ (prefixWord ++ tailWord_3735011).sum := by decide
  have hdescent : baseEnd_3735011 < baseStart_3735011 := by decide
  rcases family_descends (prefixWord ++ tailWord_3735011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3735037 : List Nat := [1, 4, 1, 1, 1, 4, 3, 2, 1, 4]
def baseStart_3735037 : Nat := 118140960795 + 3735037 * 2 ^ 59
def prefixEnd_3735037 : Nat := 4983230072969 + 3 ^ 40 * 3735037 * 2
def baseEnd_3735037 : Nat := 1278579495551472256173589

theorem tailTrace_3735037 : CollatzResearch.WordTrace tailWord_3735037 prefixEnd_3735037 1278579495551472256173589 := by
  unfold tailWord_3735037
  simp only [CollatzResearch.WordTrace]
  refine ⟨136227990969606317379411365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90818660646404211586274243 136227990969606317379411365)
  ·
    refine ⟨25542748306801184508639631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 136227990969606317379411365 25542748306801184508639631)
    ·
      refine ⟨38314122460201776762959447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25542748306801184508639631 38314122460201776762959447)
      ·
        refine ⟨57471183690302665144439171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38314122460201776762959447 57471183690302665144439171)
        ·
          refine ⟨86206775535453997716658757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57471183690302665144439171 86206775535453997716658757)
          ·
            refine ⟨16163770412897624571873517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 86206775535453997716658757 16163770412897624571873517)
            ·
              refine ⟨6061413904836609214452569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16163770412897624571873517 6061413904836609214452569)
              ·
                refine ⟨4546060428627456910839427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6061413904836609214452569 4546060428627456910839427)
                ·
                  refine ⟨6819090642941185366259141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4546060428627456910839427 6819090642941185366259141)
                  ·
                    refine ⟨1278579495551472256173589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6819090642941185366259141 1278579495551472256173589)
                    ·
                      rfl

theorem cell22_3735037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 3, 2, 1, 4].length) (baseStart_3735037 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3735037 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3735037 prefixEnd_3735037 := by exact prefixLift 3735037
  have htrace : WordTrace (prefixWord ++ tailWord_3735037) baseStart_3735037 baseEnd_3735037 := by
    simpa [prefixWord, tailWord_3735037, baseEnd_3735037] using wordTrace_append hprefix tailTrace_3735037
  have hstable : (prefixWord ++ tailWord_3735037).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3735037).length < 2 ^ (prefixWord ++ tailWord_3735037).sum := by decide
  have hdescent : baseEnd_3735037 < baseStart_3735037 := by decide
  rcases family_descends (prefixWord ++ tailWord_3735037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3735050 : List Nat := [3, 1, 2, 2, 2, 2, 1, 1, 3, 5]
def baseStart_3735050 : Nat := 118140960795 + 3735050 * 2 ^ 59
def prefixEnd_3735050 : Nat := 4983230072969 + 3 ^ 40 * 3735050 * 2
def baseEnd_3735050 : Nat := 1278583945717144555598549

theorem tailTrace_3735050 : CollatzResearch.WordTrace tailWord_3735050 prefixEnd_3735050 1278583945717144555598549 := by
  unfold tailWord_3735050
  simp only [CollatzResearch.WordTrace]
  refine ⟨34057116279639805149908651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90818976745706147066423069 34057116279639805149908651)
  ·
    refine ⟨51085674419459707724862977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34057116279639805149908651 51085674419459707724862977)
    ·
      refine ⟨38314255814594780793647233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51085674419459707724862977 38314255814594780793647233)
      ·
        refine ⟨28735691860946085595235425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38314255814594780793647233 28735691860946085595235425)
        ·
          refine ⟨21551768895709564196426569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28735691860946085595235425 21551768895709564196426569)
          ·
            refine ⟨16163826671782173147319927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21551768895709564196426569 16163826671782173147319927)
            ·
              refine ⟨24245740007673259720979891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16163826671782173147319927 24245740007673259720979891)
              ·
                refine ⟨36368610011509889581469837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24245740007673259720979891 36368610011509889581469837)
                ·
                  refine ⟨13638228754316208593051189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36368610011509889581469837 13638228754316208593051189)
                  ·
                    refine ⟨1278583945717144555598549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13638228754316208593051189 1278583945717144555598549)
                    ·
                      rfl

theorem cell22_3735050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 1, 3, 5].length) (baseStart_3735050 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3735050 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3735050 prefixEnd_3735050 := by exact prefixLift 3735050
  have htrace : WordTrace (prefixWord ++ tailWord_3735050) baseStart_3735050 baseEnd_3735050 := by
    simpa [prefixWord, tailWord_3735050, baseEnd_3735050] using wordTrace_append hprefix tailTrace_3735050
  have hstable : (prefixWord ++ tailWord_3735050).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3735050).length < 2 ^ (prefixWord ++ tailWord_3735050).sum := by decide
  have hdescent : baseEnd_3735050 < baseStart_3735050 := by decide
  rcases family_descends (prefixWord ++ tailWord_3735050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3735063 : List Nat := [1, 1, 3, 17]
def baseStart_3735063 : Nat := 118140960795 + 3735063 * 2 ^ 59
def prefixEnd_3735063 : Nat := 4983230072969 + 3 ^ 40 * 3735063 * 2
def baseEnd_3735063 : Nat := 1753893547164357825821

theorem tailTrace_3735063 : CollatzResearch.WordTrace tailWord_3735063 prefixEnd_3735063 1753893547164357825821 := by
  unfold tailWord_3735063
  simp only [CollatzResearch.WordTrace]
  refine ⟨136228939267512123819857843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90819292845008082546571895 136228939267512123819857843)
  ·
    refine ⟨204343408901268185729786765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136228939267512123819857843 204343408901268185729786765)
    ·
      refine ⟨76628778337975569648670037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 204343408901268185729786765 76628778337975569648670037)
      ·
        refine ⟨1753893547164357825821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 17 76628778337975569648670037 1753893547164357825821)
        ·
          rfl

theorem cell22_3735063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 17].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 17].length) (baseStart_3735063 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3735063 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3735063 prefixEnd_3735063 := by exact prefixLift 3735063
  have htrace : WordTrace (prefixWord ++ tailWord_3735063) baseStart_3735063 baseEnd_3735063 := by
    simpa [prefixWord, tailWord_3735063, baseEnd_3735063] using wordTrace_append hprefix tailTrace_3735063
  have hstable : (prefixWord ++ tailWord_3735063).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3735063).length < 2 ^ (prefixWord ++ tailWord_3735063).sum := by decide
  have hdescent : baseEnd_3735063 < baseStart_3735063 := by decide
  rcases family_descends (prefixWord ++ tailWord_3735063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3735097 : List Nat := [1, 2, 1, 5, 1, 3, 3, 6]
def baseStart_3735097 : Nat := 118140960795 + 3735097 * 2 ^ 59
def prefixEnd_3735097 : Nat := 4983230072969 + 3 ^ 40 * 3735097 * 2
def baseEnd_3735097 : Nat := 142066670530850233297045

theorem tailTrace_3735097 : CollatzResearch.WordTrace tailWord_3735097 prefixEnd_3735097 142066670530850233297045 := by
  unfold tailWord_3735097
  simp only [CollatzResearch.WordTrace]
  refine ⟨136230179349388947626595545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90820119566259298417730363 136230179349388947626595545)
  ·
    refine ⟨102172634512041710719946659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136230179349388947626595545 102172634512041710719946659)
    ·
      refine ⟨153258951768062566079919989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102172634512041710719946659 153258951768062566079919989)
      ·
        refine ⟨14368026728255865569992499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 153258951768062566079919989 14368026728255865569992499)
        ·
          refine ⟨21552040092383798354988749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14368026728255865569992499 21552040092383798354988749)
          ·
            refine ⟨8082015034643924383120781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21552040092383798354988749 8082015034643924383120781)
            ·
              refine ⟨3030755637991471643670293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8082015034643924383120781 3030755637991471643670293)
              ·
                refine ⟨142066670530850233297045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3030755637991471643670293 142066670530850233297045)
                ·
                  rfl

theorem cell22_3735097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 3, 6].length) (baseStart_3735097 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3735097 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3735097 prefixEnd_3735097 := by exact prefixLift 3735097
  have htrace : WordTrace (prefixWord ++ tailWord_3735097) baseStart_3735097 baseEnd_3735097 := by
    simpa [prefixWord, tailWord_3735097, baseEnd_3735097] using wordTrace_append hprefix tailTrace_3735097
  have hstable : (prefixWord ++ tailWord_3735097).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3735097).length < 2 ^ (prefixWord ++ tailWord_3735097).sum := by decide
  have hdescent : baseEnd_3735097 < baseStart_3735097 := by decide
  rcases family_descends (prefixWord ++ tailWord_3735097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3735155 : List Nat := [1, 1, 1, 2, 2, 1, 1, 2, 7, 4]
def baseStart_3735155 : Nat := 118140960795 + 3735155 * 2 ^ 59
def prefixEnd_3735155 : Nat := 4983230072969 + 3 ^ 40 * 3735155 * 2
def baseEnd_3735155 : Nat := 1278619889362959281723227

theorem tailTrace_3735155 : CollatzResearch.WordTrace tailWord_3735155 prefixEnd_3735155 1278619889362959281723227 := by
  unfold tailWord_3735155
  simp only [CollatzResearch.WordTrace]
  refine ⟨136232294783178823532206919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90821529855452549021471279 136232294783178823532206919)
  ·
    refine ⟨204348442174768235298310379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136232294783178823532206919 204348442174768235298310379)
    ·
      refine ⟨306522663262152352947465569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204348442174768235298310379 306522663262152352947465569)
      ·
        refine ⟨229891997446614264710599177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 306522663262152352947465569 229891997446614264710599177)
        ·
          refine ⟨172418998084960698532949383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 229891997446614264710599177 172418998084960698532949383)
          ·
            refine ⟨258628497127441047799424075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 172418998084960698532949383 258628497127441047799424075)
            ·
              refine ⟨387942745691161571699136113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 258628497127441047799424075 387942745691161571699136113)
              ·
                refine ⟨290957059268371178774352085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 387942745691161571699136113 290957059268371178774352085)
                ·
                  refine ⟨6819306076602449502523877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 290957059268371178774352085 6819306076602449502523877)
                  ·
                    refine ⟨1278619889362959281723227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6819306076602449502523877 1278619889362959281723227)
                    ·
                      rfl

theorem cell22_3735155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 2, 7, 4].length) (baseStart_3735155 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3735155 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3735155 prefixEnd_3735155 := by exact prefixLift 3735155
  have htrace : WordTrace (prefixWord ++ tailWord_3735155) baseStart_3735155 baseEnd_3735155 := by
    simpa [prefixWord, tailWord_3735155, baseEnd_3735155] using wordTrace_append hprefix tailTrace_3735155
  have hstable : (prefixWord ++ tailWord_3735155).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3735155).length < 2 ^ (prefixWord ++ tailWord_3735155).sum := by decide
  have hdescent : baseEnd_3735155 < baseStart_3735155 := by decide
  rcases family_descends (prefixWord ++ tailWord_3735155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3735185 : List Nat := [1, 2, 2, 1, 1, 1, 1, 3, 5, 5]
def baseStart_3735185 : Nat := 118140960795 + 3735185 * 2 ^ 59
def prefixEnd_3735185 : Nat := 4983230072969 + 3 ^ 40 * 3735185 * 2
def baseEnd_3735185 : Nat := 1278630158976049203473135

theorem tailTrace_3735185 : CollatzResearch.WordTrace tailWord_3735185 prefixEnd_3735185 1278630158976049203473135 := by
  unfold tailWord_3735185
  simp only [CollatzResearch.WordTrace]
  refine ⟨136233388973070138655799009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90822259315380092437199339 136233388973070138655799009)
  ·
    refine ⟨102175041729802603991849257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136233388973070138655799009 102175041729802603991849257)
    ·
      refine ⟨76631281297351952993886943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102175041729802603991849257 76631281297351952993886943)
      ·
        refine ⟨114946921946027929490830415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76631281297351952993886943 114946921946027929490830415)
        ·
          refine ⟨172420382919041894236245623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114946921946027929490830415 172420382919041894236245623)
          ·
            refine ⟨258630574378562841354368435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 172420382919041894236245623 258630574378562841354368435)
            ·
              refine ⟨387945861567844262031552653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 258630574378562841354368435 387945861567844262031552653)
              ·
                refine ⟨145479698087941598261832245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 387945861567844262031552653 145479698087941598261832245)
                ·
                  refine ⟨13638721695744524837046773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 145479698087941598261832245 13638721695744524837046773)
                  ·
                    refine ⟨1278630158976049203473135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13638721695744524837046773 1278630158976049203473135)
                    ·
                      rfl

theorem cell22_3735185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 5].length) (baseStart_3735185 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3735185 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3735185 prefixEnd_3735185 := by exact prefixLift 3735185
  have htrace : WordTrace (prefixWord ++ tailWord_3735185) baseStart_3735185 baseEnd_3735185 := by
    simpa [prefixWord, tailWord_3735185, baseEnd_3735185] using wordTrace_append hprefix tailTrace_3735185
  have hstable : (prefixWord ++ tailWord_3735185).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3735185).length < 2 ^ (prefixWord ++ tailWord_3735185).sum := by decide
  have hdescent : baseEnd_3735185 < baseStart_3735185 := by decide
  rcases family_descends (prefixWord ++ tailWord_3735185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3735215 : List Nat := [1, 1, 2, 1, 2, 4, 1, 10]
def baseStart_3735215 : Nat := 118140960795 + 3735215 * 2 ^ 59
def prefixEnd_3735215 : Nat := 4983230072969 + 3 ^ 40 * 3735215 * 2
def baseEnd_3735215 : Nat := 142071158732126569469227

theorem tailTrace_3735215 : CollatzResearch.WordTrace tailWord_3735215 prefixEnd_3735215 142071158732126569469227 := by
  unfold tailWord_3735215
  simp only [CollatzResearch.WordTrace]
  refine ⟨136234483162961453779391099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90822988775307635852927399 136234483162961453779391099)
  ·
    refine ⟨204351724744442180669086649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136234483162961453779391099 204351724744442180669086649)
    ·
      refine ⟨153263793558331635501814987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 204351724744442180669086649 153263793558331635501814987)
      ·
        refine ⟨229895690337497453252722481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153263793558331635501814987 229895690337497453252722481)
        ·
          refine ⟨172421767753123089939541861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 229895690337497453252722481 172421767753123089939541861)
          ·
            refine ⟨32329081453710579363664099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 172421767753123089939541861 32329081453710579363664099)
            ·
              refine ⟨48493622180565869045496149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32329081453710579363664099 48493622180565869045496149)
              ·
                refine ⟨142071158732126569469227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 48493622180565869045496149 142071158732126569469227)
                ·
                  rfl

theorem cell22_3735215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 10].length) (baseStart_3735215 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3735215 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3735215 prefixEnd_3735215 := by exact prefixLift 3735215
  have htrace : WordTrace (prefixWord ++ tailWord_3735215) baseStart_3735215 baseEnd_3735215 := by
    simpa [prefixWord, tailWord_3735215, baseEnd_3735215] using wordTrace_append hprefix tailTrace_3735215
  have hstable : (prefixWord ++ tailWord_3735215).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3735215).length < 2 ^ (prefixWord ++ tailWord_3735215).sum := by decide
  have hdescent : baseEnd_3735215 < baseStart_3735215 := by decide
  rcases family_descends (prefixWord ++ tailWord_3735215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3735236 : List Nat := [2, 3, 3, 1, 1, 1, 4, 2, 2, 3]
def baseStart_3735236 : Nat := 118140960795 + 3735236 * 2 ^ 59
def prefixEnd_3735236 : Nat := 4983230072969 + 3 ^ 40 * 3735236 * 2
def baseEnd_3735236 : Nat := 1278647617318302070447979

theorem tailTrace_3735236 : CollatzResearch.WordTrace tailWord_3735236 prefixEnd_3735236 1278647617318302070447979 := by
  unfold tailWord_3735236
  simp only [CollatzResearch.WordTrace]
  refine ⟨68117624547942687182952781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90823499397256916243937041 68117624547942687182952781)
  ·
    refine ⟨25544109205478507693607293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68117624547942687182952781 25544109205478507693607293)
    ·
      refine ⟨9579040952054440385102735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25544109205478507693607293 9579040952054440385102735)
      ·
        refine ⟨14368561428081660577654103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9579040952054440385102735 14368561428081660577654103)
        ·
          refine ⟨21552842142122490866481155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14368561428081660577654103 21552842142122490866481155)
          ·
            refine ⟨32329263213183736299721733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21552842142122490866481155 32329263213183736299721733)
            ·
              refine ⟨6061736852471950556197825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32329263213183736299721733 6061736852471950556197825)
              ·
                refine ⟨4546302639353962917148369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6061736852471950556197825 4546302639353962917148369)
                ·
                  refine ⟨3409726979515472187861277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4546302639353962917148369 3409726979515472187861277)
                  ·
                    refine ⟨1278647617318302070447979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3409726979515472187861277 1278647617318302070447979)
                    ·
                      rfl

theorem cell22_3735236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 4, 2, 2, 3].length) (baseStart_3735236 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3735236 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3735236 prefixEnd_3735236 := by exact prefixLift 3735236
  have htrace : WordTrace (prefixWord ++ tailWord_3735236) baseStart_3735236 baseEnd_3735236 := by
    simpa [prefixWord, tailWord_3735236, baseEnd_3735236] using wordTrace_append hprefix tailTrace_3735236
  have hstable : (prefixWord ++ tailWord_3735236).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3735236).length < 2 ^ (prefixWord ++ tailWord_3735236).sum := by decide
  have hdescent : baseEnd_3735236 < baseStart_3735236 := by decide
  rcases family_descends (prefixWord ++ tailWord_3735236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3735247 : List Nat := [1, 1, 2, 1, 1, 3, 1, 2, 7, 3]
def baseStart_3735247 : Nat := 118140960795 + 3735247 * 2 ^ 59
def prefixEnd_3735247 : Nat := 4983230072969 + 3 ^ 40 * 3735247 * 2
def baseEnd_3735247 : Nat := 1278651382843101708422945

theorem tailTrace_3735247 : CollatzResearch.WordTrace tailWord_3735247 prefixEnd_3735247 1278651382843101708422945 := by
  unfold tailWord_3735247
  simp only [CollatzResearch.WordTrace]
  refine ⟨136235650298845523244555995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90823766865897015496370663 136235650298845523244555995)
  ·
    refine ⟨204353475448268284866833993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136235650298845523244555995 204353475448268284866833993)
    ·
      refine ⟨153265106586201213650125495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 204353475448268284866833993 153265106586201213650125495)
      ·
        refine ⟨229897659879301820475188243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153265106586201213650125495 229897659879301820475188243)
        ·
          refine ⟨344846489818952730712782365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 229897659879301820475188243 344846489818952730712782365)
          ·
            refine ⟨129317433682107274017293387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 344846489818952730712782365 129317433682107274017293387)
            ·
              refine ⟨193976150523160911025940081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129317433682107274017293387 193976150523160911025940081)
              ·
                refine ⟨145482112892370683269455061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 193976150523160911025940081 145482112892370683269455061)
                ·
                  refine ⟨3409737020914937889127853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 145482112892370683269455061 3409737020914937889127853)
                  ·
                    refine ⟨1278651382843101708422945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3409737020914937889127853 1278651382843101708422945)
                    ·
                      rfl

theorem cell22_3735247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 2, 7, 3].length) (baseStart_3735247 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3735247 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3735247 prefixEnd_3735247 := by exact prefixLift 3735247
  have htrace : WordTrace (prefixWord ++ tailWord_3735247) baseStart_3735247 baseEnd_3735247 := by
    simpa [prefixWord, tailWord_3735247, baseEnd_3735247] using wordTrace_append hprefix tailTrace_3735247
  have hstable : (prefixWord ++ tailWord_3735247).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3735247).length < 2 ^ (prefixWord ++ tailWord_3735247).sum := by decide
  have hdescent : baseEnd_3735247 < baseStart_3735247 := by decide
  rcases family_descends (prefixWord ++ tailWord_3735247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3735281 : List Nat := [1, 2, 2, 2, 2, 3, 1, 5, 1, 3]
def baseStart_3735281 : Nat := 118140960795 + 3735281 * 2 ^ 59
def prefixEnd_3735281 : Nat := 4983230072969 + 3 ^ 40 * 3735281 * 2
def baseEnd_3735281 : Nat := 1278663021737936953072841

theorem tailTrace_3735281 : CollatzResearch.WordTrace tailWord_3735281 prefixEnd_3735281 1278663021737936953072841 := by
  unfold tailWord_3735281
  simp only [CollatzResearch.WordTrace]
  refine ⟨136236890380722347051293697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90824593587148231367529131 136236890380722347051293697)
  ·
    refine ⟨102177667785541760288470273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136236890380722347051293697 102177667785541760288470273)
    ·
      refine ⟨76633250839156320216352705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102177667785541760288470273 76633250839156320216352705)
      ·
        refine ⟨57474938129367240162264529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76633250839156320216352705 57474938129367240162264529)
        ·
          refine ⟨43106203597025430121698397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57474938129367240162264529 43106203597025430121698397)
          ·
            refine ⟨16164826348884536295636899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43106203597025430121698397 16164826348884536295636899)
            ·
              refine ⟨24247239523326804443455349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16164826348884536295636899 24247239523326804443455349)
              ·
                refine ⟨2273178705311887916573939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24247239523326804443455349 2273178705311887916573939)
                ·
                  refine ⟨3409768057967831874860909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2273178705311887916573939 3409768057967831874860909)
                  ·
                    refine ⟨1278663021737936953072841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3409768057967831874860909 1278663021737936953072841)
                    ·
                      rfl

theorem cell22_3735281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 5, 1, 3].length) (baseStart_3735281 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3735281 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3735281 prefixEnd_3735281 := by exact prefixLift 3735281
  have htrace : WordTrace (prefixWord ++ tailWord_3735281) baseStart_3735281 baseEnd_3735281 := by
    simpa [prefixWord, tailWord_3735281, baseEnd_3735281] using wordTrace_append hprefix tailTrace_3735281
  have hstable : (prefixWord ++ tailWord_3735281).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3735281).length < 2 ^ (prefixWord ++ tailWord_3735281).sum := by decide
  have hdescent : baseEnd_3735281 < baseStart_3735281 := by decide
  rcases family_descends (prefixWord ++ tailWord_3735281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3735292 : List Nat := [2, 2, 2, 1, 3, 1, 1, 1, 4, 5]
def baseStart_3735292 : Nat := 118140960795 + 3735292 * 2 ^ 59
def prefixEnd_3735292 : Nat := 4983230072969 + 3 ^ 40 * 3735292 * 2
def baseEnd_3735292 : Nat := 1278666787262736591047807

theorem tailTrace_3735292 : CollatzResearch.WordTrace tailWord_3735292 prefixEnd_3735292 1278666787262736591047807 := by
  unfold tailWord_3735292
  simp only [CollatzResearch.WordTrace]
  refine ⟨68118645791841247964972065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90824861055788330619962753 68118645791841247964972065)
  ·
    refine ⟨51088984343880935973729049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68118645791841247964972065 51088984343880935973729049)
    ·
      refine ⟨38316738257910701980296787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51088984343880935973729049 38316738257910701980296787)
      ·
        refine ⟨57475107386866052970445181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38316738257910701980296787 57475107386866052970445181)
        ·
          refine ⟨21553165270074769863916943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57475107386866052970445181 21553165270074769863916943)
          ·
            refine ⟨32329747905112154795875415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21553165270074769863916943 32329747905112154795875415)
            ·
              refine ⟨48494621857668232193813123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32329747905112154795875415 48494621857668232193813123)
              ·
                refine ⟨72741932786502348290719685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48494621857668232193813123 72741932786502348290719685)
                ·
                  refine ⟨13639112397469190304509941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 72741932786502348290719685 13639112397469190304509941)
                  ·
                    refine ⟨1278666787262736591047807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13639112397469190304509941 1278666787262736591047807)
                    ·
                      rfl

theorem cell22_3735292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 1, 4, 5].length) (baseStart_3735292 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3735292 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3735292 prefixEnd_3735292 := by exact prefixLift 3735292
  have htrace : WordTrace (prefixWord ++ tailWord_3735292) baseStart_3735292 baseEnd_3735292 := by
    simpa [prefixWord, tailWord_3735292, baseEnd_3735292] using wordTrace_append hprefix tailTrace_3735292
  have hstable : (prefixWord ++ tailWord_3735292).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3735292).length < 2 ^ (prefixWord ++ tailWord_3735292).sum := by decide
  have hdescent : baseEnd_3735292 < baseStart_3735292 := by decide
  rcases family_descends (prefixWord ++ tailWord_3735292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3735298 : List Nat := [3, 4, 1, 1, 1, 1, 1, 6, 1, 3]
def baseStart_3735298 : Nat := 118140960795 + 3735298 * 2 ^ 59
def prefixEnd_3735298 : Nat := 4983230072969 + 3 ^ 40 * 3735298 * 2
def baseEnd_3735298 : Nat := 1278668841185354575397789

theorem tailTrace_3735298 : CollatzResearch.WordTrace tailWord_3735298 prefixEnd_3735298 1278668841185354575397789 := by
  unfold tailWord_3735298
  simp only [CollatzResearch.WordTrace]
  refine ⟨34059377605415189738665637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90825006947773839303108365 34059377605415189738665637)
  ·
    refine ⟨6386133301015348075999807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34059377605415189738665637 6386133301015348075999807)
    ·
      refine ⟨9579199951523022113999711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6386133301015348075999807 9579199951523022113999711)
      ·
        refine ⟨14368799927284533170999567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9579199951523022113999711 14368799927284533170999567)
        ·
          refine ⟨21553199890926799756499351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14368799927284533170999567 21553199890926799756499351)
          ·
            refine ⟨32329799836390199634749027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21553199890926799756499351 32329799836390199634749027)
            ·
              refine ⟨48494699754585299452123541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32329799836390199634749027 48494699754585299452123541)
              ·
                refine ⟨2273189050996185911818291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 48494699754585299452123541 2273189050996185911818291)
                ·
                  refine ⟨3409783576494278867727437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2273189050996185911818291 3409783576494278867727437)
                  ·
                    refine ⟨1278668841185354575397789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3409783576494278867727437 1278668841185354575397789)
                    ·
                      rfl

theorem cell22_3735298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 6, 1, 3].length) (baseStart_3735298 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3735298 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3735298 prefixEnd_3735298 := by exact prefixLift 3735298
  have htrace : WordTrace (prefixWord ++ tailWord_3735298) baseStart_3735298 baseEnd_3735298 := by
    simpa [prefixWord, tailWord_3735298, baseEnd_3735298] using wordTrace_append hprefix tailTrace_3735298
  have hstable : (prefixWord ++ tailWord_3735298).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3735298).length < 2 ^ (prefixWord ++ tailWord_3735298).sum := by decide
  have hdescent : baseEnd_3735298 < baseStart_3735298 := by decide
  rcases family_descends (prefixWord ++ tailWord_3735298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3735307 : List Nat := [1, 1, 1, 1, 5, 1, 2, 1, 5, 4]
def baseStart_3735307 : Nat := 118140960795 + 3735307 * 2 ^ 59
def prefixEnd_3735307 : Nat := 4983230072969 + 3 ^ 40 * 3735307 * 2
def baseEnd_3735307 : Nat := 1278671922069281551922761

theorem tailTrace_3735307 : CollatzResearch.WordTrace tailWord_3735307 prefixEnd_3735307 1278671922069281551922761 := by
  unfold tailWord_3735307
  simp only [CollatzResearch.WordTrace]
  refine ⟨136237838678628153491740175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90825225785752102327826783 136237838678628153491740175)
  ·
    refine ⟨204356758017942230237610263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136237838678628153491740175 204356758017942230237610263)
    ·
      refine ⟨306535137026913345356415395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204356758017942230237610263 306535137026913345356415395)
      ·
        refine ⟨459802705540370018034623093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 306535137026913345356415395 459802705540370018034623093)
        ·
          refine ⟨43106503644409689190745915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 459802705540370018034623093 43106503644409689190745915)
          ·
            refine ⟨64659755466614533786118873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43106503644409689190745915 64659755466614533786118873)
            ·
              refine ⟨48494816599960900339589155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64659755466614533786118873 48494816599960900339589155)
              ·
                refine ⟨72742224899941350509383733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48494816599960900339589155 72742224899941350509383733)
                ·
                  refine ⟨6819583584369501610254725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 72742224899941350509383733 6819583584369501610254725)
                  ·
                    refine ⟨1278671922069281551922761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6819583584369501610254725 1278671922069281551922761)
                    ·
                      rfl

theorem cell22_3735307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 1, 5, 4].length) (baseStart_3735307 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3735307 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3735307 prefixEnd_3735307 := by exact prefixLift 3735307
  have htrace : WordTrace (prefixWord ++ tailWord_3735307) baseStart_3735307 baseEnd_3735307 := by
    simpa [prefixWord, tailWord_3735307, baseEnd_3735307] using wordTrace_append hprefix tailTrace_3735307
  have hstable : (prefixWord ++ tailWord_3735307).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3735307).length < 2 ^ (prefixWord ++ tailWord_3735307).sum := by decide
  have hdescent : baseEnd_3735307 < baseStart_3735307 := by decide
  rcases family_descends (prefixWord ++ tailWord_3735307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3735367 : List Nat := [1, 1, 4, 1, 2, 1, 3, 9]
def baseStart_3735367 : Nat := 118140960795 + 3735367 * 2 ^ 59
def prefixEnd_3735367 : Nat := 4983230072969 + 3 ^ 40 * 3735367 * 2
def baseEnd_3735367 : Nat := 142076940143940155046953

theorem tailTrace_3735367 : CollatzResearch.WordTrace tailWord_3735367 prefixEnd_3735367 142076940143940155046953 := by
  unfold tailWord_3735367
  simp only [CollatzResearch.WordTrace]
  refine ⟨136240027058410783738924355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90826684705607189159282903 136240027058410783738924355)
  ·
    refine ⟨204360040587616175608386533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136240027058410783738924355 204360040587616175608386533)
    ·
      refine ⟨38317507610178032926572475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 204360040587616175608386533 38317507610178032926572475)
      ·
        refine ⟨57476261415267049389858713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38317507610178032926572475 57476261415267049389858713)
        ·
          refine ⟨43107196061450287042394035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57476261415267049389858713 43107196061450287042394035)
          ·
            refine ⟨64660794092175430563591053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43107196061450287042394035 64660794092175430563591053)
            ·
              refine ⟨24247797784565786461346645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64660794092175430563591053 24247797784565786461346645)
              ·
                refine ⟨142076940143940155046953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 24247797784565786461346645 142076940143940155046953)
                ·
                  rfl

theorem cell22_3735367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 9].length) (baseStart_3735367 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3735367 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3735367 prefixEnd_3735367 := by exact prefixLift 3735367
  have htrace : WordTrace (prefixWord ++ tailWord_3735367) baseStart_3735367 baseEnd_3735367 := by
    simpa [prefixWord, tailWord_3735367, baseEnd_3735367] using wordTrace_append hprefix tailTrace_3735367
  have hstable : (prefixWord ++ tailWord_3735367).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3735367).length < 2 ^ (prefixWord ++ tailWord_3735367).sum := by decide
  have hdescent : baseEnd_3735367 < baseStart_3735367 := by decide
  rcases family_descends (prefixWord ++ tailWord_3735367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3735429 : List Nat := [1, 3, 1, 1, 3, 2, 1, 5, 5]
def baseStart_3735429 : Nat := 118140960795 + 3735429 * 2 ^ 59
def prefixEnd_3735429 : Nat := 4983230072969 + 3 ^ 40 * 3735429 * 2
def baseEnd_3735429 : Nat := 426237895054171300124129

theorem tailTrace_3735429 : CollatzResearch.WordTrace tailWord_3735429 prefixEnd_3735429 426237895054171300124129 := by
  unfold tailWord_3735429
  simp only [CollatzResearch.WordTrace]
  refine ⟨136242288384186168327681341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90828192256124112218454227 136242288384186168327681341)
  ·
    refine ⟨51090858144069813122880503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136242288384186168327681341 51090858144069813122880503)
    ·
      refine ⟨76636287216104719684320755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51090858144069813122880503 76636287216104719684320755)
      ·
        refine ⟨114954430824157079526481133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76636287216104719684320755 114954430824157079526481133)
        ·
          refine ⟨43107911559058904822430425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 114954430824157079526481133 43107911559058904822430425)
          ·
            refine ⟨32330933669294178616822819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43107911559058904822430425 32330933669294178616822819)
            ·
              refine ⟨48496400503941267925234229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32330933669294178616822819 48496400503941267925234229)
              ·
                refine ⟨4546537547244493867990709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 48496400503941267925234229 4546537547244493867990709)
                ·
                  refine ⟨426237895054171300124129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4546537547244493867990709 426237895054171300124129)
                  ·
                    rfl

theorem cell22_3735429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 5, 5].length) (baseStart_3735429 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3735429 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3735429 prefixEnd_3735429 := by exact prefixLift 3735429
  have htrace : WordTrace (prefixWord ++ tailWord_3735429) baseStart_3735429 baseEnd_3735429 := by
    simpa [prefixWord, tailWord_3735429, baseEnd_3735429] using wordTrace_append hprefix tailTrace_3735429
  have hstable : (prefixWord ++ tailWord_3735429).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3735429).length < 2 ^ (prefixWord ++ tailWord_3735429).sum := by decide
  have hdescent : baseEnd_3735429 < baseStart_3735429 := by decide
  rcases family_descends (prefixWord ++ tailWord_3735429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3735450 : List Nat := [3, 1, 1, 4, 2, 2, 2, 3, 1, 3]
def baseStart_3735450 : Nat := 118140960795 + 3735450 * 2 ^ 59
def prefixEnd_3735450 : Nat := 4983230072969 + 3 ^ 40 * 3735450 * 2
def baseEnd_3735450 : Nat := 1278720873891676845597323

theorem tailTrace_3735450 : CollatzResearch.WordTrace tailWord_3735450 prefixEnd_3735450 1278720873891676845597323 := by
  unfold tailWord_3735450
  simp only [CollatzResearch.WordTrace]
  refine ⟨34060763579277522228548951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90828702878073392609463869 34060763579277522228548951)
  ·
    refine ⟨51091145368916283342823427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34060763579277522228548951 51091145368916283342823427)
    ·
      refine ⟨76636718053374425014235141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51091145368916283342823427 76636718053374425014235141)
      ·
        refine ⟨14369384635007704690169089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 76636718053374425014235141 14369384635007704690169089)
        ·
          refine ⟨10777038476255778517626817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14369384635007704690169089 10777038476255778517626817)
          ·
            refine ⟨8082778857191833888220113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10777038476255778517626817 8082778857191833888220113)
            ·
              refine ⟨6062084142893875416165085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8082778857191833888220113 6062084142893875416165085)
              ·
                refine ⟨2273281553585203281061907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6062084142893875416165085 2273281553585203281061907)
                ·
                  refine ⟨3409922330377804921592861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2273281553585203281061907 3409922330377804921592861)
                  ·
                    refine ⟨1278720873891676845597323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3409922330377804921592861 1278720873891676845597323)
                    ·
                      rfl

theorem cell22_3735450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 2, 3, 1, 3].length) (baseStart_3735450 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3735450 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3735450 prefixEnd_3735450 := by exact prefixLift 3735450
  have htrace : WordTrace (prefixWord ++ tailWord_3735450) baseStart_3735450 baseEnd_3735450 := by
    simpa [prefixWord, tailWord_3735450, baseEnd_3735450] using wordTrace_append hprefix tailTrace_3735450
  have hstable : (prefixWord ++ tailWord_3735450).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3735450).length < 2 ^ (prefixWord ++ tailWord_3735450).sum := by decide
  have hdescent : baseEnd_3735450 < baseStart_3735450 := by decide
  rcases family_descends (prefixWord ++ tailWord_3735450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3735463 : List Nat := [1, 1, 6, 1, 2, 3, 1, 2, 5]
def baseStart_3735463 : Nat := 118140960795 + 3735463 * 2 ^ 59
def prefixEnd_3735463 : Nat := 4983230072969 + 3 ^ 40 * 3735463 * 2
def baseEnd_3735463 : Nat := 426241774685783048340761

theorem tailTrace_3735463 : CollatzResearch.WordTrace tailWord_3735463 prefixEnd_3735463 426241774685783048340761 := by
  unfold tailWord_3735463
  simp only [CollatzResearch.WordTrace]
  refine ⟨136243528466062992134419043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90829018977375328089612695 136243528466062992134419043)
  ·
    refine ⟨204365292699094488201628565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136243528466062992134419043 204365292699094488201628565)
    ·
      refine ⟨9579623095270054134451339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 204365292699094488201628565 9579623095270054134451339)
      ·
        refine ⟨14369434642905081201677009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9579623095270054134451339 14369434642905081201677009)
        ·
          refine ⟨10777075982178810901257757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14369434642905081201677009 10777075982178810901257757)
          ·
            refine ⟨4041403493317054087971659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10777075982178810901257757 4041403493317054087971659)
            ·
              refine ⟨6062105239975581131957489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4041403493317054087971659 6062105239975581131957489)
              ·
                refine ⟨4546578929981685848968117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6062105239975581131957489 4546578929981685848968117)
                ·
                  refine ⟨426241774685783048340761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4546578929981685848968117 426241774685783048340761)
                  ·
                    rfl

theorem cell22_3735463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 3, 1, 2, 5].length) (baseStart_3735463 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3735463 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3735463 prefixEnd_3735463 := by exact prefixLift 3735463
  have htrace : WordTrace (prefixWord ++ tailWord_3735463) baseStart_3735463 baseEnd_3735463 := by
    simpa [prefixWord, tailWord_3735463, baseEnd_3735463] using wordTrace_append hprefix tailTrace_3735463
  have hstable : (prefixWord ++ tailWord_3735463).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3735463).length < 2 ^ (prefixWord ++ tailWord_3735463).sum := by decide
  have hdescent : baseEnd_3735463 < baseStart_3735463 := by decide
  rcases family_descends (prefixWord ++ tailWord_3735463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3735504 : List Nat := [2, 1, 1, 1, 1, 2, 6, 1, 1, 6]
def baseStart_3735504 : Nat := 118140960795 + 3735504 * 2 ^ 59
def prefixEnd_3735504 : Nat := 4983230072969 + 3 ^ 40 * 3735504 * 2
def baseEnd_3735504 : Nat := 1278739359195238704747157

theorem tailTrace_3735504 : CollatzResearch.WordTrace tailWord_3735504 prefixEnd_3735504 1278739359195238704747157 := by
  unfold tailWord_3735504
  simp only [CollatzResearch.WordTrace]
  refine ⟨68122511929457228068330783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90830015905942970757774377 68122511929457228068330783)
  ·
    refine ⟨102183767894185842102496175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68122511929457228068330783 102183767894185842102496175)
    ·
      refine ⟨153275651841278763153744263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102183767894185842102496175 153275651841278763153744263)
      ·
        refine ⟨229913477761918144730616395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153275651841278763153744263 229913477761918144730616395)
        ·
          refine ⟨344870216642877217095924593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 229913477761918144730616395 344870216642877217095924593)
          ·
            refine ⟨258652662482157912821943445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 344870216642877217095924593 258652662482157912821943445)
            ·
              refine ⟨12124343553851152163528599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 258652662482157912821943445 12124343553851152163528599)
              ·
                refine ⟨18186515330776728245292899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12124343553851152163528599 18186515330776728245292899)
                ·
                  refine ⟨27279772996165092367939349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18186515330776728245292899 27279772996165092367939349)
                  ·
                    refine ⟨1278739359195238704747157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27279772996165092367939349 1278739359195238704747157)
                    ·
                      rfl

theorem cell22_3735504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 6, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 6, 1, 1, 6].length) (baseStart_3735504 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3735504 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3735504 prefixEnd_3735504 := by exact prefixLift 3735504
  have htrace : WordTrace (prefixWord ++ tailWord_3735504) baseStart_3735504 baseEnd_3735504 := by
    simpa [prefixWord, tailWord_3735504, baseEnd_3735504] using wordTrace_append hprefix tailTrace_3735504
  have hstable : (prefixWord ++ tailWord_3735504).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3735504).length < 2 ^ (prefixWord ++ tailWord_3735504).sum := by decide
  have hdescent : baseEnd_3735504 < baseStart_3735504 := by decide
  rcases family_descends (prefixWord ++ tailWord_3735504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3735519 : List Nat := [1, 1, 2, 3, 4, 1, 10]
def baseStart_3735519 : Nat := 118140960795 + 3735519 * 2 ^ 59
def prefixEnd_3735519 : Nat := 4983230072969 + 3 ^ 40 * 3735519 * 2
def baseEnd_3735519 : Nat := 47360907185251246874893

theorem tailTrace_3735519 : CollatzResearch.WordTrace tailWord_3735519 prefixEnd_3735519 47360907185251246874893 := by
  unfold tailWord_3735519
  simp only [CollatzResearch.WordTrace]
  refine ⟨136245570953860113698457611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90830380635906742465638407 136245570953860113698457611)
  ·
    refine ⟨204368356430790170547686417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136245570953860113698457611 204368356430790170547686417)
    ·
      refine ⟨153276267323092627910764813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 204368356430790170547686417 153276267323092627910764813)
      ·
        refine ⟨57478600246159735466536805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 153276267323092627910764813 57478600246159735466536805)
        ·
          refine ⟨10777237546154950399975651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57478600246159735466536805 10777237546154950399975651)
          ·
            refine ⟨16165856319232425599963477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10777237546154950399975651 16165856319232425599963477)
            ·
              refine ⟨47360907185251246874893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 16165856319232425599963477 47360907185251246874893)
              ·
                rfl

theorem cell22_3735519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 10].length) (baseStart_3735519 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3735519 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3735519 prefixEnd_3735519 := by exact prefixLift 3735519
  have htrace : WordTrace (prefixWord ++ tailWord_3735519) baseStart_3735519 baseEnd_3735519 := by
    simpa [prefixWord, tailWord_3735519, baseEnd_3735519] using wordTrace_append hprefix tailTrace_3735519
  have hstable : (prefixWord ++ tailWord_3735519).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3735519).length < 2 ^ (prefixWord ++ tailWord_3735519).sum := by decide
  have hdescent : baseEnd_3735519 < baseStart_3735519 := by decide
  rcases family_descends (prefixWord ++ tailWord_3735519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3735551 : List Nat := [1, 1, 2, 2, 1, 2, 1, 6, 3, 3]
def baseStart_3735551 : Nat := 118140960795 + 3735551 * 2 ^ 59
def prefixEnd_3735551 : Nat := 4983230072969 + 3 ^ 40 * 3735551 * 2
def baseEnd_3735551 : Nat := 1278755448255746248822013

theorem tailTrace_3735551 : CollatzResearch.WordTrace tailWord_3735551 prefixEnd_3735551 1278755448255746248822013 := by
  unfold tailWord_3735551
  simp only [CollatzResearch.WordTrace]
  refine ⟨136246738089744183163622507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90831158726496122109081671 136246738089744183163622507)
  ·
    refine ⟨204370107134616274745433761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136246738089744183163622507 204370107134616274745433761)
    ·
      refine ⟨153277580350962206059075321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 204370107134616274745433761 153277580350962206059075321)
      ·
        refine ⟨114958185263221654544306491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153277580350962206059075321 114958185263221654544306491)
        ·
          refine ⟨172437277894832481816459737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114958185263221654544306491 172437277894832481816459737)
          ·
            refine ⟨129327958421124361362344803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 172437277894832481816459737 129327958421124361362344803)
            ·
              refine ⟨193991937631686542043517205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129327958421124361362344803 193991937631686542043517205)
              ·
                refine ⟨9093372076485306658289869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 193991937631686542043517205 9093372076485306658289869)
                ·
                  refine ⟨3410014528681989996858701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9093372076485306658289869 3410014528681989996858701)
                  ·
                    refine ⟨1278755448255746248822013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3410014528681989996858701 1278755448255746248822013)
                    ·
                      rfl

theorem cell22_3735551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 6, 3, 3].length) (baseStart_3735551 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3735551 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3735551 prefixEnd_3735551 := by exact prefixLift 3735551
  have htrace : WordTrace (prefixWord ++ tailWord_3735551) baseStart_3735551 baseEnd_3735551 := by
    simpa [prefixWord, tailWord_3735551, baseEnd_3735551] using wordTrace_append hprefix tailTrace_3735551
  have hstable : (prefixWord ++ tailWord_3735551).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3735551).length < 2 ^ (prefixWord ++ tailWord_3735551).sum := by decide
  have hdescent : baseEnd_3735551 < baseStart_3735551 := by decide
  rcases family_descends (prefixWord ++ tailWord_3735551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3735598 : List Nat := [4, 1, 3, 1, 1, 2, 2, 3, 5]
def baseStart_3735598 : Nat := 118140960795 + 3735598 * 2 ^ 59
def prefixEnd_3735598 : Nat := 4983230072969 + 3 ^ 40 * 3735598 * 2
def baseEnd_3735598 : Nat := 426257179105417930965623

theorem tailTrace_3735598 : CollatzResearch.WordTrace tailWord_3735598 prefixEnd_3735598 426257179105417930965623 := by
  unfold tailWord_3735598
  simp only [CollatzResearch.WordTrace]
  refine ⟨17031056540071738773822931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 90832301547049273460388965 17031056540071738773822931)
  ·
    refine ⟨25546584810107608160734397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17031056540071738773822931 25546584810107608160734397)
    ·
      refine ⟨9579969303790353060275399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25546584810107608160734397 9579969303790353060275399)
      ·
        refine ⟨14369953955685529590413099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9579969303790353060275399 14369953955685529590413099)
        ·
          refine ⟨21554930933528294385619649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14369953955685529590413099 21554930933528294385619649)
          ·
            refine ⟨16166198200146220789214737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21554930933528294385619649 16166198200146220789214737)
            ·
              refine ⟨12124648650109665591911053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16166198200146220789214737 12124648650109665591911053)
              ·
                refine ⟨4546743243791124596966645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12124648650109665591911053 4546743243791124596966645)
                ·
                  refine ⟨426257179105417930965623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4546743243791124596966645 426257179105417930965623)
                  ·
                    rfl

theorem cell22_3735598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 2, 3, 5].length) (baseStart_3735598 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3735598 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3735598 prefixEnd_3735598 := by exact prefixLift 3735598
  have htrace : WordTrace (prefixWord ++ tailWord_3735598) baseStart_3735598 baseEnd_3735598 := by
    simpa [prefixWord, tailWord_3735598, baseEnd_3735598] using wordTrace_append hprefix tailTrace_3735598
  have hstable : (prefixWord ++ tailWord_3735598).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3735598).length < 2 ^ (prefixWord ++ tailWord_3735598).sum := by decide
  have hdescent : baseEnd_3735598 < baseStart_3735598 := by decide
  rcases family_descends (prefixWord ++ tailWord_3735598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3735671 : List Nat := [1, 1, 3, 1, 1, 6, 1, 8]
def baseStart_3735671 : Nat := 118140960795 + 3735671 * 2 ^ 59
def prefixEnd_3735671 : Nat := 4983230072969 + 3 ^ 40 * 3735671 * 2
def baseEnd_3735671 : Nat := 142088502967567326202405

theorem tailTrace_3735671 : CollatzResearch.WordTrace tailWord_3735671 prefixEnd_3735671 142088502967567326202405 := by
  unfold tailWord_3735671
  simp only [CollatzResearch.WordTrace]
  refine ⟨136251114849309443657990867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90834076566206295771993911 136251114849309443657990867)
  ·
    refine ⟨204376672273964165486986301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136251114849309443657990867 204376672273964165486986301)
    ·
      refine ⟨76641252102736562057619863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 204376672273964165486986301 76641252102736562057619863)
      ·
        refine ⟨114961878154104843086429795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76641252102736562057619863 114961878154104843086429795)
        ·
          refine ⟨172442817231157264629644693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114961878154104843086429795 172442817231157264629644693)
          ·
            refine ⟨8083257057710496779514595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 172442817231157264629644693 8083257057710496779514595)
            ·
              refine ⟨12124885586565745169271893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8083257057710496779514595 12124885586565745169271893)
              ·
                refine ⟨142088502967567326202405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12124885586565745169271893 142088502967567326202405)
                ·
                  rfl

theorem cell22_3735671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 1, 8].length) (baseStart_3735671 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3735671 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3735671 prefixEnd_3735671 := by exact prefixLift 3735671
  have htrace : WordTrace (prefixWord ++ tailWord_3735671) baseStart_3735671 baseEnd_3735671 := by
    simpa [prefixWord, tailWord_3735671, baseEnd_3735671] using wordTrace_append hprefix tailTrace_3735671
  have hstable : (prefixWord ++ tailWord_3735671).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3735671).length < 2 ^ (prefixWord ++ tailWord_3735671).sum := by decide
  have hdescent : baseEnd_3735671 < baseStart_3735671 := by decide
  rcases family_descends (prefixWord ++ tailWord_3735671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3735688 : List Nat := [2, 1, 3, 4, 1, 3, 8]
def baseStart_3735688 : Nat := 118140960795 + 3735688 * 2 ^ 59
def prefixEnd_3735688 : Nat := 4983230072969 + 3 ^ 40 * 3735688 * 2
def baseEnd_3735688 : Nat := 47363049857611983635059

theorem tailTrace_3735688 : CollatzResearch.WordTrace tailWord_3735688 prefixEnd_3735688 47363049857611983635059 := by
  unfold tailWord_3735688
  simp only [CollatzResearch.WordTrace]
  refine ⟨68125867445123927780679859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90834489926831903707573145 68125867445123927780679859)
  ·
    refine ⟨102188801167685891671019789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68125867445123927780679859 102188801167685891671019789)
    ·
      refine ⟨38320800437882209376632421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102188801167685891671019789 38320800437882209376632421)
      ·
        refine ⟨7185150082102914258118579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38320800437882209376632421 7185150082102914258118579)
        ·
          refine ⟨10777725123154371387177869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7185150082102914258118579 10777725123154371387177869)
          ·
            refine ⟨4041646921182889270191701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10777725123154371387177869 4041646921182889270191701)
            ·
              refine ⟨47363049857611983635059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4041646921182889270191701 47363049857611983635059)
              ·
                rfl

theorem cell22_3735688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 3, 8].length) (baseStart_3735688 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3735688 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3735688 prefixEnd_3735688 := by exact prefixLift 3735688
  have htrace : WordTrace (prefixWord ++ tailWord_3735688) baseStart_3735688 baseEnd_3735688 := by
    simpa [prefixWord, tailWord_3735688, baseEnd_3735688] using wordTrace_append hprefix tailTrace_3735688
  have hstable : (prefixWord ++ tailWord_3735688).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3735688).length < 2 ^ (prefixWord ++ tailWord_3735688).sum := by decide
  have hdescent : baseEnd_3735688 < baseStart_3735688 := by decide
  rcases family_descends (prefixWord ++ tailWord_3735688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3735701 : List Nat := [1, 3, 2, 1, 1, 1, 4, 1, 2, 6]
def baseStart_3735701 : Nat := 118140960795 + 3735701 * 2 ^ 59
def prefixEnd_3735701 : Nat := 4983230072969 + 3 ^ 40 * 3735701 * 2
def baseEnd_3735701 : Nat := 1278806796321195857571553

theorem tailTrace_3735701 : CollatzResearch.WordTrace tailWord_3735701 prefixEnd_3735701 1278806796321195857571553 := by
  unfold tailWord_3735701
  simp only [CollatzResearch.WordTrace]
  refine ⟨136252209039200758781582957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90834806026133839187721971 136252209039200758781582957)
  ·
    refine ⟨51094578389700284543093609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136252209039200758781582957 51094578389700284543093609)
    ·
      refine ⟨38320933792275213407320207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51094578389700284543093609 38320933792275213407320207)
      ·
        refine ⟨57481400688412820110980311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38320933792275213407320207 57481400688412820110980311)
        ·
          refine ⟨86222101032619230166470467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57481400688412820110980311 86222101032619230166470467)
          ·
            refine ⟨129333151548928845249705701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86222101032619230166470467 129333151548928845249705701)
            ·
              refine ⟨24249965915424158484319819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 129333151548928845249705701 24249965915424158484319819)
              ·
                refine ⟨36374948873136237726479729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24249965915424158484319819 36374948873136237726479729)
                ·
                  refine ⟨27281211654852178294859797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36374948873136237726479729 27281211654852178294859797)
                  ·
                    refine ⟨1278806796321195857571553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27281211654852178294859797 1278806796321195857571553)
                    ·
                      rfl

theorem cell22_3735701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 1, 2, 6].length) (baseStart_3735701 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3735701 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3735701 prefixEnd_3735701 := by exact prefixLift 3735701
  have htrace : WordTrace (prefixWord ++ tailWord_3735701) baseStart_3735701 baseEnd_3735701 := by
    simpa [prefixWord, tailWord_3735701, baseEnd_3735701] using wordTrace_append hprefix tailTrace_3735701
  have hstable : (prefixWord ++ tailWord_3735701).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3735701).length < 2 ^ (prefixWord ++ tailWord_3735701).sum := by decide
  have hdescent : baseEnd_3735701 < baseStart_3735701 := by decide
  rcases family_descends (prefixWord ++ tailWord_3735701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3735731 : List Nat := [1, 1, 1, 2, 3, 2, 1, 2, 4, 5]
def baseStart_3735731 : Nat := 118140960795 + 3735731 * 2 ^ 59
def prefixEnd_3735731 : Nat := 4983230072969 + 3 ^ 40 * 3735731 * 2
def baseEnd_3735731 : Nat := 1278817065934285779321461

theorem tailTrace_3735731 : CollatzResearch.WordTrace tailWord_3735731 prefixEnd_3735731 1278817065934285779321461 := by
  unfold tailWord_3735731
  simp only [CollatzResearch.WordTrace]
  refine ⟨136253303229092073905175047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90835535486061382603450031 136253303229092073905175047)
  ·
    refine ⟨204379954843638110857762571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136253303229092073905175047 204379954843638110857762571)
    ·
      refine ⟨306569932265457166286643857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204379954843638110857762571 306569932265457166286643857)
      ·
        refine ⟨229927449199092874714982893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 306569932265457166286643857 229927449199092874714982893)
        ·
          refine ⟨86222793449659828018118585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 229927449199092874714982893 86222793449659828018118585)
          ·
            refine ⟨64667095087244871013588939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86222793449659828018118585 64667095087244871013588939)
            ·
              refine ⟨97000642630867306520383409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64667095087244871013588939 97000642630867306520383409)
              ·
                refine ⟨72750481973150479890287557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 97000642630867306520383409 72750481973150479890287557)
                ·
                  refine ⟨13640715369965714979428917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 72750481973150479890287557 13640715369965714979428917)
                  ·
                    refine ⟨1278817065934285779321461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13640715369965714979428917 1278817065934285779321461)
                    ·
                      rfl

theorem cell22_3735731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 2, 4, 5].length) (baseStart_3735731 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3735731 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3735731 prefixEnd_3735731 := by exact prefixLift 3735731
  have htrace : WordTrace (prefixWord ++ tailWord_3735731) baseStart_3735731 baseEnd_3735731 := by
    simpa [prefixWord, tailWord_3735731, baseEnd_3735731] using wordTrace_append hprefix tailTrace_3735731
  have hstable : (prefixWord ++ tailWord_3735731).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3735731).length < 2 ^ (prefixWord ++ tailWord_3735731).sum := by decide
  have hdescent : baseEnd_3735731 < baseStart_3735731 := by decide
  rcases family_descends (prefixWord ++ tailWord_3735731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3735765 : List Nat := [1, 3, 2, 4, 2, 1, 1, 1, 2, 5]
def baseStart_3735765 : Nat := 118140960795 + 3735765 * 2 ^ 59
def prefixEnd_3735765 : Nat := 4983230072969 + 3 ^ 40 * 3735765 * 2
def baseEnd_3735765 : Nat := 1278828704829121023971357

theorem tailTrace_3735765 : CollatzResearch.WordTrace tailWord_3735765 prefixEnd_3735765 1278828704829121023971357 := by
  unfold tailWord_3735765
  simp only [CollatzResearch.WordTrace]
  refine ⟨136254543310968897711912749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90836362207312598474608499 136254543310968897711912749)
  ·
    refine ⟨51095453741613336641967281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136254543310968897711912749 51095453741613336641967281)
    ·
      refine ⟨38321590306210002481475461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51095453741613336641967281 38321590306210002481475461)
      ·
        refine ⟨7185298182414375465276649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38321590306210002481475461 7185298182414375465276649)
        ·
          refine ⟨5388973636810781598957487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7185298182414375465276649 5388973636810781598957487)
          ·
            refine ⟨8083460455216172398436231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5388973636810781598957487 8083460455216172398436231)
            ·
              refine ⟨12125190682824258597654347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8083460455216172398436231 12125190682824258597654347)
              ·
                refine ⟨18187786024236387896481521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12125190682824258597654347 18187786024236387896481521)
                ·
                  refine ⟨13640839518177290922361141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18187786024236387896481521 13640839518177290922361141)
                  ·
                    refine ⟨1278828704829121023971357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13640839518177290922361141 1278828704829121023971357)
                    ·
                      rfl

theorem cell22_3735765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 1, 1, 2, 5].length) (baseStart_3735765 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3735765 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3735765 prefixEnd_3735765 := by exact prefixLift 3735765
  have htrace : WordTrace (prefixWord ++ tailWord_3735765) baseStart_3735765 baseEnd_3735765 := by
    simpa [prefixWord, tailWord_3735765, baseEnd_3735765] using wordTrace_append hprefix tailTrace_3735765
  have hstable : (prefixWord ++ tailWord_3735765).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3735765).length < 2 ^ (prefixWord ++ tailWord_3735765).sum := by decide
  have hdescent : baseEnd_3735765 < baseStart_3735765 := by decide
  rcases family_descends (prefixWord ++ tailWord_3735765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3735793 : List Nat := [1, 2, 2, 2, 2, 1, 4, 2, 1, 5]
def baseStart_3735793 : Nat := 118140960795 + 3735793 * 2 ^ 59
def prefixEnd_3735793 : Nat := 4983230072969 + 3 ^ 40 * 3735793 * 2
def baseEnd_3735793 : Nat := 1278838289801338284271271

theorem tailTrace_3735793 : CollatzResearch.WordTrace tailWord_3735793 prefixEnd_3735793 1278838289801338284271271 := by
  unfold tailWord_3735793
  simp only [CollatzResearch.WordTrace]
  refine ⟨136255564554867458493932033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90837043036578305662621355 136255564554867458493932033)
  ·
    refine ⟨102191673416150593870449025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136255564554867458493932033 102191673416150593870449025)
    ·
      refine ⟨76643755062112945402836769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102191673416150593870449025 76643755062112945402836769)
      ·
        refine ⟨57482816296584709052127577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76643755062112945402836769 57482816296584709052127577)
        ·
          refine ⟨43112112222438531789095683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57482816296584709052127577 43112112222438531789095683)
          ·
            refine ⟨64668168333657797683643525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43112112222438531789095683 64668168333657797683643525)
            ·
              refine ⟨12125281562560837065683161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64668168333657797683643525 12125281562560837065683161)
              ·
                refine ⟨9093961171920627799262371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12125281562560837065683161 9093961171920627799262371)
                ·
                  refine ⟨13640941757880941698893557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9093961171920627799262371 13640941757880941698893557)
                  ·
                    refine ⟨1278838289801338284271271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13640941757880941698893557 1278838289801338284271271)
                    ·
                      rfl

theorem cell22_3735793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 4, 2, 1, 5].length) (baseStart_3735793 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3735793 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3735793 prefixEnd_3735793 := by exact prefixLift 3735793
  have htrace : WordTrace (prefixWord ++ tailWord_3735793) baseStart_3735793 baseEnd_3735793 := by
    simpa [prefixWord, tailWord_3735793, baseEnd_3735793] using wordTrace_append hprefix tailTrace_3735793
  have hstable : (prefixWord ++ tailWord_3735793).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3735793).length < 2 ^ (prefixWord ++ tailWord_3735793).sum := by decide
  have hdescent : baseEnd_3735793 < baseStart_3735793 := by decide
  rcases family_descends (prefixWord ++ tailWord_3735793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3735795 : List Nat := [1, 1, 1, 2, 2, 4, 4, 3, 4]
def baseStart_3735795 : Nat := 118140960795 + 3735795 * 2 ^ 59
def prefixEnd_3735795 : Nat := 4983230072969 + 3 ^ 40 * 3735795 * 2
def baseEnd_3735795 : Nat := 426279658147403648573755

theorem tailTrace_3735795 : CollatzResearch.WordTrace tailWord_3735795 prefixEnd_3735795 426279658147403648573755 := by
  unfold tailWord_3735795
  simp only [CollatzResearch.WordTrace]
  refine ⟨136255637500860212835504839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90837091667240141890336559 136255637500860212835504839)
  ·
    refine ⟨204383456251290319253257259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136255637500860212835504839 204383456251290319253257259)
    ·
      refine ⟨306575184376935478879885889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204383456251290319253257259 306575184376935478879885889)
      ·
        refine ⟨229931388282701609159914417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 306575184376935478879885889 229931388282701609159914417)
        ·
          refine ⟨172448541212026206869935813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 229931388282701609159914417 172448541212026206869935813)
          ·
            refine ⟨32334101477254913788112965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 172448541212026206869935813 32334101477254913788112965)
            ·
              refine ⟨6062644026985296335271181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32334101477254913788112965 6062644026985296335271181)
              ·
                refine ⟨2273491510119486125726693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6062644026985296335271181 2273491510119486125726693)
                ·
                  refine ⟨426279658147403648573755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2273491510119486125726693 426279658147403648573755)
                  ·
                    rfl

theorem cell22_3735795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 4, 3, 4].length) (baseStart_3735795 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3735795 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3735795 prefixEnd_3735795 := by exact prefixLift 3735795
  have htrace : WordTrace (prefixWord ++ tailWord_3735795) baseStart_3735795 baseEnd_3735795 := by
    simpa [prefixWord, tailWord_3735795, baseEnd_3735795] using wordTrace_append hprefix tailTrace_3735795
  have hstable : (prefixWord ++ tailWord_3735795).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3735795).length < 2 ^ (prefixWord ++ tailWord_3735795).sum := by decide
  have hdescent : baseEnd_3735795 < baseStart_3735795 := by decide
  rcases family_descends (prefixWord ++ tailWord_3735795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3735808 : List Nat := [2, 1, 1, 2, 1, 1, 4, 4, 2, 4]
def baseStart_3735808 : Nat := 118140960795 + 3735808 * 2 ^ 59
def prefixEnd_3735808 : Nat := 4983230072969 + 3 ^ 40 * 3735808 * 2
def baseEnd_3735808 : Nat := 1278843424607883245146225

theorem tailTrace_3735808 : CollatzResearch.WordTrace tailWord_3735808 prefixEnd_3735808 1278843424607883245146225 := by
  unfold tailWord_3735808
  simp only [CollatzResearch.WordTrace]
  refine ⟨68128055824906558027864039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90837407766542077370485385 68128055824906558027864039)
  ·
    refine ⟨102192083737359837041796059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68128055824906558027864039 102192083737359837041796059)
    ·
      refine ⟨153288125606039755562694089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102192083737359837041796059 153288125606039755562694089)
      ·
        refine ⟨114966094204529816672020567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153288125606039755562694089 114966094204529816672020567)
        ·
          refine ⟨172449141306794725008030851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114966094204529816672020567 172449141306794725008030851)
          ·
            refine ⟨258673711960192087512046277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 172449141306794725008030851 258673711960192087512046277)
            ·
              refine ⟨48501320992536016408508677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 258673711960192087512046277 48501320992536016408508677)
              ·
                refine ⟨9093997686100503076595377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48501320992536016408508677 9093997686100503076595377)
                ·
                  refine ⟨6820498264575377307446533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9093997686100503076595377 6820498264575377307446533)
                  ·
                    refine ⟨1278843424607883245146225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6820498264575377307446533 1278843424607883245146225)
                    ·
                      rfl

theorem cell22_3735808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 4, 2, 4].length) (baseStart_3735808 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3735808 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3735808 prefixEnd_3735808 := by exact prefixLift 3735808
  have htrace : WordTrace (prefixWord ++ tailWord_3735808) baseStart_3735808 baseEnd_3735808 := by
    simpa [prefixWord, tailWord_3735808, baseEnd_3735808] using wordTrace_append hprefix tailTrace_3735808
  have hstable : (prefixWord ++ tailWord_3735808).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3735808).length < 2 ^ (prefixWord ++ tailWord_3735808).sum := by decide
  have hdescent : baseEnd_3735808 < baseStart_3735808 := by decide
  rcases family_descends (prefixWord ++ tailWord_3735808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3735840 : List Nat := [2, 1, 1, 5, 2, 1, 4, 6]
def baseStart_3735840 : Nat := 118140960795 + 3735840 * 2 ^ 59
def prefixEnd_3735840 : Nat := 4983230072969 + 3 ^ 40 * 3735840 * 2
def baseEnd_3735840 : Nat := 142094930984649536482903

theorem tailTrace_3735840 : CollatzResearch.WordTrace tailWord_3735840 prefixEnd_3735840 142094930984649536482903 := by
  unfold tailWord_3735840
  simp only [CollatzResearch.WordTrace]
  refine ⟨68128639392848592760446487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90838185857131457013928649 68128639392848592760446487)
  ·
    refine ⟨102192959089272889140669731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68128639392848592760446487 102192959089272889140669731)
    ·
      refine ⟨153289438633909333711004597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102192959089272889140669731 153289438633909333711004597)
      ·
        refine ⟨14370884871929000035406681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 153289438633909333711004597 14370884871929000035406681)
        ·
          refine ⟨10778163653946750026555011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14370884871929000035406681 10778163653946750026555011)
          ·
            refine ⟨16167245480920125039832517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10778163653946750026555011 16167245480920125039832517)
            ·
              refine ⟨3031358527672523444968597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16167245480920125039832517 3031358527672523444968597)
              ·
                refine ⟨142094930984649536482903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3031358527672523444968597 142094930984649536482903)
                ·
                  rfl

theorem cell22_3735840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 4, 6].length) (baseStart_3735840 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3735840 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3735840 prefixEnd_3735840 := by exact prefixLift 3735840
  have htrace : WordTrace (prefixWord ++ tailWord_3735840) baseStart_3735840 baseEnd_3735840 := by
    simpa [prefixWord, tailWord_3735840, baseEnd_3735840] using wordTrace_append hprefix tailTrace_3735840
  have hstable : (prefixWord ++ tailWord_3735840).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3735840).length < 2 ^ (prefixWord ++ tailWord_3735840).sum := by decide
  have hdescent : baseEnd_3735840 < baseStart_3735840 := by decide
  rcases family_descends (prefixWord ++ tailWord_3735840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3735868 : List Nat := [2, 2, 2, 2, 1, 2, 1, 3, 7]
def baseStart_3735868 : Nat := 118140960795 + 3735868 * 2 ^ 59
def prefixEnd_3735868 : Nat := 4983230072969 + 3 ^ 40 * 3735868 * 2
def baseEnd_3735868 : Nat := 426287987944687696215347

theorem tailTrace_3735868 : CollatzResearch.WordTrace tailWord_3735868 prefixEnd_3735868 426287987944687696215347 := by
  unfold tailWord_3735868
  simp only [CollatzResearch.WordTrace]
  refine ⟨68129150014797873151456129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90838866686397164201941505 68129150014797873151456129)
  ·
    refine ⟨51096862511098404863592097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68129150014797873151456129 51096862511098404863592097)
    ·
      refine ⟨38322646883323803647694073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51096862511098404863592097 38322646883323803647694073)
      ·
        refine ⟨28741985162492852735770555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38322646883323803647694073 28741985162492852735770555)
        ·
          refine ⟨43112977743739279103655833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28741985162492852735770555 43112977743739279103655833)
          ·
            refine ⟨32334733307804459327741875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43112977743739279103655833 32334733307804459327741875)
            ·
              refine ⟨48502099961706688991612813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32334733307804459327741875 48502099961706688991612813)
              ·
                refine ⟨18188287485640008371854805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48502099961706688991612813 18188287485640008371854805)
                ·
                  refine ⟨426287987944687696215347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18188287485640008371854805 426287987944687696215347)
                  ·
                    rfl

theorem cell22_3735868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 3, 7].length) (baseStart_3735868 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3735868 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3735868 prefixEnd_3735868 := by exact prefixLift 3735868
  have htrace : WordTrace (prefixWord ++ tailWord_3735868) baseStart_3735868 baseEnd_3735868 := by
    simpa [prefixWord, tailWord_3735868, baseEnd_3735868] using wordTrace_append hprefix tailTrace_3735868
  have hstable : (prefixWord ++ tailWord_3735868).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3735868).length < 2 ^ (prefixWord ++ tailWord_3735868).sum := by decide
  have hdescent : baseEnd_3735868 < baseStart_3735868 := by decide
  rcases family_descends (prefixWord ++ tailWord_3735868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3735945 : List Nat := [1, 2, 1, 1, 6, 1, 1, 3, 1, 5]
def baseStart_3735945 : Nat := 118140960795 + 3735945 * 2 ^ 59
def prefixEnd_3735945 : Nat := 4983230072969 + 3 ^ 40 * 3735945 * 2
def baseEnd_3735945 : Nat := 1278890322507660554470805

theorem tailTrace_3735945 : CollatzResearch.WordTrace tailWord_3735945 prefixEnd_3735945 1278890322507660554470805 := by
  unfold tailWord_3735945
  simp only [CollatzResearch.WordTrace]
  refine ⟨136261108450316788453465289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90840738966877858968976859 136261108450316788453465289)
  ·
    refine ⟨102195831337737591340098967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136261108450316788453465289 102195831337737591340098967)
    ·
      refine ⟨153293747006606387010148451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102195831337737591340098967 153293747006606387010148451)
      ·
        refine ⟨229940620509909580515222677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153293747006606387010148451 229940620509909580515222677)
        ·
          refine ⟨10778466586402011586651063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 229940620509909580515222677 10778466586402011586651063)
          ·
            refine ⟨16167699879603017379976595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10778466586402011586651063 16167699879603017379976595)
            ·
              refine ⟨24251549819404526069964893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16167699879603017379976595 24251549819404526069964893)
              ·
                refine ⟨9094331182276697276236835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24251549819404526069964893 9094331182276697276236835)
                ·
                  refine ⟨13641496773415045914355253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9094331182276697276236835 13641496773415045914355253)
                  ·
                    refine ⟨1278890322507660554470805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13641496773415045914355253 1278890322507660554470805)
                    ·
                      rfl

theorem cell22_3735945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 3, 1, 5].length) (baseStart_3735945 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3735945 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3735945 prefixEnd_3735945 := by exact prefixLift 3735945
  have htrace : WordTrace (prefixWord ++ tailWord_3735945) baseStart_3735945 baseEnd_3735945 := by
    simpa [prefixWord, tailWord_3735945, baseEnd_3735945] using wordTrace_append hprefix tailTrace_3735945
  have hstable : (prefixWord ++ tailWord_3735945).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3735945).length < 2 ^ (prefixWord ++ tailWord_3735945).sum := by decide
  have hdescent : baseEnd_3735945 < baseStart_3735945 := by decide
  rcases family_descends (prefixWord ++ tailWord_3735945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3735966 : List Nat := [4, 3, 1, 2, 1, 1, 4, 1, 1, 4]
def baseStart_3735966 : Nat := 118140960795 + 3735966 * 2 ^ 59
def prefixEnd_3735966 : Nat := 4983230072969 + 3 ^ 40 * 3735966 * 2
def baseEnd_3735966 : Nat := 1278897511236823499695741

theorem tailTrace_3735966 : CollatzResearch.WordTrace tailWord_3735966 prefixEnd_3735966 1278897511236823499695741 := by
  unfold tailWord_3735966
  simp only [CollatzResearch.WordTrace]
  refine ⟨17032734297905088629997469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 90841249588827139359986501 17032734297905088629997469)
  ·
    refine ⟨6387275361714408236249051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17032734297905088629997469 6387275361714408236249051)
    ·
      refine ⟨9580913042571612354373577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6387275361714408236249051 9580913042571612354373577)
      ·
        refine ⟨7185684781928709265780183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9580913042571612354373577 7185684781928709265780183)
        ·
          refine ⟨10778527172893063898670275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7185684781928709265780183 10778527172893063898670275)
          ·
            refine ⟨16167790759339595848005413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10778527172893063898670275 16167790759339595848005413)
            ·
              refine ⟨3031460767376174221501015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16167790759339595848005413 3031460767376174221501015)
              ·
                refine ⟨4547191151064261332251523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3031460767376174221501015 4547191151064261332251523)
                ·
                  refine ⟨6820786726596391998377285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4547191151064261332251523 6820786726596391998377285)
                  ·
                    refine ⟨1278897511236823499695741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6820786726596391998377285 1278897511236823499695741)
                    ·
                      rfl

theorem cell22_3735966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 4, 1, 1, 4].length) (baseStart_3735966 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3735966 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3735966 prefixEnd_3735966 := by exact prefixLift 3735966
  have htrace : WordTrace (prefixWord ++ tailWord_3735966) baseStart_3735966 baseEnd_3735966 := by
    simpa [prefixWord, tailWord_3735966, baseEnd_3735966] using wordTrace_append hprefix tailTrace_3735966
  have hstable : (prefixWord ++ tailWord_3735966).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3735966).length < 2 ^ (prefixWord ++ tailWord_3735966).sum := by decide
  have hdescent : baseEnd_3735966 < baseStart_3735966 := by decide
  rcases family_descends (prefixWord ++ tailWord_3735966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3735975 : List Nat := [1, 1, 6, 1, 1, 3, 9]
def baseStart_3735975 : Nat := 118140960795 + 3735975 * 2 ^ 59
def prefixEnd_3735975 : Nat := 4983230072969 + 3 ^ 40 * 3735975 * 2
def baseEnd_3735975 : Nat := 47366688597064832452619

theorem tailTrace_3735975 : CollatzResearch.WordTrace tailWord_3735975 prefixEnd_3735975 47366688597064832452619 := by
  unfold tailWord_3735975
  simp only [CollatzResearch.WordTrace]
  refine ⟨136262202640208103577057379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90841468426805402384704919 136262202640208103577057379)
  ·
    refine ⟨204393303960312155365586069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136262202640208103577057379 204393303960312155365586069)
    ·
      refine ⟨9580936123139632282761847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 204393303960312155365586069 9580936123139632282761847)
      ·
        refine ⟨14371404184709448424142771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9580936123139632282761847 14371404184709448424142771)
        ·
          refine ⟨21557106277064172636214157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14371404184709448424142771 21557106277064172636214157)
          ·
            refine ⟨8083914853899064738580309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21557106277064172636214157 8083914853899064738580309)
            ·
              refine ⟨47366688597064832452619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8083914853899064738580309 47366688597064832452619)
              ·
                rfl

theorem cell22_3735975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 9].length) (baseStart_3735975 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3735975 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3735975 prefixEnd_3735975 := by exact prefixLift 3735975
  have htrace : WordTrace (prefixWord ++ tailWord_3735975) baseStart_3735975 baseEnd_3735975 := by
    simpa [prefixWord, tailWord_3735975, baseEnd_3735975] using wordTrace_append hprefix tailTrace_3735975
  have hstable : (prefixWord ++ tailWord_3735975).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3735975).length < 2 ^ (prefixWord ++ tailWord_3735975).sum := by decide
  have hdescent : baseEnd_3735975 < baseStart_3735975 := by decide
  rcases family_descends (prefixWord ++ tailWord_3735975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3735996 : List Nat := [2, 2, 2, 4, 1, 2, 3, 1, 2, 3]
def baseStart_3735996 : Nat := 118140960795 + 3735996 * 2 ^ 59
def prefixEnd_3735996 : Nat := 4983230072969 + 3 ^ 40 * 3735996 * 2
def baseEnd_3735996 : Nat := 1278907780849913421445649

theorem tailTrace_3735996 : CollatzResearch.WordTrace tailWord_3735996 prefixEnd_3735996 1278907780849913421445649 := by
  unfold tailWord_3735996
  simp only [CollatzResearch.WordTrace]
  refine ⟨68131484286566012081785921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90841979048754682775714561 68131484286566012081785921)
  ·
    refine ⟨51098613214924509061339441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68131484286566012081785921 51098613214924509061339441)
    ·
      refine ⟨38323959911193381796004581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51098613214924509061339441 38323959911193381796004581)
      ·
        refine ⟨7185742483348759086750859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38323959911193381796004581 7185742483348759086750859)
        ·
          refine ⟨10778613725023138630126289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7185742483348759086750859 10778613725023138630126289)
          ·
            refine ⟨8083960293767353972594717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10778613725023138630126289 8083960293767353972594717)
            ·
              refine ⟨3031485110162757739723019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8083960293767353972594717 3031485110162757739723019)
              ·
                refine ⟨4547227665244136609584529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3031485110162757739723019 4547227665244136609584529)
                ·
                  refine ⟨3410420748933102457188397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4547227665244136609584529 3410420748933102457188397)
                  ·
                    refine ⟨1278907780849913421445649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3410420748933102457188397 1278907780849913421445649)
                    ·
                      rfl

theorem cell22_3735996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 3, 1, 2, 3].length) (baseStart_3735996 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3735996 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3735996 prefixEnd_3735996 := by exact prefixLift 3735996
  have htrace : WordTrace (prefixWord ++ tailWord_3735996) baseStart_3735996 baseEnd_3735996 := by
    simpa [prefixWord, tailWord_3735996, baseEnd_3735996] using wordTrace_append hprefix tailTrace_3735996
  have hstable : (prefixWord ++ tailWord_3735996).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3735996).length < 2 ^ (prefixWord ++ tailWord_3735996).sum := by decide
  have hdescent : baseEnd_3735996 < baseStart_3735996 := by decide
  rcases family_descends (prefixWord ++ tailWord_3735996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3736007 : List Nat := [1, 1, 4, 1, 1, 4, 2, 2, 3, 3]
def baseStart_3736007 : Nat := 118140960795 + 3736007 * 2 ^ 59
def prefixEnd_3736007 : Nat := 4983230072969 + 3 ^ 40 * 3736007 * 2
def baseEnd_3736007 : Nat := 1278911546374713059420615

theorem tailTrace_3736007 : CollatzResearch.WordTrace tailWord_3736007 prefixEnd_3736007 1278911546374713059420615 := by
  unfold tailWord_3736007
  simp only [CollatzResearch.WordTrace]
  refine ⟨136263369776092173042222275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90842246517394782028148183 136263369776092173042222275)
  ·
    refine ⟨204395054664138259563333413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136263369776092173042222275 204395054664138259563333413)
    ·
      refine ⟨38324072749525923668125015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 204395054664138259563333413 38324072749525923668125015)
      ·
        refine ⟨57486109124288885502187523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38324072749525923668125015 57486109124288885502187523)
        ·
          refine ⟨86229163686433328253281285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57486109124288885502187523 86229163686433328253281285)
          ·
            refine ⟨16167968191206249047490241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 86229163686433328253281285 16167968191206249047490241)
            ·
              refine ⟨12125976143404686785617681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16167968191206249047490241 12125976143404686785617681)
              ·
                refine ⟨9094482107553515089213261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12125976143404686785617681 9094482107553515089213261)
                ·
                  refine ⟨3410430790332568158454973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9094482107553515089213261 3410430790332568158454973)
                  ·
                    refine ⟨1278911546374713059420615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3410430790332568158454973 1278911546374713059420615)
                    ·
                      rfl

theorem cell22_3736007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 2, 2, 3, 3].length) (baseStart_3736007 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3736007 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3736007 prefixEnd_3736007 := by exact prefixLift 3736007
  have htrace : WordTrace (prefixWord ++ tailWord_3736007) baseStart_3736007 baseEnd_3736007 := by
    simpa [prefixWord, tailWord_3736007, baseEnd_3736007] using wordTrace_append hprefix tailTrace_3736007
  have hstable : (prefixWord ++ tailWord_3736007).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3736007).length < 2 ^ (prefixWord ++ tailWord_3736007).sum := by decide
  have hdescent : baseEnd_3736007 < baseStart_3736007 := by decide
  rcases family_descends (prefixWord ++ tailWord_3736007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3736095 : List Nat := [1, 1, 2, 4, 1, 1, 1, 2, 3, 6]
def baseStart_3736095 : Nat := 118140960795 + 3736095 * 2 ^ 59
def prefixEnd_3736095 : Nat := 4983230072969 + 3 ^ 40 * 3736095 * 2
def baseEnd_3736095 : Nat := 1278941670573110163220345

theorem tailTrace_3736095 : CollatzResearch.WordTrace tailWord_3736095 prefixEnd_3736095 1278941670573110163220345 := by
  unfold tailWord_3736095
  simp only [CollatzResearch.WordTrace]
  refine ⟨136266579399773364071425739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90844386266515576047617159 136266579399773364071425739)
  ·
    refine ⟨204399869099660046107138609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136266579399773364071425739 204399869099660046107138609)
    ·
      refine ⟨153299901824745034580353957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 204399869099660046107138609 153299901824745034580353957)
      ·
        refine ⟨28743731592139693983816367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 153299901824745034580353957 28743731592139693983816367)
        ·
          refine ⟨43115597388209540975724551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28743731592139693983816367 43115597388209540975724551)
          ·
            refine ⟨64673396082314311463586827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43115597388209540975724551 64673396082314311463586827)
            ·
              refine ⟨97010094123471467195380241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64673396082314311463586827 97010094123471467195380241)
              ·
                refine ⟨72757570592603600396535181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 97010094123471467195380241 72757570592603600396535181)
                ·
                  refine ⟨27284088972226350148700693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 72757570592603600396535181 27284088972226350148700693)
                  ·
                    refine ⟨1278941670573110163220345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27284088972226350148700693 1278941670573110163220345)
                    ·
                      rfl

theorem cell22_3736095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 2, 3, 6].length) (baseStart_3736095 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3736095 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3736095 prefixEnd_3736095 := by exact prefixLift 3736095
  have htrace : WordTrace (prefixWord ++ tailWord_3736095) baseStart_3736095 baseEnd_3736095 := by
    simpa [prefixWord, tailWord_3736095, baseEnd_3736095] using wordTrace_append hprefix tailTrace_3736095
  have hstable : (prefixWord ++ tailWord_3736095).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3736095).length < 2 ^ (prefixWord ++ tailWord_3736095).sum := by decide
  have hdescent : baseEnd_3736095 < baseStart_3736095 := by decide
  rcases family_descends (prefixWord ++ tailWord_3736095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3736099 : List Nat := [1, 1, 1, 4, 4, 2, 1, 4, 4]
def baseStart_3736099 : Nat := 118140960795 + 3736099 * 2 ^ 59
def prefixEnd_3736099 : Nat := 4983230072969 + 3 ^ 40 * 3736099 * 2
def baseEnd_3736099 : Nat := 426314346618285162040111

theorem tailTrace_3736099 : CollatzResearch.WordTrace tailWord_3736099 prefixEnd_3736099 426314346618285162040111 := by
  unfold tailWord_3736099
  simp only [CollatzResearch.WordTrace]
  refine ⟨136266725291758872754571351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90844483527839248503047567 136266725291758872754571351)
  ·
    refine ⟨204400087937638309131857027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136266725291758872754571351 204400087937638309131857027)
    ·
      refine ⟨306600131906457463697785541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204400087937638309131857027 306600131906457463697785541)
      ·
        refine ⟨57487524732460774443334789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 306600131906457463697785541 57487524732460774443334789)
        ·
          refine ⟨10778910887336395208125273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57487524732460774443334789 10778910887336395208125273)
          ·
            refine ⟨8084183165502296406093955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10778910887336395208125273 8084183165502296406093955)
            ·
              refine ⟨12126274748253444609140933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8084183165502296406093955 12126274748253444609140933)
              ·
                refine ⟨2273676515297520864213925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12126274748253444609140933 2273676515297520864213925)
                ·
                  refine ⟨426314346618285162040111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2273676515297520864213925 426314346618285162040111)
                  ·
                    rfl

theorem cell22_3736099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 1, 4, 4].length) (baseStart_3736099 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3736099 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3736099 prefixEnd_3736099 := by exact prefixLift 3736099
  have htrace : WordTrace (prefixWord ++ tailWord_3736099) baseStart_3736099 baseEnd_3736099 := by
    simpa [prefixWord, tailWord_3736099, baseEnd_3736099] using wordTrace_append hprefix tailTrace_3736099
  have hstable : (prefixWord ++ tailWord_3736099).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3736099).length < 2 ^ (prefixWord ++ tailWord_3736099).sum := by decide
  have hdescent : baseEnd_3736099 < baseStart_3736099 := by decide
  rcases family_descends (prefixWord ++ tailWord_3736099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3736114 : List Nat := [3, 2, 1, 1, 2, 1, 4, 3, 2, 3]
def baseStart_3736114 : Nat := 118140960795 + 3736114 * 2 ^ 59
def prefixEnd_3736114 : Nat := 4983230072969 + 3 ^ 40 * 3736114 * 2
def baseEnd_3736114 : Nat := 1278948174661400446995287

theorem tailTrace_3736114 : CollatzResearch.WordTrace tailWord_3736114 prefixEnd_3736114 1278948174661400446995287 := by
  unfold tailWord_3736114
  simp only [CollatzResearch.WordTrace]
  refine ⟨34066818096676132579091849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90844848257803020210911597 34066818096676132579091849)
  ·
    refine ⟨25550113572507099434318887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34066818096676132579091849 25550113572507099434318887)
    ·
      refine ⟨38325170358760649151478331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25550113572507099434318887 38325170358760649151478331)
      ·
        refine ⟨57487755538140973727217497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38325170358760649151478331 57487755538140973727217497)
        ·
          refine ⟨43115816653605730295413123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57487755538140973727217497 43115816653605730295413123)
          ·
            refine ⟨64673724980408595443119685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43115816653605730295413123 64673724980408595443119685)
            ·
              refine ⟨12126323433826611645584941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64673724980408595443119685 12126323433826611645584941)
              ·
                refine ⟨4547371287684979367094353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12126323433826611645584941 4547371287684979367094353)
                ·
                  refine ⟨3410528465763734525320765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4547371287684979367094353 3410528465763734525320765)
                  ·
                    refine ⟨1278948174661400446995287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3410528465763734525320765 1278948174661400446995287)
                    ·
                      rfl

theorem cell22_3736114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 4, 3, 2, 3].length) (baseStart_3736114 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3736114 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3736114 prefixEnd_3736114 := by exact prefixLift 3736114
  have htrace : WordTrace (prefixWord ++ tailWord_3736114) baseStart_3736114 baseEnd_3736114 := by
    simpa [prefixWord, tailWord_3736114, baseEnd_3736114] using wordTrace_append hprefix tailTrace_3736114
  have hstable : (prefixWord ++ tailWord_3736114).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3736114).length < 2 ^ (prefixWord ++ tailWord_3736114).sum := by decide
  have hdescent : baseEnd_3736114 < baseStart_3736114 := by decide
  rcases family_descends (prefixWord ++ tailWord_3736114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3736116 : List Nat := [2, 5, 1, 3, 1, 1, 1, 2, 6]
def baseStart_3736116 : Nat := 118140960795 + 3736116 * 2 ^ 59
def prefixEnd_3736116 : Nat := 4983230072969 + 3 ^ 40 * 3736116 * 2
def baseEnd_3736116 : Nat := 426316286434091036148427

theorem tailTrace_3736116 : CollatzResearch.WordTrace tailWord_3736116 prefixEnd_3736116 426316286434091036148427 := by
  unfold tailWord_3736116
  simp only [CollatzResearch.WordTrace]
  refine ⟨68133672666348642328970101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90844896888464856438626801 68133672666348642328970101)
  ·
    refine ⟨6387531812470185218340947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 68133672666348642328970101 6387531812470185218340947)
    ·
      refine ⟨9581297718705277827511421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6387531812470185218340947 9581297718705277827511421)
      ·
        refine ⟨3592986644514479185316783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9581297718705277827511421 3592986644514479185316783)
        ·
          refine ⟨5389479966771718777975175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3592986644514479185316783 5389479966771718777975175)
          ·
            refine ⟨8084219950157578166962763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5389479966771718777975175 8084219950157578166962763)
            ·
              refine ⟨12126329925236367250444145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8084219950157578166962763 12126329925236367250444145)
              ·
                refine ⟨9094747443927275437833109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12126329925236367250444145 9094747443927275437833109)
                ·
                  refine ⟨426316286434091036148427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9094747443927275437833109 426316286434091036148427)
                  ·
                    rfl

theorem cell22_3736116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 1, 2, 6].length) (baseStart_3736116 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3736116 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3736116 prefixEnd_3736116 := by exact prefixLift 3736116
  have htrace : WordTrace (prefixWord ++ tailWord_3736116) baseStart_3736116 baseEnd_3736116 := by
    simpa [prefixWord, tailWord_3736116, baseEnd_3736116] using wordTrace_append hprefix tailTrace_3736116
  have hstable : (prefixWord ++ tailWord_3736116).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3736116).length < 2 ^ (prefixWord ++ tailWord_3736116).sum := by decide
  have hdescent : baseEnd_3736116 < baseStart_3736116 := by decide
  rcases family_descends (prefixWord ++ tailWord_3736116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3736127 : List Nat := [1, 1, 2, 2, 3, 2, 5, 6]
def baseStart_3736127 : Nat := 118140960795 + 3736127 * 2 ^ 59
def prefixEnd_3736127 : Nat := 4983230072969 + 3 ^ 40 * 3736127 * 2
def baseEnd_3736127 : Nat := 142105847203008082935583

theorem tailTrace_3736127 : CollatzResearch.WordTrace tailWord_3736127 prefixEnd_3736127 142105847203008082935583 := by
  unfold tailWord_3736127
  simp only [CollatzResearch.WordTrace]
  refine ⟨136267746535657433536590635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90845164357104955691060423 136267746535657433536590635)
  ·
    refine ⟨204401619803486150304885953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136267746535657433536590635 204401619803486150304885953)
    ·
      refine ⟨153301214852614612728664465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 204401619803486150304885953 153301214852614612728664465)
      ·
        refine ⟨114975911139460959546498349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153301214852614612728664465 114975911139460959546498349)
        ·
          refine ⟨43115966677297859829936881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 114975911139460959546498349 43115966677297859829936881)
          ·
            refine ⟨32336975007973394872452661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43115966677297859829936881 32336975007973394872452661)
            ·
              refine ⟨3031591406997505769292437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 32336975007973394872452661 3031591406997505769292437)
              ·
                refine ⟨142105847203008082935583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3031591406997505769292437 142105847203008082935583)
                ·
                  rfl

theorem cell22_3736127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 5, 6].length) (baseStart_3736127 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3736127 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3736127 prefixEnd_3736127 := by exact prefixLift 3736127
  have htrace : WordTrace (prefixWord ++ tailWord_3736127) baseStart_3736127 baseEnd_3736127 := by
    simpa [prefixWord, tailWord_3736127, baseEnd_3736127] using wordTrace_append hprefix tailTrace_3736127
  have hstable : (prefixWord ++ tailWord_3736127).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3736127).length < 2 ^ (prefixWord ++ tailWord_3736127).sum := by decide
  have hdescent : baseEnd_3736127 < baseStart_3736127 := by decide
  rcases family_descends (prefixWord ++ tailWord_3736127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3736129 : List Nat := [1, 2, 5, 1, 1, 2, 3, 1, 2, 4]
def baseStart_3736129 : Nat := 118140960795 + 3736129 * 2 ^ 59
def prefixEnd_3736129 : Nat := 4983230072969 + 3 ^ 40 * 3736129 * 2
def baseEnd_3736129 : Nat := 1278953309467945407870241

theorem tailTrace_3736129 : CollatzResearch.WordTrace tailWord_3736129 prefixEnd_3736129 1278953309467945407870241 := by
  unfold tailWord_3736129
  simp only [CollatzResearch.WordTrace]
  refine ⟨136267819481650187878163441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90845212987766791918775627 136267819481650187878163441)
  ·
    refine ⟨102200864611237640908622581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136267819481650187878163441 102200864611237640908622581)
    ·
      refine ⟨9581331057303528835183367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 102200864611237640908622581 9581331057303528835183367)
      ·
        refine ⟨14371996585955293252775051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9581331057303528835183367 14371996585955293252775051)
        ·
          refine ⟨21557994878932939879162577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14371996585955293252775051 21557994878932939879162577)
          ·
            refine ⟨16168496159199704909371933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21557994878932939879162577 16168496159199704909371933)
            ·
              refine ⟨6063186059699889341014475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16168496159199704909371933 6063186059699889341014475)
              ·
                refine ⟨9094779089549834011521713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6063186059699889341014475 9094779089549834011521713)
                ·
                  refine ⟨6821084317162375508641285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9094779089549834011521713 6821084317162375508641285)
                  ·
                    refine ⟨1278953309467945407870241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6821084317162375508641285 1278953309467945407870241)
                    ·
                      rfl

theorem cell22_3736129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 3, 1, 2, 4].length) (baseStart_3736129 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3736129 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3736129 prefixEnd_3736129 := by exact prefixLift 3736129
  have htrace : WordTrace (prefixWord ++ tailWord_3736129) baseStart_3736129 baseEnd_3736129 := by
    simpa [prefixWord, tailWord_3736129, baseEnd_3736129] using wordTrace_append hprefix tailTrace_3736129
  have hstable : (prefixWord ++ tailWord_3736129).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3736129).length < 2 ^ (prefixWord ++ tailWord_3736129).sum := by decide
  have hdescent : baseEnd_3736129 < baseStart_3736129 := by decide
  rcases family_descends (prefixWord ++ tailWord_3736129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
