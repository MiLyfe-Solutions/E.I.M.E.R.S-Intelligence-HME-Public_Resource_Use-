import V185TrunkScan22Chunk396

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_3541130 : List Nat := [3, 1, 2, 3, 1, 3, 1, 1, 3, 4]
def baseStart_3541130 : Nat := 118140960795 + 3541130 * 2 ^ 59
def prefixEnd_3541130 : Nat := 4983230072969 + 3 ^ 40 * 3541130 * 2
def baseEnd_3541130 : Nat := 1212201166703890364193097

theorem tailTrace_3541130 : CollatzResearch.WordTrace tailWord_3541130 prefixEnd_3541130 1212201166703890364193097 := by
  unfold tailWord_3541130
  simp only [CollatzResearch.WordTrace]
  refine ⟨32288905415274565425091211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86103747774065507800243229 32288905415274565425091211)
  ·
    refine ⟨48433358122911848137636817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32288905415274565425091211 48433358122911848137636817)
    ·
      refine ⟨36325018592183886103227613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48433358122911848137636817 36325018592183886103227613)
      ·
        refine ⟨13621881972068957288710355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36325018592183886103227613 13621881972068957288710355)
        ·
          refine ⟨20432822958103435933065533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13621881972068957288710355 20432822958103435933065533)
          ·
            refine ⟨7662308609288788474899575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20432822958103435933065533 7662308609288788474899575)
            ·
              refine ⟨11493462913933182712349363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7662308609288788474899575 11493462913933182712349363)
              ·
                refine ⟨17240194370899774068524045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11493462913933182712349363 17240194370899774068524045)
                ·
                  refine ⟨6465072889087415275696517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17240194370899774068524045 6465072889087415275696517)
                  ·
                    refine ⟨1212201166703890364193097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6465072889087415275696517 1212201166703890364193097)
                    ·
                      rfl

theorem cell22_3541130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 1, 1, 3, 4].length) (baseStart_3541130 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3541130 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3541130 prefixEnd_3541130 := by exact prefixLift 3541130
  have htrace : WordTrace (prefixWord ++ tailWord_3541130) baseStart_3541130 baseEnd_3541130 := by
    simpa [prefixWord, tailWord_3541130, baseEnd_3541130] using wordTrace_append hprefix tailTrace_3541130
  have hstable : (prefixWord ++ tailWord_3541130).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3541130).length < 2 ^ (prefixWord ++ tailWord_3541130).sum := by decide
  have hdescent : baseEnd_3541130 < baseStart_3541130 := by decide
  rcases family_descends (prefixWord ++ tailWord_3541130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3541256 : List Nat := [2, 1, 3, 2, 3, 3, 1, 3, 1, 3]
def baseStart_3541256 : Nat := 118140960795 + 3541256 * 2 ^ 59
def prefixEnd_3541256 : Nat := 4983230072969 + 3 ^ 40 * 3541256 * 2
def baseEnd_3541256 : Nat := 1212244299078868035542711

theorem tailTrace_3541256 : CollatzResearch.WordTrace tailWord_3541256 prefixEnd_3541256 1212244299078868035542711 := by
  unfold tailWord_3541256
  simp only [CollatzResearch.WordTrace]
  refine ⟨64580108629320892609725811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86106811505761190146301081 64580108629320892609725811)
  ·
    refine ⟨96870162943981338914588717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64580108629320892609725811 96870162943981338914588717)
    ·
      refine ⟨36326311103993002092970769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96870162943981338914588717 36326311103993002092970769)
      ·
        refine ⟨27244733327994751569728077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36326311103993002092970769 27244733327994751569728077)
        ·
          refine ⟨10216774997998031838648029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27244733327994751569728077 10216774997998031838648029)
          ·
            refine ⟨3831290624249261939493011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10216774997998031838648029 3831290624249261939493011)
            ·
              refine ⟨5746935936373892909239517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3831290624249261939493011 5746935936373892909239517)
              ·
                refine ⟨2155100976140209840964819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5746935936373892909239517 2155100976140209840964819)
                ·
                  refine ⟨3232651464210314761447229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2155100976140209840964819 3232651464210314761447229)
                  ·
                    refine ⟨1212244299078868035542711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3232651464210314761447229 1212244299078868035542711)
                    ·
                      rfl

theorem cell22_3541256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 3, 1, 3, 1, 3].length) (baseStart_3541256 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3541256 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3541256 prefixEnd_3541256 := by exact prefixLift 3541256
  have htrace : WordTrace (prefixWord ++ tailWord_3541256) baseStart_3541256 baseEnd_3541256 := by
    simpa [prefixWord, tailWord_3541256, baseEnd_3541256] using wordTrace_append hprefix tailTrace_3541256
  have hstable : (prefixWord ++ tailWord_3541256).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3541256).length < 2 ^ (prefixWord ++ tailWord_3541256).sum := by decide
  have hdescent : baseEnd_3541256 < baseStart_3541256 := by decide
  rcases family_descends (prefixWord ++ tailWord_3541256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3541263 : List Nat := [1, 1, 2, 1, 1, 1, 3, 4, 8]
def baseStart_3541263 : Nat := 118140960795 + 3541263 * 2 ^ 59
def prefixEnd_3541263 : Nat := 4983230072969 + 3 ^ 40 * 3541263 * 2
def baseEnd_3541263 : Nat := 404082231773974116872563

theorem tailTrace_3541263 : CollatzResearch.WordTrace tailWord_3541263 prefixEnd_3541263 404082231773974116872563 := by
  unfold tailWord_3541263
  simp only [CollatzResearch.WordTrace]
  refine ⟨129160472569616425414956443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86106981713077616943304295 129160472569616425414956443)
  ·
    refine ⟨193740708854424638122434665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129160472569616425414956443 193740708854424638122434665)
    ·
      refine ⟨145305531640818478591825999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193740708854424638122434665 145305531640818478591825999)
      ·
        refine ⟨217958297461227717887738999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145305531640818478591825999 217958297461227717887738999)
        ·
          refine ⟨326937446191841576831608499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 217958297461227717887738999 326937446191841576831608499)
          ·
            refine ⟨490406169287762365247412749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 326937446191841576831608499 490406169287762365247412749)
            ·
              refine ⟨183902313482910886967779781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 490406169287762365247412749 183902313482910886967779781)
              ·
                refine ⟨34481683778045791306458709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 183902313482910886967779781 34481683778045791306458709)
                ·
                  refine ⟨404082231773974116872563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 34481683778045791306458709 404082231773974116872563)
                  ·
                    rfl

theorem cell22_3541263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 4, 8].length) (baseStart_3541263 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3541263 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3541263 prefixEnd_3541263 := by exact prefixLift 3541263
  have htrace : WordTrace (prefixWord ++ tailWord_3541263) baseStart_3541263 baseEnd_3541263 := by
    simpa [prefixWord, tailWord_3541263, baseEnd_3541263] using wordTrace_append hprefix tailTrace_3541263
  have hstable : (prefixWord ++ tailWord_3541263).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3541263).length < 2 ^ (prefixWord ++ tailWord_3541263).sum := by decide
  have hdescent : baseEnd_3541263 < baseStart_3541263 := by decide
  rcases family_descends (prefixWord ++ tailWord_3541263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3541325 : List Nat := [1, 6, 1, 14]
def baseStart_3541325 : Nat := 118140960795 + 3541325 * 2 ^ 59
def prefixEnd_3541325 : Nat := 4983230072969 + 3 ^ 40 * 3541325 * 2
def baseEnd_3541325 : Nat := 1662918956363477168131

theorem tailTrace_3541325 : CollatzResearch.WordTrace tailWord_3541325 prefixEnd_3541325 1662918956363477168131 := by
  unfold tailWord_3541325
  simp only [CollatzResearch.WordTrace]
  refine ⟨129162733895391810003713429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86108489263594540002475619 129162733895391810003713429)
  ·
    refine ⟨6054503151346491093924067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 129162733895391810003713429 6054503151346491093924067)
    ·
      refine ⟨9081754727019736640886101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6054503151346491093924067 9081754727019736640886101)
      ·
        refine ⟨1662918956363477168131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 14 9081754727019736640886101 1662918956363477168131)
        ·
          rfl

theorem cell22_3541325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 14].length) (baseStart_3541325 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3541325 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3541325 prefixEnd_3541325 := by exact prefixLift 3541325
  have htrace : WordTrace (prefixWord ++ tailWord_3541325) baseStart_3541325 baseEnd_3541325 := by
    simpa [prefixWord, tailWord_3541325, baseEnd_3541325] using wordTrace_append hprefix tailTrace_3541325
  have hstable : (prefixWord ++ tailWord_3541325).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3541325).length < 2 ^ (prefixWord ++ tailWord_3541325).sum := by decide
  have hdescent : baseEnd_3541325 < baseStart_3541325 := by decide
  rcases family_descends (prefixWord ++ tailWord_3541325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3541329 : List Nat := [1, 2, 2, 1, 4, 3, 2, 2, 2, 3]
def baseStart_3541329 : Nat := 118140960795 + 3541329 * 2 ^ 59
def prefixEnd_3541329 : Nat := 4983230072969 + 3 ^ 40 * 3541329 * 2
def baseEnd_3541329 : Nat := 1212269288470720178467487

theorem tailTrace_3541329 : CollatzResearch.WordTrace tailWord_3541329 prefixEnd_3541329 1212269288470720178467487 := by
  unfold tailWord_3541329
  simp only [CollatzResearch.WordTrace]
  refine ⟨129162879787377318686859041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86108586524918212457906027 129162879787377318686859041)
  ·
    refine ⟨96872159840532989015144281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129162879787377318686859041 96872159840532989015144281)
    ·
      refine ⟨72654119880399741761358211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96872159840532989015144281 72654119880399741761358211)
      ·
        refine ⟨108981179820599612642037317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72654119880399741761358211 108981179820599612642037317)
        ·
          refine ⟨20433971216362427370381997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 108981179820599612642037317 20433971216362427370381997)
          ·
            refine ⟨7662739206135910263893249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20433971216362427370381997 7662739206135910263893249)
            ·
              refine ⟨5747054404601932697919937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7662739206135910263893249 5747054404601932697919937)
              ·
                refine ⟨4310290803451449523439953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5747054404601932697919937 4310290803451449523439953)
                ·
                  refine ⟨3232718102588587142579965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4310290803451449523439953 3232718102588587142579965)
                  ·
                    refine ⟨1212269288470720178467487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3232718102588587142579965 1212269288470720178467487)
                    ·
                      rfl

theorem cell22_3541329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 2, 2, 2, 3].length) (baseStart_3541329 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3541329 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3541329 prefixEnd_3541329 := by exact prefixLift 3541329
  have htrace : WordTrace (prefixWord ++ tailWord_3541329) baseStart_3541329 baseEnd_3541329 := by
    simpa [prefixWord, tailWord_3541329, baseEnd_3541329] using wordTrace_append hprefix tailTrace_3541329
  have hstable : (prefixWord ++ tailWord_3541329).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3541329).length < 2 ^ (prefixWord ++ tailWord_3541329).sum := by decide
  have hdescent : baseEnd_3541329 < baseStart_3541329 := by decide
  rcases family_descends (prefixWord ++ tailWord_3541329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3541387 : List Nat := [1, 1, 1, 1, 4, 4, 3, 2, 5]
def baseStart_3541387 : Nat := 118140960795 + 3541387 * 2 ^ 59
def prefixEnd_3541387 : Nat := 4983230072969 + 3 ^ 40 * 3541387 * 2
def baseEnd_3541387 : Nat := 404096381018675786839103

theorem tailTrace_3541387 : CollatzResearch.WordTrace tailWord_3541387 prefixEnd_3541387 404096381018675786839103 := by
  unfold tailWord_3541387
  simp only [CollatzResearch.WordTrace]
  refine ⟨129164995221167194592470415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86109996814111463061646943 129164995221167194592470415)
  ·
    refine ⟨193747492831750791888705623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129164995221167194592470415 193747492831750791888705623)
    ·
      refine ⟨290621239247626187833058435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193747492831750791888705623 290621239247626187833058435)
      ·
        refine ⟨435931858871439281749587653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 290621239247626187833058435 435931858871439281749587653)
        ·
          refine ⟨81737223538394865328047685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 435931858871439281749587653 81737223538394865328047685)
          ·
            refine ⟨15325729413449037249008941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 81737223538394865328047685 15325729413449037249008941)
            ·
              refine ⟨5747148530043388968378353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15325729413449037249008941 5747148530043388968378353)
              ·
                refine ⟨4310361397532541726283765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5747148530043388968378353 4310361397532541726283765)
                ·
                  refine ⟨404096381018675786839103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4310361397532541726283765 404096381018675786839103)
                  ·
                    rfl

theorem cell22_3541387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 3, 2, 5].length) (baseStart_3541387 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3541387 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3541387 prefixEnd_3541387 := by exact prefixLift 3541387
  have htrace : WordTrace (prefixWord ++ tailWord_3541387) baseStart_3541387 baseEnd_3541387 := by
    simpa [prefixWord, tailWord_3541387, baseEnd_3541387] using wordTrace_append hprefix tailTrace_3541387
  have hstable : (prefixWord ++ tailWord_3541387).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3541387).length < 2 ^ (prefixWord ++ tailWord_3541387).sum := by decide
  have hdescent : baseEnd_3541387 < baseStart_3541387 := by decide
  rcases family_descends (prefixWord ++ tailWord_3541387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3541402 : List Nat := [3, 1, 1, 4, 1, 2, 2, 1, 2, 5]
def baseStart_3541402 : Nat := 118140960795 + 3541402 * 2 ^ 59
def prefixEnd_3541402 : Nat := 4983230072969 + 3 ^ 40 * 3541402 * 2
def baseEnd_3541402 : Nat := 1212294277862572321392263

theorem tailTrace_3541402 : CollatzResearch.WordTrace tailWord_3541402 prefixEnd_3541402 1212294277862572321392263 := by
  unfold tailWord_3541402
  simp only [CollatzResearch.WordTrace]
  refine ⟨32291385579028213038566615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86110361544075234769510973 32291385579028213038566615)
  ·
    refine ⟨48437078368542319557849923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32291385579028213038566615 48437078368542319557849923)
    ·
      refine ⟨72655617552813479336774885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48437078368542319557849923 72655617552813479336774885)
      ·
        refine ⟨13622928291152527375645291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 72655617552813479336774885 13622928291152527375645291)
        ·
          refine ⟨20434392436728791063467937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13622928291152527375645291 20434392436728791063467937)
          ·
            refine ⟨15325794327546593297600953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20434392436728791063467937 15325794327546593297600953)
            ·
              refine ⟨11494345745659944973200715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15325794327546593297600953 11494345745659944973200715)
              ·
                refine ⟨17241518618489917459801073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11494345745659944973200715 17241518618489917459801073)
                ·
                  refine ⟨12931138963867438094850805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17241518618489917459801073 12931138963867438094850805)
                  ·
                    refine ⟨1212294277862572321392263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12931138963867438094850805 1212294277862572321392263)
                    ·
                      rfl

theorem cell22_3541402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 2, 1, 2, 5].length) (baseStart_3541402 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3541402 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3541402 prefixEnd_3541402 := by exact prefixLift 3541402
  have htrace : WordTrace (prefixWord ++ tailWord_3541402) baseStart_3541402 baseEnd_3541402 := by
    simpa [prefixWord, tailWord_3541402, baseEnd_3541402] using wordTrace_append hprefix tailTrace_3541402
  have hstable : (prefixWord ++ tailWord_3541402).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3541402).length < 2 ^ (prefixWord ++ tailWord_3541402).sum := by decide
  have hdescent : baseEnd_3541402 < baseStart_3541402 := by decide
  rcases family_descends (prefixWord ++ tailWord_3541402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3541445 : List Nat := [1, 3, 1, 1, 1, 1, 1, 1, 2, 10]
def baseStart_3541445 : Nat := 118140960795 + 3541445 * 2 ^ 59
def prefixEnd_3541445 : Nat := 4983230072969 + 3 ^ 40 * 3541445 * 2
def baseEnd_3541445 : Nat := 1212308997641334542567131

theorem tailTrace_3541445 : CollatzResearch.WordTrace tailWord_3541445 prefixEnd_3541445 1212308997641334542567131 := by
  unfold tailWord_3541445
  simp only [CollatzResearch.WordTrace]
  refine ⟨129167110654957070498081789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86111407103304713665387859 129167110654957070498081789)
  ·
    refine ⟨48437666495608901436780671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129167110654957070498081789 48437666495608901436780671)
    ·
      refine ⟨72656499743413352155171007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48437666495608901436780671 72656499743413352155171007)
      ·
        refine ⟨108984749615120028232756511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72656499743413352155171007 108984749615120028232756511)
        ·
          refine ⟨163477124422680042349134767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108984749615120028232756511 163477124422680042349134767)
          ·
            refine ⟨245215686634020063523702151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163477124422680042349134767 245215686634020063523702151)
            ·
              refine ⟨367823529951030095285553227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 245215686634020063523702151 367823529951030095285553227)
              ·
                refine ⟨551735294926545142928329841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 367823529951030095285553227 551735294926545142928329841)
                ·
                  refine ⟨413801471194908857196247381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 551735294926545142928329841 413801471194908857196247381)
                  ·
                    refine ⟨1212308997641334542567131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 413801471194908857196247381 1212308997641334542567131)
                    ·
                      rfl

theorem cell22_3541445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 2, 10].length) (baseStart_3541445 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3541445 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3541445 prefixEnd_3541445 := by exact prefixLift 3541445
  have htrace : WordTrace (prefixWord ++ tailWord_3541445) baseStart_3541445 baseEnd_3541445 := by
    simpa [prefixWord, tailWord_3541445, baseEnd_3541445] using wordTrace_append hprefix tailTrace_3541445
  have hstable : (prefixWord ++ tailWord_3541445).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3541445).length < 2 ^ (prefixWord ++ tailWord_3541445).sum := by decide
  have hdescent : baseEnd_3541445 < baseStart_3541445 := by decide
  rcases family_descends (prefixWord ++ tailWord_3541445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3541479 : List Nat := [1, 1, 5, 2, 1, 1, 4, 1, 2, 4]
def baseStart_3541479 : Nat := 118140960795 + 3541479 * 2 ^ 59
def prefixEnd_3541479 : Nat := 4983230072969 + 3 ^ 40 * 3541479 * 2
def baseEnd_3541479 : Nat := 1212320636536169787217027

theorem tailTrace_3541479 : CollatzResearch.WordTrace tailWord_3541479 prefixEnd_3541479 1212320636536169787217027 := by
  unfold tailWord_3541479
  simp only [CollatzResearch.WordTrace]
  refine ⟨129168350736833894304819491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86112233824555929536546327 129168350736833894304819491)
  ·
    refine ⟨193752526105250841457229237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129168350736833894304819491 193752526105250841457229237)
    ·
      refine ⟨18164299322367266386615241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 193752526105250841457229237 18164299322367266386615241)
      ·
        refine ⟨13623224491775449789961431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18164299322367266386615241 13623224491775449789961431)
        ·
          refine ⟨20434836737663174684942147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13623224491775449789961431 20434836737663174684942147)
          ·
            refine ⟨30652255106494762027413221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20434836737663174684942147 30652255106494762027413221)
            ·
              refine ⟨5747297832467767880139979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30652255106494762027413221 5747297832467767880139979)
              ·
                refine ⟨8620946748701651820209969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5747297832467767880139979 8620946748701651820209969)
                ·
                  refine ⟨6465710061526238865157477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8620946748701651820209969 6465710061526238865157477)
                  ·
                    refine ⟨1212320636536169787217027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6465710061526238865157477 1212320636536169787217027)
                    ·
                      rfl

theorem cell22_3541479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 4, 1, 2, 4].length) (baseStart_3541479 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3541479 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3541479 prefixEnd_3541479 := by exact prefixLift 3541479
  have htrace : WordTrace (prefixWord ++ tailWord_3541479) baseStart_3541479 baseEnd_3541479 := by
    simpa [prefixWord, tailWord_3541479, baseEnd_3541479] using wordTrace_append hprefix tailTrace_3541479
  have hstable : (prefixWord ++ tailWord_3541479).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3541479).length < 2 ^ (prefixWord ++ tailWord_3541479).sum := by decide
  have hdescent : baseEnd_3541479 < baseStart_3541479 := by decide
  rcases family_descends (prefixWord ++ tailWord_3541479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3541511 : List Nat := [1, 1, 4, 3, 4, 1, 1, 7]
def baseStart_3541511 : Nat := 118140960795 + 3541511 * 2 ^ 59
def prefixEnd_3541511 : Nat := 4983230072969 + 3 ^ 40 * 3541511 * 2
def baseEnd_3541511 : Nat := 134703510087792485601881

theorem tailTrace_3541511 : CollatzResearch.WordTrace tailWord_3541511 prefixEnd_3541511 134703510087792485601881 := by
  unfold tailWord_3541511
  simp only [CollatzResearch.WordTrace]
  refine ⟨129169517872717963769984387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86113011915145309179989591 129169517872717963769984387)
  ·
    refine ⟨193754276809076945654976581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129169517872717963769984387 193754276809076945654976581)
    ·
      refine ⟨36328926901701927310308109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 193754276809076945654976581 36328926901701927310308109)
      ·
        refine ⟨13623347588138222741365541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36328926901701927310308109 13623347588138222741365541)
        ·
          refine ⟨2554377672775916764006039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13623347588138222741365541 2554377672775916764006039)
          ·
            refine ⟨3831566509163875146009059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2554377672775916764006039 3831566509163875146009059)
            ·
              refine ⟨5747349763745812719013589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3831566509163875146009059 5747349763745812719013589)
              ·
                refine ⟨134703510087792485601881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5747349763745812719013589 134703510087792485601881)
                ·
                  rfl

theorem cell22_3541511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 4, 1, 1, 7].length) (baseStart_3541511 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3541511 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3541511 prefixEnd_3541511 := by exact prefixLift 3541511
  have htrace : WordTrace (prefixWord ++ tailWord_3541511) baseStart_3541511 baseEnd_3541511 := by
    simpa [prefixWord, tailWord_3541511, baseEnd_3541511] using wordTrace_append hprefix tailTrace_3541511
  have hstable : (prefixWord ++ tailWord_3541511).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3541511).length < 2 ^ (prefixWord ++ tailWord_3541511).sum := by decide
  have hdescent : baseEnd_3541511 < baseStart_3541511 := by decide
  rcases family_descends (prefixWord ++ tailWord_3541511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3541537 : List Nat := [1, 2, 3, 2, 2, 1, 1, 2, 1, 7]
def baseStart_3541537 : Nat := 118140960795 + 3541537 * 2 ^ 59
def prefixEnd_3541537 : Nat := 4983230072969 + 3 ^ 40 * 3541537 * 2
def baseEnd_3541537 : Nat := 1212340491121476969266849

theorem tailTrace_3541537 : CollatzResearch.WordTrace tailWord_3541537 prefixEnd_3541537 1212340491121476969266849 := by
  unfold tailWord_3541537
  simp only [CollatzResearch.WordTrace]
  refine ⟨129170466170623770210430865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86113644113749180140287243 129170466170623770210430865)
  ·
    refine ⟨96877849627967827657823149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129170466170623770210430865 96877849627967827657823149)
    ·
      refine ⟨36329193610487935371683681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96877849627967827657823149 36329193610487935371683681)
      ·
        refine ⟨27246895207865951528762761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36329193610487935371683681 27246895207865951528762761)
        ·
          refine ⟨20435171405899463646572071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27246895207865951528762761 20435171405899463646572071)
          ·
            refine ⟨30652757108849195469858107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20435171405899463646572071 30652757108849195469858107)
            ·
              refine ⟨45979135663273793204787161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30652757108849195469858107 45979135663273793204787161)
              ·
                refine ⟨34484351747455344903590371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45979135663273793204787161 34484351747455344903590371)
                ·
                  refine ⟨51726527621183017355385557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34484351747455344903590371 51726527621183017355385557)
                  ·
                    refine ⟨1212340491121476969266849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 51726527621183017355385557 1212340491121476969266849)
                    ·
                      rfl

theorem cell22_3541537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 2, 1, 7].length) (baseStart_3541537 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3541537 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3541537 prefixEnd_3541537 := by exact prefixLift 3541537
  have htrace : WordTrace (prefixWord ++ tailWord_3541537) baseStart_3541537 baseEnd_3541537 := by
    simpa [prefixWord, tailWord_3541537, baseEnd_3541537] using wordTrace_append hprefix tailTrace_3541537
  have hstable : (prefixWord ++ tailWord_3541537).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3541537).length < 2 ^ (prefixWord ++ tailWord_3541537).sum := by decide
  have hdescent : baseEnd_3541537 < baseStart_3541537 := by decide
  rcases family_descends (prefixWord ++ tailWord_3541537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3541549 : List Nat := [1, 5, 4, 1, 2, 1, 1, 2, 2, 3]
def baseStart_3541549 : Nat := 118140960795 + 3541549 * 2 ^ 59
def prefixEnd_3541549 : Nat := 4983230072969 + 3 ^ 40 * 3541549 * 2
def baseEnd_3541549 : Nat := 1212344598966712937966813

theorem tailTrace_3541549 : CollatzResearch.WordTrace tailWord_3541549 prefixEnd_3541549 1212344598966712937966813 := by
  unfold tailWord_3541549
  simp only [CollatzResearch.WordTrace]
  refine ⟨129170903846580296259867701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86113935897720197506578467 129170903846580296259867701)
  ·
    refine ⟨12109772235616902774362597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 129170903846580296259867701 12109772235616902774362597)
    ·
      refine ⟨2270582294178169270192987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12109772235616902774362597 2270582294178169270192987)
      ·
        refine ⟨3405873441267253905289481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2270582294178169270192987 3405873441267253905289481)
        ·
          refine ⟨2554405080950440428967111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3405873441267253905289481 2554405080950440428967111)
          ·
            refine ⟨3831607621425660643450667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2554405080950440428967111 3831607621425660643450667)
            ·
              refine ⟨5747411432138490965176001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3831607621425660643450667 5747411432138490965176001)
              ·
                refine ⟨4310558574103868223882001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5747411432138490965176001 4310558574103868223882001)
                ·
                  refine ⟨3232918930577901167911501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4310558574103868223882001 3232918930577901167911501)
                  ·
                    refine ⟨1212344598966712937966813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3232918930577901167911501 1212344598966712937966813)
                    ·
                      rfl

theorem cell22_3541549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 2, 1, 1, 2, 2, 3].length) (baseStart_3541549 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3541549 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3541549 prefixEnd_3541549 := by exact prefixLift 3541549
  have htrace : WordTrace (prefixWord ++ tailWord_3541549) baseStart_3541549 baseEnd_3541549 := by
    simpa [prefixWord, tailWord_3541549, baseEnd_3541549] using wordTrace_append hprefix tailTrace_3541549
  have hstable : (prefixWord ++ tailWord_3541549).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3541549).length < 2 ^ (prefixWord ++ tailWord_3541549).sum := by decide
  have hdescent : baseEnd_3541549 < baseStart_3541549 := by decide
  rcases family_descends (prefixWord ++ tailWord_3541549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3541586 : List Nat := [3, 2, 2, 1, 2, 1, 4, 2, 1, 4]
def baseStart_3541586 : Nat := 118140960795 + 3541586 * 2 ^ 59
def prefixEnd_3541586 : Nat := 4983230072969 + 3 ^ 40 * 3541586 * 2
def baseEnd_3541586 : Nat := 1212357264822857174791699

theorem tailTrace_3541586 : CollatzResearch.WordTrace tailWord_3541586 prefixEnd_3541586 1212357264822857174791699 := by
  unfold tailWord_3541586
  simp only [CollatzResearch.WordTrace]
  refine ⟨32293063336861562894741153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86114835564964167719309741 32293063336861562894741153)
  ·
    refine ⟨24219797502646172171055865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32293063336861562894741153 24219797502646172171055865)
    ·
      refine ⟨18164848126984629128291899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24219797502646172171055865 18164848126984629128291899)
      ·
        refine ⟨27247272190476943692437849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18164848126984629128291899 27247272190476943692437849)
        ·
          refine ⟨20435454142857707769328387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27247272190476943692437849 20435454142857707769328387)
          ·
            refine ⟨30653181214286561653992581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20435454142857707769328387 30653181214286561653992581)
            ·
              refine ⟨5747471477678730310123609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30653181214286561653992581 5747471477678730310123609)
              ·
                refine ⟨4310603608259047732592707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5747471477678730310123609 4310603608259047732592707)
                ·
                  refine ⟨6465905412388571598889061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4310603608259047732592707 6465905412388571598889061)
                  ·
                    refine ⟨1212357264822857174791699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6465905412388571598889061 1212357264822857174791699)
                    ·
                      rfl

theorem cell22_3541586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 4, 2, 1, 4].length) (baseStart_3541586 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3541586 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3541586 prefixEnd_3541586 := by exact prefixLift 3541586
  have htrace : WordTrace (prefixWord ++ tailWord_3541586) baseStart_3541586 baseEnd_3541586 := by
    simpa [prefixWord, tailWord_3541586, baseEnd_3541586] using wordTrace_append hprefix tailTrace_3541586
  have hstable : (prefixWord ++ tailWord_3541586).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3541586).length < 2 ^ (prefixWord ++ tailWord_3541586).sum := by decide
  have hdescent : baseEnd_3541586 < baseStart_3541586 := by decide
  rcases family_descends (prefixWord ++ tailWord_3541586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3541601 : List Nat := [1, 2, 3, 1, 1, 4, 3, 3, 4]
def baseStart_3541601 : Nat := 118140960795 + 3541601 * 2 ^ 59
def prefixEnd_3541601 : Nat := 4983230072969 + 3 ^ 40 * 3541601 * 2
def baseEnd_3541601 : Nat := 404120799876467378555551

theorem tailTrace_3541601 : CollatzResearch.WordTrace tailWord_3541601 prefixEnd_3541601 404120799876467378555551 := by
  unfold tailWord_3541601
  simp only [CollatzResearch.WordTrace]
  refine ⟨129172800442391909140760657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86115200294927939427173771 129172800442391909140760657)
  ·
    refine ⟨96879600331793931855570493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129172800442391909140760657 96879600331793931855570493)
    ·
      refine ⟨36329850124422724445838935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96879600331793931855570493 36329850124422724445838935)
      ·
        refine ⟨54494775186634086668758403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36329850124422724445838935 54494775186634086668758403)
        ·
          refine ⟨81742162779951130003137605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54494775186634086668758403 81742162779951130003137605)
          ·
            refine ⟨15326655521240836875588301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 81742162779951130003137605 15326655521240836875588301)
            ·
              refine ⟨5747495820465313828345613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15326655521240836875588301 5747495820465313828345613)
              ·
                refine ⟨2155310932674492685629605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5747495820465313828345613 2155310932674492685629605)
                ·
                  refine ⟨404120799876467378555551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2155310932674492685629605 404120799876467378555551)
                  ·
                    rfl

theorem cell22_3541601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 3, 3, 4].length) (baseStart_3541601 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3541601 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3541601 prefixEnd_3541601 := by exact prefixLift 3541601
  have htrace : WordTrace (prefixWord ++ tailWord_3541601) baseStart_3541601 baseEnd_3541601 := by
    simpa [prefixWord, tailWord_3541601, baseEnd_3541601] using wordTrace_append hprefix tailTrace_3541601
  have hstable : (prefixWord ++ tailWord_3541601).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3541601).length < 2 ^ (prefixWord ++ tailWord_3541601).sum := by decide
  have hdescent : baseEnd_3541601 < baseStart_3541601 := by decide
  rcases family_descends (prefixWord ++ tailWord_3541601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3541612 : List Nat := [2, 2, 1, 1, 3, 1, 12]
def baseStart_3541612 : Nat := 118140960795 + 3541612 * 2 ^ 59
def prefixEnd_3541612 : Nat := 4983230072969 + 3 ^ 40 * 3541612 * 2
def baseEnd_3541612 : Nat := 44902450561266732357097

theorem tailTrace_3541612 : CollatzResearch.WordTrace tailWord_3541612 prefixEnd_3541612 44902450561266732357097 := by
  unfold tailWord_3541612
  simp only [CollatzResearch.WordTrace]
  refine ⟨64586600822676029009705545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86115467763568038679607393 64586600822676029009705545)
  ·
    refine ⟨48439950617007021757279159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64586600822676029009705545 48439950617007021757279159)
    ·
      refine ⟨72659925925510532635918739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48439950617007021757279159 72659925925510532635918739)
      ·
        refine ⟨108989888888265798953878109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72659925925510532635918739 108989888888265798953878109)
        ·
          refine ⟨40871208333099674607704291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 108989888888265798953878109 40871208333099674607704291)
          ·
            refine ⟨61306812499649511911556437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40871208333099674607704291 61306812499649511911556437)
            ·
              refine ⟨44902450561266732357097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 61306812499649511911556437 44902450561266732357097)
              ·
                rfl

theorem cell22_3541612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 12].length) (baseStart_3541612 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3541612 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3541612 prefixEnd_3541612 := by exact prefixLift 3541612
  have htrace : WordTrace (prefixWord ++ tailWord_3541612) baseStart_3541612 baseEnd_3541612 := by
    simpa [prefixWord, tailWord_3541612, baseEnd_3541612] using wordTrace_append hprefix tailTrace_3541612
  have hstable : (prefixWord ++ tailWord_3541612).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3541612).length < 2 ^ (prefixWord ++ tailWord_3541612).sum := by decide
  have hdescent : baseEnd_3541612 < baseStart_3541612 := by decide
  rcases family_descends (prefixWord ++ tailWord_3541612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3541618 : List Nat := [3, 2, 1, 2, 5, 1, 1, 1, 6]
def baseStart_3541618 : Nat := 118140960795 + 3541618 * 2 ^ 59
def prefixEnd_3541618 : Nat := 4983230072969 + 3 ^ 40 * 3541618 * 2
def baseEnd_3541618 : Nat := 404122739692273252663867

theorem tailTrace_3541618 : CollatzResearch.WordTrace tailWord_3541618 prefixEnd_3541618 404122739692273252663867 := by
  unfold tailWord_3541618
  simp only [CollatzResearch.WordTrace]
  refine ⟨32293355120832580261032377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86115613655553547362753005 32293355120832580261032377)
  ·
    refine ⟨24220016340624435195774283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32293355120832580261032377 24220016340624435195774283)
    ·
      refine ⟨36330024510936652793661425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24220016340624435195774283 36330024510936652793661425)
      ·
        refine ⟨27247518383202489595246069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36330024510936652793661425 27247518383202489595246069)
        ·
          refine ⟨2554454848425233399554319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 27247518383202489595246069 2554454848425233399554319)
          ·
            refine ⟨3831682272637850099331479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2554454848425233399554319 3831682272637850099331479)
            ·
              refine ⟨5747523408956775148997219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3831682272637850099331479 5747523408956775148997219)
              ·
                refine ⟨8621285113435162723495829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5747523408956775148997219 8621285113435162723495829)
                ·
                  refine ⟨404122739692273252663867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8621285113435162723495829 404122739692273252663867)
                  ·
                    rfl

theorem cell22_3541618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 5, 1, 1, 1, 6].length) (baseStart_3541618 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3541618 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3541618 prefixEnd_3541618 := by exact prefixLift 3541618
  have htrace : WordTrace (prefixWord ++ tailWord_3541618) baseStart_3541618 baseEnd_3541618 := by
    simpa [prefixWord, tailWord_3541618, baseEnd_3541618] using wordTrace_append hprefix tailTrace_3541618
  have hstable : (prefixWord ++ tailWord_3541618).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3541618).length < 2 ^ (prefixWord ++ tailWord_3541618).sum := by decide
  have hdescent : baseEnd_3541618 < baseStart_3541618 := by decide
  rcases family_descends (prefixWord ++ tailWord_3541618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3541627 : List Nat := [1, 1, 1, 1, 1, 4, 2, 2, 2, 7]
def baseStart_3541627 : Nat := 118140960795 + 3541627 * 2 ^ 59
def prefixEnd_3541627 : Nat := 4983230072969 + 3 ^ 40 * 3541627 * 2
def baseEnd_3541627 : Nat := 1212371299960746734516573

theorem tailTrace_3541627 : CollatzResearch.WordTrace tailWord_3541627 prefixEnd_3541627 1212371299960746734516573 := by
  unfold tailWord_3541627
  simp only [CollatzResearch.WordTrace]
  refine ⟨129173748740297715581207135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86115832493531810387471423 129173748740297715581207135)
  ·
    refine ⟨193760623110446573371810703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129173748740297715581207135 193760623110446573371810703)
    ·
      refine ⟨290640934665669860057716055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193760623110446573371810703 290640934665669860057716055)
      ·
        refine ⟨435961401998504790086574083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 290640934665669860057716055 435961401998504790086574083)
        ·
          refine ⟨653942102997757185129861125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 435961401998504790086574083 653942102997757185129861125)
          ·
            refine ⟨122614144312079472211848961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 653942102997757185129861125 122614144312079472211848961)
            ·
              refine ⟨91960608234059604158886721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 122614144312079472211848961 91960608234059604158886721)
              ·
                refine ⟨68970456175544703119165041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 91960608234059604158886721 68970456175544703119165041)
                ·
                  refine ⟨51727842131658527339373781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68970456175544703119165041 51727842131658527339373781)
                  ·
                    refine ⟨1212371299960746734516573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 51727842131658527339373781 1212371299960746734516573)
                    ·
                      rfl

theorem cell22_3541627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 2, 2, 7].length) (baseStart_3541627 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3541627 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3541627 prefixEnd_3541627 := by exact prefixLift 3541627
  have htrace : WordTrace (prefixWord ++ tailWord_3541627) baseStart_3541627 baseEnd_3541627 := by
    simpa [prefixWord, tailWord_3541627, baseEnd_3541627] using wordTrace_append hprefix tailTrace_3541627
  have hstable : (prefixWord ++ tailWord_3541627).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3541627).length < 2 ^ (prefixWord ++ tailWord_3541627).sum := by decide
  have hdescent : baseEnd_3541627 < baseStart_3541627 := by decide
  rcases family_descends (prefixWord ++ tailWord_3541627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3541721 : List Nat := [1, 2, 1, 2, 3, 2, 3, 3, 1, 4]
def baseStart_3541721 : Nat := 118140960795 + 3541721 * 2 ^ 59
def prefixEnd_3541721 : Nat := 4983230072969 + 3 ^ 40 * 3541721 * 2
def baseEnd_3541721 : Nat := 1212403478081761822666285

theorem tailTrace_3541721 : CollatzResearch.WordTrace tailWord_3541721 prefixEnd_3541721 1212403478081761822666285 := by
  unfold tailWord_3541721
  simp only [CollatzResearch.WordTrace]
  refine ⟨129177177201957169635129017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86118118134638113090086011 129177177201957169635129017)
  ·
    refine ⟨96882882901467877226346763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129177177201957169635129017 96882882901467877226346763)
    ·
      refine ⟨145324324352201815839520145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96882882901467877226346763 145324324352201815839520145)
      ·
        refine ⟨108993243264151361879640109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145324324352201815839520145 108993243264151361879640109)
        ·
          refine ⟨40872466224056760704865041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 108993243264151361879640109 40872466224056760704865041)
          ·
            refine ⟨30654349668042570528648781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40872466224056760704865041 30654349668042570528648781)
            ·
              refine ⟨11495381125515963948243293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30654349668042570528648781 11495381125515963948243293)
              ·
                refine ⟨4310767922068486480591235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11495381125515963948243293 4310767922068486480591235)
                ·
                  refine ⟨6466151883102729720886853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4310767922068486480591235 6466151883102729720886853)
                  ·
                    refine ⟨1212403478081761822666285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6466151883102729720886853 1212403478081761822666285)
                    ·
                      rfl

theorem cell22_3541721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 3, 3, 1, 4].length) (baseStart_3541721 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3541721 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3541721 prefixEnd_3541721 := by exact prefixLift 3541721
  have htrace : WordTrace (prefixWord ++ tailWord_3541721) baseStart_3541721 baseEnd_3541721 := by
    simpa [prefixWord, tailWord_3541721, baseEnd_3541721] using wordTrace_append hprefix tailTrace_3541721
  have hstable : (prefixWord ++ tailWord_3541721).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3541721).length < 2 ^ (prefixWord ++ tailWord_3541721).sum := by decide
  have hdescent : baseEnd_3541721 < baseStart_3541721 := by decide
  rcases family_descends (prefixWord ++ tailWord_3541721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3541783 : List Nat := [1, 1, 3, 4, 3, 1, 1, 2, 2, 4]
def baseStart_3541783 : Nat := 118140960795 + 3541783 * 2 ^ 59
def prefixEnd_3541783 : Nat := 4983230072969 + 3 ^ 40 * 3541783 * 2
def baseEnd_3541783 : Nat := 1212424701948814327616095

theorem tailTrace_3541783 : CollatzResearch.WordTrace tailWord_3541783 prefixEnd_3541783 1212424701948814327616095 := by
  unfold tailWord_3541783
  simp only [CollatzResearch.WordTrace]
  refine ⟨129179438527732554223886003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86119625685155036149257335 129179438527732554223886003)
  ·
    refine ⟨193769157791598831335829005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129179438527732554223886003 193769157791598831335829005)
    ·
      refine ⟨72663434171849561750935877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 193769157791598831335829005 72663434171849561750935877)
      ·
        refine ⟨13624393907221792828300477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 72663434171849561750935877 13624393907221792828300477)
        ·
          refine ⟨5109147715208172310612679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13624393907221792828300477 5109147715208172310612679)
          ·
            refine ⟨7663721572812258465919019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5109147715208172310612679 7663721572812258465919019)
            ·
              refine ⟨11495582359218387698878529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7663721572812258465919019 11495582359218387698878529)
              ·
                refine ⟨8621686769413790774158897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11495582359218387698878529 8621686769413790774158897)
                ·
                  refine ⟨6466265077060343080619173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8621686769413790774158897 6466265077060343080619173)
                  ·
                    refine ⟨1212424701948814327616095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6466265077060343080619173 1212424701948814327616095)
                    ·
                      rfl

theorem cell22_3541783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 1, 2, 2, 4].length) (baseStart_3541783 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3541783 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3541783 prefixEnd_3541783 := by exact prefixLift 3541783
  have htrace : WordTrace (prefixWord ++ tailWord_3541783) baseStart_3541783 baseEnd_3541783 := by
    simpa [prefixWord, tailWord_3541783, baseEnd_3541783] using wordTrace_append hprefix tailTrace_3541783
  have hstable : (prefixWord ++ tailWord_3541783).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3541783).length < 2 ^ (prefixWord ++ tailWord_3541783).sum := by decide
  have hdescent : baseEnd_3541783 < baseStart_3541783 := by decide
  rcases family_descends (prefixWord ++ tailWord_3541783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3541802 : List Nat := [3, 1, 4, 3, 1, 1, 1, 3, 2, 3]
def baseStart_3541802 : Nat := 118140960795 + 3541802 * 2 ^ 59
def prefixEnd_3541802 : Nat := 4983230072969 + 3 ^ 40 * 3541802 * 2
def baseEnd_3541802 : Nat := 1212431206037104611391037

theorem tailTrace_3541802 : CollatzResearch.WordTrace tailWord_3541802 prefixEnd_3541802 1212431206037104611391037 := by
  unfold tailWord_3541802
  simp only [CollatzResearch.WordTrace]
  refine ⟨32295032878665930117206915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86120087676442480312551773 32295032878665930117206915)
  ·
    refine ⟨48442549317998895175810373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32295032878665930117206915 48442549317998895175810373)
    ·
      refine ⟨9082977997124792845464445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48442549317998895175810373 9082977997124792845464445)
      ·
        refine ⟨3406116748921797317049167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9082977997124792845464445 3406116748921797317049167)
        ·
          refine ⟨5109175123382695975573751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3406116748921797317049167 5109175123382695975573751)
          ·
            refine ⟨7663762685074043963360627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5109175123382695975573751 7663762685074043963360627)
            ·
              refine ⟨11495644027611065945040941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7663762685074043963360627 11495644027611065945040941)
              ·
                refine ⟨4310866510354149729390353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11495644027611065945040941 4310866510354149729390353)
                ·
                  refine ⟨3233149882765612297042765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4310866510354149729390353 3233149882765612297042765)
                  ·
                    refine ⟨1212431206037104611391037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3233149882765612297042765 1212431206037104611391037)
                    ·
                      rfl

theorem cell22_3541802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 1, 3, 2, 3].length) (baseStart_3541802 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3541802 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3541802 prefixEnd_3541802 := by exact prefixLift 3541802
  have htrace : WordTrace (prefixWord ++ tailWord_3541802) baseStart_3541802 baseEnd_3541802 := by
    simpa [prefixWord, tailWord_3541802, baseEnd_3541802] using wordTrace_append hprefix tailTrace_3541802
  have hstable : (prefixWord ++ tailWord_3541802).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3541802).length < 2 ^ (prefixWord ++ tailWord_3541802).sum := by decide
  have hdescent : baseEnd_3541802 < baseStart_3541802 := by decide
  rcases family_descends (prefixWord ++ tailWord_3541802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3541847 : List Nat := [1, 1, 3, 2, 4, 1, 4, 2, 1, 3]
def baseStart_3541847 : Nat := 118140960795 + 3541847 * 2 ^ 59
def prefixEnd_3541847 : Nat := 4983230072969 + 3 ^ 40 * 3541847 * 2
def baseEnd_3541847 : Nat := 1212446610456739494015899

theorem tailTrace_3541847 : CollatzResearch.WordTrace tailWord_3541847 prefixEnd_3541847 1212446610456739494015899 := by
  unfold tailWord_3541847
  simp only [CollatzResearch.WordTrace]
  refine ⟨129181772799500693154215795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86121181866333795436143863 129181772799500693154215795)
  ·
    refine ⟨193772659199251039731323693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129181772799500693154215795 193772659199251039731323693)
    ·
      refine ⟨72664747199719139899246385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 193772659199251039731323693 72664747199719139899246385)
      ·
        refine ⟨54498560399789354924434789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72664747199719139899246385 54498560399789354924434789)
        ·
          refine ⟨10218480074960504048331523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 54498560399789354924434789 10218480074960504048331523)
          ·
            refine ⟨15327720112440756072497285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10218480074960504048331523 15327720112440756072497285)
            ·
              refine ⟨2873947521082641763593241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15327720112440756072497285 2873947521082641763593241)
              ·
                refine ⟨2155460640811981322694931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2873947521082641763593241 2155460640811981322694931)
                ·
                  refine ⟨3233190961217971984042397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2155460640811981322694931 3233190961217971984042397)
                  ·
                    refine ⟨1212446610456739494015899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3233190961217971984042397 1212446610456739494015899)
                    ·
                      rfl

theorem cell22_3541847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 4, 2, 1, 3].length) (baseStart_3541847 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3541847 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3541847 prefixEnd_3541847 := by exact prefixLift 3541847
  have htrace : WordTrace (prefixWord ++ tailWord_3541847) baseStart_3541847 baseEnd_3541847 := by
    simpa [prefixWord, tailWord_3541847, baseEnd_3541847] using wordTrace_append hprefix tailTrace_3541847
  have hstable : (prefixWord ++ tailWord_3541847).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3541847).length < 2 ^ (prefixWord ++ tailWord_3541847).sum := by decide
  have hdescent : baseEnd_3541847 < baseStart_3541847 := by decide
  rcases family_descends (prefixWord ++ tailWord_3541847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3541856 : List Nat := [2, 1, 1, 3, 3, 1, 1, 1, 5, 4]
def baseStart_3541856 : Nat := 118140960795 + 3541856 * 2 ^ 59
def prefixEnd_3541856 : Nat := 4983230072969 + 3 ^ 40 * 3541856 * 2
def baseEnd_3541856 : Nat := 1212449691340666470540871

theorem tailTrace_3541856 : CollatzResearch.WordTrace tailWord_3541856 prefixEnd_3541856 1212449691340666470540871 := by
  unfold tailWord_3541856
  simp only [CollatzResearch.WordTrace]
  refine ⟨64591050528234043845646711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86121400704312058460862281 64591050528234043845646711)
  ·
    refine ⟨96886575792351065768470067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64591050528234043845646711 96886575792351065768470067)
    ·
      refine ⟨145329863688526598652705101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96886575792351065768470067 145329863688526598652705101)
      ·
        refine ⟨54498698883197474494764413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 145329863688526598652705101 54498698883197474494764413)
        ·
          refine ⟨20437012081199052935536655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54498698883197474494764413 20437012081199052935536655)
          ·
            refine ⟨30655518121798579403304983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20437012081199052935536655 30655518121798579403304983)
            ·
              refine ⟨45983277182697869104957475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30655518121798579403304983 45983277182697869104957475)
              ·
                refine ⟨68974915774046803657436213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45983277182697869104957475 68974915774046803657436213)
                ·
                  refine ⟨6466398353816887842884645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 68974915774046803657436213 6466398353816887842884645)
                  ·
                    refine ⟨1212449691340666470540871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6466398353816887842884645 1212449691340666470540871)
                    ·
                      rfl

theorem cell22_3541856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 1, 5, 4].length) (baseStart_3541856 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3541856 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3541856 prefixEnd_3541856 := by exact prefixLift 3541856
  have htrace : WordTrace (prefixWord ++ tailWord_3541856) baseStart_3541856 baseEnd_3541856 := by
    simpa [prefixWord, tailWord_3541856, baseEnd_3541856] using wordTrace_append hprefix tailTrace_3541856
  have hstable : (prefixWord ++ tailWord_3541856).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3541856).length < 2 ^ (prefixWord ++ tailWord_3541856).sum := by decide
  have hdescent : baseEnd_3541856 < baseStart_3541856 := by decide
  rcases family_descends (prefixWord ++ tailWord_3541856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3542023 : List Nat := [1, 1, 4, 3, 1, 1, 2, 3, 6]
def baseStart_3542023 : Nat := 118140960795 + 3542023 * 2 ^ 59
def prefixEnd_3542023 : Nat := 4983230072969 + 3 ^ 40 * 3542023 * 2
def baseEnd_3542023 : Nat := 404168952951177900538453

theorem tailTrace_3542023 : CollatzResearch.WordTrace tailWord_3542023 prefixEnd_3542023 404168952951177900538453 := by
  unfold tailWord_3542023
  simp only [CollatzResearch.WordTrace]
  refine ⟨129188192046863075212622723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86125461364575383475081815 129188192046863075212622723)
  ·
    refine ⟨193782288070294612818934085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129188192046863075212622723 193782288070294612818934085)
    ·
      refine ⟨36334179013180239903550141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 193782288070294612818934085 36334179013180239903550141)
      ·
        refine ⟨13625317129942589963831303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36334179013180239903550141 13625317129942589963831303)
        ·
          refine ⟨20437975694913884945746955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13625317129942589963831303 20437975694913884945746955)
          ·
            refine ⟨30656963542370827418620433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20437975694913884945746955 30656963542370827418620433)
            ·
              refine ⟨22992722656778120563965325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30656963542370827418620433 22992722656778120563965325)
              ·
                refine ⟨8622270996291795211486997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22992722656778120563965325 8622270996291795211486997)
                ·
                  refine ⟨404168952951177900538453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8622270996291795211486997 404168952951177900538453)
                  ·
                    rfl

theorem cell22_3542023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 3, 6].length) (baseStart_3542023 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3542023 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3542023 prefixEnd_3542023 := by exact prefixLift 3542023
  have htrace : WordTrace (prefixWord ++ tailWord_3542023) baseStart_3542023 baseEnd_3542023 := by
    simpa [prefixWord, tailWord_3542023, baseEnd_3542023] using wordTrace_append hprefix tailTrace_3542023
  have hstable : (prefixWord ++ tailWord_3542023).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3542023).length < 2 ^ (prefixWord ++ tailWord_3542023).sum := by decide
  have hdescent : baseEnd_3542023 < baseStart_3542023 := by decide
  rcases family_descends (prefixWord ++ tailWord_3542023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3542053 : List Nat := [1, 3, 1, 2, 2, 2, 3, 1, 1, 6]
def baseStart_3542053 : Nat := 118140960795 + 3542053 * 2 ^ 59
def prefixEnd_3542053 : Nat := 4983230072969 + 3 ^ 40 * 3542053 * 2
def baseEnd_3542053 : Nat := 1212517128466623623365267

theorem tailTrace_3542053 : CollatzResearch.WordTrace tailWord_3542053 prefixEnd_3542053 1212517128466623623365267 := by
  unfold tailWord_3542053
  simp only [CollatzResearch.WordTrace]
  refine ⟨129189286236754390336214813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86126190824502926890809875 129189286236754390336214813)
  ·
    refine ⟨48445982338782896376080555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129189286236754390336214813 48445982338782896376080555)
    ·
      refine ⟨72668973508174344564120833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48445982338782896376080555 72668973508174344564120833)
      ·
        refine ⟨54501730131130758423090625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72668973508174344564120833 54501730131130758423090625)
        ·
          refine ⟨40876297598348068817317969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54501730131130758423090625 40876297598348068817317969)
          ·
            refine ⟨30657223198761051612988477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40876297598348068817317969 30657223198761051612988477)
            ·
              refine ⟨11496458699535394354870679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30657223198761051612988477 11496458699535394354870679)
              ·
                refine ⟨17244688049303091532306019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11496458699535394354870679 17244688049303091532306019)
                ·
                  refine ⟨25867032073954637298459029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17244688049303091532306019 25867032073954637298459029)
                  ·
                    refine ⟨1212517128466623623365267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25867032073954637298459029 1212517128466623623365267)
                    ·
                      rfl

theorem cell22_3542053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 3, 1, 1, 6].length) (baseStart_3542053 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3542053 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3542053 prefixEnd_3542053 := by exact prefixLift 3542053
  have htrace : WordTrace (prefixWord ++ tailWord_3542053) baseStart_3542053 baseEnd_3542053 := by
    simpa [prefixWord, tailWord_3542053, baseEnd_3542053] using wordTrace_append hprefix tailTrace_3542053
  have hstable : (prefixWord ++ tailWord_3542053).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3542053).length < 2 ^ (prefixWord ++ tailWord_3542053).sum := by decide
  have hdescent : baseEnd_3542053 < baseStart_3542053 := by decide
  rcases family_descends (prefixWord ++ tailWord_3542053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3542072 : List Nat := [2, 1, 2, 1, 5, 1, 3, 2, 2, 3]
def baseStart_3542072 : Nat := 118140960795 + 3542072 * 2 ^ 59
def prefixEnd_3542072 : Nat := 4983230072969 + 3 ^ 40 * 3542072 * 2
def baseEnd_3542072 : Nat := 1212523632554913907140209

theorem tailTrace_3542072 : CollatzResearch.WordTrace tailWord_3542072 prefixEnd_3542072 1212523632554913907140209 := by
  unfold tailWord_3542072
  simp only [CollatzResearch.WordTrace]
  refine ⟨64594989611842778290578235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86126652815790371054104313 64594989611842778290578235)
  ·
    refine ⟨96892484417764167435867353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64594989611842778290578235 96892484417764167435867353)
    ·
      refine ⟨72669363313323125576900515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96892484417764167435867353 72669363313323125576900515)
      ·
        refine ⟨109004044969984688365350773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72669363313323125576900515 109004044969984688365350773)
        ·
          refine ⟨10219129215936064534251635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 109004044969984688365350773 10219129215936064534251635)
          ·
            refine ⟨15328693823904096801377453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10219129215936064534251635 15328693823904096801377453)
            ·
              refine ⟨5748260183964036300516545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15328693823904096801377453 5748260183964036300516545)
              ·
                refine ⟨4311195137973027225387409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5748260183964036300516545 4311195137973027225387409)
                ·
                  refine ⟨3233396353479770419040557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4311195137973027225387409 3233396353479770419040557)
                  ·
                    refine ⟨1212523632554913907140209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3233396353479770419040557 1212523632554913907140209)
                    ·
                      rfl

theorem cell22_3542072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 3, 2, 2, 3].length) (baseStart_3542072 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3542072 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3542072 prefixEnd_3542072 := by exact prefixLift 3542072
  have htrace : WordTrace (prefixWord ++ tailWord_3542072) baseStart_3542072 baseEnd_3542072 := by
    simpa [prefixWord, tailWord_3542072, baseEnd_3542072] using wordTrace_append hprefix tailTrace_3542072
  have hstable : (prefixWord ++ tailWord_3542072).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3542072).length < 2 ^ (prefixWord ++ tailWord_3542072).sum := by decide
  have hdescent : baseEnd_3542072 < baseStart_3542072 := by decide
  rcases family_descends (prefixWord ++ tailWord_3542072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3542113 : List Nat := [1, 2, 3, 1, 1, 2, 3, 2, 7]
def baseStart_3542113 : Nat := 118140960795 + 3542113 * 2 ^ 59
def prefixEnd_3542113 : Nat := 4983230072969 + 3 ^ 40 * 3542113 * 2
def baseEnd_3542113 : Nat := 404179222564267822288361

theorem tailTrace_3542113 : CollatzResearch.WordTrace tailWord_3542113 prefixEnd_3542113 404179222564267822288361 := by
  unfold tailWord_3542113
  simp only [CollatzResearch.WordTrace]
  refine ⟨129191474616537020583398993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86127649744358013722265995 129191474616537020583398993)
  ·
    refine ⟨96893605962402765437549245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129191474616537020583398993 96893605962402765437549245)
    ·
      refine ⟨36335102235901037039080967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96893605962402765437549245 36335102235901037039080967)
      ·
        refine ⟨54502653353851555558621451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36335102235901037039080967 54502653353851555558621451)
        ·
          refine ⟨81753980030777333337932177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54502653353851555558621451 81753980030777333337932177)
          ·
            refine ⟨61315485023083000003449133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81753980030777333337932177 61315485023083000003449133)
            ·
              refine ⟨22993306883656125001293425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61315485023083000003449133 22993306883656125001293425)
              ·
                refine ⟨17244980162742093750970069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22993306883656125001293425 17244980162742093750970069)
                ·
                  refine ⟨404179222564267822288361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17244980162742093750970069 404179222564267822288361)
                  ·
                    rfl

theorem cell22_3542113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 2, 7].length) (baseStart_3542113 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3542113 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3542113 prefixEnd_3542113 := by exact prefixLift 3542113
  have htrace : WordTrace (prefixWord ++ tailWord_3542113) baseStart_3542113 baseEnd_3542113 := by
    simpa [prefixWord, tailWord_3542113, baseEnd_3542113] using wordTrace_append hprefix tailTrace_3542113
  have hstable : (prefixWord ++ tailWord_3542113).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3542113).length < 2 ^ (prefixWord ++ tailWord_3542113).sum := by decide
  have hdescent : baseEnd_3542113 < baseStart_3542113 := by decide
  rcases family_descends (prefixWord ++ tailWord_3542113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3542130 : List Nat := [3, 2, 1, 2, 2, 1, 2, 4, 5]
def baseStart_3542130 : Nat := 118140960795 + 3542130 * 2 ^ 59
def prefixEnd_3542130 : Nat := 4983230072969 + 3 ^ 40 * 3542130 * 2
def baseEnd_3542130 : Nat := 404181162380073696396677

theorem tailTrace_3542130 : CollatzResearch.WordTrace tailWord_3542130 prefixEnd_3542130 404181162380073696396677 := by
  unfold tailWord_3542130
  simp only [CollatzResearch.WordTrace]
  refine ⟨32298023664368858121691961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86128063104983621657845229 32298023664368858121691961)
  ·
    refine ⟨24223517748276643591268971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32298023664368858121691961 24223517748276643591268971)
    ·
      refine ⟨36335276622414965386903457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24223517748276643591268971 36335276622414965386903457)
      ·
        refine ⟨27251457466811224040177593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36335276622414965386903457 27251457466811224040177593)
        ·
          refine ⟨20438593100108418030133195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27251457466811224040177593 20438593100108418030133195)
          ·
            refine ⟨30657889650162627045199793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20438593100108418030133195 30657889650162627045199793)
            ·
              refine ⟨22993417237621970283899845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30657889650162627045199793 22993417237621970283899845)
              ·
                refine ⟨4311265732054119428231221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22993417237621970283899845 4311265732054119428231221)
                ·
                  refine ⟨404181162380073696396677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4311265732054119428231221 404181162380073696396677)
                  ·
                    rfl

theorem cell22_3542130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 4, 5].length) (baseStart_3542130 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3542130 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3542130 prefixEnd_3542130 := by exact prefixLift 3542130
  have htrace : WordTrace (prefixWord ++ tailWord_3542130) baseStart_3542130 baseEnd_3542130 := by
    simpa [prefixWord, tailWord_3542130, baseEnd_3542130] using wordTrace_append hprefix tailTrace_3542130
  have hstable : (prefixWord ++ tailWord_3542130).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3542130).length < 2 ^ (prefixWord ++ tailWord_3542130).sum := by decide
  have hdescent : baseEnd_3542130 < baseStart_3542130 := by decide
  rcases family_descends (prefixWord ++ tailWord_3542130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3542160 : List Nat := [2, 1, 1, 1, 1, 1, 4, 6, 1, 4]
def baseStart_3542160 : Nat := 118140960795 + 3542160 * 2 ^ 59
def prefixEnd_3542160 : Nat := 4983230072969 + 3 ^ 40 * 3542160 * 2
def baseEnd_3542160 : Nat := 1212553756753311010939939

theorem tailTrace_3542160 : CollatzResearch.WordTrace tailWord_3542160 prefixEnd_3542160 1212553756753311010939939 := by
  unfold tailWord_3542160
  simp only [CollatzResearch.WordTrace]
  refine ⟨64596594423683373805179967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86128792564911165073573289 64596594423683373805179967)
  ·
    refine ⟨96894891635525060707769951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64596594423683373805179967 96894891635525060707769951)
    ·
      refine ⟨145342337453287591061654927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96894891635525060707769951 145342337453287591061654927)
      ·
        refine ⟨218013506179931386592482391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145342337453287591061654927 218013506179931386592482391)
        ·
          refine ⟨327020259269897079888723587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 218013506179931386592482391 327020259269897079888723587)
          ·
            refine ⟨490530388904845619833085381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 327020259269897079888723587 490530388904845619833085381)
            ·
              refine ⟨91974447919658553718703509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 490530388904845619833085381 91974447919658553718703509)
              ·
                refine ⟨4311302246233994705564227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 91974447919658553718703509 4311302246233994705564227)
                ·
                  refine ⟨6466953369350992058346341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4311302246233994705564227 6466953369350992058346341)
                  ·
                    refine ⟨1212553756753311010939939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6466953369350992058346341 1212553756753311010939939)
                    ·
                      rfl

theorem cell22_3542160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 6, 1, 4].length) (baseStart_3542160 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3542160 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3542160 prefixEnd_3542160 := by exact prefixLift 3542160
  have htrace : WordTrace (prefixWord ++ tailWord_3542160) baseStart_3542160 baseEnd_3542160 := by
    simpa [prefixWord, tailWord_3542160, baseEnd_3542160] using wordTrace_append hprefix tailTrace_3542160
  have hstable : (prefixWord ++ tailWord_3542160).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3542160).length < 2 ^ (prefixWord ++ tailWord_3542160).sum := by decide
  have hdescent : baseEnd_3542160 < baseStart_3542160 := by decide
  rcases family_descends (prefixWord ++ tailWord_3542160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3542203 : List Nat := [1, 1, 1, 1, 1, 2, 4, 11]
def baseStart_3542203 : Nat := 118140960795 + 3542203 * 2 ^ 59
def prefixEnd_3542203 : Nat := 4983230072969 + 3 ^ 40 * 3542203 * 2
def baseEnd_3542203 : Nat := 134729830725785914679423

theorem tailTrace_3542203 : CollatzResearch.WordTrace tailWord_3542203 prefixEnd_3542203 134729830725785914679423 := by
  unfold tailWord_3542203
  simp only [CollatzResearch.WordTrace]
  refine ⟨129194757186210965954175263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86129838124140643969450175 129194757186210965954175263)
  ·
    refine ⟨193792135779316448931262895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129194757186210965954175263 193792135779316448931262895)
    ·
      refine ⟨290688203668974673396894343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193792135779316448931262895 290688203668974673396894343)
      ·
        refine ⟨436032305503462010095341515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 290688203668974673396894343 436032305503462010095341515)
        ·
          refine ⟨654048458255193015143012273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 436032305503462010095341515 654048458255193015143012273)
          ·
            refine ⟨490536343691394761357259205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 654048458255193015143012273 490536343691394761357259205)
            ·
              refine ⟨91975564442136517754486101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 490536343691394761357259205 91975564442136517754486101)
              ·
                refine ⟨134729830725785914679423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 91975564442136517754486101 134729830725785914679423)
                ·
                  rfl

theorem cell22_3542203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 11].length) (baseStart_3542203 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3542203 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3542203 prefixEnd_3542203 := by exact prefixLift 3542203
  have htrace : WordTrace (prefixWord ++ tailWord_3542203) baseStart_3542203 baseEnd_3542203 := by
    simpa [prefixWord, tailWord_3542203, baseEnd_3542203] using wordTrace_append hprefix tailTrace_3542203
  have hstable : (prefixWord ++ tailWord_3542203).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3542203).length < 2 ^ (prefixWord ++ tailWord_3542203).sum := by decide
  have hdescent : baseEnd_3542203 < baseStart_3542203 := by decide
  rcases family_descends (prefixWord ++ tailWord_3542203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3542205 : List Nat := [1, 4, 1, 2, 1, 1, 2, 2, 4, 4]
def baseStart_3542205 : Nat := 118140960795 + 3542205 * 2 ^ 59
def prefixEnd_3542205 : Nat := 4983230072969 + 3 ^ 40 * 3542205 * 2
def baseEnd_3542205 : Nat := 1212569161172945893564801

theorem tailTrace_3542205 : CollatzResearch.WordTrace tailWord_3542205 prefixEnd_3542205 1212569161172945893564801 := by
  unfold tailWord_3542205
  simp only [CollatzResearch.WordTrace]
  refine ⟨129194830132203720295748069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86129886754802480197165379 129194830132203720295748069)
  ·
    refine ⟨24224030649788197555452763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 129194830132203720295748069 24224030649788197555452763)
    ·
      refine ⟨36336045974682296333179145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24224030649788197555452763 36336045974682296333179145)
      ·
        refine ⟨27252034481011722249884359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36336045974682296333179145 27252034481011722249884359)
        ·
          refine ⟨40878051721517583374826539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27252034481011722249884359 40878051721517583374826539)
          ·
            refine ⟨61317077582276375062239809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40878051721517583374826539 61317077582276375062239809)
            ·
              refine ⟨45987808186707281296679857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61317077582276375062239809 45987808186707281296679857)
              ·
                refine ⟨34490856140030460972509893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45987808186707281296679857 34490856140030460972509893)
                ·
                  refine ⟨6467035526255711432345605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34490856140030460972509893 6467035526255711432345605)
                  ·
                    refine ⟨1212569161172945893564801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6467035526255711432345605 1212569161172945893564801)
                    ·
                      rfl

theorem cell22_3542205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 2, 4, 4].length) (baseStart_3542205 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3542205 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3542205 prefixEnd_3542205 := by exact prefixLift 3542205
  have htrace : WordTrace (prefixWord ++ tailWord_3542205) baseStart_3542205 baseEnd_3542205 := by
    simpa [prefixWord, tailWord_3542205, baseEnd_3542205] using wordTrace_append hprefix tailTrace_3542205
  have hstable : (prefixWord ++ tailWord_3542205).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3542205).length < 2 ^ (prefixWord ++ tailWord_3542205).sum := by decide
  have hdescent : baseEnd_3542205 < baseStart_3542205 := by decide
  rcases family_descends (prefixWord ++ tailWord_3542205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3542207 : List Nat := [1, 1, 2, 2, 2, 2, 4, 3, 2, 3]
def baseStart_3542207 : Nat := 118140960795 + 3542207 * 2 ^ 59
def prefixEnd_3542207 : Nat := 4983230072969 + 3 ^ 40 * 3542207 * 2
def baseEnd_3542207 : Nat := 1212569845813818555014795

theorem tailTrace_3542207 : CollatzResearch.WordTrace tailWord_3542207 prefixEnd_3542207 1212569845813818555014795 := by
  unfold tailWord_3542207
  simp only [CollatzResearch.WordTrace]
  refine ⟨129194903078196474637320875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86129935385464316424880583 129194903078196474637320875)
  ·
    refine ⟨193792354617294711955981313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129194903078196474637320875 193792354617294711955981313)
    ·
      refine ⟨145344265962971033966985985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193792354617294711955981313 145344265962971033966985985)
      ·
        refine ⟨109008199472228275475239489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145344265962971033966985985 109008199472228275475239489)
        ·
          refine ⟨81756149604171206606429617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109008199472228275475239489 81756149604171206606429617)
          ·
            refine ⟨61317112203128404954822213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81756149604171206606429617 61317112203128404954822213)
            ·
              refine ⟨11496958538086575929029165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 61317112203128404954822213 11496958538086575929029165)
              ·
                refine ⟨4311359451782465973385937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11496958538086575929029165 4311359451782465973385937)
                ·
                  refine ⟨3233519588836849480039453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4311359451782465973385937 3233519588836849480039453)
                  ·
                    refine ⟨1212569845813818555014795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3233519588836849480039453 1212569845813818555014795)
                    ·
                      rfl

theorem cell22_3542207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 4, 3, 2, 3].length) (baseStart_3542207 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3542207 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3542207 prefixEnd_3542207 := by exact prefixLift 3542207
  have htrace : WordTrace (prefixWord ++ tailWord_3542207) baseStart_3542207 baseEnd_3542207 := by
    simpa [prefixWord, tailWord_3542207, baseEnd_3542207] using wordTrace_append hprefix tailTrace_3542207
  have hstable : (prefixWord ++ tailWord_3542207).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3542207).length < 2 ^ (prefixWord ++ tailWord_3542207).sum := by decide
  have hdescent : baseEnd_3542207 < baseStart_3542207 := by decide
  rcases family_descends (prefixWord ++ tailWord_3542207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3542222 : List Nat := [4, 1, 1, 1, 5, 1, 1, 1, 1, 6]
def baseStart_3542222 : Nat := 118140960795 + 3542222 * 2 ^ 59
def prefixEnd_3542222 : Nat := 4983230072969 + 3 ^ 40 * 3542222 * 2
def baseEnd_3542222 : Nat := 1212574980620363515889749

theorem tailTrace_3542222 : CollatzResearch.WordTrace tailWord_3542222 prefixEnd_3542222 1212574980620363515889749 := by
  unfold tailWord_3542222
  simp only [CollatzResearch.WordTrace]
  refine ⟨16149431271642766524889615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 86130300115428088132744613 16149431271642766524889615)
  ·
    refine ⟨24224146907464149787334423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16149431271642766524889615 24224146907464149787334423)
    ·
      refine ⟨36336220361196224681001635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24224146907464149787334423 36336220361196224681001635)
      ·
        refine ⟨54504330541794337021502453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36336220361196224681001635 54504330541794337021502453)
        ·
          refine ⟨5109780988293219095765855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 54504330541794337021502453 5109780988293219095765855)
          ·
            refine ⟨7664671482439828643648783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5109780988293219095765855 7664671482439828643648783)
            ·
              refine ⟨11497007223659742965473175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7664671482439828643648783 11497007223659742965473175)
              ·
                refine ⟨17245510835489614448209763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11497007223659742965473175 17245510835489614448209763)
                ·
                  refine ⟨25868266253234421672314645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17245510835489614448209763 25868266253234421672314645)
                  ·
                    refine ⟨1212574980620363515889749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25868266253234421672314645 1212574980620363515889749)
                    ·
                      rfl

theorem cell22_3542222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 1, 1, 1, 6].length) (baseStart_3542222 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3542222 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3542222 prefixEnd_3542222 := by exact prefixLift 3542222
  have htrace : WordTrace (prefixWord ++ tailWord_3542222) baseStart_3542222 baseEnd_3542222 := by
    simpa [prefixWord, tailWord_3542222, baseEnd_3542222] using wordTrace_append hprefix tailTrace_3542222
  have hstable : (prefixWord ++ tailWord_3542222).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3542222).length < 2 ^ (prefixWord ++ tailWord_3542222).sum := by decide
  have hdescent : baseEnd_3542222 < baseStart_3542222 := by decide
  rcases family_descends (prefixWord ++ tailWord_3542222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3542228 : List Nat := [2, 4, 1, 4, 1, 2, 2, 1, 1, 4]
def baseStart_3542228 : Nat := 118140960795 + 3542228 * 2 ^ 59
def prefixEnd_3542228 : Nat := 4983230072969 + 3 ^ 40 * 3542228 * 2
def baseEnd_3542228 : Nat := 1212577034542981500239731

theorem tailTrace_3542228 : CollatzResearch.WordTrace tailWord_3542228 prefixEnd_3542228 1212577034542981500239731 := by
  unfold tailWord_3542228
  simp only [CollatzResearch.WordTrace]
  refine ⟨64597834505560197611917669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86130446007413596815890225 64597834505560197611917669)
  ·
    refine ⟨12112093969792537052234563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 64597834505560197611917669 12112093969792537052234563)
    ·
      refine ⟨18168140954688805578351845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12112093969792537052234563 18168140954688805578351845)
      ·
        refine ⟨3406526429004151045940971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18168140954688805578351845 3406526429004151045940971)
        ·
          refine ⟨5109789643506226568911457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3406526429004151045940971 5109789643506226568911457)
          ·
            refine ⟨3832342232629669926683593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5109789643506226568911457 3832342232629669926683593)
            ·
              refine ⟨2874256674472252445012695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3832342232629669926683593 2874256674472252445012695)
              ·
                refine ⟨4311385011708378667519043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2874256674472252445012695 4311385011708378667519043)
                ·
                  refine ⟨6467077517562568001278565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4311385011708378667519043 6467077517562568001278565)
                  ·
                    refine ⟨1212577034542981500239731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6467077517562568001278565 1212577034542981500239731)
                    ·
                      rfl

theorem cell22_3542228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 2, 2, 1, 1, 4].length) (baseStart_3542228 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3542228 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3542228 prefixEnd_3542228 := by exact prefixLift 3542228
  have htrace : WordTrace (prefixWord ++ tailWord_3542228) baseStart_3542228 baseEnd_3542228 := by
    simpa [prefixWord, tailWord_3542228, baseEnd_3542228] using wordTrace_append hprefix tailTrace_3542228
  have hstable : (prefixWord ++ tailWord_3542228).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3542228).length < 2 ^ (prefixWord ++ tailWord_3542228).sum := by decide
  have hdescent : baseEnd_3542228 < baseStart_3542228 := by decide
  rcases family_descends (prefixWord ++ tailWord_3542228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3542237 : List Nat := [1, 4, 3, 2, 2, 1, 9]
def baseStart_3542237 : Nat := 118140960795 + 3542237 * 2 ^ 59
def prefixEnd_3542237 : Nat := 4983230072969 + 3 ^ 40 * 3542237 * 2
def baseEnd_3542237 : Nat := 44910374645441054694989

theorem tailTrace_3542237 : CollatzResearch.WordTrace tailWord_3542237 prefixEnd_3542237 44910374645441054694989 := by
  unfold tailWord_3542237
  simp only [CollatzResearch.WordTrace]
  refine ⟨129195997268087789760912965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86130664845391859840608643 129195997268087789760912965)
  ·
    refine ⟨24224249487766460580171181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 129195997268087789760912965 24224249487766460580171181)
    ·
      refine ⟨9084093557912422717564193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24224249487766460580171181 9084093557912422717564193)
      ·
        refine ⟨6813070168434317038173145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9084093557912422717564193 6813070168434317038173145)
        ·
          refine ⟨5109802626325737778629859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6813070168434317038173145 5109802626325737778629859)
          ·
            refine ⟨7664703939488606667944789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5109802626325737778629859 7664703939488606667944789)
            ·
              refine ⟨44910374645441054694989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7664703939488606667944789 44910374645441054694989)
              ·
                rfl

theorem cell22_3542237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 9].length) (baseStart_3542237 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3542237 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3542237 prefixEnd_3542237 := by exact prefixLift 3542237
  have htrace : WordTrace (prefixWord ++ tailWord_3542237) baseStart_3542237 baseEnd_3542237 := by
    simpa [prefixWord, tailWord_3542237, baseEnd_3542237] using wordTrace_append hprefix tailTrace_3542237
  have hstable : (prefixWord ++ tailWord_3542237).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3542237).length < 2 ^ (prefixWord ++ tailWord_3542237).sum := by decide
  have hdescent : baseEnd_3542237 < baseStart_3542237 := by decide
  rcases family_descends (prefixWord ++ tailWord_3542237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3542252 : List Nat := [2, 2, 1, 1, 2, 4, 1, 3, 3, 3]
def baseStart_3542252 : Nat := 118140960795 + 3542252 * 2 ^ 59
def prefixEnd_3542252 : Nat := 4983230072969 + 3 ^ 40 * 3542252 * 2
def baseEnd_3542252 : Nat := 1212585250233453437639657

theorem tailTrace_3542252 : CollatzResearch.WordTrace tailWord_3542252 prefixEnd_3542252 1212585250233453437639657 := by
  unfold tailWord_3542252
  simp only [CollatzResearch.WordTrace]
  refine ⟨64598272181516723661354505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86131029575355631548472673 64598272181516723661354505)
  ·
    refine ⟨48448704136137542746015879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64598272181516723661354505 48448704136137542746015879)
    ·
      refine ⟨72673056204206314119023819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48448704136137542746015879 72673056204206314119023819)
      ·
        refine ⟨109009584306309471178535729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72673056204206314119023819 109009584306309471178535729)
        ·
          refine ⟨81757188229732103383901797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109009584306309471178535729 81757188229732103383901797)
          ·
            refine ⟨15329472793074769384481587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 81757188229732103383901797 15329472793074769384481587)
            ·
              refine ⟨22994209189612154076722381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15329472793074769384481587 22994209189612154076722381)
              ·
                refine ⟨8622828446104557778770893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22994209189612154076722381 8622828446104557778770893)
                ·
                  refine ⟨3233560667289209167039085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8622828446104557778770893 3233560667289209167039085)
                  ·
                    refine ⟨1212585250233453437639657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3233560667289209167039085 1212585250233453437639657)
                    ·
                      rfl

theorem cell22_3542252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 3, 3].length) (baseStart_3542252 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3542252 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3542252 prefixEnd_3542252 := by exact prefixLift 3542252
  have htrace : WordTrace (prefixWord ++ tailWord_3542252) baseStart_3542252 baseEnd_3542252 := by
    simpa [prefixWord, tailWord_3542252, baseEnd_3542252] using wordTrace_append hprefix tailTrace_3542252
  have hstable : (prefixWord ++ tailWord_3542252).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3542252).length < 2 ^ (prefixWord ++ tailWord_3542252).sum := by decide
  have hdescent : baseEnd_3542252 < baseStart_3542252 := by decide
  rcases family_descends (prefixWord ++ tailWord_3542252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3542286 : List Nat := [4, 1, 1, 2, 1, 3, 3, 3, 1, 3]
def baseStart_3542286 : Nat := 118140960795 + 3542286 * 2 ^ 59
def prefixEnd_3542286 : Nat := 4983230072969 + 3 ^ 40 * 3542286 * 2
def baseEnd_3542286 : Nat := 1212596889128288682289553

theorem tailTrace_3542286 : CollatzResearch.WordTrace tailWord_3542286 prefixEnd_3542286 1212596889128288682289553 := by
  unfold tailWord_3542286
  simp only [CollatzResearch.WordTrace]
  refine ⟨16149723055613783891180839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 86131856296606847419631141 16149723055613783891180839)
  ·
    refine ⟨24224584583420675836771259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16149723055613783891180839 24224584583420675836771259)
    ·
      refine ⟨36336876875131013755156889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24224584583420675836771259 36336876875131013755156889)
      ·
        refine ⟨27252657656348260316367667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36336876875131013755156889 27252657656348260316367667)
        ·
          refine ⟨40878986484522390474551501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27252657656348260316367667 40878986484522390474551501)
          ·
            refine ⟨15329619931695896427956813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40878986484522390474551501 15329619931695896427956813)
            ·
              refine ⟨5748607474385961160483805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15329619931695896427956813 5748607474385961160483805)
              ·
                refine ⟨2155727802894735435181427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5748607474385961160483805 2155727802894735435181427)
                ·
                  refine ⟨3233591704342103152772141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2155727802894735435181427 3233591704342103152772141)
                  ·
                    refine ⟨1212596889128288682289553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3233591704342103152772141 1212596889128288682289553)
                    ·
                      rfl

theorem cell22_3542286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 3, 3, 1, 3].length) (baseStart_3542286 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3542286 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3542286 prefixEnd_3542286 := by exact prefixLift 3542286
  have htrace : WordTrace (prefixWord ++ tailWord_3542286) baseStart_3542286 baseEnd_3542286 := by
    simpa [prefixWord, tailWord_3542286, baseEnd_3542286] using wordTrace_append hprefix tailTrace_3542286
  have hstable : (prefixWord ++ tailWord_3542286).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3542286).length < 2 ^ (prefixWord ++ tailWord_3542286).sum := by decide
  have hdescent : baseEnd_3542286 < baseStart_3542286 := by decide
  rcases family_descends (prefixWord ++ tailWord_3542286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3542303 : List Nat := [1, 1, 2, 4, 4, 1, 3, 2, 1, 3]
def baseStart_3542303 : Nat := 118140960795 + 3542303 * 2 ^ 59
def prefixEnd_3542303 : Nat := 4983230072969 + 3 ^ 40 * 3542303 * 2
def baseEnd_3542303 : Nat := 1212602708575706304614501

theorem tailTrace_3542303 : CollatzResearch.WordTrace tailWord_3542303 prefixEnd_3542303 1212602708575706304614501 := by
  unfold tailWord_3542303
  simp only [CollatzResearch.WordTrace]
  refine ⟨129198404485848683032815563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86132269657232455355210375 129198404485848683032815563)
  ·
    refine ⟨193797606728773024549223345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129198404485848683032815563 193797606728773024549223345)
    ·
      refine ⟨145348205046579768411917509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193797606728773024549223345 145348205046579768411917509)
      ·
        refine ⟨27252788446233706577234533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 145348205046579768411917509 27252788446233706577234533)
        ·
          refine ⟨5109897833668819983231475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27252788446233706577234533 5109897833668819983231475)
          ·
            refine ⟨7664846750503229974847213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5109897833668819983231475 7664846750503229974847213)
            ·
              refine ⟨2874317531438711240567705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7664846750503229974847213 2874317531438711240567705)
              ·
                refine ⟨2155738148579033430425779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2874317531438711240567705 2155738148579033430425779)
                ·
                  refine ⟨3233607222868550145638669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2155738148579033430425779 3233607222868550145638669)
                  ·
                    refine ⟨1212602708575706304614501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3233607222868550145638669 1212602708575706304614501)
                    ·
                      rfl

theorem cell22_3542303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 3, 2, 1, 3].length) (baseStart_3542303 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3542303 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3542303 prefixEnd_3542303 := by exact prefixLift 3542303
  have htrace : WordTrace (prefixWord ++ tailWord_3542303) baseStart_3542303 baseEnd_3542303 := by
    simpa [prefixWord, tailWord_3542303, baseEnd_3542303] using wordTrace_append hprefix tailTrace_3542303
  have hstable : (prefixWord ++ tailWord_3542303).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3542303).length < 2 ^ (prefixWord ++ tailWord_3542303).sum := by decide
  have hdescent : baseEnd_3542303 < baseStart_3542303 := by decide
  rcases family_descends (prefixWord ++ tailWord_3542303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3542329 : List Nat := [1, 2, 1, 6, 2, 1, 1, 1, 3, 4]
def baseStart_3542329 : Nat := 118140960795 + 3542329 * 2 ^ 59
def prefixEnd_3542329 : Nat := 4983230072969 + 3 ^ 40 * 3542329 * 2
def baseEnd_3542329 : Nat := 1212611608907050903464421

theorem tailTrace_3542329 : CollatzResearch.WordTrace tailWord_3542329 prefixEnd_3542329 1212611608907050903464421 := by
  unfold tailWord_3542329
  simp only [CollatzResearch.WordTrace]
  refine ⟨129199352783754489473262041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86132901855836326315508027 129199352783754489473262041)
  ·
    refine ⟨96899514587815867104946531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129199352783754489473262041 96899514587815867104946531)
    ·
      refine ⟨145349271881723800657419797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96899514587815867104946531 145349271881723800657419797)
      ·
        refine ⟨6813247119455803155816553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 145349271881723800657419797 6813247119455803155816553)
        ·
          refine ⟨5109935339591852366862415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6813247119455803155816553 5109935339591852366862415)
          ·
            refine ⟨7664903009387778550293623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5109935339591852366862415 7664903009387778550293623)
            ·
              refine ⟨11497354514081667825440435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7664903009387778550293623 11497354514081667825440435)
              ·
                refine ⟨17246031771122501738160653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11497354514081667825440435 17246031771122501738160653)
                ·
                  refine ⟨6467261914170938151810245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17246031771122501738160653 6467261914170938151810245)
                  ·
                    refine ⟨1212611608907050903464421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6467261914170938151810245 1212611608907050903464421)
                    ·
                      rfl

theorem cell22_3542329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 1, 1, 3, 4].length) (baseStart_3542329 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3542329 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3542329 prefixEnd_3542329 := by exact prefixLift 3542329
  have htrace : WordTrace (prefixWord ++ tailWord_3542329) baseStart_3542329 baseEnd_3542329 := by
    simpa [prefixWord, tailWord_3542329, baseEnd_3542329] using wordTrace_append hprefix tailTrace_3542329
  have hstable : (prefixWord ++ tailWord_3542329).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3542329).length < 2 ^ (prefixWord ++ tailWord_3542329).sum := by decide
  have hdescent : baseEnd_3542329 < baseStart_3542329 := by decide
  rcases family_descends (prefixWord ++ tailWord_3542329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3542359 : List Nat := [1, 1, 3, 2, 3, 2, 1, 4, 2, 3]
def baseStart_3542359 : Nat := 118140960795 + 3542359 * 2 ^ 59
def prefixEnd_3542359 : Nat := 4983230072969 + 3 ^ 40 * 3542359 * 2
def baseEnd_3542359 : Nat := 1212621878520140825214329

theorem tailTrace_3542359 : CollatzResearch.WordTrace tailWord_3542359 prefixEnd_3542359 1212621878520140825214329 := by
  unfold tailWord_3542359
  simp only [CollatzResearch.WordTrace]
  refine ⟨129200446973645804596854131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86133631315763869731236087 129200446973645804596854131)
  ·
    refine ⟨193800670460468706895281197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129200446973645804596854131 193800670460468706895281197)
    ·
      refine ⟨72675251422675765085730449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 193800670460468706895281197 72675251422675765085730449)
      ·
        refine ⟨54506438567006823814297837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72675251422675765085730449 54506438567006823814297837)
        ·
          refine ⟨20439914462627558930361689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54506438567006823814297837 20439914462627558930361689)
          ·
            refine ⟨15329935846970669197771267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20439914462627558930361689 15329935846970669197771267)
            ·
              refine ⟨22994903770456003796656901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15329935846970669197771267 22994903770456003796656901)
              ·
                refine ⟨4311544456960500711873169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22994903770456003796656901 4311544456960500711873169)
                ·
                  refine ⟨3233658342720375533904877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4311544456960500711873169 3233658342720375533904877)
                  ·
                    refine ⟨1212621878520140825214329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3233658342720375533904877 1212621878520140825214329)
                    ·
                      rfl

theorem cell22_3542359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 4, 2, 3].length) (baseStart_3542359 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3542359 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3542359 prefixEnd_3542359 := by exact prefixLift 3542359
  have htrace : WordTrace (prefixWord ++ tailWord_3542359) baseStart_3542359 baseEnd_3542359 := by
    simpa [prefixWord, tailWord_3542359, baseEnd_3542359] using wordTrace_append hprefix tailTrace_3542359
  have hstable : (prefixWord ++ tailWord_3542359).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3542359).length < 2 ^ (prefixWord ++ tailWord_3542359).sum := by decide
  have hdescent : baseEnd_3542359 < baseStart_3542359 := by decide
  rcases family_descends (prefixWord ++ tailWord_3542359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3542372 : List Nat := [2, 3, 1, 1, 3, 2, 3, 7]
def baseStart_3542372 : Nat := 118140960795 + 3542372 * 2 ^ 59
def prefixEnd_3542372 : Nat := 4983230072969 + 3 ^ 40 * 3542372 * 2
def baseEnd_3542372 : Nat := 134736258742868124959921

theorem tailTrace_3542372 : CollatzResearch.WordTrace tailWord_3542372 prefixEnd_3542372 134736258742868124959921 := by
  unfold tailWord_3542372
  simp only [CollatzResearch.WordTrace]
  refine ⟨64600460561299353908538685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86133947415065805211384913 64600460561299353908538685)
  ·
    refine ⟨24225172710487257715702007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64600460561299353908538685 24225172710487257715702007)
    ·
      refine ⟨36337759065730886573553011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24225172710487257715702007 36337759065730886573553011)
      ·
        refine ⟨54506638598596329860329517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36337759065730886573553011 54506638598596329860329517)
        ·
          refine ⟨20439989474473623697623569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54506638598596329860329517 20439989474473623697623569)
          ·
            refine ⟨15329992105855217773217677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20439989474473623697623569 15329992105855217773217677)
            ·
              refine ⟨5748747039695706664956629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15329992105855217773217677 5748747039695706664956629)
              ·
                refine ⟨134736258742868124959921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5748747039695706664956629 134736258742868124959921)
                ·
                  rfl

theorem cell22_3542372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 3, 7].length) (baseStart_3542372 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3542372 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3542372 prefixEnd_3542372 := by exact prefixLift 3542372
  have htrace : WordTrace (prefixWord ++ tailWord_3542372) baseStart_3542372 baseEnd_3542372 := by
    simpa [prefixWord, tailWord_3542372, baseEnd_3542372] using wordTrace_append hprefix tailTrace_3542372
  have hstable : (prefixWord ++ tailWord_3542372).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3542372).length < 2 ^ (prefixWord ++ tailWord_3542372).sum := by decide
  have hdescent : baseEnd_3542372 < baseStart_3542372 := by decide
  rcases family_descends (prefixWord ++ tailWord_3542372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3542421 : List Nat := [1, 3, 2, 1, 1, 2, 4, 4, 1, 3]
def baseStart_3542421 : Nat := 118140960795 + 3542421 * 2 ^ 59
def prefixEnd_3542421 : Nat := 4983230072969 + 3 ^ 40 * 3542421 * 2
def baseEnd_3542421 : Nat := 1212643102387193330164139

theorem tailTrace_3542421 : CollatzResearch.WordTrace tailWord_3542421 prefixEnd_3542421 1212643102387193330164139 := by
  unfold tailWord_3542421
  simp only [CollatzResearch.WordTrace]
  refine ⟨129202708299421189185611117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86135138866280792790407411 129202708299421189185611117)
  ·
    refine ⟨48451015612282945944604169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129202708299421189185611117 48451015612282945944604169)
    ·
      refine ⟨36338261709212209458453127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48451015612282945944604169 36338261709212209458453127)
      ·
        refine ⟨54507392563818314187679691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36338261709212209458453127 54507392563818314187679691)
        ·
          refine ⟨81761088845727471281519537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54507392563818314187679691 81761088845727471281519537)
          ·
            refine ⟨61320816634295603461139653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81761088845727471281519537 61320816634295603461139653)
            ·
              refine ⟨11497653118930425648963685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 61320816634295603461139653 11497653118930425648963685)
              ·
                refine ⟨2155809959799454809180691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11497653118930425648963685 2155809959799454809180691)
                ·
                  refine ⟨3233714939699182213771037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2155809959799454809180691 3233714939699182213771037)
                  ·
                    refine ⟨1212643102387193330164139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3233714939699182213771037 1212643102387193330164139)
                    ·
                      rfl

theorem cell22_3542421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 4, 4, 1, 3].length) (baseStart_3542421 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3542421 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3542421 prefixEnd_3542421 := by exact prefixLift 3542421
  have htrace : WordTrace (prefixWord ++ tailWord_3542421) baseStart_3542421 baseEnd_3542421 := by
    simpa [prefixWord, tailWord_3542421, baseEnd_3542421] using wordTrace_append hprefix tailTrace_3542421
  have hstable : (prefixWord ++ tailWord_3542421).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3542421).length < 2 ^ (prefixWord ++ tailWord_3542421).sum := by decide
  have hdescent : baseEnd_3542421 < baseStart_3542421 := by decide
  rcases family_descends (prefixWord ++ tailWord_3542421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3542432 : List Nat := [2, 1, 1, 4, 1, 2, 1, 3, 2, 5]
def baseStart_3542432 : Nat := 118140960795 + 3542432 * 2 ^ 59
def prefixEnd_3542432 : Nat := 4983230072969 + 3 ^ 40 * 3542432 * 2
def baseEnd_3542432 : Nat := 1212646867911992968139105

theorem tailTrace_3542432 : CollatzResearch.WordTrace tailWord_3542432 prefixEnd_3542432 1212646867911992968139105 := by
  unfold tailWord_3542432
  simp only [CollatzResearch.WordTrace]
  refine ⟨64601554751190669032130775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86135406334920892042841033 64601554751190669032130775)
  ·
    refine ⟨96902332126786003548196163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64601554751190669032130775 96902332126786003548196163)
    ·
      refine ⟨145353498190179005322294245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96902332126786003548196163 145353498190179005322294245)
      ·
        refine ⟨27253780910658563497930171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 145353498190179005322294245 27253780910658563497930171)
        ·
          refine ⟨40880671365987845246895257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27253780910658563497930171 40880671365987845246895257)
          ·
            refine ⟨30660503524490883935171443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40880671365987845246895257 30660503524490883935171443)
            ·
              refine ⟨45990755286736325902757165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30660503524490883935171443 45990755286736325902757165)
              ·
                refine ⟨17246533232526122213533937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45990755286736325902757165 17246533232526122213533937)
                ·
                  refine ⟨12934899924394591660150453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17246533232526122213533937 12934899924394591660150453)
                  ·
                    refine ⟨1212646867911992968139105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12934899924394591660150453 1212646867911992968139105)
                    ·
                      rfl

theorem cell22_3542432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 3, 2, 5].length) (baseStart_3542432 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3542432 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3542432 prefixEnd_3542432 := by exact prefixLift 3542432
  have htrace : WordTrace (prefixWord ++ tailWord_3542432) baseStart_3542432 baseEnd_3542432 := by
    simpa [prefixWord, tailWord_3542432, baseEnd_3542432] using wordTrace_append hprefix tailTrace_3542432
  have hstable : (prefixWord ++ tailWord_3542432).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3542432).length < 2 ^ (prefixWord ++ tailWord_3542432).sum := by decide
  have hdescent : baseEnd_3542432 < baseStart_3542432 := by decide
  rcases family_descends (prefixWord ++ tailWord_3542432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3542447 : List Nat := [1, 1, 2, 1, 2, 2, 1, 5, 3, 4]
def baseStart_3542447 : Nat := 118140960795 + 3542447 * 2 ^ 59
def prefixEnd_3542447 : Nat := 4983230072969 + 3 ^ 40 * 3542447 * 2
def baseEnd_3542447 : Nat := 1212652002718537929014059

theorem tailTrace_3542447 : CollatzResearch.WordTrace tailWord_3542447 prefixEnd_3542447 1212652002718537929014059 := by
  unfold tailWord_3542447
  simp only [CollatzResearch.WordTrace]
  refine ⟨129203656597326995626057595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86135771064884663750705063 129203656597326995626057595)
  ·
    refine ⟨193805484895990493439086393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129203656597326995626057595 193805484895990493439086393)
    ·
      refine ⟨145354113671992870079314795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193805484895990493439086393 145354113671992870079314795)
      ·
        refine ⟨218031170507989305118972193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145354113671992870079314795 218031170507989305118972193)
        ·
          refine ⟨163523377880991978839229145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 218031170507989305118972193 163523377880991978839229145)
          ·
            refine ⟨122642533410743984129421859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 163523377880991978839229145 122642533410743984129421859)
            ·
              refine ⟨183963800116115976194132789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122642533410743984129421859 183963800116115976194132789)
              ·
                refine ⟨17246606260885872768199949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 183963800116115976194132789 17246606260885872768199949)
                ·
                  refine ⟨6467477347832202288074981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17246606260885872768199949 6467477347832202288074981)
                  ·
                    refine ⟨1212652002718537929014059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6467477347832202288074981 1212652002718537929014059)
                    ·
                      rfl

theorem cell22_3542447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 5, 3, 4].length) (baseStart_3542447 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3542447 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3542447 prefixEnd_3542447 := by exact prefixLift 3542447
  have htrace : WordTrace (prefixWord ++ tailWord_3542447) baseStart_3542447 baseEnd_3542447 := by
    simpa [prefixWord, tailWord_3542447, baseEnd_3542447] using wordTrace_append hprefix tailTrace_3542447
  have hstable : (prefixWord ++ tailWord_3542447).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3542447).length < 2 ^ (prefixWord ++ tailWord_3542447).sum := by decide
  have hdescent : baseEnd_3542447 < baseStart_3542447 := by decide
  rcases family_descends (prefixWord ++ tailWord_3542447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3542464 : List Nat := [2, 1, 1, 2, 3, 1, 4, 3, 1, 4]
def baseStart_3542464 : Nat := 118140960795 + 3542464 * 2 ^ 59
def prefixEnd_3542464 : Nat := 4983230072969 + 3 ^ 40 * 3542464 * 2
def baseEnd_3542464 : Nat := 1212657822165955551339007

theorem tailTrace_3542464 : CollatzResearch.WordTrace tailWord_3542464 prefixEnd_3542464 1212657822165955551339007 := by
  unfold tailWord_3542464
  simp only [CollatzResearch.WordTrace]
  refine ⟨64602138319132703764713223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86136184425510271686284297 64602138319132703764713223)
  ·
    refine ⟨96903207478699055647069835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64602138319132703764713223 96903207478699055647069835)
    ·
      refine ⟨145354811218048583470604753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96903207478699055647069835 145354811218048583470604753)
      ·
        refine ⟨109016108413536437602953565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145354811218048583470604753 109016108413536437602953565)
        ·
          refine ⟨40881040655076164101107587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 109016108413536437602953565 40881040655076164101107587)
          ·
            refine ⟨61321560982614246151661381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40881040655076164101107587 61321560982614246151661381)
            ·
              refine ⟨11497792684240171153436509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 61321560982614246151661381 11497792684240171153436509)
              ·
                refine ⟨4311672256590064182538691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11497792684240171153436509 4311672256590064182538691)
                ·
                  refine ⟨6467508384885096273808037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4311672256590064182538691 6467508384885096273808037)
                  ·
                    refine ⟨1212657822165955551339007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6467508384885096273808037 1212657822165955551339007)
                    ·
                      rfl

theorem cell22_3542464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 4, 3, 1, 4].length) (baseStart_3542464 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3542464 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3542464 prefixEnd_3542464 := by exact prefixLift 3542464
  have htrace : WordTrace (prefixWord ++ tailWord_3542464) baseStart_3542464 baseEnd_3542464 := by
    simpa [prefixWord, tailWord_3542464, baseEnd_3542464] using wordTrace_append hprefix tailTrace_3542464
  have hstable : (prefixWord ++ tailWord_3542464).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3542464).length < 2 ^ (prefixWord ++ tailWord_3542464).sum := by decide
  have hdescent : baseEnd_3542464 < baseStart_3542464 := by decide
  rcases family_descends (prefixWord ++ tailWord_3542464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3542479 : List Nat := [1, 1, 2, 1, 1, 4, 2, 6, 4]
def baseStart_3542479 : Nat := 118140960795 + 3542479 * 2 ^ 59
def prefixEnd_3542479 : Nat := 4983230072969 + 3 ^ 40 * 3542479 * 2
def baseEnd_3542479 : Nat := 404220985657500170737987

theorem tailTrace_3542479 : CollatzResearch.WordTrace tailWord_3542479 prefixEnd_3542479 404220985657500170737987 := by
  unfold tailWord_3542479
  simp only [CollatzResearch.WordTrace]
  refine ⟨129204823733211065091222491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86136549155474043394148327 129204823733211065091222491)
  ·
    refine ⟨193807235599816597636833737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129204823733211065091222491 193807235599816597636833737)
    ·
      refine ⟨145355426699862448227625303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193807235599816597636833737 145355426699862448227625303)
      ·
        refine ⟨218033140049793672341437955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145355426699862448227625303 218033140049793672341437955)
        ·
          refine ⟨327049710074690508512156933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 218033140049793672341437955 327049710074690508512156933)
          ·
            refine ⟨61321820639004470346029425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 327049710074690508512156933 61321820639004470346029425)
            ·
              refine ⟨45991365479253352759522069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61321820639004470346029425 45991365479253352759522069)
              ·
                refine ⟨2155845256840000910602597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 45991365479253352759522069 2155845256840000910602597)
                ·
                  refine ⟨404220985657500170737987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2155845256840000910602597 404220985657500170737987)
                  ·
                    rfl

theorem cell22_3542479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 6, 4].length) (baseStart_3542479 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3542479 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3542479 prefixEnd_3542479 := by exact prefixLift 3542479
  have htrace : WordTrace (prefixWord ++ tailWord_3542479) baseStart_3542479 baseEnd_3542479 := by
    simpa [prefixWord, tailWord_3542479, baseEnd_3542479] using wordTrace_append hprefix tailTrace_3542479
  have hstable : (prefixWord ++ tailWord_3542479).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3542479).length < 2 ^ (prefixWord ++ tailWord_3542479).sum := by decide
  have hdescent : baseEnd_3542479 < baseStart_3542479 := by decide
  rcases family_descends (prefixWord ++ tailWord_3542479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3542530 : List Nat := [3, 4, 1, 2, 1, 1, 4, 2, 4]
def baseStart_3542530 : Nat := 118140960795 + 3542530 * 2 ^ 59
def prefixEnd_3542530 : Nat := 4983230072969 + 3 ^ 40 * 3542530 * 2
def baseEnd_3542530 : Nat := 404226805104917793062935

theorem tailTrace_3542530 : CollatzResearch.WordTrace tailWord_3542530 prefixEnd_3542530 404226805104917793062935 := by
  unfold tailWord_3542530
  simp only [CollatzResearch.WordTrace]
  refine ⟨32301670964006575200332261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86137789237350867200886029 32301670964006575200332261)
  ·
    refine ⟨6056563305751232850062299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32301670964006575200332261 6056563305751232850062299)
    ·
      refine ⟨9084844958626849275093449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6056563305751232850062299 9084844958626849275093449)
      ·
        refine ⟨6813633718970136956320087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9084844958626849275093449 6813633718970136956320087)
        ·
          refine ⟨10220450578455205434480131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6813633718970136956320087 10220450578455205434480131)
          ·
            refine ⟨15330675867682808151720197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10220450578455205434480131 15330675867682808151720197)
            ·
              refine ⟨2874501725190526528447537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15330675867682808151720197 2874501725190526528447537)
              ·
                refine ⟨2155876293892894896335653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2874501725190526528447537 2155876293892894896335653)
                ·
                  refine ⟨404226805104917793062935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2155876293892894896335653 404226805104917793062935)
                  ·
                    rfl

theorem cell22_3542530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 4, 2, 4].length) (baseStart_3542530 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3542530 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3542530 prefixEnd_3542530 := by exact prefixLift 3542530
  have htrace : WordTrace (prefixWord ++ tailWord_3542530) baseStart_3542530 baseEnd_3542530 := by
    simpa [prefixWord, tailWord_3542530, baseEnd_3542530] using wordTrace_append hprefix tailTrace_3542530
  have hstable : (prefixWord ++ tailWord_3542530).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3542530).length < 2 ^ (prefixWord ++ tailWord_3542530).sum := by decide
  have hdescent : baseEnd_3542530 < baseStart_3542530 := by decide
  rcases family_descends (prefixWord ++ tailWord_3542530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3542537 : List Nat := [1, 2, 1, 1, 3, 1, 3, 1, 1, 8]
def baseStart_3542537 : Nat := 118140960795 + 3542537 * 2 ^ 59
def prefixEnd_3542537 : Nat := 4983230072969 + 3 ^ 40 * 3542537 * 2
def baseEnd_3542537 : Nat := 1212682811557807694263783

theorem tailTrace_3542537 : CollatzResearch.WordTrace tailWord_3542537 prefixEnd_3542537 1212682811557807694263783 := by
  unfold tailWord_3542537
  simp only [CollatzResearch.WordTrace]
  refine ⟨129206939167000940996833865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86137959444667293997889243 129206939167000940996833865)
  ·
    refine ⟨96905204375250705747625399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129206939167000940996833865 96905204375250705747625399)
    ·
      refine ⟨145357806562876058621438099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96905204375250705747625399 145357806562876058621438099)
      ·
        refine ⟨218036709844314087932157149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145357806562876058621438099 218036709844314087932157149)
        ·
          refine ⟨81763766191617782974558931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 218036709844314087932157149 81763766191617782974558931)
          ·
            refine ⟨122645649287426674461838397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81763766191617782974558931 122645649287426674461838397)
            ·
              refine ⟨45992118482785002923189399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 122645649287426674461838397 45992118482785002923189399)
              ·
                refine ⟨68988177724177504384784099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45992118482785002923189399 68988177724177504384784099)
                ·
                  refine ⟨103482266586266256577176149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68988177724177504384784099 103482266586266256577176149)
                  ·
                    refine ⟨1212682811557807694263783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 103482266586266256577176149 1212682811557807694263783)
                    ·
                      rfl

theorem cell22_3542537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 1, 1, 8].length) (baseStart_3542537 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3542537 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3542537 prefixEnd_3542537 := by exact prefixLift 3542537
  have htrace : WordTrace (prefixWord ++ tailWord_3542537) baseStart_3542537 baseEnd_3542537 := by
    simpa [prefixWord, tailWord_3542537, baseEnd_3542537] using wordTrace_append hprefix tailTrace_3542537
  have hstable : (prefixWord ++ tailWord_3542537).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3542537).length < 2 ^ (prefixWord ++ tailWord_3542537).sum := by decide
  have hdescent : baseEnd_3542537 < baseStart_3542537 := by decide
  rcases family_descends (prefixWord ++ tailWord_3542537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3542556 : List Nat := [2, 2, 3, 1, 2, 1, 3, 2, 3, 3]
def baseStart_3542556 : Nat := 118140960795 + 3542556 * 2 ^ 59
def prefixEnd_3542556 : Nat := 4983230072969 + 3 ^ 40 * 3542556 * 2
def baseEnd_3542556 : Nat := 1212689315646097978038725

theorem tailTrace_3542556 : CollatzResearch.WordTrace tailWord_3542556 prefixEnd_3542556 1212689315646097978038725 := by
  unfold tailWord_3542556
  simp only [CollatzResearch.WordTrace]
  refine ⟨64603816076966053620887761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86138421435954738161183681 64603816076966053620887761)
  ·
    refine ⟨48452862057724540215665821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64603816076966053620887761 48452862057724540215665821)
    ·
      refine ⟨18169823271646702580874683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48452862057724540215665821 18169823271646702580874683)
      ·
        refine ⟨27254734907470053871312025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18169823271646702580874683 27254734907470053871312025)
        ·
          refine ⟨20441051180602540403484019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27254734907470053871312025 20441051180602540403484019)
          ·
            refine ⟨30661576770903810605226029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20441051180602540403484019 30661576770903810605226029)
            ·
              refine ⟨11498091289088928976959761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30661576770903810605226029 11498091289088928976959761)
              ·
                refine ⟨8623568466816696732719821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11498091289088928976959761 8623568466816696732719821)
                ·
                  refine ⟨3233838175056261274769933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8623568466816696732719821 3233838175056261274769933)
                  ·
                    refine ⟨1212689315646097978038725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3233838175056261274769933 1212689315646097978038725)
                    ·
                      rfl

theorem cell22_3542556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 3, 2, 3, 3].length) (baseStart_3542556 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3542556 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3542556 prefixEnd_3542556 := by exact prefixLift 3542556
  have htrace : WordTrace (prefixWord ++ tailWord_3542556) baseStart_3542556 baseEnd_3542556 := by
    simpa [prefixWord, tailWord_3542556, baseEnd_3542556] using wordTrace_append hprefix tailTrace_3542556
  have hstable : (prefixWord ++ tailWord_3542556).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3542556).length < 2 ^ (prefixWord ++ tailWord_3542556).sum := by decide
  have hdescent : baseEnd_3542556 < baseStart_3542556 := by decide
  rcases family_descends (prefixWord ++ tailWord_3542556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3542584 : List Nat := [2, 1, 2, 1, 4, 2, 1, 2, 2, 5]
def baseStart_3542584 : Nat := 118140960795 + 3542584 * 2 ^ 59
def prefixEnd_3542584 : Nat := 4983230072969 + 3 ^ 40 * 3542584 * 2
def baseEnd_3542584 : Nat := 1212698900618315238338639

theorem tailTrace_3542584 : CollatzResearch.WordTrace tailWord_3542584 prefixEnd_3542584 1212698900618315238338639 := by
  unfold tailWord_3542584
  simp only [CollatzResearch.WordTrace]
  refine ⟨64604326698915334011897403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86139102265220445349196537 64604326698915334011897403)
  ·
    refine ⟨96906490048373001017846105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64604326698915334011897403 96906490048373001017846105)
    ·
      refine ⟨72679867536279750763384579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96906490048373001017846105 72679867536279750763384579)
      ·
        refine ⟨109019801304419626145076869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72679867536279750763384579 109019801304419626145076869)
        ·
          refine ⟨20441212744578679902201913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 109019801304419626145076869 20441212744578679902201913)
          ·
            refine ⟨15330909558434009926651435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20441212744578679902201913 15330909558434009926651435)
            ·
              refine ⟨22996364337651014889977153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15330909558434009926651435 22996364337651014889977153)
              ·
                refine ⟨17247273253238261167482865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22996364337651014889977153 17247273253238261167482865)
                ·
                  refine ⟨12935454939928695875612149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17247273253238261167482865 12935454939928695875612149)
                  ·
                    refine ⟨1212698900618315238338639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12935454939928695875612149 1212698900618315238338639)
                    ·
                      rfl

theorem cell22_3542584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 2, 2, 5].length) (baseStart_3542584 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3542584 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3542584 prefixEnd_3542584 := by exact prefixLift 3542584
  have htrace : WordTrace (prefixWord ++ tailWord_3542584) baseStart_3542584 baseEnd_3542584 := by
    simpa [prefixWord, tailWord_3542584, baseEnd_3542584] using wordTrace_append hprefix tailTrace_3542584
  have hstable : (prefixWord ++ tailWord_3542584).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3542584).length < 2 ^ (prefixWord ++ tailWord_3542584).sum := by decide
  have hdescent : baseEnd_3542584 < baseStart_3542584 := by decide
  rcases family_descends (prefixWord ++ tailWord_3542584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3542663 : List Nat := [1, 1, 4, 2, 1, 4, 1, 3, 2, 3]
def baseStart_3542663 : Nat := 118140960795 + 3542663 * 2 ^ 59
def prefixEnd_3542663 : Nat := 4983230072969 + 3 ^ 40 * 3542663 * 2
def baseEnd_3542663 : Nat := 1212725943932785365613397

theorem tailTrace_3542663 : CollatzResearch.WordTrace tailWord_3542663 prefixEnd_3542663 1212725943932785365613397 := by
  unfold tailWord_3542663
  simp only [CollatzResearch.WordTrace]
  refine ⟨129211534764544464515920643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86141023176362976343947095 129211534764544464515920643)
  ·
    refine ⟨193817302146816696773880965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129211534764544464515920643 193817302146816696773880965)
    ·
      refine ⟨36340744152528130645102681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 193817302146816696773880965 36340744152528130645102681)
      ·
        refine ⟨27255558114396097983827011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36340744152528130645102681 27255558114396097983827011)
        ·
          refine ⟨40883337171594146975740517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27255558114396097983827011 40883337171594146975740517)
          ·
            refine ⟨7665625719673902557951347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40883337171594146975740517 7665625719673902557951347)
            ·
              refine ⟨11498438579510853836927021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7665625719673902557951347 11498438579510853836927021)
              ·
                refine ⟨4311914467316570188847633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11498438579510853836927021 4311914467316570188847633)
                ·
                  refine ⟨3233935850487427641635725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4311914467316570188847633 3233935850487427641635725)
                  ·
                    refine ⟨1212725943932785365613397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3233935850487427641635725 1212725943932785365613397)
                    ·
                      rfl

theorem cell22_3542663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 1, 3, 2, 3].length) (baseStart_3542663 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3542663 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3542663 prefixEnd_3542663 := by exact prefixLift 3542663
  have htrace : WordTrace (prefixWord ++ tailWord_3542663) baseStart_3542663 baseEnd_3542663 := by
    simpa [prefixWord, tailWord_3542663, baseEnd_3542663] using wordTrace_append hprefix tailTrace_3542663
  have hstable : (prefixWord ++ tailWord_3542663).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3542663).length < 2 ^ (prefixWord ++ tailWord_3542663).sum := by decide
  have hdescent : baseEnd_3542663 < baseStart_3542663 := by decide
  rcases family_descends (prefixWord ++ tailWord_3542663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3542704 : List Nat := [2, 1, 1, 1, 2, 1, 4, 3, 7]
def baseStart_3542704 : Nat := 118140960795 + 3542704 * 2 ^ 59
def prefixEnd_3542704 : Nat := 4983230072969 + 3 ^ 40 * 3542704 * 2
def baseEnd_3542704 : Nat := 404246659690224975112757

theorem tailTrace_3542704 : CollatzResearch.WordTrace tailWord_3542704 prefixEnd_3542704 404246659690224975112757 := by
  unfold tailWord_3542704
  simp only [CollatzResearch.WordTrace]
  refine ⟨64606515078697964259081583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86142020104930619012108777 64606515078697964259081583)
  ·
    refine ⟨96909772618046946388622375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64606515078697964259081583 96909772618046946388622375)
    ·
      refine ⟨145364658927070419582933563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96909772618046946388622375 145364658927070419582933563)
      ·
        refine ⟨218046988390605629374400345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145364658927070419582933563 218046988390605629374400345)
        ·
          refine ⟨163535241292954222030800259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 218046988390605629374400345 163535241292954222030800259)
          ·
            refine ⟨245302861939431333046200389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163535241292954222030800259 245302861939431333046200389)
            ·
              refine ⟨45994286613643374946162573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 245302861939431333046200389 45994286613643374946162573)
              ·
                refine ⟨17247857480116265604810965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45994286613643374946162573 17247857480116265604810965)
                ·
                  refine ⟨404246659690224975112757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17247857480116265604810965 404246659690224975112757)
                  ·
                    rfl

theorem cell22_3542704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 3, 7].length) (baseStart_3542704 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3542704 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3542704 prefixEnd_3542704 := by exact prefixLift 3542704
  have htrace : WordTrace (prefixWord ++ tailWord_3542704) baseStart_3542704 baseEnd_3542704 := by
    simpa [prefixWord, tailWord_3542704, baseEnd_3542704] using wordTrace_append hprefix tailTrace_3542704
  have hstable : (prefixWord ++ tailWord_3542704).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3542704).length < 2 ^ (prefixWord ++ tailWord_3542704).sum := by decide
  have hdescent : baseEnd_3542704 < baseStart_3542704 := by decide
  rcases family_descends (prefixWord ++ tailWord_3542704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3542710 : List Nat := [5, 1, 3, 1, 1, 3, 1, 7]
def baseStart_3542710 : Nat := 118140960795 + 3542710 * 2 ^ 59
def prefixEnd_3542710 : Nat := 4983230072969 + 3 ^ 40 * 3542710 * 2
def baseEnd_3542710 : Nat := 134749114777032545520917

theorem tailTrace_3542710 : CollatzResearch.WordTrace tailWord_3542710 prefixEnd_3542710 134749114777032545520917 := by
  unfold tailWord_3542710
  simp only [CollatzResearch.WordTrace]
  refine ⟨8075828062210886971430099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 86142165996916127695254389 8075828062210886971430099)
  ·
    refine ⟨12113742093316330457145149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8075828062210886971430099 12113742093316330457145149)
    ·
      refine ⟨4542653284993623921429431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12113742093316330457145149 4542653284993623921429431)
      ·
        refine ⟨6813979927490435882144147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4542653284993623921429431 6813979927490435882144147)
        ·
          refine ⟨10220969891235653823216221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6813979927490435882144147 10220969891235653823216221)
          ·
            refine ⟨3832863709213370183706083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10220969891235653823216221 3832863709213370183706083)
            ·
              refine ⟨5749295563820055275559125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3832863709213370183706083 5749295563820055275559125)
              ·
                refine ⟨134749114777032545520917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5749295563820055275559125 134749114777032545520917)
                ·
                  rfl

theorem cell22_3542710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 3, 1, 7].length) (baseStart_3542710 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3542710 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3542710 prefixEnd_3542710 := by exact prefixLift 3542710
  have htrace : WordTrace (prefixWord ++ tailWord_3542710) baseStart_3542710 baseEnd_3542710 := by
    simpa [prefixWord, tailWord_3542710, baseEnd_3542710] using wordTrace_append hprefix tailTrace_3542710
  have hstable : (prefixWord ++ tailWord_3542710).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3542710).length < 2 ^ (prefixWord ++ tailWord_3542710).sum := by decide
  have hdescent : baseEnd_3542710 < baseStart_3542710 := by decide
  rcases family_descends (prefixWord ++ tailWord_3542710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3542755 : List Nat := [1, 1, 1, 7, 2, 2, 1, 2, 5]
def baseStart_3542755 : Nat := 118140960795 + 3542755 * 2 ^ 59
def prefixEnd_3542755 : Nat := 4983230072969 + 3 ^ 40 * 3542755 * 2
def baseEnd_3542755 : Nat := 404252479137642597437705

theorem tailTrace_3542755 : CollatzResearch.WordTrace tailWord_3542755 prefixEnd_3542755 404252479137642597437705 := by
  unfold tailWord_3542755
  simp only [CollatzResearch.WordTrace]
  refine ⟨129214890280211164228269719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86143260186807442818846479 129214890280211164228269719)
  ·
    refine ⟨193822335420316746342404579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129214890280211164228269719 193822335420316746342404579)
    ·
      refine ⟨290733503130475119513606869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193822335420316746342404579 290733503130475119513606869)
      ·
        refine ⟨6814066479620510613600161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 290733503130475119513606869 6814066479620510613600161)
        ·
          refine ⟨5110549859715382960200121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6814066479620510613600161 5110549859715382960200121)
          ·
            refine ⟨3832912394786537220150091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5110549859715382960200121 3832912394786537220150091)
            ·
              refine ⟨5749368592179805830225137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3832912394786537220150091 5749368592179805830225137)
              ·
                refine ⟨4312026444134854372668853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5749368592179805830225137 4312026444134854372668853)
                ·
                  refine ⟨404252479137642597437705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4312026444134854372668853 404252479137642597437705)
                  ·
                    rfl

theorem cell22_3542755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 2, 1, 2, 5].length) (baseStart_3542755 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3542755 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3542755 prefixEnd_3542755 := by exact prefixLift 3542755
  have htrace : WordTrace (prefixWord ++ tailWord_3542755) baseStart_3542755 baseEnd_3542755 := by
    simpa [prefixWord, tailWord_3542755, baseEnd_3542755] using wordTrace_append hprefix tailTrace_3542755
  have hstable : (prefixWord ++ tailWord_3542755).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3542755).length < 2 ^ (prefixWord ++ tailWord_3542755).sum := by decide
  have hdescent : baseEnd_3542755 < baseStart_3542755 := by decide
  rcases family_descends (prefixWord ++ tailWord_3542755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3542781 : List Nat := [1, 4, 1, 1, 1, 1, 2, 5, 1, 5]
def baseStart_3542781 : Nat := 118140960795 + 3542781 * 2 ^ 59
def prefixEnd_3542781 : Nat := 4983230072969 + 3 ^ 40 * 3542781 * 2
def baseEnd_3542781 : Nat := 1212766337744272391163035

theorem tailTrace_3542781 : CollatzResearch.WordTrace tailWord_3542781 prefixEnd_3542781 1212766337744272391163035 := by
  unfold tailWord_3542781
  simp only [CollatzResearch.WordTrace]
  refine ⟨129215838578116970668716197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86143892385411313779144131 129215838578116970668716197)
  ·
    refine ⟨24227969733396932000384287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 129215838578116970668716197 24227969733396932000384287)
    ·
      refine ⟨36341954600095398000576431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24227969733396932000384287 36341954600095398000576431)
      ·
        refine ⟨54512931900143097000864647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36341954600095398000576431 54512931900143097000864647)
        ·
          refine ⟨81769397850214645501296971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54512931900143097000864647 81769397850214645501296971)
          ·
            refine ⟨122654096775321968251945457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81769397850214645501296971 122654096775321968251945457)
            ·
              refine ⟨91990572581491476188959093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 122654096775321968251945457 91990572581491476188959093)
              ·
                refine ⟨8624116179514825892714915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 91990572581491476188959093 8624116179514825892714915)
                ·
                  refine ⟨12936174269272238839072373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8624116179514825892714915 12936174269272238839072373)
                  ·
                    refine ⟨1212766337744272391163035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12936174269272238839072373 1212766337744272391163035)
                    ·
                      rfl

theorem cell22_3542781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 5, 1, 5].length) (baseStart_3542781 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3542781 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3542781 prefixEnd_3542781 := by exact prefixLift 3542781
  have htrace : WordTrace (prefixWord ++ tailWord_3542781) baseStart_3542781 baseEnd_3542781 := by
    simpa [prefixWord, tailWord_3542781, baseEnd_3542781] using wordTrace_append hprefix tailTrace_3542781
  have hstable : (prefixWord ++ tailWord_3542781).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3542781).length < 2 ^ (prefixWord ++ tailWord_3542781).sum := by decide
  have hdescent : baseEnd_3542781 < baseStart_3542781 := by decide
  rcases family_descends (prefixWord ++ tailWord_3542781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3542796 : List Nat := [2, 2, 1, 2, 2, 1, 4, 1, 1, 6]
def baseStart_3542796 : Nat := 118140960795 + 3542796 * 2 ^ 59
def prefixEnd_3542796 : Nat := 4983230072969 + 3 ^ 40 * 3542796 * 2
def baseEnd_3542796 : Nat := 1212771472550817352037989

theorem tailTrace_3542796 : CollatzResearch.WordTrace tailWord_3542796 prefixEnd_3542796 1212771472550817352037989 := by
  unfold tailWord_3542796
  simp only [CollatzResearch.WordTrace]
  refine ⟨64608192836531314115256121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86144257115375085487008161 64608192836531314115256121)
  ·
    refine ⟨48456144627398485586442091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64608192836531314115256121 48456144627398485586442091)
    ·
      refine ⟨72684216941097728379663137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48456144627398485586442091 72684216941097728379663137)
      ·
        refine ⟨54513162705823296284747353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72684216941097728379663137 54513162705823296284747353)
        ·
          refine ⟨40884872029367472213560515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54513162705823296284747353 40884872029367472213560515)
          ·
            refine ⟨61327308044051208320340773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40884872029367472213560515 61327308044051208320340773)
            ·
              refine ⟨11498870258259601560063895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 61327308044051208320340773 11498870258259601560063895)
              ·
                refine ⟨17248305387389402340095843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11498870258259601560063895 17248305387389402340095843)
                ·
                  refine ⟨25872458081084103510143765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17248305387389402340095843 25872458081084103510143765)
                  ·
                    refine ⟨1212771472550817352037989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25872458081084103510143765 1212771472550817352037989)
                    ·
                      rfl

theorem cell22_3542796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 4, 1, 1, 6].length) (baseStart_3542796 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3542796 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3542796 prefixEnd_3542796 := by exact prefixLift 3542796
  have htrace : WordTrace (prefixWord ++ tailWord_3542796) baseStart_3542796 baseEnd_3542796 := by
    simpa [prefixWord, tailWord_3542796, baseEnd_3542796] using wordTrace_append hprefix tailTrace_3542796
  have hstable : (prefixWord ++ tailWord_3542796).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3542796).length < 2 ^ (prefixWord ++ tailWord_3542796).sum := by decide
  have hdescent : baseEnd_3542796 < baseStart_3542796 := by decide
  rcases family_descends (prefixWord ++ tailWord_3542796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3542798 : List Nat := [4, 1, 1, 2, 1, 1, 3, 2, 4, 3]
def baseStart_3542798 : Nat := 118140960795 + 3542798 * 2 ^ 59
def prefixEnd_3542798 : Nat := 4983230072969 + 3 ^ 40 * 3542798 * 2
def baseEnd_3542798 : Nat := 1212772157191690013487983

theorem tailTrace_3542798 : CollatzResearch.WordTrace tailWord_3542798 prefixEnd_3542798 1212772157191690013487983 := by
  unfold tailWord_3542798
  simp only [CollatzResearch.WordTrace]
  refine ⟨16152057327381922821510631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 86144305746036921714723365 16152057327381922821510631)
  ·
    refine ⟨24228085991072884232265947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16152057327381922821510631 24228085991072884232265947)
    ·
      refine ⟨36342128986609326348398921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24228085991072884232265947 36342128986609326348398921)
      ·
        refine ⟨27256596739956994761299191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36342128986609326348398921 27256596739956994761299191)
        ·
          refine ⟨40884895109935492141948787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27256596739956994761299191 40884895109935492141948787)
          ·
            refine ⟨61327342664903238212923181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40884895109935492141948787 61327342664903238212923181)
            ·
              refine ⟨22997753499338714329846193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61327342664903238212923181 22997753499338714329846193)
              ·
                refine ⟨17248315124504035747384645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22997753499338714329846193 17248315124504035747384645)
                ·
                  refine ⟨3234059085844506702634621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17248315124504035747384645 3234059085844506702634621)
                  ·
                    refine ⟨1212772157191690013487983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3234059085844506702634621 1212772157191690013487983)
                    ·
                      rfl

theorem cell22_3542798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 2, 4, 3].length) (baseStart_3542798 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3542798 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3542798 prefixEnd_3542798 := by exact prefixLift 3542798
  have htrace : WordTrace (prefixWord ++ tailWord_3542798) baseStart_3542798 baseEnd_3542798 := by
    simpa [prefixWord, tailWord_3542798, baseEnd_3542798] using wordTrace_append hprefix tailTrace_3542798
  have hstable : (prefixWord ++ tailWord_3542798).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3542798).length < 2 ^ (prefixWord ++ tailWord_3542798).sum := by decide
  have hdescent : baseEnd_3542798 < baseStart_3542798 := by decide
  rcases family_descends (prefixWord ++ tailWord_3542798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3542873 : List Nat := [1, 2, 1, 2, 2, 3, 4, 2, 5]
def baseStart_3542873 : Nat := 118140960795 + 3542873 * 2 ^ 59
def prefixEnd_3542873 : Nat := 4983230072969 + 3 ^ 40 * 3542873 * 2
def baseEnd_3542873 : Nat := 404265943741471605954251

theorem tailTrace_3542873 : CollatzResearch.WordTrace tailWord_3542873 prefixEnd_3542873 404265943741471605954251 := by
  unfold tailWord_3542873
  simp only [CollatzResearch.WordTrace]
  refine ⟨129219194093783670381065273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86146129395855780254043515 129219194093783670381065273)
  ·
    refine ⟨96914395570337752785798955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129219194093783670381065273 96914395570337752785798955)
    ·
      refine ⟨145371593355506629178698433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96914395570337752785798955 145371593355506629178698433)
      ·
        refine ⟨109028695016629971884023825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145371593355506629178698433 109028695016629971884023825)
        ·
          refine ⟨81771521262472478913017869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109028695016629971884023825 81771521262472478913017869)
          ·
            refine ⟨30664320473427179592381701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81771521262472478913017869 30664320473427179592381701)
            ·
              refine ⟨5749560088767596173571569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30664320473427179592381701 5749560088767596173571569)
              ·
                refine ⟨4312170066575697130178677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5749560088767596173571569 4312170066575697130178677)
                ·
                  refine ⟨404265943741471605954251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4312170066575697130178677 404265943741471605954251)
                  ·
                    rfl

theorem cell22_3542873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 4, 2, 5].length) (baseStart_3542873 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3542873 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3542873 prefixEnd_3542873 := by exact prefixLift 3542873
  have htrace : WordTrace (prefixWord ++ tailWord_3542873) baseStart_3542873 baseEnd_3542873 := by
    simpa [prefixWord, tailWord_3542873, baseEnd_3542873] using wordTrace_append hprefix tailTrace_3542873
  have hstable : (prefixWord ++ tailWord_3542873).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3542873).length < 2 ^ (prefixWord ++ tailWord_3542873).sum := by decide
  have hdescent : baseEnd_3542873 < baseStart_3542873 := by decide
  rcases family_descends (prefixWord ++ tailWord_3542873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3542888 : List Nat := [2, 1, 4, 2, 1, 1, 3, 1, 2, 5]
def baseStart_3542888 : Nat := 118140960795 + 3542888 * 2 ^ 59
def prefixEnd_3542888 : Nat := 4983230072969 + 3 ^ 40 * 3542888 * 2
def baseEnd_3542888 : Nat := 1212802966030959778737707

theorem tailTrace_3542888 : CollatzResearch.WordTrace tailWord_3542888 prefixEnd_3542888 1212802966030959778737707 := by
  unfold tailWord_3542888
  simp only [CollatzResearch.WordTrace]
  refine ⟨64609870594364663971430659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86146494125819551961907545 64609870594364663971430659)
  ·
    refine ⟨96914805891546995957145989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64609870594364663971430659 96914805891546995957145989)
    ·
      refine ⟨18171526104665061741964873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 96914805891546995957145989 18171526104665061741964873)
      ·
        refine ⟨13628644578498796306473655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18171526104665061741964873 13628644578498796306473655)
        ·
          refine ⟨20442966867748194459710483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13628644578498796306473655 20442966867748194459710483)
          ·
            refine ⟨30664450301622291689565725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20442966867748194459710483 30664450301622291689565725)
            ·
              refine ⟨11499168863108359383587147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30664450301622291689565725 11499168863108359383587147)
              ·
                refine ⟨17248753294662539075380721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11499168863108359383587147 17248753294662539075380721)
                ·
                  refine ⟨12936564970996904306535541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17248753294662539075380721 12936564970996904306535541)
                  ·
                    refine ⟨1212802966030959778737707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12936564970996904306535541 1212802966030959778737707)
                    ·
                      rfl

theorem cell22_3542888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 3, 1, 2, 5].length) (baseStart_3542888 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3542888 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3542888 prefixEnd_3542888 := by exact prefixLift 3542888
  have htrace : WordTrace (prefixWord ++ tailWord_3542888) baseStart_3542888 baseEnd_3542888 := by
    simpa [prefixWord, tailWord_3542888, baseEnd_3542888] using wordTrace_append hprefix tailTrace_3542888
  have hstable : (prefixWord ++ tailWord_3542888).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3542888).length < 2 ^ (prefixWord ++ tailWord_3542888).sum := by decide
  have hdescent : baseEnd_3542888 < baseStart_3542888 := by decide
  rcases family_descends (prefixWord ++ tailWord_3542888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3542935 : List Nat := [1, 1, 3, 3, 1, 3, 2, 4, 4]
def baseStart_3542935 : Nat := 118140960795 + 3542935 * 2 ^ 59
def prefixEnd_3542935 : Nat := 4983230072969 + 3 ^ 40 * 3542935 * 2
def baseEnd_3542935 : Nat := 404273018363822440937521

theorem tailTrace_3542935 : CollatzResearch.WordTrace tailWord_3542935 prefixEnd_3542935 404273018363822440937521 := by
  unfold tailWord_3542935
  simp only [CollatzResearch.WordTrace]
  refine ⟨129221455419559054969822259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86147636946372703313214839 129221455419559054969822259)
  ·
    refine ⟨193832183129338582454733389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129221455419559054969822259 193832183129338582454733389)
    ·
      refine ⟨72687068673501968420525021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 193832183129338582454733389 72687068673501968420525021)
      ·
        refine ⟨27257650752563238157696883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72687068673501968420525021 27257650752563238157696883)
        ·
          refine ⟨40886476128844857236545325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27257650752563238157696883 40886476128844857236545325)
          ·
            refine ⟨15332428548316821463704497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40886476128844857236545325 15332428548316821463704497)
            ·
              refine ⟨11499321411237616097778373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15332428548316821463704497 11499321411237616097778373)
              ·
                refine ⟨2156122764607053018333445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11499321411237616097778373 2156122764607053018333445)
                ·
                  refine ⟨404273018363822440937521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2156122764607053018333445 404273018363822440937521)
                  ·
                    rfl

theorem cell22_3542935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 2, 4, 4].length) (baseStart_3542935 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3542935 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3542935 prefixEnd_3542935 := by exact prefixLift 3542935
  have htrace : WordTrace (prefixWord ++ tailWord_3542935) baseStart_3542935 baseEnd_3542935 := by
    simpa [prefixWord, tailWord_3542935, baseEnd_3542935] using wordTrace_append hprefix tailTrace_3542935
  have hstable : (prefixWord ++ tailWord_3542935).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3542935).length < 2 ^ (prefixWord ++ tailWord_3542935).sum := by decide
  have hdescent : baseEnd_3542935 < baseStart_3542935 := by decide
  rcases family_descends (prefixWord ++ tailWord_3542935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3542948 : List Nat := [2, 3, 1, 2, 1, 3, 1, 2, 1, 6]
def baseStart_3542948 : Nat := 118140960795 + 3542948 * 2 ^ 59
def prefixEnd_3542948 : Nat := 4983230072969 + 3 ^ 40 * 3542948 * 2
def baseEnd_3542948 : Nat := 1212823505257139622237523

theorem tailTrace_3542948 : CollatzResearch.WordTrace tailWord_3542948 prefixEnd_3542948 1212823505257139622237523 := by
  unfold tailWord_3542948
  simp only [CollatzResearch.WordTrace]
  refine ⟨64610964784255979095022749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86147953045674638793363665 64610964784255979095022749)
  ·
    refine ⟨24229111794095992160633531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64610964784255979095022749 24229111794095992160633531)
    ·
      refine ⟨36343667691143988240950297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24229111794095992160633531 36343667691143988240950297)
      ·
        refine ⟨27257750768357991180712723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36343667691143988240950297 27257750768357991180712723)
        ·
          refine ⟨40886626152536986771069085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27257750768357991180712723 40886626152536986771069085)
          ·
            refine ⟨15332484807201370039150907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40886626152536986771069085 15332484807201370039150907)
            ·
              refine ⟨22998727210802055058726361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15332484807201370039150907 22998727210802055058726361)
              ·
                refine ⟨17249045408101541294044771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22998727210802055058726361 17249045408101541294044771)
                ·
                  refine ⟨25873568112152311941067157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17249045408101541294044771 25873568112152311941067157)
                  ·
                    refine ⟨1212823505257139622237523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25873568112152311941067157 1212823505257139622237523)
                    ·
                      rfl

theorem cell22_3542948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 2, 1, 6].length) (baseStart_3542948 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3542948 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3542948 prefixEnd_3542948 := by exact prefixLift 3542948
  have htrace : WordTrace (prefixWord ++ tailWord_3542948) baseStart_3542948 baseEnd_3542948 := by
    simpa [prefixWord, tailWord_3542948, baseEnd_3542948] using wordTrace_append hprefix tailTrace_3542948
  have hstable : (prefixWord ++ tailWord_3542948).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3542948).length < 2 ^ (prefixWord ++ tailWord_3542948).sum := by decide
  have hdescent : baseEnd_3542948 < baseStart_3542948 := by decide
  rcases family_descends (prefixWord ++ tailWord_3542948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3543001 : List Nat := [1, 2, 1, 2, 7, 1, 2, 1, 2, 3]
def baseStart_3543001 : Nat := 118140960795 + 3543001 * 2 ^ 59
def prefixEnd_3543001 : Nat := 4983230072969 + 3 ^ 40 * 3543001 * 2
def baseEnd_3543001 : Nat := 1212841648240265150662361

theorem tailTrace_3543001 : CollatzResearch.WordTrace tailWord_3543001 prefixEnd_3543001 1212841648240265150662361 := by
  unfold tailWord_3543001
  simp only [CollatzResearch.WordTrace]
  refine ⟨129223862637319948241724857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86149241758213298827816571 129223862637319948241724857)
  ·
    refine ⟨96917896977989961181293643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129223862637319948241724857 96917896977989961181293643)
    ·
      refine ⟨145376845466984941771940465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96917896977989961181293643 145376845466984941771940465)
      ·
        refine ⟨109032634100238706328955349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145376845466984941771940465 109032634100238706328955349)
        ·
          refine ⟨2555452361724344679584891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 109032634100238706328955349 2555452361724344679584891)
          ·
            refine ⟨3833178542586517019377337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2555452361724344679584891 3833178542586517019377337)
            ·
              refine ⟨2874883906939887764533003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3833178542586517019377337 2874883906939887764533003)
              ·
                refine ⟨4312325860409831646799505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2874883906939887764533003 4312325860409831646799505)
                ·
                  refine ⟨3234244395307373735099629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4312325860409831646799505 3234244395307373735099629)
                  ·
                    refine ⟨1212841648240265150662361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3234244395307373735099629 1212841648240265150662361)
                    ·
                      rfl

theorem cell22_3543001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 7, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 7, 1, 2, 1, 2, 3].length) (baseStart_3543001 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3543001 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3543001 prefixEnd_3543001 := by exact prefixLift 3543001
  have htrace : WordTrace (prefixWord ++ tailWord_3543001) baseStart_3543001 baseEnd_3543001 := by
    simpa [prefixWord, tailWord_3543001, baseEnd_3543001] using wordTrace_append hprefix tailTrace_3543001
  have hstable : (prefixWord ++ tailWord_3543001).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3543001).length < 2 ^ (prefixWord ++ tailWord_3543001).sum := by decide
  have hdescent : baseEnd_3543001 < baseStart_3543001 := by decide
  rcases family_descends (prefixWord ++ tailWord_3543001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3543089 : List Nat := [1, 2, 2, 3, 1, 5, 2, 1, 1, 4]
def baseStart_3543089 : Nat := 118140960795 + 3543089 * 2 ^ 59
def prefixEnd_3543089 : Nat := 4983230072969 + 3 ^ 40 * 3543089 * 2
def baseEnd_3543089 : Nat := 1212871772438662254462091

theorem tailTrace_3543089 : CollatzResearch.WordTrace tailWord_3543089 prefixEnd_3543089 1212871772438662254462091 := by
  unfold tailWord_3543089
  simp only [CollatzResearch.WordTrace]
  refine ⟨129227072261001139270928321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86151381507334092847285547 129227072261001139270928321)
  ·
    refine ⟨96920304195750854453196241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129227072261001139270928321 96920304195750854453196241)
    ·
      refine ⟨72690228146813140839897181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96920304195750854453196241 72690228146813140839897181)
      ·
        refine ⟨27258835555054927814961443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72690228146813140839897181 27258835555054927814961443)
        ·
          refine ⟨40888253332582391722442165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27258835555054927814961443 40888253332582391722442165)
          ·
            refine ⟨3833273749929599223978953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 40888253332582391722442165 3833273749929599223978953)
            ·
              refine ⟨2874955312447199417984215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3833273749929599223978953 2874955312447199417984215)
              ·
                refine ⟨4312432968670799126976323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2874955312447199417984215 4312432968670799126976323)
                ·
                  refine ⟨6468649453006198690464485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4312432968670799126976323 6468649453006198690464485)
                  ·
                    refine ⟨1212871772438662254462091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6468649453006198690464485 1212871772438662254462091)
                    ·
                      rfl

theorem cell22_3543089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 5, 2, 1, 1, 4].length) (baseStart_3543089 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3543089 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3543089 prefixEnd_3543089 := by exact prefixLift 3543089
  have htrace : WordTrace (prefixWord ++ tailWord_3543089) baseStart_3543089 baseEnd_3543089 := by
    simpa [prefixWord, tailWord_3543089, baseEnd_3543089] using wordTrace_append hprefix tailTrace_3543089
  have hstable : (prefixWord ++ tailWord_3543089).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3543089).length < 2 ^ (prefixWord ++ tailWord_3543089).sum := by decide
  have hdescent : baseEnd_3543089 < baseStart_3543089 := by decide
  rcases family_descends (prefixWord ++ tailWord_3543089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3543100 : List Nat := [2, 2, 2, 2, 2, 1, 2, 1, 4, 4]
def baseStart_3543100 : Nat := 118140960795 + 3543100 * 2 ^ 59
def prefixEnd_3543100 : Nat := 4983230072969 + 3 ^ 40 * 3543100 * 2
def baseEnd_3543100 : Nat := 1212875537963461892437057

theorem tailTrace_3543100 : CollatzResearch.WordTrace tailWord_3543100 prefixEnd_3543100 1212875537963461892437057 := by
  unfold tailWord_3543100
  simp only [CollatzResearch.WordTrace]
  refine ⟨64613736731980644074789377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86151648975974192099719169 64613736731980644074789377)
  ·
    refine ⟨48460302548985483056092033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64613736731980644074789377 48460302548985483056092033)
    ·
      refine ⟨36345226911739112292069025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48460302548985483056092033 36345226911739112292069025)
      ·
        refine ⟨27258920183804334219051769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36345226911739112292069025 27258920183804334219051769)
        ·
          refine ⟨20444190137853250664288827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27258920183804334219051769 20444190137853250664288827)
          ·
            refine ⟨30666285206779875996433241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20444190137853250664288827 30666285206779875996433241)
            ·
              refine ⟨22999713905084906997324931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30666285206779875996433241 22999713905084906997324931)
              ·
                refine ⟨34499570857627360495987397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22999713905084906997324931 34499570857627360495987397)
                ·
                  refine ⟨6468669535805130092997637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34499570857627360495987397 6468669535805130092997637)
                  ·
                    refine ⟨1212875537963461892437057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6468669535805130092997637 1212875537963461892437057)
                    ·
                      rfl

theorem cell22_3543100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 1, 4, 4].length) (baseStart_3543100 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3543100 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3543100 prefixEnd_3543100 := by exact prefixLift 3543100
  have htrace : WordTrace (prefixWord ++ tailWord_3543100) baseStart_3543100 baseEnd_3543100 := by
    simpa [prefixWord, tailWord_3543100, baseEnd_3543100] using wordTrace_append hprefix tailTrace_3543100
  have hstable : (prefixWord ++ tailWord_3543100).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3543100).length < 2 ^ (prefixWord ++ tailWord_3543100).sum := by decide
  have hdescent : baseEnd_3543100 < baseStart_3543100 := by decide
  rcases family_descends (prefixWord ++ tailWord_3543100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3543132 : List Nat := [2, 2, 4, 1, 1, 2, 4, 6]
def baseStart_3543132 : Nat := 118140960795 + 3543132 * 2 ^ 59
def prefixEnd_3543132 : Nat := 4983230072969 + 3 ^ 40 * 3543132 * 2
def baseEnd_3543132 : Nat := 134765165801936052848551

theorem tailTrace_3543132 : CollatzResearch.WordTrace tailWord_3543132 prefixEnd_3543132 134765165801936052848551 := by
  unfold tailWord_3543132
  simp only [CollatzResearch.WordTrace]
  refine ⟨64614320299922678807371825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86152427066563571743162433 64614320299922678807371825)
  ·
    refine ⟨48460740224942009105528869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64614320299922678807371825 48460740224942009105528869)
    ·
      refine ⟨9086388792176626707286663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48460740224942009105528869 9086388792176626707286663)
      ·
        refine ⟨13629583188264940060929995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9086388792176626707286663 13629583188264940060929995)
        ·
          refine ⟨20444374782397410091394993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13629583188264940060929995 20444374782397410091394993)
          ·
            refine ⟨15333281086798057568546245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20444374782397410091394993 15333281086798057568546245)
            ·
              refine ⟨2874990203774635794102421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15333281086798057568546245 2874990203774635794102421)
              ·
                refine ⟨134765165801936052848551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2874990203774635794102421 134765165801936052848551)
                ·
                  rfl

theorem cell22_3543132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 4, 6].length) (baseStart_3543132 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3543132 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3543132 prefixEnd_3543132 := by exact prefixLift 3543132
  have htrace : WordTrace (prefixWord ++ tailWord_3543132) baseStart_3543132 baseEnd_3543132 := by
    simpa [prefixWord, tailWord_3543132, baseEnd_3543132] using wordTrace_append hprefix tailTrace_3543132
  have hstable : (prefixWord ++ tailWord_3543132).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3543132).length < 2 ^ (prefixWord ++ tailWord_3543132).sum := by decide
  have hdescent : baseEnd_3543132 < baseStart_3543132 := by decide
  rcases family_descends (prefixWord ++ tailWord_3543132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3543138 : List Nat := [3, 3, 2, 2, 3, 1, 1, 3, 4]
def baseStart_3543138 : Nat := 118140960795 + 3543138 * 2 ^ 59
def prefixEnd_3543138 : Nat := 4983230072969 + 3 ^ 40 * 3543138 * 2
def baseEnd_3543138 : Nat := 404296182046680819995647

theorem tailTrace_3543138 : CollatzResearch.WordTrace tailWord_3543138 prefixEnd_3543138 404296182046680819995647 := by
  unfold tailWord_3543138
  simp only [CollatzResearch.WordTrace]
  refine ⟨32307214859455905159865517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86152572958549080426308045 32307214859455905159865517)
  ·
    refine ⟨12115205572295964434949569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32307214859455905159865517 12115205572295964434949569)
    ·
      refine ⟨9086404179221973326212177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12115205572295964434949569 9086404179221973326212177)
      ·
        refine ⟨6814803134416479994659133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9086404179221973326212177 6814803134416479994659133)
        ·
          refine ⟨2555551175406179997997175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6814803134416479994659133 2555551175406179997997175)
          ·
            refine ⟨3833326763109269996995763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2555551175406179997997175 3833326763109269996995763)
            ·
              refine ⟨5749990144663904995493645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3833326763109269996995763 5749990144663904995493645)
              ·
                refine ⟨2156246304248964373310117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5749990144663904995493645 2156246304248964373310117)
                ·
                  refine ⟨404296182046680819995647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2156246304248964373310117 404296182046680819995647)
                  ·
                    rfl

theorem cell22_3543138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 3, 1, 1, 3, 4].length) (baseStart_3543138 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3543138 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3543138 prefixEnd_3543138 := by exact prefixLift 3543138
  have htrace : WordTrace (prefixWord ++ tailWord_3543138) baseStart_3543138 baseEnd_3543138 := by
    simpa [prefixWord, tailWord_3543138, baseEnd_3543138] using wordTrace_append hprefix tailTrace_3543138
  have hstable : (prefixWord ++ tailWord_3543138).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3543138).length < 2 ^ (prefixWord ++ tailWord_3543138).sum := by decide
  have hdescent : baseEnd_3543138 < baseStart_3543138 := by decide
  rcases family_descends (prefixWord ++ tailWord_3543138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3543160 : List Nat := [2, 1, 2, 1, 1, 1, 3, 6, 5]
def baseStart_3543160 : Nat := 118140960795 + 3543160 * 2 ^ 59
def prefixEnd_3543160 : Nat := 4983230072969 + 3 ^ 40 * 3543160 * 2
def baseEnd_3543160 : Nat := 404298692396547245312291

theorem tailTrace_3543160 : CollatzResearch.WordTrace tailWord_3543160 prefixEnd_3543160 404298692396547245312291 := by
  unfold tailWord_3543160
  simp only [CollatzResearch.WordTrace]
  refine ⟨64614830921871959198381467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86153107895829278931175289 64614830921871959198381467)
  ·
    refine ⟨96922246382807938797572201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64614830921871959198381467 96922246382807938797572201)
    ·
      refine ⟨72691684787105954098179151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96922246382807938797572201 72691684787105954098179151)
      ·
        refine ⟨109037527180658931147268727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72691684787105954098179151 109037527180658931147268727)
        ·
          refine ⟨163556290770988396720903091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109037527180658931147268727 163556290770988396720903091)
          ·
            refine ⟨245334436156482595081354637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163556290770988396720903091 245334436156482595081354637)
            ·
              refine ⟨92000413558680973155507989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 245334436156482595081354637 92000413558680973155507989)
              ·
                refine ⟨4312519385563170616664437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 92000413558680973155507989 4312519385563170616664437)
                ·
                  refine ⟨404298692396547245312291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4312519385563170616664437 404298692396547245312291)
                  ·
                    rfl

theorem cell22_3543160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 6, 5].length) (baseStart_3543160 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3543160 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3543160 prefixEnd_3543160 := by exact prefixLift 3543160
  have htrace : WordTrace (prefixWord ++ tailWord_3543160) baseStart_3543160 baseEnd_3543160 := by
    simpa [prefixWord, tailWord_3543160, baseEnd_3543160] using wordTrace_append hprefix tailTrace_3543160
  have hstable : (prefixWord ++ tailWord_3543160).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3543160).length < 2 ^ (prefixWord ++ tailWord_3543160).sum := by decide
  have hdescent : baseEnd_3543160 < baseStart_3543160 := by decide
  rcases family_descends (prefixWord ++ tailWord_3543160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3543164 : List Nat := [2, 2, 2, 1, 1, 6, 1, 1, 3, 3]
def baseStart_3543164 : Nat := 118140960795 + 3543164 * 2 ^ 59
def prefixEnd_3543164 : Nat := 4983230072969 + 3 ^ 40 * 3543164 * 2
def baseEnd_3543164 : Nat := 1212897446471387058836861

theorem tailTrace_3543164 : CollatzResearch.WordTrace tailWord_3543164 prefixEnd_3543164 1212897446471387058836861 := by
  unfold tailWord_3543164
  simp only [CollatzResearch.WordTrace]
  refine ⟨64614903867864713539954273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86153205157152951386605697 64614903867864713539954273)
  ·
    refine ⟨48461177900898535154965705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64614903867864713539954273 48461177900898535154965705)
    ·
      refine ⟨36345883425673901366224279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48461177900898535154965705 36345883425673901366224279)
      ·
        refine ⟨54518825138510852049336419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36345883425673901366224279 54518825138510852049336419)
        ·
          refine ⟨81778237707766278074004629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54518825138510852049336419 81778237707766278074004629)
          ·
            refine ⟨3833354892551544284718967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 81778237707766278074004629 3833354892551544284718967)
            ·
              refine ⟨5750032338827316427078451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3833354892551544284718967 5750032338827316427078451)
              ·
                refine ⟨8625048508240974640617677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5750032338827316427078451 8625048508240974640617677)
                ·
                  refine ⟨3234393190590365490231629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8625048508240974640617677 3234393190590365490231629)
                  ·
                    refine ⟨1212897446471387058836861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3234393190590365490231629 1212897446471387058836861)
                    ·
                      rfl

theorem cell22_3543164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 6, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 6, 1, 1, 3, 3].length) (baseStart_3543164 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3543164 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3543164 prefixEnd_3543164 := by exact prefixLift 3543164
  have htrace : WordTrace (prefixWord ++ tailWord_3543164) baseStart_3543164 baseEnd_3543164 := by
    simpa [prefixWord, tailWord_3543164, baseEnd_3543164] using wordTrace_append hprefix tailTrace_3543164
  have hstable : (prefixWord ++ tailWord_3543164).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3543164).length < 2 ^ (prefixWord ++ tailWord_3543164).sum := by decide
  have hdescent : baseEnd_3543164 < baseStart_3543164 := by decide
  rcases family_descends (prefixWord ++ tailWord_3543164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3543175 : List Nat := [1, 1, 4, 2, 1, 1, 2, 3, 2, 5]
def baseStart_3543175 : Nat := 118140960795 + 3543175 * 2 ^ 59
def prefixEnd_3543175 : Nat := 4983230072969 + 3 ^ 40 * 3543175 * 2
def baseEnd_3543175 : Nat := 1212901211996186696811827

theorem tailTrace_3543175 : CollatzResearch.WordTrace tailWord_3543175 prefixEnd_3543175 1212901211996186696811827 := by
  unfold tailWord_3543175
  simp only [CollatzResearch.WordTrace]
  refine ⟨129230208938689575958558979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86153472625793050639039319 129230208938689575958558979)
  ·
    refine ⟨193845313408034363937838469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129230208938689575958558979 193845313408034363937838469)
    ·
      refine ⟨36345996264006443238344713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 193845313408034363937838469 36345996264006443238344713)
      ·
        refine ⟨27259497198004832428758535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36345996264006443238344713 27259497198004832428758535)
        ·
          refine ⟨40889245797007248643137803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27259497198004832428758535 40889245797007248643137803)
          ·
            refine ⟨61333868695510872964706705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40889245797007248643137803 61333868695510872964706705)
            ·
              refine ⟨46000401521633154723530029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61333868695510872964706705 46000401521633154723530029)
              ·
                refine ⟨17250150570612433021323761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46000401521633154723530029 17250150570612433021323761)
                ·
                  refine ⟨12937612927959324765992821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17250150570612433021323761 12937612927959324765992821)
                  ·
                    refine ⟨1212901211996186696811827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12937612927959324765992821 1212901211996186696811827)
                    ·
                      rfl

theorem cell22_3543175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 3, 2, 5].length) (baseStart_3543175 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3543175 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3543175 prefixEnd_3543175 := by exact prefixLift 3543175
  have htrace : WordTrace (prefixWord ++ tailWord_3543175) baseStart_3543175 baseEnd_3543175 := by
    simpa [prefixWord, tailWord_3543175, baseEnd_3543175] using wordTrace_append hprefix tailTrace_3543175
  have hstable : (prefixWord ++ tailWord_3543175).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3543175).length < 2 ^ (prefixWord ++ tailWord_3543175).sum := by decide
  have hdescent : baseEnd_3543175 < baseStart_3543175 := by decide
  rcases family_descends (prefixWord ++ tailWord_3543175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3543271 : List Nat := [1, 1, 5, 3, 1, 1, 3, 2, 2, 3]
def baseStart_3543271 : Nat := 118140960795 + 3543271 * 2 ^ 59
def prefixEnd_3543271 : Nat := 4983230072969 + 3 ^ 40 * 3543271 * 2
def baseEnd_3543271 : Nat := 1212934074758074446411533

theorem tailTrace_3543271 : CollatzResearch.WordTrace tailWord_3543271 prefixEnd_3543271 1212934074758074446411533 := by
  unfold tailWord_3543271
  simp only [CollatzResearch.WordTrace]
  refine ⟨129233710346341784354053667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86155806897561189569369111 129233710346341784354053667)
  ·
    refine ⟨193850565519512676531080501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129233710346341784354053667 193850565519512676531080501)
    ·
      refine ⟨18173490517454313424788797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 193850565519512676531080501 18173490517454313424788797)
      ·
        refine ⟨6815058944045367534295799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18173490517454313424788797 6815058944045367534295799)
        ·
          refine ⟨10222588416068051301443699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6815058944045367534295799 10222588416068051301443699)
          ·
            refine ⟨15333882624102076952165549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10222588416068051301443699 15333882624102076952165549)
            ·
              refine ⟨5750205984038278857062081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15333882624102076952165549 5750205984038278857062081)
              ·
                refine ⟨4312654488028709142796561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5750205984038278857062081 4312654488028709142796561)
                ·
                  refine ⟨3234490866021531857097421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4312654488028709142796561 3234490866021531857097421)
                  ·
                    refine ⟨1212934074758074446411533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3234490866021531857097421 1212934074758074446411533)
                    ·
                      rfl

theorem cell22_3543271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 3, 2, 2, 3].length) (baseStart_3543271 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3543271 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3543271 prefixEnd_3543271 := by exact prefixLift 3543271
  have htrace : WordTrace (prefixWord ++ tailWord_3543271) baseStart_3543271 baseEnd_3543271 := by
    simpa [prefixWord, tailWord_3543271, baseEnd_3543271] using wordTrace_append hprefix tailTrace_3543271
  have hstable : (prefixWord ++ tailWord_3543271).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3543271).length < 2 ^ (prefixWord ++ tailWord_3543271).sum := by decide
  have hdescent : baseEnd_3543271 < baseStart_3543271 := by decide
  rcases family_descends (prefixWord ++ tailWord_3543271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3543280 : List Nat := [2, 1, 1, 1, 3, 1, 1, 3, 1, 8]
def baseStart_3543280 : Nat := 118140960795 + 3543280 * 2 ^ 59
def prefixEnd_3543280 : Nat := 4983230072969 + 3 ^ 40 * 3543280 * 2
def baseEnd_3543280 : Nat := 1212937155642001422936505

theorem tailTrace_3543280 : CollatzResearch.WordTrace tailWord_3543280 prefixEnd_3543280 1212937155642001422936505 := by
  unfold tailWord_3543280
  simp only [CollatzResearch.WordTrace]
  refine ⟨64617019301654589445565647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86156025735539452594087529 64617019301654589445565647)
  ·
    refine ⟨96925528952481884168348471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64617019301654589445565647 96925528952481884168348471)
    ·
      refine ⟨145388293428722826252522707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96925528952481884168348471 145388293428722826252522707)
      ·
        refine ⟨218082440143084239378784061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145388293428722826252522707 218082440143084239378784061)
        ·
          refine ⟨81780915053656589767044023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 218082440143084239378784061 81780915053656589767044023)
          ·
            refine ⟨122671372580484884650566035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81780915053656589767044023 122671372580484884650566035)
            ·
              refine ⟨184007058870727326975849053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122671372580484884650566035 184007058870727326975849053)
              ·
                refine ⟨69002647076522747615943395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 184007058870727326975849053 69002647076522747615943395)
                ·
                  refine ⟨103503970614784121423915093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69002647076522747615943395 103503970614784121423915093)
                  ·
                    refine ⟨1212937155642001422936505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 103503970614784121423915093 1212937155642001422936505)
                    ·
                      rfl

theorem cell22_3543280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 3, 1, 8].length) (baseStart_3543280 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3543280 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3543280 prefixEnd_3543280 := by exact prefixLift 3543280
  have htrace : WordTrace (prefixWord ++ tailWord_3543280) baseStart_3543280 baseEnd_3543280 := by
    simpa [prefixWord, tailWord_3543280, baseEnd_3543280] using wordTrace_append hprefix tailTrace_3543280
  have hstable : (prefixWord ++ tailWord_3543280).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3543280).length < 2 ^ (prefixWord ++ tailWord_3543280).sum := by decide
  have hdescent : baseEnd_3543280 < baseStart_3543280 := by decide
  rcases family_descends (prefixWord ++ tailWord_3543280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3543333 : List Nat := [1, 3, 1, 2, 6, 1, 1, 1, 3, 3]
def baseStart_3543333 : Nat := 118140960795 + 3543333 * 2 ^ 59
def prefixEnd_3543333 : Nat := 4983230072969 + 3 ^ 40 * 3543333 * 2
def baseEnd_3543333 : Nat := 1212955298625126951361343

theorem tailTrace_3543333 : CollatzResearch.WordTrace tailWord_3543333 prefixEnd_3543333 1212955298625126951361343 := by
  unfold tailWord_3543333
  simp only [CollatzResearch.WordTrace]
  refine ⟨129235971672117168942810653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86157314448078112628540435 129235971672117168942810653)
  ·
    refine ⟨48463489377043938353553995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129235971672117168942810653 48463489377043938353553995)
    ·
      refine ⟨72695234065565907530330993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48463489377043938353553995 72695234065565907530330993)
      ·
        refine ⟨54521425549174430647748245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72695234065565907530330993 54521425549174430647748245)
        ·
          refine ⟨2555691822617551436613199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 54521425549174430647748245 2555691822617551436613199)
          ·
            refine ⟨3833537733926327154919799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2555691822617551436613199 3833537733926327154919799)
            ·
              refine ⟨5750306600889490732379699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3833537733926327154919799 5750306600889490732379699)
              ·
                refine ⟨8625459901334236098569549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5750306600889490732379699 8625459901334236098569549)
                ·
                  refine ⟨3234547463000338536963581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8625459901334236098569549 3234547463000338536963581)
                  ·
                    refine ⟨1212955298625126951361343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3234547463000338536963581 1212955298625126951361343)
                    ·
                      rfl

theorem cell22_3543333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 6, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 6, 1, 1, 1, 3, 3].length) (baseStart_3543333 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3543333 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3543333 prefixEnd_3543333 := by exact prefixLift 3543333
  have htrace : WordTrace (prefixWord ++ tailWord_3543333) baseStart_3543333 baseEnd_3543333 := by
    simpa [prefixWord, tailWord_3543333, baseEnd_3543333] using wordTrace_append hprefix tailTrace_3543333
  have hstable : (prefixWord ++ tailWord_3543333).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3543333).length < 2 ^ (prefixWord ++ tailWord_3543333).sum := by decide
  have hdescent : baseEnd_3543333 < baseStart_3543333 := by decide
  rcases family_descends (prefixWord ++ tailWord_3543333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3543376 : List Nat := [2, 1, 1, 1, 1, 7, 3, 1, 1, 4]
def baseStart_3543376 : Nat := 118140960795 + 3543376 * 2 ^ 59
def prefixEnd_3543376 : Nat := 4983230072969 + 3 ^ 40 * 3543376 * 2
def baseEnd_3543376 : Nat := 1212970018403889172536211

theorem tailTrace_3543376 : CollatzResearch.WordTrace tailWord_3543376 prefixEnd_3543376 1212970018403889172536211 := by
  unfold tailWord_3543376
  simp only [CollatzResearch.WordTrace]
  refine ⟨64618770005480693643312991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86158360007307591524417321 64618770005480693643312991)
  ·
    refine ⟨96928155008221040464969487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64618770005480693643312991 96928155008221040464969487)
    ·
      refine ⟨145392232512331560697454231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96928155008221040464969487 145392232512331560697454231)
      ·
        refine ⟨218088348768497341046181347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145392232512331560697454231 218088348768497341046181347)
        ·
          refine ⟨327132523152746011569272021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 218088348768497341046181347 327132523152746011569272021)
          ·
            refine ⟨7667168511392484646154813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 327132523152746011569272021 7667168511392484646154813)
            ·
              refine ⟨2875188191772181742308055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7667168511392484646154813 2875188191772181742308055)
              ·
                refine ⟨4312782287658272613462083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2875188191772181742308055 4312782287658272613462083)
                ·
                  refine ⟨6469173431487408920193125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4312782287658272613462083 6469173431487408920193125)
                  ·
                    refine ⟨1212970018403889172536211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6469173431487408920193125 1212970018403889172536211)
                    ·
                      rfl

theorem cell22_3543376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 3, 1, 1, 4].length) (baseStart_3543376 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3543376 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3543376 prefixEnd_3543376 := by exact prefixLift 3543376
  have htrace : WordTrace (prefixWord ++ tailWord_3543376) baseStart_3543376 baseEnd_3543376 := by
    simpa [prefixWord, tailWord_3543376, baseEnd_3543376] using wordTrace_append hprefix tailTrace_3543376
  have hstable : (prefixWord ++ tailWord_3543376).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3543376).length < 2 ^ (prefixWord ++ tailWord_3543376).sum := by decide
  have hdescent : baseEnd_3543376 < baseStart_3543376 := by decide
  rcases family_descends (prefixWord ++ tailWord_3543376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3543391 : List Nat := [1, 1, 2, 3, 1, 2, 6, 2, 4]
def baseStart_3543391 : Nat := 118140960795 + 3543391 * 2 ^ 59
def prefixEnd_3543391 : Nat := 4983230072969 + 3 ^ 40 * 3543391 * 2
def baseEnd_3543391 : Nat := 404325051070144711137055

theorem tailTrace_3543391 : CollatzResearch.WordTrace tailWord_3543391 prefixEnd_3543391 404325051070144711137055 := by
  unfold tailWord_3543391
  simp only [CollatzResearch.WordTrace]
  refine ⟨129238087105907044848422027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86158724737271363232281351 129238087105907044848422027)
  ·
    refine ⟨193857130658860567272633041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129238087105907044848422027 193857130658860567272633041)
    ·
      refine ⟨145392847994145425454474781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193857130658860567272633041 145392847994145425454474781)
      ·
        refine ⟨54522317997804534545428043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 145392847994145425454474781 54522317997804534545428043)
        ·
          refine ⟨81783476996706801818142065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54522317997804534545428043 81783476996706801818142065)
          ·
            refine ⟨61337607747530101363606549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81783476996706801818142065 61337607747530101363606549)
            ·
              refine ⟨2875200363165473501419057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 61337607747530101363606549 2875200363165473501419057)
              ·
                refine ⟨2156400272374105126064293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2875200363165473501419057 2156400272374105126064293)
                ·
                  refine ⟨404325051070144711137055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2156400272374105126064293 404325051070144711137055)
                  ·
                    rfl

theorem cell22_3543391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 6, 2, 4].length) (baseStart_3543391 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3543391 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3543391 prefixEnd_3543391 := by exact prefixLift 3543391
  have htrace : WordTrace (prefixWord ++ tailWord_3543391) baseStart_3543391 baseEnd_3543391 := by
    simpa [prefixWord, tailWord_3543391, baseEnd_3543391] using wordTrace_append hprefix tailTrace_3543391
  have hstable : (prefixWord ++ tailWord_3543391).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3543391).length < 2 ^ (prefixWord ++ tailWord_3543391).sum := by decide
  have hdescent : baseEnd_3543391 < baseStart_3543391 := by decide
  rcases family_descends (prefixWord ++ tailWord_3543391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3543419 : List Nat := [1, 1, 1, 1, 1, 8, 3, 6]
def baseStart_3543419 : Nat := 118140960795 + 3543419 * 2 ^ 59
def prefixEnd_3543419 : Nat := 4983230072969 + 3 ^ 40 * 3543419 * 2
def baseEnd_3543419 : Nat := 134776082020294599301231

theorem tailTrace_3543419 : CollatzResearch.WordTrace tailWord_3543419 prefixEnd_3543419 134776082020294599301231 := by
  unfold tailWord_3543419
  simp only [CollatzResearch.WordTrace]
  refine ⟨129239108349805605630441311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86159405566537070420294207 129239108349805605630441311)
  ·
    refine ⟨193858662524708408445661967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129239108349805605630441311 193858662524708408445661967)
    ·
      refine ⟨290787993787062612668492951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193858662524708408445661967 290787993787062612668492951)
      ·
        refine ⟨436181990680593919002739427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 290787993787062612668492951 436181990680593919002739427)
        ·
          refine ⟨654272986020890878504109141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 436181990680593919002739427 654272986020890878504109141)
          ·
            refine ⟨7667261554932314982470029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 654272986020890878504109141 7667261554932314982470029)
            ·
              refine ⟨2875223083099618118426261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7667261554932314982470029 2875223083099618118426261)
              ·
                refine ⟨134776082020294599301231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2875223083099618118426261 134776082020294599301231)
                ·
                  rfl

theorem cell22_3543419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 3, 6].length) (baseStart_3543419 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3543419 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3543419 prefixEnd_3543419 := by exact prefixLift 3543419
  have htrace : WordTrace (prefixWord ++ tailWord_3543419) baseStart_3543419 baseEnd_3543419 := by
    simpa [prefixWord, tailWord_3543419, baseEnd_3543419] using wordTrace_append hprefix tailTrace_3543419
  have hstable : (prefixWord ++ tailWord_3543419).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3543419).length < 2 ^ (prefixWord ++ tailWord_3543419).sum := by decide
  have hdescent : baseEnd_3543419 < baseStart_3543419 := by decide
  rcases family_descends (prefixWord ++ tailWord_3543419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3543421 : List Nat := [1, 4, 1, 1, 2, 5, 1, 1, 2, 4]
def baseStart_3543421 : Nat := 118140960795 + 3543421 * 2 ^ 59
def prefixEnd_3543421 : Nat := 4983230072969 + 3 ^ 40 * 3543421 * 2
def baseEnd_3543421 : Nat := 1212985422823524055161073

theorem tailTrace_3543421 : CollatzResearch.WordTrace tailWord_3543421 prefixEnd_3543421 1212985422823524055161073 := by
  unfold tailWord_3543421
  simp only [CollatzResearch.WordTrace]
  refine ⟨129239181295798359972014117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86159454197198906648009411 129239181295798359972014117)
  ·
    refine ⟨24232346492962192494752647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 129239181295798359972014117 24232346492962192494752647)
    ·
      refine ⟨36348519739443288742128971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24232346492962192494752647 36348519739443288742128971)
      ·
        refine ⟨54522779609164933113193457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36348519739443288742128971 54522779609164933113193457)
        ·
          refine ⟨40892084706873699834895093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54522779609164933113193457 40892084706873699834895093)
          ·
            refine ⟨3833632941269409359521415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 40892084706873699834895093 3833632941269409359521415)
            ·
              refine ⟨5750449411904114039282123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3833632941269409359521415 5750449411904114039282123)
              ·
                refine ⟨8625674117856171058923185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5750449411904114039282123 8625674117856171058923185)
                ·
                  refine ⟨6469255588392128294192389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8625674117856171058923185 6469255588392128294192389)
                  ·
                    refine ⟨1212985422823524055161073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6469255588392128294192389 1212985422823524055161073)
                    ·
                      rfl

theorem cell22_3543421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 5, 1, 1, 2, 4].length) (baseStart_3543421 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3543421 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3543421 prefixEnd_3543421 := by exact prefixLift 3543421
  have htrace : WordTrace (prefixWord ++ tailWord_3543421) baseStart_3543421 baseEnd_3543421 := by
    simpa [prefixWord, tailWord_3543421, baseEnd_3543421] using wordTrace_append hprefix tailTrace_3543421
  have hstable : (prefixWord ++ tailWord_3543421).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3543421).length < 2 ^ (prefixWord ++ tailWord_3543421).sum := by decide
  have hdescent : baseEnd_3543421 < baseStart_3543421 := by decide
  rcases family_descends (prefixWord ++ tailWord_3543421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3543485 : List Nat := [1, 4, 1, 2, 2, 4, 1, 3, 1, 3]
def baseStart_3543485 : Nat := 118140960795 + 3543485 * 2 ^ 59
def prefixEnd_3543485 : Nat := 4983230072969 + 3 ^ 40 * 3543485 * 2
def baseEnd_3543485 : Nat := 1213007331331449221560877

theorem tailTrace_3543485 : CollatzResearch.WordTrace tailWord_3543485 prefixEnd_3543485 1213007331331449221560877 := by
  unfold tailWord_3543485
  simp only [CollatzResearch.WordTrace]
  refine ⟨129241515567566498902343909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86161010378377665934895939 129241515567566498902343909)
  ·
    refine ⟨24232784168918718544189483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 129241515567566498902343909 24232784168918718544189483)
    ·
      refine ⟨36349176253378077816284225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24232784168918718544189483 36349176253378077816284225)
      ·
        refine ⟨27261882190033558362213169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36349176253378077816284225 27261882190033558362213169)
        ·
          refine ⟨20446411642525168771659877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27261882190033558362213169 20446411642525168771659877)
          ·
            refine ⟨3833702182973469144686227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20446411642525168771659877 3833702182973469144686227)
            ·
              refine ⟨5750553274460203717029341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3833702182973469144686227 5750553274460203717029341)
              ·
                refine ⟨2156457477922576393886003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5750553274460203717029341 2156457477922576393886003)
                ·
                  refine ⟨3234686216883864590829005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2156457477922576393886003 3234686216883864590829005)
                  ·
                    refine ⟨1213007331331449221560877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3234686216883864590829005 1213007331331449221560877)
                    ·
                      rfl

theorem cell22_3543485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 4, 1, 3, 1, 3].length) (baseStart_3543485 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3543485 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3543485 prefixEnd_3543485 := by exact prefixLift 3543485
  have htrace : WordTrace (prefixWord ++ tailWord_3543485) baseStart_3543485 baseEnd_3543485 := by
    simpa [prefixWord, tailWord_3543485, baseEnd_3543485] using wordTrace_append hprefix tailTrace_3543485
  have hstable : (prefixWord ++ tailWord_3543485).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3543485).length < 2 ^ (prefixWord ++ tailWord_3543485).sum := by decide
  have hdescent : baseEnd_3543485 < baseStart_3543485 := by decide
  rcases family_descends (prefixWord ++ tailWord_3543485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3543528 : List Nat := [2, 1, 4, 1, 1, 5, 1, 2, 1, 4]
def baseStart_3543528 : Nat := 118140960795 + 3543528 * 2 ^ 59
def prefixEnd_3543528 : Nat := 4983230072969 + 3 ^ 40 * 3543528 * 2
def baseEnd_3543528 : Nat := 1213022051110211442735745

theorem tailTrace_3543528 : CollatzResearch.WordTrace tailWord_3543528 prefixEnd_3543528 1213022051110211442735745 := by
  unfold tailWord_3543528
  simp only [CollatzResearch.WordTrace]
  refine ⟨64621541953205358623079619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86162055937607144830772825 64621541953205358623079619)
  ·
    refine ⟨96932312929808037934619429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64621541953205358623079619 96932312929808037934619429)
    ·
      refine ⟨18174808674339007112741143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 96932312929808037934619429 18174808674339007112741143)
      ·
        refine ⟨27262213011508510669111715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18174808674339007112741143 27262213011508510669111715)
        ·
          refine ⟨40893319517262766003667573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27262213011508510669111715 40893319517262766003667573)
          ·
            refine ⟨3833748704743384312843835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 40893319517262766003667573 3833748704743384312843835)
            ·
              refine ⟨5750623057115076469265753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3833748704743384312843835 5750623057115076469265753)
              ·
                refine ⟨4312967292836307351949315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5750623057115076469265753 4312967292836307351949315)
                ·
                  refine ⟨6469450939254461027923973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4312967292836307351949315 6469450939254461027923973)
                  ·
                    refine ⟨1213022051110211442735745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6469450939254461027923973 1213022051110211442735745)
                    ·
                      rfl

theorem cell22_3543528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 5, 1, 2, 1, 4].length) (baseStart_3543528 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3543528 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3543528 prefixEnd_3543528 := by exact prefixLift 3543528
  have htrace : WordTrace (prefixWord ++ tailWord_3543528) baseStart_3543528 baseEnd_3543528 := by
    simpa [prefixWord, tailWord_3543528, baseEnd_3543528] using wordTrace_append hprefix tailTrace_3543528
  have hstable : (prefixWord ++ tailWord_3543528).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3543528).length < 2 ^ (prefixWord ++ tailWord_3543528).sum := by decide
  have hdescent : baseEnd_3543528 < baseStart_3543528 := by decide
  rcases family_descends (prefixWord ++ tailWord_3543528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3543616 : List Nat := [2, 1, 1, 2, 2, 2, 5, 2, 5]
def baseStart_3543616 : Nat := 118140960795 + 3543616 * 2 ^ 59
def prefixEnd_3543616 : Nat := 4983230072969 + 3 ^ 40 * 3543616 * 2
def baseEnd_3543616 : Nat := 404350725102869515511825

theorem tailTrace_3543616 : CollatzResearch.WordTrace tailWord_3543616 prefixEnd_3543616 404350725102869515511825 := by
  unfold tailWord_3543616
  simp only [CollatzResearch.WordTrace]
  refine ⟨64623146765045954137681351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86164195686727938850241801 64623146765045954137681351)
  ·
    refine ⟨96934720147568931206522027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64623146765045954137681351 96934720147568931206522027)
    ·
      refine ⟨145402080221353396809783041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96934720147568931206522027 145402080221353396809783041)
      ·
        refine ⟨109051560166015047607337281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145402080221353396809783041 109051560166015047607337281)
        ·
          refine ⟨81788670124511285705502961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109051560166015047607337281 81788670124511285705502961)
          ·
            refine ⟨61341502593383464279127221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81788670124511285705502961 61341502593383464279127221)
            ·
              refine ⟨5750765868129699776168177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 61341502593383464279127221 5750765868129699776168177)
              ·
                refine ⟨4313074401097274832126133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5750765868129699776168177 4313074401097274832126133)
                ·
                  refine ⟨404350725102869515511825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4313074401097274832126133 404350725102869515511825)
                  ·
                    rfl

theorem cell22_3543616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 5, 2, 5].length) (baseStart_3543616 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3543616 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3543616 prefixEnd_3543616 := by exact prefixLift 3543616
  have htrace : WordTrace (prefixWord ++ tailWord_3543616) baseStart_3543616 baseEnd_3543616 := by
    simpa [prefixWord, tailWord_3543616, baseEnd_3543616] using wordTrace_append hprefix tailTrace_3543616
  have hstable : (prefixWord ++ tailWord_3543616).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3543616).length < 2 ^ (prefixWord ++ tailWord_3543616).sum := by decide
  have hdescent : baseEnd_3543616 < baseStart_3543616 := by decide
  rcases family_descends (prefixWord ++ tailWord_3543616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3543633 : List Nat := [1, 2, 2, 1, 3, 4, 3, 1, 5]
def baseStart_3543633 : Nat := 118140960795 + 3543633 * 2 ^ 59
def prefixEnd_3543633 : Nat := 4983230072969 + 3 ^ 40 * 3543633 * 2
def baseEnd_3543633 : Nat := 404352664918675389620141

theorem tailTrace_3543633 : CollatzResearch.WordTrace tailWord_3543633 prefixEnd_3543633 404352664918675389620141 := by
  unfold tailWord_3543633
  simp only [CollatzResearch.WordTrace]
  refine ⟨129246913571030320178731553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86164609047353546785821035 129246913571030320178731553)
  ·
    refine ⟨96935185178272740134048665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129246913571030320178731553 96935185178272740134048665)
    ·
      refine ⟨72701388883704555100536499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96935185178272740134048665 72701388883704555100536499)
      ·
        refine ⟨109052083325556832650804749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72701388883704555100536499 109052083325556832650804749)
        ·
          refine ⟨40894531247083812244051781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 109052083325556832650804749 40894531247083812244051781)
          ·
            refine ⟨7667724608828214795759709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40894531247083812244051781 7667724608828214795759709)
            ·
              refine ⟨2875396728310580548409891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7667724608828214795759709 2875396728310580548409891)
              ·
                refine ⟨4313095092465870822614837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2875396728310580548409891 4313095092465870822614837)
                ·
                  refine ⟨404352664918675389620141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4313095092465870822614837 404352664918675389620141)
                  ·
                    rfl

theorem cell22_3543633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 3, 1, 5].length) (baseStart_3543633 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3543633 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3543633 prefixEnd_3543633 := by exact prefixLift 3543633
  have htrace : WordTrace (prefixWord ++ tailWord_3543633) baseStart_3543633 baseEnd_3543633 := by
    simpa [prefixWord, tailWord_3543633, baseEnd_3543633] using wordTrace_append hprefix tailTrace_3543633
  have hstable : (prefixWord ++ tailWord_3543633).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3543633).length < 2 ^ (prefixWord ++ tailWord_3543633).sum := by decide
  have hdescent : baseEnd_3543633 < baseStart_3543633 := by decide
  rcases family_descends (prefixWord ++ tailWord_3543633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3543708 : List Nat := [2, 2, 3, 2, 2, 1, 1, 3, 2, 4]
def baseStart_3543708 : Nat := 118140960795 + 3543708 * 2 ^ 59
def prefixEnd_3543708 : Nat := 4983230072969 + 3 ^ 40 * 3543708 * 2
def baseEnd_3543708 : Nat := 1213083668788750973235193

theorem tailTrace_3543708 : CollatzResearch.WordTrace tailWord_3543708 prefixEnd_3543708 1213083668788750973235193 := by
  unfold tailWord_3543708
  simp only [CollatzResearch.WordTrace]
  refine ⟨64624824522879303993855889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86166432697172405325141185 64624824522879303993855889)
  ·
    refine ⟨48468618392159477995391917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64624824522879303993855889 48468618392159477995391917)
    ·
      refine ⟨18175731897059804248271969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48468618392159477995391917 18175731897059804248271969)
      ·
        refine ⟨13631798922794853186203977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18175731897059804248271969 13631798922794853186203977)
        ·
          refine ⟨10223849192096139889652983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13631798922794853186203977 10223849192096139889652983)
          ·
            refine ⟨15335773788144209834479475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10223849192096139889652983 15335773788144209834479475)
            ·
              refine ⟨23003660682216314751719213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15335773788144209834479475 23003660682216314751719213)
              ·
                refine ⟨8626372755831118031894705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23003660682216314751719213 8626372755831118031894705)
                ·
                  refine ⟨6469779566873338523921029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8626372755831118031894705 6469779566873338523921029)
                  ·
                    refine ⟨1213083668788750973235193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6469779566873338523921029 1213083668788750973235193)
                    ·
                      rfl

theorem cell22_3543708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 3, 2, 4].length) (baseStart_3543708 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3543708 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3543708 prefixEnd_3543708 := by exact prefixLift 3543708
  have htrace : WordTrace (prefixWord ++ tailWord_3543708) baseStart_3543708 baseEnd_3543708 := by
    simpa [prefixWord, tailWord_3543708, baseEnd_3543708] using wordTrace_append hprefix tailTrace_3543708
  have hstable : (prefixWord ++ tailWord_3543708).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3543708).length < 2 ^ (prefixWord ++ tailWord_3543708).sum := by decide
  have hdescent : baseEnd_3543708 < baseStart_3543708 := by decide
  rcases family_descends (prefixWord ++ tailWord_3543708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3543729 : List Nat := [1, 2, 2, 6, 1, 2, 2, 2, 4]
def baseStart_3543729 : Nat := 118140960795 + 3543729 * 2 ^ 59
def prefixEnd_3543729 : Nat := 4983230072969 + 3 ^ 40 * 3543729 * 2
def baseEnd_3543729 : Nat := 404363619172637972820043

theorem tailTrace_3543729 : CollatzResearch.WordTrace tailWord_3543729 prefixEnd_3543729 404363619172637972820043 := by
  unfold tailWord_3543729
  simp only [CollatzResearch.WordTrace]
  refine ⟨129250414978682528574226241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86166943319121685716150827 129250414978682528574226241)
  ·
    refine ⟨96937811234011896430669681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129250414978682528574226241 96937811234011896430669681)
    ·
      refine ⟨72703358425508922323002261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96937811234011896430669681 72703358425508922323002261)
      ·
        refine ⟨3407969926195730733890731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 72703358425508922323002261 3407969926195730733890731)
        ·
          refine ⟨5111954889293596100836097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3407969926195730733890731 5111954889293596100836097)
          ·
            refine ⟨3833966166970197075627073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5111954889293596100836097 3833966166970197075627073)
            ·
              refine ⟨2875474625227647806720305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3833966166970197075627073 2875474625227647806720305)
              ·
                refine ⟨2156605968920735855040229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2875474625227647806720305 2156605968920735855040229)
                ·
                  refine ⟨404363619172637972820043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2156605968920735855040229 404363619172637972820043)
                  ·
                    rfl

theorem cell22_3543729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 2, 2, 2, 4].length) (baseStart_3543729 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3543729 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3543729 prefixEnd_3543729 := by exact prefixLift 3543729
  have htrace : WordTrace (prefixWord ++ tailWord_3543729) baseStart_3543729 baseEnd_3543729 := by
    simpa [prefixWord, tailWord_3543729, baseEnd_3543729] using wordTrace_append hprefix tailTrace_3543729
  have hstable : (prefixWord ++ tailWord_3543729).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3543729).length < 2 ^ (prefixWord ++ tailWord_3543729).sum := by decide
  have hdescent : baseEnd_3543729 < baseStart_3543729 := by decide
  rcases family_descends (prefixWord ++ tailWord_3543729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3543738 : List Nat := [3, 1, 1, 1, 2, 3, 2, 3, 3, 3]
def baseStart_3543738 : Nat := 118140960795 + 3543738 * 2 ^ 59
def prefixEnd_3543738 : Nat := 4983230072969 + 3 ^ 40 * 3543738 * 2
def baseEnd_3543738 : Nat := 1213093938401840894985101

theorem tailTrace_3543738 : CollatzResearch.WordTrace tailWord_3543738 prefixEnd_3543738 1213093938401840894985101 := by
  unfold tailWord_3543738
  simp only [CollatzResearch.WordTrace]
  refine ⟨32312685808912480777825967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86167162157099948740869245 32312685808912480777825967)
  ·
    refine ⟨48469028713368721166738951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32312685808912480777825967 48469028713368721166738951)
    ·
      refine ⟨72703543070053081750108427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48469028713368721166738951 72703543070053081750108427)
      ·
        refine ⟨109055314605079622625162641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72703543070053081750108427 109055314605079622625162641)
        ·
          refine ⟨81791485953809716968871981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109055314605079622625162641 81791485953809716968871981)
          ·
            refine ⟨30671807232678643863326993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81791485953809716968871981 30671807232678643863326993)
            ·
              refine ⟨23003855424508982897495245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30671807232678643863326993 23003855424508982897495245)
              ·
                refine ⟨8626445784190868586560717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23003855424508982897495245 8626445784190868586560717)
                ·
                  refine ⟨3234917169071575719960269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8626445784190868586560717 3234917169071575719960269)
                  ·
                    refine ⟨1213093938401840894985101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3234917169071575719960269 1213093938401840894985101)
                    ·
                      rfl

theorem cell22_3543738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 3, 3, 3].length) (baseStart_3543738 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3543738 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3543738 prefixEnd_3543738 := by exact prefixLift 3543738
  have htrace : WordTrace (prefixWord ++ tailWord_3543738) baseStart_3543738 baseEnd_3543738 := by
    simpa [prefixWord, tailWord_3543738, baseEnd_3543738] using wordTrace_append hprefix tailTrace_3543738
  have hstable : (prefixWord ++ tailWord_3543738).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3543738).length < 2 ^ (prefixWord ++ tailWord_3543738).sum := by decide
  have hdescent : baseEnd_3543738 < baseStart_3543738 := by decide
  rcases family_descends (prefixWord ++ tailWord_3543738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3543757 : List Nat := [1, 6, 2, 1, 2, 1, 3, 6]
def baseStart_3543757 : Nat := 118140960795 + 3543757 * 2 ^ 59
def prefixEnd_3543757 : Nat := 4983230072969 + 3 ^ 40 * 3543757 * 2
def baseEnd_3543757 : Nat := 134788938054459019862227

theorem tailTrace_3543757 : CollatzResearch.WordTrace tailWord_3543757 prefixEnd_3543757 134788938054459019862227 := by
  unfold tailWord_3543757
  simp only [CollatzResearch.WordTrace]
  refine ⟨129251436222581089356245525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86167624148387392904163683 129251436222581089356245525)
  ·
    refine ⟨6058661072933488563574009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 129251436222581089356245525 6058661072933488563574009)
    ·
      refine ⟨4543995804700116422680507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6058661072933488563574009 4543995804700116422680507)
      ·
        refine ⟨6815993707050174634020761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4543995804700116422680507 6815993707050174634020761)
        ·
          refine ⟨5111995280287630975515571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6815993707050174634020761 5111995280287630975515571)
          ·
            refine ⟨7667992920431446463273357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5111995280287630975515571 7667992920431446463273357)
            ·
              refine ⟨2875497345161792423727509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7667992920431446463273357 2875497345161792423727509)
              ·
                refine ⟨134788938054459019862227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2875497345161792423727509 134788938054459019862227)
                ·
                  rfl

theorem cell22_3543757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 3, 6].length) (baseStart_3543757 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3543757 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3543757 prefixEnd_3543757 := by exact prefixLift 3543757
  have htrace : WordTrace (prefixWord ++ tailWord_3543757) baseStart_3543757 baseEnd_3543757 := by
    simpa [prefixWord, tailWord_3543757, baseEnd_3543757] using wordTrace_append hprefix tailTrace_3543757
  have hstable : (prefixWord ++ tailWord_3543757).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3543757).length < 2 ^ (prefixWord ++ tailWord_3543757).sum := by decide
  have hdescent : baseEnd_3543757 < baseStart_3543757 := by decide
  rcases family_descends (prefixWord ++ tailWord_3543757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3543815 : List Nat := [1, 1, 4, 4, 1, 1, 1, 4, 1, 4]
def baseStart_3543815 : Nat := 118140960795 + 3543815 * 2 ^ 59
def prefixEnd_3543815 : Nat := 4983230072969 + 3 ^ 40 * 3543815 * 2
def baseEnd_3543815 : Nat := 1213120297075438360809865

theorem tailTrace_3543815 : CollatzResearch.WordTrace tailWord_3543815 prefixEnd_3543815 1213120297075438360809865 := by
  unfold tailWord_3543815
  simp only [CollatzResearch.WordTrace]
  refine ⟨129253551656370965261856899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86169034437580643507904599 129253551656370965261856899)
  ·
    refine ⟨193880327484556447892785349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129253551656370965261856899 193880327484556447892785349)
    ·
      refine ⟨36352561403354333979897253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 193880327484556447892785349 36352561403354333979897253)
      ·
        refine ⟨6816105263128937621230735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36352561403354333979897253 6816105263128937621230735)
        ·
          refine ⟨10224157894693406431846103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6816105263128937621230735 10224157894693406431846103)
          ·
            refine ⟨15336236842040109647769155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10224157894693406431846103 15336236842040109647769155)
            ·
              refine ⟨23004355263060164471653733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15336236842040109647769155 23004355263060164471653733)
              ·
                refine ⟨4313316611823780838435075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23004355263060164471653733 4313316611823780838435075)
                ·
                  refine ⟨6469974917735671257652613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4313316611823780838435075 6469974917735671257652613)
                  ·
                    refine ⟨1213120297075438360809865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6469974917735671257652613 1213120297075438360809865)
                    ·
                      rfl

theorem cell22_3543815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 4, 1, 4].length) (baseStart_3543815 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3543815 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3543815 prefixEnd_3543815 := by exact prefixLift 3543815
  have htrace : WordTrace (prefixWord ++ tailWord_3543815) baseStart_3543815 baseEnd_3543815 := by
    simpa [prefixWord, tailWord_3543815, baseEnd_3543815] using wordTrace_append hprefix tailTrace_3543815
  have hstable : (prefixWord ++ tailWord_3543815).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3543815).length < 2 ^ (prefixWord ++ tailWord_3543815).sum := by decide
  have hdescent : baseEnd_3543815 < baseStart_3543815 := by decide
  rcases family_descends (prefixWord ++ tailWord_3543815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3543845 : List Nat := [1, 3, 1, 2, 3, 1, 2, 4, 2, 3]
def baseStart_3543845 : Nat := 118140960795 + 3543845 * 2 ^ 59
def prefixEnd_3543845 : Nat := 4983230072969 + 3 ^ 40 * 3543845 * 2
def baseEnd_3543845 : Nat := 1213130566688528282559773

theorem tailTrace_3543845 : CollatzResearch.WordTrace tailWord_3543845 prefixEnd_3543845 1213130566688528282559773 := by
  unfold tailWord_3543845
  simp only [CollatzResearch.WordTrace]
  refine ⟨129254645846262280385448989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86169763897508186923632659 129254645846262280385448989)
  ·
    refine ⟨48470492192348355144543371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129254645846262280385448989 48470492192348355144543371)
    ·
      refine ⟨72705738288522532716815057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48470492192348355144543371 72705738288522532716815057)
      ·
        refine ⟨54529303716391899537611293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72705738288522532716815057 54529303716391899537611293)
        ·
          refine ⟨20448488893646962326604235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54529303716391899537611293 20448488893646962326604235)
          ·
            refine ⟨30672733340470443489906353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20448488893646962326604235 30672733340470443489906353)
            ·
              refine ⟨23004550005352832617429765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30672733340470443489906353 23004550005352832617429765)
              ·
                refine ⟨4313353126003656115768081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23004550005352832617429765 4313353126003656115768081)
                ·
                  refine ⟨3235014844502742086826061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4313353126003656115768081 3235014844502742086826061)
                  ·
                    refine ⟨1213130566688528282559773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3235014844502742086826061 1213130566688528282559773)
                    ·
                      rfl

theorem cell22_3543845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 4, 2, 3].length) (baseStart_3543845 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3543845 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3543845 prefixEnd_3543845 := by exact prefixLift 3543845
  have htrace : WordTrace (prefixWord ++ tailWord_3543845) baseStart_3543845 baseEnd_3543845 := by
    simpa [prefixWord, tailWord_3543845, baseEnd_3543845] using wordTrace_append hprefix tailTrace_3543845
  have hstable : (prefixWord ++ tailWord_3543845).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3543845).length < 2 ^ (prefixWord ++ tailWord_3543845).sum := by decide
  have hdescent : baseEnd_3543845 < baseStart_3543845 := by decide
  rcases family_descends (prefixWord ++ tailWord_3543845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3543858 : List Nat := [3, 2, 1, 1, 3, 1, 4, 7]
def baseStart_3543858 : Nat := 118140960795 + 3543858 * 2 ^ 59
def prefixEnd_3543858 : Nat := 4983230072969 + 3 ^ 40 * 3543858 * 2
def baseEnd_3543858 : Nat := 134792779650466731331637

theorem tailTrace_3543858 : CollatzResearch.WordTrace tailWord_3543858 prefixEnd_3543858 134792779650466731331637 := by
  unfold tailWord_3543858
  simp only [CollatzResearch.WordTrace]
  refine ⟨32313779998803795901418057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86170079996810122403781485 32313779998803795901418057)
  ·
    refine ⟨24235334999102846926063543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32313779998803795901418057 24235334999102846926063543)
    ·
      refine ⟨36353002498654270389095315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24235334999102846926063543 36353002498654270389095315)
      ·
        refine ⟨54529503747981405583642973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36353002498654270389095315 54529503747981405583642973)
        ·
          refine ⟨20448563905493027093866115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54529503747981405583642973 20448563905493027093866115)
          ·
            refine ⟨30672845858239540640799173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20448563905493027093866115 30672845858239540640799173)
            ·
              refine ⟨5751158598419913870149845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30672845858239540640799173 5751158598419913870149845)
              ·
                refine ⟨134792779650466731331637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5751158598419913870149845 134792779650466731331637)
                ·
                  rfl

theorem cell22_3543858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 4, 7].length) (baseStart_3543858 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3543858 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3543858 prefixEnd_3543858 := by exact prefixLift 3543858
  have htrace : WordTrace (prefixWord ++ tailWord_3543858) baseStart_3543858 baseEnd_3543858 := by
    simpa [prefixWord, tailWord_3543858, baseEnd_3543858] using wordTrace_append hprefix tailTrace_3543858
  have hstable : (prefixWord ++ tailWord_3543858).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3543858).length < 2 ^ (prefixWord ++ tailWord_3543858).sum := by decide
  have hdescent : baseEnd_3543858 < baseStart_3543858 := by decide
  rcases family_descends (prefixWord ++ tailWord_3543858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3543954 : List Nat := [3, 2, 3, 2, 2, 2, 1, 2, 5]
def baseStart_3543954 : Nat := 118140960795 + 3543954 * 2 ^ 59
def prefixEnd_3543954 : Nat := 4983230072969 + 3 ^ 40 * 3543954 * 2
def baseEnd_3543954 : Nat := 404389293205362777194813

theorem tailTrace_3543954 : CollatzResearch.WordTrace tailWord_3543954 prefixEnd_3543954 404389293205362777194813 := by
  unfold tailWord_3543954
  simp only [CollatzResearch.WordTrace]
  refine ⟨32314655350716848000291729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86172414268578261334111277 32314655350716848000291729)
  ·
    refine ⟨24235991513037636000218797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32314655350716848000291729 24235991513037636000218797)
    ·
      refine ⟨9088496817389113500082049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24235991513037636000218797 9088496817389113500082049)
      ·
        refine ⟨6816372613041835125061537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9088496817389113500082049 6816372613041835125061537)
        ·
          refine ⟨5112279459781376343796153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6816372613041835125061537 5112279459781376343796153)
          ·
            refine ⟨3834209594836032257847115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5112279459781376343796153 3834209594836032257847115)
            ·
              refine ⟨5751314392254048386770673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3834209594836032257847115 5751314392254048386770673)
              ·
                refine ⟨4313485794190536290078005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5751314392254048386770673 4313485794190536290078005)
                ·
                  refine ⟨404389293205362777194813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4313485794190536290078005 404389293205362777194813)
                  ·
                    rfl

theorem cell22_3543954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 2, 1, 2, 5].length) (baseStart_3543954 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3543954 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3543954 prefixEnd_3543954 := by exact prefixLift 3543954
  have htrace : WordTrace (prefixWord ++ tailWord_3543954) baseStart_3543954 baseEnd_3543954 := by
    simpa [prefixWord, tailWord_3543954, baseEnd_3543954] using wordTrace_append hprefix tailTrace_3543954
  have hstable : (prefixWord ++ tailWord_3543954).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3543954).length < 2 ^ (prefixWord ++ tailWord_3543954).sum := by decide
  have hdescent : baseEnd_3543954 < baseStart_3543954 := by decide
  rcases family_descends (prefixWord ++ tailWord_3543954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3543958 : List Nat := [5, 3, 1, 1, 1, 1, 2, 4, 1, 3]
def baseStart_3543958 : Nat := 118140960795 + 3543958 * 2 ^ 59
def prefixEnd_3543958 : Nat := 4983230072969 + 3 ^ 40 * 3543958 * 2
def baseEnd_3543958 : Nat := 1213169248897833654484427

theorem tailTrace_3543958 : CollatzResearch.WordTrace tailWord_3543958 prefixEnd_3543958 1213169248897833654484427 := by
  unfold tailWord_3543958
  simp only [CollatzResearch.WordTrace]
  refine ⟨8078672955928306292769533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 86172511529901933789541685 8078672955928306292769533)
  ·
    refine ⟨3029502358473114859788575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8078672955928306292769533 3029502358473114859788575)
    ·
      refine ⟨4544253537709672289682863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3029502358473114859788575 4544253537709672289682863)
      ·
        refine ⟨6816380306564508434524295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4544253537709672289682863 6816380306564508434524295)
        ·
          refine ⟨10224570459846762651786443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6816380306564508434524295 10224570459846762651786443)
          ·
            refine ⟨15336855689770143977679665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10224570459846762651786443 15336855689770143977679665)
            ·
              refine ⟨11502641767327607983259749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15336855689770143977679665 11502641767327607983259749)
              ·
                refine ⟨2156745331373926496861203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11502641767327607983259749 2156745331373926496861203)
                ·
                  refine ⟨3235117997060889745291805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2156745331373926496861203 3235117997060889745291805)
                  ·
                    refine ⟨1213169248897833654484427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3235117997060889745291805 1213169248897833654484427)
                    ·
                      rfl

theorem cell22_3543958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 2, 4, 1, 3].length) (baseStart_3543958 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3543958 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3543958 prefixEnd_3543958 := by exact prefixLift 3543958
  have htrace : WordTrace (prefixWord ++ tailWord_3543958) baseStart_3543958 baseEnd_3543958 := by
    simpa [prefixWord, tailWord_3543958, baseEnd_3543958] using wordTrace_append hprefix tailTrace_3543958
  have hstable : (prefixWord ++ tailWord_3543958).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3543958).length < 2 ^ (prefixWord ++ tailWord_3543958).sum := by decide
  have hdescent : baseEnd_3543958 < baseStart_3543958 := by decide
  rcases family_descends (prefixWord ++ tailWord_3543958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3543965 : List Nat := [1, 4, 2, 1, 2, 1, 4, 1, 6]
def baseStart_3543965 : Nat := 118140960795 + 3543965 * 2 ^ 59
def prefixEnd_3543965 : Nat := 4983230072969 + 3 ^ 40 * 3543965 * 2
def baseEnd_3543965 : Nat := 404390548380295989853135

theorem tailTrace_3543965 : CollatzResearch.WordTrace tailWord_3543965 prefixEnd_3543965 404390548380295989853135 := by
  unfold tailWord_3543965
  simp only [CollatzResearch.WordTrace]
  refine ⟨129259022605827540879817349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86172681737218360586544899 129259022605827540879817349)
  ·
    refine ⟨24236066738592663914965753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 129259022605827540879817349 24236066738592663914965753)
    ·
      refine ⟨18177050053944497936224315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24236066738592663914965753 18177050053944497936224315)
      ·
        refine ⟨27265575080916746904336473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18177050053944497936224315 27265575080916746904336473)
        ·
          refine ⟨20449181310687560178252355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27265575080916746904336473 20449181310687560178252355)
          ·
            refine ⟨30673771966031340267378533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20449181310687560178252355 30673771966031340267378533)
            ·
              refine ⟨5751332243630876300133475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30673771966031340267378533 5751332243630876300133475)
              ·
                refine ⟨8626998365446314450200213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5751332243630876300133475 8626998365446314450200213)
                ·
                  refine ⟨404390548380295989853135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8626998365446314450200213 404390548380295989853135)
                  ·
                    rfl

theorem cell22_3543965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 4, 1, 6].length) (baseStart_3543965 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3543965 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3543965 prefixEnd_3543965 := by exact prefixLift 3543965
  have htrace : WordTrace (prefixWord ++ tailWord_3543965) baseStart_3543965 baseEnd_3543965 := by
    simpa [prefixWord, tailWord_3543965, baseEnd_3543965] using wordTrace_append hprefix tailTrace_3543965
  have hstable : (prefixWord ++ tailWord_3543965).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3543965).length < 2 ^ (prefixWord ++ tailWord_3543965).sum := by decide
  have hdescent : baseEnd_3543965 < baseStart_3543965 := by decide
  rcases family_descends (prefixWord ++ tailWord_3543965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3544031 : List Nat := [1, 1, 2, 3, 5, 2, 2, 1, 2, 3]
def baseStart_3544031 : Nat := 118140960795 + 3544031 * 2 ^ 59
def prefixEnd_3544031 : Nat := 4983230072969 + 3 ^ 40 * 3544031 * 2
def baseEnd_3544031 : Nat := 1213194238289685797409203

theorem tailTrace_3544031 : CollatzResearch.WordTrace tailWord_3544031 prefixEnd_3544031 1213194238289685797409203 := by
  unfold tailWord_3544031
  simp only [CollatzResearch.WordTrace]
  refine ⟨129261429823588434151719947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86174286549058956101146631 129261429823588434151719947)
  ·
    refine ⟨193892144735382651227579921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129261429823588434151719947 193892144735382651227579921)
    ·
      refine ⟨145419108551536988420684941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193892144735382651227579921 145419108551536988420684941)
      ·
        refine ⟨54532165706826370657756853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 145419108551536988420684941 54532165706826370657756853)
        ·
          refine ⟨5112390535014972249164705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 54532165706826370657756853 5112390535014972249164705)
          ·
            refine ⟨3834292901261229186873529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5112390535014972249164705 3834292901261229186873529)
            ·
              refine ⟨2875719675945921890155147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3834292901261229186873529 2875719675945921890155147)
              ·
                refine ⟨4313579513918882835232721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2875719675945921890155147 4313579513918882835232721)
                ·
                  refine ⟨3235184635439162126424541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4313579513918882835232721 3235184635439162126424541)
                  ·
                    refine ⟨1213194238289685797409203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3235184635439162126424541 1213194238289685797409203)
                    ·
                      rfl

theorem cell22_3544031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 2, 2, 1, 2, 3].length) (baseStart_3544031 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3544031 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3544031 prefixEnd_3544031 := by exact prefixLift 3544031
  have htrace : WordTrace (prefixWord ++ tailWord_3544031) baseStart_3544031 baseEnd_3544031 := by
    simpa [prefixWord, tailWord_3544031, baseEnd_3544031] using wordTrace_append hprefix tailTrace_3544031
  have hstable : (prefixWord ++ tailWord_3544031).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3544031).length < 2 ^ (prefixWord ++ tailWord_3544031).sum := by decide
  have hdescent : baseEnd_3544031 < baseStart_3544031 := by decide
  rcases family_descends (prefixWord ++ tailWord_3544031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3544072 : List Nat := [2, 1, 3, 2, 1, 4, 2, 2, 5]
def baseStart_3544072 : Nat := 118140960795 + 3544072 * 2 ^ 59
def prefixEnd_3544072 : Nat := 4983230072969 + 3 ^ 40 * 3544072 * 2
def baseEnd_3544072 : Nat := 404402757809191785711359

theorem tailTrace_3544072 : CollatzResearch.WordTrace tailWord_3544072 prefixEnd_3544072 404402757809191785711359 := by
  unfold tailWord_3544072
  simp only [CollatzResearch.WordTrace]
  refine ⟨64631462608219949076981235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86175283477626598769308313 64631462608219949076981235)
  ·
    refine ⟨96947193912329923615471853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64631462608219949076981235 96947193912329923615471853)
    ·
      refine ⟨36355197717123721355801945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96947193912329923615471853 36355197717123721355801945)
      ·
        refine ⟨27266398287842791016851459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36355197717123721355801945 27266398287842791016851459)
        ·
          refine ⟨40899597431764186525277189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27266398287842791016851459 40899597431764186525277189)
          ·
            refine ⟨7668674518455784973489473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40899597431764186525277189 7668674518455784973489473)
            ·
              refine ⟨5751505888841838730117105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7668674518455784973489473 5751505888841838730117105)
              ·
                refine ⟨4313629416631379047587829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5751505888841838730117105 4313629416631379047587829)
                ·
                  refine ⟨404402757809191785711359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4313629416631379047587829 404402757809191785711359)
                  ·
                    rfl

theorem cell22_3544072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 2, 2, 5].length) (baseStart_3544072 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3544072 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3544072 prefixEnd_3544072 := by exact prefixLift 3544072
  have htrace : WordTrace (prefixWord ++ tailWord_3544072) baseStart_3544072 baseEnd_3544072 := by
    simpa [prefixWord, tailWord_3544072, baseEnd_3544072] using wordTrace_append hprefix tailTrace_3544072
  have hstable : (prefixWord ++ tailWord_3544072).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3544072).length < 2 ^ (prefixWord ++ tailWord_3544072).sum := by decide
  have hdescent : baseEnd_3544072 < baseStart_3544072 := by decide
  rcases family_descends (prefixWord ++ tailWord_3544072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3544076 : List Nat := [2, 2, 1, 2, 3, 2, 4, 2, 1, 3]
def baseStart_3544076 : Nat := 118140960795 + 3544076 * 2 ^ 59
def prefixEnd_3544076 : Nat := 4983230072969 + 3 ^ 40 * 3544076 * 2
def baseEnd_3544076 : Nat := 1213209642709320680034065

theorem tailTrace_3544076 : CollatzResearch.WordTrace tailWord_3544076 prefixEnd_3544076 1213209642709320680034065 := by
  unfold tailWord_3544076
  simp only [CollatzResearch.WordTrace]
  refine ⟨64631535554212703418554041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86175380738950271224738721 64631535554212703418554041)
  ·
    refine ⟨48473651665659527563915531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64631535554212703418554041 48473651665659527563915531)
    ·
      refine ⟨72710477498489291345873297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48473651665659527563915531 72710477498489291345873297)
      ·
        refine ⟨54532858123866968509404973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72710477498489291345873297 54532858123866968509404973)
        ·
          refine ⟨20449821796450113191026865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54532858123866968509404973 20449821796450113191026865)
          ·
            refine ⟨15337366347337584893270149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20449821796450113191026865 15337366347337584893270149)
            ·
              refine ⟨2875756190125797167488153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15337366347337584893270149 2875756190125797167488153)
              ·
                refine ⟨2156817142594347875616115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2875756190125797167488153 2156817142594347875616115)
                ·
                  refine ⟨3235225713891521813424173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2156817142594347875616115 3235225713891521813424173)
                  ·
                    refine ⟨1213209642709320680034065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3235225713891521813424173 1213209642709320680034065)
                    ·
                      rfl

theorem cell22_3544076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 4, 2, 1, 3].length) (baseStart_3544076 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3544076 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3544076 prefixEnd_3544076 := by exact prefixLift 3544076
  have htrace : WordTrace (prefixWord ++ tailWord_3544076) baseStart_3544076 baseEnd_3544076 := by
    simpa [prefixWord, tailWord_3544076, baseEnd_3544076] using wordTrace_append hprefix tailTrace_3544076
  have hstable : (prefixWord ++ tailWord_3544076).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3544076).length < 2 ^ (prefixWord ++ tailWord_3544076).sum := by decide
  have hdescent : baseEnd_3544076 < baseStart_3544076 := by decide
  rcases family_descends (prefixWord ++ tailWord_3544076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3544087 : List Nat := [1, 1, 3, 5, 1, 2, 1, 1, 2, 5]
def baseStart_3544087 : Nat := 118140960795 + 3544087 * 2 ^ 59
def prefixEnd_3544087 : Nat := 4983230072969 + 3 ^ 40 * 3544087 * 2
def baseEnd_3544087 : Nat := 1213213408234120318009031

theorem tailTrace_3544087 : CollatzResearch.WordTrace tailWord_3544087 prefixEnd_3544087 1213213408234120318009031 := by
  unfold tailWord_3544087
  simp only [CollatzResearch.WordTrace]
  refine ⟨129263472311385555715758515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86175648207590370477172343 129263472311385555715758515)
  ·
    refine ⟨193895208467078333573637773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129263472311385555715758515 193895208467078333573637773)
    ·
      refine ⟨72710703175154375090114165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 193895208467078333573637773 72710703175154375090114165)
      ·
        refine ⟨6816628422670722664698203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 72710703175154375090114165 6816628422670722664698203)
        ·
          refine ⟨10224942634006083997047305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6816628422670722664698203 10224942634006083997047305)
          ·
            refine ⟨7668706975504562997785479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10224942634006083997047305 7668706975504562997785479)
            ·
              refine ⟨11503060463256844496678219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7668706975504562997785479 11503060463256844496678219)
              ·
                refine ⟨17254590694885266745017329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11503060463256844496678219 17254590694885266745017329)
                ·
                  refine ⟨12940943021163950058762997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17254590694885266745017329 12940943021163950058762997)
                  ·
                    refine ⟨1213213408234120318009031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12940943021163950058762997 1213213408234120318009031)
                    ·
                      rfl

theorem cell22_3544087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 1, 1, 2, 5].length) (baseStart_3544087 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3544087 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3544087 prefixEnd_3544087 := by exact prefixLift 3544087
  have htrace : WordTrace (prefixWord ++ tailWord_3544087) baseStart_3544087 baseEnd_3544087 := by
    simpa [prefixWord, tailWord_3544087, baseEnd_3544087] using wordTrace_append hprefix tailTrace_3544087
  have hstable : (prefixWord ++ tailWord_3544087).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3544087).length < 2 ^ (prefixWord ++ tailWord_3544087).sum := by decide
  have hdescent : baseEnd_3544087 < baseStart_3544087 := by decide
  rcases family_descends (prefixWord ++ tailWord_3544087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3544134 : List Nat := [6, 1, 1, 1, 1, 2, 1, 3, 6]
def baseStart_3544134 : Nat := 118140960795 + 3544134 * 2 ^ 59
def prefixEnd_3544134 : Nat := 4983230072969 + 3 ^ 40 * 3544134 * 2
def baseEnd_3544134 : Nat := 404409832431542620694629

theorem tailTrace_3544134 : CollatzResearch.WordTrace tailWord_3544134 prefixEnd_3544134 404409832431542620694629 := by
  unfold tailWord_3544134
  simp only [CollatzResearch.WordTrace]
  refine ⟨4039537079444227585709983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 86176791028143521828479637 4039537079444227585709983)
  ·
    refine ⟨6059305619166341378564975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4039537079444227585709983 6059305619166341378564975)
    ·
      refine ⟨9088958428749512067847463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6059305619166341378564975 9088958428749512067847463)
      ·
        refine ⟨13633437643124268101771195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9088958428749512067847463 13633437643124268101771195)
        ·
          refine ⟨20450156464686402152656793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13633437643124268101771195 20450156464686402152656793)
          ·
            refine ⟨15337617348514801614492595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20450156464686402152656793 15337617348514801614492595)
            ·
              refine ⟨23006426022772202421738893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15337617348514801614492595 23006426022772202421738893)
              ·
                refine ⟨8627409758539575908152085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23006426022772202421738893 8627409758539575908152085)
                ·
                  refine ⟨404409832431542620694629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8627409758539575908152085 404409832431542620694629)
                  ·
                    rfl

theorem cell22_3544134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 3, 6].length) (baseStart_3544134 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3544134 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3544134 prefixEnd_3544134 := by exact prefixLift 3544134
  have htrace : WordTrace (prefixWord ++ tailWord_3544134) baseStart_3544134 baseEnd_3544134 := by
    simpa [prefixWord, tailWord_3544134, baseEnd_3544134] using wordTrace_append hprefix tailTrace_3544134
  have hstable : (prefixWord ++ tailWord_3544134).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3544134).length < 2 ^ (prefixWord ++ tailWord_3544134).sum := by decide
  have hdescent : baseEnd_3544134 < baseStart_3544134 := by decide
  rcases family_descends (prefixWord ++ tailWord_3544134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3544160 : List Nat := [2, 1, 1, 3, 2, 2, 1, 1, 2, 7]
def baseStart_3544160 : Nat := 118140960795 + 3544160 * 2 ^ 59
def prefixEnd_3544160 : Nat := 4983230072969 + 3 ^ 40 * 3544160 * 2
def baseEnd_3544160 : Nat := 1213238397625972460933807

theorem tailTrace_3544160 : CollatzResearch.WordTrace tailWord_3544160 prefixEnd_3544160 1213238397625972460933807 := by
  unfold tailWord_3544160
  simp only [CollatzResearch.WordTrace]
  refine ⟨64633067420060544591582967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86177423226747392788777289 64633067420060544591582967)
  ·
    refine ⟨96949601130090816887374451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64633067420060544591582967 96949601130090816887374451)
    ·
      refine ⟨145424401695136225331061677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96949601130090816887374451 145424401695136225331061677)
      ·
        refine ⟨54534150635676084499148129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 145424401695136225331061677 54534150635676084499148129)
        ·
          refine ⟨40900612976757063374361097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54534150635676084499148129 40900612976757063374361097)
          ·
            refine ⟨30675459732567797530770823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40900612976757063374361097 30675459732567797530770823)
            ·
              refine ⟨46013189598851696296156235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30675459732567797530770823 46013189598851696296156235)
              ·
                refine ⟨69019784398277544444234353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46013189598851696296156235 69019784398277544444234353)
                ·
                  refine ⟨51764838298708158333175765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69019784398277544444234353 51764838298708158333175765)
                  ·
                    refine ⟨1213238397625972460933807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 51764838298708158333175765 1213238397625972460933807)
                    ·
                      rfl

theorem cell22_3544160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 1, 2, 7].length) (baseStart_3544160 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3544160 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3544160 prefixEnd_3544160 := by exact prefixLift 3544160
  have htrace : WordTrace (prefixWord ++ tailWord_3544160) baseStart_3544160 baseEnd_3544160 := by
    simpa [prefixWord, tailWord_3544160, baseEnd_3544160] using wordTrace_append hprefix tailTrace_3544160
  have hstable : (prefixWord ++ tailWord_3544160).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3544160).length < 2 ^ (prefixWord ++ tailWord_3544160).sum := by decide
  have hdescent : baseEnd_3544160 < baseStart_3544160 := by decide
  rcases family_descends (prefixWord ++ tailWord_3544160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3544168 : List Nat := [2, 1, 4, 4, 1, 2, 1, 3, 4]
def baseStart_3544168 : Nat := 118140960795 + 3544168 * 2 ^ 59
def prefixEnd_3544168 : Nat := 4983230072969 + 3 ^ 40 * 3544168 * 2
def baseEnd_3544168 : Nat := 404413712063154368911261

theorem tailTrace_3544168 : CollatzResearch.WordTrace tailWord_3544168 prefixEnd_3544168 404413712063154368911261 := by
  unfold tailWord_3544168
  simp only [CollatzResearch.WordTrace]
  refine ⟨64633213312046053274728579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86177617749394737699638105 64633213312046053274728579)
  ·
    refine ⟨96949819968069079912092869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64633213312046053274728579 96949819968069079912092869)
    ·
      refine ⟨18178091244012952483517413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 96949819968069079912092869 18178091244012952483517413)
      ·
        refine ⟨3408392108252428590659515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18178091244012952483517413 3408392108252428590659515)
        ·
          refine ⟨5112588162378642885989273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3408392108252428590659515 5112588162378642885989273)
          ·
            refine ⟨3834441121783982164491955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5112588162378642885989273 3834441121783982164491955)
            ·
              refine ⟨5751661682675973246737933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3834441121783982164491955 5751661682675973246737933)
              ·
                refine ⟨2156873131003489967526725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5751661682675973246737933 2156873131003489967526725)
                ·
                  refine ⟨404413712063154368911261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2156873131003489967526725 404413712063154368911261)
                  ·
                    rfl

theorem cell22_3544168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 2, 1, 3, 4].length) (baseStart_3544168 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3544168 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3544168 prefixEnd_3544168 := by exact prefixLift 3544168
  have htrace : WordTrace (prefixWord ++ tailWord_3544168) baseStart_3544168 baseEnd_3544168 := by
    simpa [prefixWord, tailWord_3544168, baseEnd_3544168] using wordTrace_append hprefix tailTrace_3544168
  have hstable : (prefixWord ++ tailWord_3544168).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3544168).length < 2 ^ (prefixWord ++ tailWord_3544168).sum := by decide
  have hdescent : baseEnd_3544168 < baseStart_3544168 := by decide
  rcases family_descends (prefixWord ++ tailWord_3544168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3544181 : List Nat := [1, 3, 4, 3, 1, 1, 1, 2, 2, 4]
def baseStart_3544181 : Nat := 118140960795 + 3544181 * 2 ^ 59
def prefixEnd_3544181 : Nat := 4983230072969 + 3 ^ 40 * 3544181 * 2
def baseEnd_3544181 : Nat := 1213245586355135406158743

theorem tailTrace_3544181 : CollatzResearch.WordTrace tailWord_3544181 prefixEnd_3544181 1213245586355135406158743 := by
  unfold tailWord_3544181
  simp only [CollatzResearch.WordTrace]
  refine ⟨129266900773045009769680397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86177933848696673179786931 129266900773045009769680397)
  ·
    refine ⟨48475087789891878663630149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129266900773045009769680397 48475087789891878663630149)
    ·
      refine ⟨9089078960604727249430653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48475087789891878663630149 9089078960604727249430653)
      ·
        refine ⟨3408404610226772718536495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9089078960604727249430653 3408404610226772718536495)
        ·
          refine ⟨5112606915340159077804743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3408404610226772718536495 5112606915340159077804743)
          ·
            refine ⟨7668910373010238616707115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5112606915340159077804743 7668910373010238616707115)
            ·
              refine ⟨11503365559515357925060673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7668910373010238616707115 11503365559515357925060673)
              ·
                refine ⟨8627524169636518443795505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11503365559515357925060673 8627524169636518443795505)
                ·
                  refine ⟨6470643127227388832846629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8627524169636518443795505 6470643127227388832846629)
                  ·
                    refine ⟨1213245586355135406158743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6470643127227388832846629 1213245586355135406158743)
                    ·
                      rfl

theorem cell22_3544181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 1, 2, 2, 4].length) (baseStart_3544181 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3544181 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3544181 prefixEnd_3544181 := by exact prefixLift 3544181
  have htrace : WordTrace (prefixWord ++ tailWord_3544181) baseStart_3544181 baseEnd_3544181 := by
    simpa [prefixWord, tailWord_3544181, baseEnd_3544181] using wordTrace_append hprefix tailTrace_3544181
  have hstable : (prefixWord ++ tailWord_3544181).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3544181).length < 2 ^ (prefixWord ++ tailWord_3544181).sum := by decide
  have hdescent : baseEnd_3544181 < baseStart_3544181 := by decide
  rcases family_descends (prefixWord ++ tailWord_3544181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3544200 : List Nat := [2, 1, 3, 4, 3, 1, 2, 1, 2, 3]
def baseStart_3544200 : Nat := 118140960795 + 3544200 * 2 ^ 59
def prefixEnd_3544200 : Nat := 4983230072969 + 3 ^ 40 * 3544200 * 2
def baseEnd_3544200 : Nat := 1213252090443425689933685

theorem tailTrace_3544200 : CollatzResearch.WordTrace tailWord_3544200 prefixEnd_3544200 1213252090443425689933685 := by
  unfold tailWord_3544200
  simp only [CollatzResearch.WordTrace]
  refine ⟨64633796879988088007311027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86178395839984117343081369 64633796879988088007311027)
  ·
    refine ⟨96950695319982132010966541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64633796879988088007311027 96950695319982132010966541)
    ·
      refine ⟨36356510744993299504112453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96950695319982132010966541 36356510744993299504112453)
      ·
        refine ⟨6816845764686243657021085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36356510744993299504112453 6816845764686243657021085)
        ·
          refine ⟨2556317161757341371382907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6816845764686243657021085 2556317161757341371382907)
          ·
            refine ⟨3834475742636012057074361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2556317161757341371382907 3834475742636012057074361)
            ·
              refine ⟨2875856806977009042805771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3834475742636012057074361 2875856806977009042805771)
              ·
                refine ⟨4313785210465513564208657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2875856806977009042805771 4313785210465513564208657)
                ·
                  refine ⟨3235338907849135173156493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4313785210465513564208657 3235338907849135173156493)
                  ·
                    refine ⟨1213252090443425689933685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3235338907849135173156493 1213252090443425689933685)
                    ·
                      rfl

theorem cell22_3544200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 3, 1, 2, 1, 2, 3].length) (baseStart_3544200 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3544200 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3544200 prefixEnd_3544200 := by exact prefixLift 3544200
  have htrace : WordTrace (prefixWord ++ tailWord_3544200) baseStart_3544200 baseEnd_3544200 := by
    simpa [prefixWord, tailWord_3544200, baseEnd_3544200] using wordTrace_append hprefix tailTrace_3544200
  have hstable : (prefixWord ++ tailWord_3544200).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3544200).length < 2 ^ (prefixWord ++ tailWord_3544200).sum := by decide
  have hdescent : baseEnd_3544200 < baseStart_3544200 := by decide
  rcases family_descends (prefixWord ++ tailWord_3544200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3544254 : List Nat := [4, 2, 1, 1, 3, 1, 1, 2, 3, 4]
def baseStart_3544254 : Nat := 118140960795 + 3544254 * 2 ^ 59
def prefixEnd_3544254 : Nat := 4983230072969 + 3 ^ 40 * 3544254 * 2
def baseEnd_3544254 : Nat := 1213270575746987549083519

theorem tailTrace_3544254 : CollatzResearch.WordTrace tailWord_3544254 prefixEnd_3544254 1213270575746987549083519 := by
  unfold tailWord_3544254
  simp only [CollatzResearch.WordTrace]
  refine ⟨16158695412722567904635977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 86179708867853695491391877 16158695412722567904635977)
  ·
    refine ⟨12119021559541925928476983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16158695412722567904635977 12119021559541925928476983)
    ·
      refine ⟨18178532339312888892715475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12119021559541925928476983 18178532339312888892715475)
      ·
        refine ⟨27267798508969333339073213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18178532339312888892715475 27267798508969333339073213)
        ·
          refine ⟨10225424440863500002152455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27267798508969333339073213 10225424440863500002152455)
          ·
            refine ⟨15338136661295250003228683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10225424440863500002152455 15338136661295250003228683)
            ·
              refine ⟨23007204991942875004843025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15338136661295250003228683 23007204991942875004843025)
              ·
                refine ⟨17255403743957156253632269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23007204991942875004843025 17255403743957156253632269)
                ·
                  refine ⟨6470776403983933595112101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17255403743957156253632269 6470776403983933595112101)
                  ·
                    refine ⟨1213270575746987549083519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6470776403983933595112101 1213270575746987549083519)
                    ·
                      rfl

theorem cell22_3544254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 2, 3, 4].length) (baseStart_3544254 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3544254 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3544254 prefixEnd_3544254 := by exact prefixLift 3544254
  have htrace : WordTrace (prefixWord ++ tailWord_3544254) baseStart_3544254 baseEnd_3544254 := by
    simpa [prefixWord, tailWord_3544254, baseEnd_3544254] using wordTrace_append hprefix tailTrace_3544254
  have hstable : (prefixWord ++ tailWord_3544254).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3544254).length < 2 ^ (prefixWord ++ tailWord_3544254).sum := by decide
  have hdescent : baseEnd_3544254 < baseStart_3544254 := by decide
  rcases family_descends (prefixWord ++ tailWord_3544254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3544301 : List Nat := [1, 5, 1, 2, 2, 2, 1, 1, 4, 3]
def baseStart_3544301 : Nat := 118140960795 + 3544301 * 2 ^ 59
def prefixEnd_3544301 : Nat := 4983230072969 + 3 ^ 40 * 3544301 * 2
def baseEnd_3544301 : Nat := 1213286664807495093158375

theorem tailTrace_3544301 : CollatzResearch.WordTrace tailWord_3544301 prefixEnd_3544301 1213286664807495093158375 := by
  unfold tailWord_3544301
  simp only [CollatzResearch.WordTrace]
  refine ⟨129271277532610270264048757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86180851688406846842699171 129271277532610270264048757)
  ·
    refine ⟨12119182268682212837254571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 129271277532610270264048757 12119182268682212837254571)
    ·
      refine ⟨18178773403023319255881857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12119182268682212837254571 18178773403023319255881857)
      ·
        refine ⟨13634080052267489441911393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18178773403023319255881857 13634080052267489441911393)
        ·
          refine ⟨10225560039200617081433545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13634080052267489441911393 10225560039200617081433545)
          ·
            refine ⟨7669170029400462811075159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10225560039200617081433545 7669170029400462811075159)
            ·
              refine ⟨11503755044100694216612739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7669170029400462811075159 11503755044100694216612739)
              ·
                refine ⟨17255632566151041324919109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11503755044100694216612739 17255632566151041324919109)
                ·
                  refine ⟨3235431106153320248422333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17255632566151041324919109 3235431106153320248422333)
                  ·
                    refine ⟨1213286664807495093158375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3235431106153320248422333 1213286664807495093158375)
                    ·
                      rfl

theorem cell22_3544301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 1, 1, 4, 3].length) (baseStart_3544301 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3544301 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3544301 prefixEnd_3544301 := by exact prefixLift 3544301
  have htrace : WordTrace (prefixWord ++ tailWord_3544301) baseStart_3544301 baseEnd_3544301 := by
    simpa [prefixWord, tailWord_3544301, baseEnd_3544301] using wordTrace_append hprefix tailTrace_3544301
  have hstable : (prefixWord ++ tailWord_3544301).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3544301).length < 2 ^ (prefixWord ++ tailWord_3544301).sum := by decide
  have hdescent : baseEnd_3544301 < baseStart_3544301 := by decide
  rcases family_descends (prefixWord ++ tailWord_3544301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3544329 : List Nat := [1, 2, 1, 1, 3, 3, 1, 4, 3, 3]
def baseStart_3544329 : Nat := 118140960795 + 3544329 * 2 ^ 59
def prefixEnd_3544329 : Nat := 4983230072969 + 3 ^ 40 * 3544329 * 2
def baseEnd_3544329 : Nat := 1213296249779712353458289

theorem tailTrace_3544329 : CollatzResearch.WordTrace tailWord_3544329 prefixEnd_3544329 1213296249779712353458289 := by
  unfold tailWord_3544329
  simp only [CollatzResearch.WordTrace]
  refine ⟨129272298776508831046068041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86181532517672554030712027 129272298776508831046068041)
  ·
    refine ⟨96954224082381623284551031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129272298776508831046068041 96954224082381623284551031)
    ·
      refine ⟨145431336123572434926826547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96954224082381623284551031 145431336123572434926826547)
      ·
        refine ⟨218147004185358652390239821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145431336123572434926826547 218147004185358652390239821)
        ·
          refine ⟨81805126569509494646339933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 218147004185358652390239821 81805126569509494646339933)
          ·
            refine ⟨30676922463566060492377475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81805126569509494646339933 30676922463566060492377475)
            ·
              refine ⟨46015383695349090738566213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30676922463566060492377475 46015383695349090738566213)
              ·
                refine ⟨8627884442877954513481165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46015383695349090738566213 8627884442877954513481165)
                ·
                  refine ⟨3235456666079232942555437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8627884442877954513481165 3235456666079232942555437)
                  ·
                    refine ⟨1213296249779712353458289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3235456666079232942555437 1213296249779712353458289)
                    ·
                      rfl

theorem cell22_3544329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 4, 3, 3].length) (baseStart_3544329 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3544329 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3544329 prefixEnd_3544329 := by exact prefixLift 3544329
  have htrace : WordTrace (prefixWord ++ tailWord_3544329) baseStart_3544329 baseEnd_3544329 := by
    simpa [prefixWord, tailWord_3544329, baseEnd_3544329] using wordTrace_append hprefix tailTrace_3544329
  have hstable : (prefixWord ++ tailWord_3544329).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3544329).length < 2 ^ (prefixWord ++ tailWord_3544329).sum := by decide
  have hdescent : baseEnd_3544329 < baseStart_3544329 := by decide
  rcases family_descends (prefixWord ++ tailWord_3544329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3544387 : List Nat := [1, 1, 1, 3, 1, 3, 1, 3, 8]
def baseStart_3544387 : Nat := 118140960795 + 3544387 * 2 ^ 59
def prefixEnd_3544387 : Nat := 4983230072969 + 3 ^ 40 * 3544387 * 2
def baseEnd_3544387 : Nat := 404438701455006511836037

theorem tailTrace_3544387 : CollatzResearch.WordTrace tailWord_3544387 prefixEnd_3544387 404438701455006511836037 := by
  unfold tailWord_3544387
  simp only [CollatzResearch.WordTrace]
  refine ⟨129274414210298706951679415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86182942806865804634452943 129274414210298706951679415)
  ·
    refine ⟨193911621315448060427519123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129274414210298706951679415 193911621315448060427519123)
    ·
      refine ⟨290867431973172090641278685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193911621315448060427519123 290867431973172090641278685)
      ·
        refine ⟨109075286989939533990479507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 290867431973172090641278685 109075286989939533990479507)
        ·
          refine ⟨163612930484909300985719261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109075286989939533990479507 163612930484909300985719261)
          ·
            refine ⟨61354848931840987869644723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 163612930484909300985719261 61354848931840987869644723)
            ·
              refine ⟨92032273397761481804467085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61354848931840987869644723 92032273397761481804467085)
              ·
                refine ⟨34512102524160555676675157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 92032273397761481804467085 34512102524160555676675157)
                ·
                  refine ⟨404438701455006511836037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 34512102524160555676675157 404438701455006511836037)
                  ·
                    rfl

theorem cell22_3544387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 3, 8].length) (baseStart_3544387 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3544387 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3544387 prefixEnd_3544387 := by exact prefixLift 3544387
  have htrace : WordTrace (prefixWord ++ tailWord_3544387) baseStart_3544387 baseEnd_3544387 := by
    simpa [prefixWord, tailWord_3544387, baseEnd_3544387] using wordTrace_append hprefix tailTrace_3544387
  have hstable : (prefixWord ++ tailWord_3544387).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3544387).length < 2 ^ (prefixWord ++ tailWord_3544387).sum := by decide
  have hdescent : baseEnd_3544387 < baseStart_3544387 := by decide
  rcases family_descends (prefixWord ++ tailWord_3544387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3544421 : List Nat := [1, 3, 1, 3, 1, 2, 3, 4, 4]
def baseStart_3544421 : Nat := 118140960795 + 3544421 * 2 ^ 59
def prefixEnd_3544421 : Nat := 4983230072969 + 3 ^ 40 * 3544421 * 2
def baseEnd_3544421 : Nat := 404442581086618260052669

theorem tailTrace_3544421 : CollatzResearch.WordTrace tailWord_3544421 prefixEnd_3544421 404442581086618260052669 := by
  unfold tailWord_3544421
  simp only [CollatzResearch.WordTrace]
  refine ⟨129275654292175530758417117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86183769528117020505611411 129275654292175530758417117)
  ·
    refine ⟨48478370359565824034406419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129275654292175530758417117 48478370359565824034406419)
    ·
      refine ⟨72717555539348736051609629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48478370359565824034406419 72717555539348736051609629)
      ·
        refine ⟨27269083327255776019353611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72717555539348736051609629 27269083327255776019353611)
        ·
          refine ⟨40903624990883664029030417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27269083327255776019353611 40903624990883664029030417)
          ·
            refine ⟨30677718743162748021772813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40903624990883664029030417 30677718743162748021772813)
            ·
              refine ⟨11504144528686030508164805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30677718743162748021772813 11504144528686030508164805)
              ·
                refine ⟨2157027099128630720280901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11504144528686030508164805 2157027099128630720280901)
                ·
                  refine ⟨404442581086618260052669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2157027099128630720280901 404442581086618260052669)
                  ·
                    rfl

theorem cell22_3544421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 3, 4, 4].length) (baseStart_3544421 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3544421 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3544421 prefixEnd_3544421 := by exact prefixLift 3544421
  have htrace : WordTrace (prefixWord ++ tailWord_3544421) baseStart_3544421 baseEnd_3544421 := by
    simpa [prefixWord, tailWord_3544421, baseEnd_3544421] using wordTrace_append hprefix tailTrace_3544421
  have hstable : (prefixWord ++ tailWord_3544421).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3544421).length < 2 ^ (prefixWord ++ tailWord_3544421).sum := by decide
  have hdescent : baseEnd_3544421 < baseStart_3544421 := by decide
  rcases family_descends (prefixWord ++ tailWord_3544421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3544434 : List Nat := [3, 2, 1, 2, 1, 2, 2, 2, 1, 6]
def baseStart_3544434 : Nat := 118140960795 + 3544434 * 2 ^ 59
def prefixEnd_3544434 : Nat := 4983230072969 + 3 ^ 40 * 3544434 * 2
def baseEnd_3544434 : Nat := 1213332193425527079582967

theorem tailTrace_3544434 : CollatzResearch.WordTrace tailWord_3544434 prefixEnd_3544434 1213332193425527079582967 := by
  unfold tailWord_3544434
  simp only [CollatzResearch.WordTrace]
  refine ⟨32319032110282108494660089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86184085627418955985760237 32319032110282108494660089)
  ·
    refine ⟨24239274082711581370995067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32319032110282108494660089 24239274082711581370995067)
    ·
      refine ⟨36358911124067372056492601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24239274082711581370995067 36358911124067372056492601)
      ·
        refine ⟨27269183343050529042369451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36358911124067372056492601 27269183343050529042369451)
        ·
          refine ⟨40903775014575793563554177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27269183343050529042369451 40903775014575793563554177)
          ·
            refine ⟨30677831260931845172665633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40903775014575793563554177 30677831260931845172665633)
            ·
              refine ⟨23008373445698883879499225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30677831260931845172665633 23008373445698883879499225)
              ·
                refine ⟨17256280084274162909624419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23008373445698883879499225 17256280084274162909624419)
                ·
                  refine ⟨25884420126411244364436629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17256280084274162909624419 25884420126411244364436629)
                  ·
                    refine ⟨1213332193425527079582967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25884420126411244364436629 1213332193425527079582967)
                    ·
                      rfl

theorem cell22_3544434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 2, 1, 6].length) (baseStart_3544434 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3544434 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3544434 prefixEnd_3544434 := by exact prefixLift 3544434
  have htrace : WordTrace (prefixWord ++ tailWord_3544434) baseStart_3544434 baseEnd_3544434 := by
    simpa [prefixWord, tailWord_3544434, baseEnd_3544434] using wordTrace_append hprefix tailTrace_3544434
  have hstable : (prefixWord ++ tailWord_3544434).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3544434).length < 2 ^ (prefixWord ++ tailWord_3544434).sum := by decide
  have hdescent : baseEnd_3544434 < baseStart_3544434 := by decide
  rcases family_descends (prefixWord ++ tailWord_3544434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3544451 : List Nat := [1, 1, 1, 3, 5, 1, 3, 1, 2, 4]
def baseStart_3544451 : Nat := 118140960795 + 3544451 * 2 ^ 59
def prefixEnd_3544451 : Nat := 4983230072969 + 3 ^ 40 * 3544451 * 2
def baseEnd_3544451 : Nat := 1213338012872944701907915

theorem tailTrace_3544451 : CollatzResearch.WordTrace tailWord_3544451 prefixEnd_3544451 1213338012872944701907915 := by
  unfold tailWord_3544451
  simp only [CollatzResearch.WordTrace]
  refine ⟨129276748482066845882009207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86184498988044563921339471 129276748482066845882009207)
  ·
    refine ⟨193915122723100268823013811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129276748482066845882009207 193915122723100268823013811)
    ·
      refine ⟨290872684084650403234520717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193915122723100268823013811 290872684084650403234520717)
      ·
        refine ⟨109077256531743901212945269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 290872684084650403234520717 109077256531743901212945269)
        ·
          refine ⟨10225992799850990738713619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 109077256531743901212945269 10225992799850990738713619)
          ·
            refine ⟨15338989199776486108070429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10225992799850990738713619 15338989199776486108070429)
            ·
              refine ⟨5752120949916182290526411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15338989199776486108070429 5752120949916182290526411)
              ·
                refine ⟨8628181424874273435789617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5752120949916182290526411 8628181424874273435789617)
                ·
                  refine ⟨6471136068655705076842213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8628181424874273435789617 6471136068655705076842213)
                  ·
                    refine ⟨1213338012872944701907915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6471136068655705076842213 1213338012872944701907915)
                    ·
                      rfl

theorem cell22_3544451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 3, 1, 2, 4].length) (baseStart_3544451 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3544451 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3544451 prefixEnd_3544451 := by exact prefixLift 3544451
  have htrace : WordTrace (prefixWord ++ tailWord_3544451) baseStart_3544451 baseEnd_3544451 := by
    simpa [prefixWord, tailWord_3544451, baseEnd_3544451] using wordTrace_append hprefix tailTrace_3544451
  have hstable : (prefixWord ++ tailWord_3544451).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3544451).length < 2 ^ (prefixWord ++ tailWord_3544451).sum := by decide
  have hdescent : baseEnd_3544451 < baseStart_3544451 := by decide
  rcases family_descends (prefixWord ++ tailWord_3544451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3544532 : List Nat := [2, 4, 1, 2, 4, 1, 1, 1, 3, 3]
def baseStart_3544532 : Nat := 118140960795 + 3544532 * 2 ^ 59
def prefixEnd_3544532 : Nat := 4983230072969 + 3 ^ 40 * 3544532 * 2
def baseEnd_3544532 : Nat := 1213365740828287490632667

theorem tailTrace_3544532 : CollatzResearch.WordTrace tailWord_3544532 prefixEnd_3544532 1213365740828287490632667 := by
  unfold tailWord_3544532
  simp only [CollatzResearch.WordTrace]
  refine ⟨64639851397386698357853925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86186468529848931143805233 64639851397386698357853925)
  ·
    refine ⟨12119972137010005942097611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 64639851397386698357853925 12119972137010005942097611)
    ·
      refine ⟨18179958205515008913146417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12119972137010005942097611 18179958205515008913146417)
      ·
        refine ⟨13634968654136256684859813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18179958205515008913146417 13634968654136256684859813)
        ·
          refine ⟨2556556622650548128411215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13634968654136256684859813 2556556622650548128411215)
          ·
            refine ⟨3834834933975822192616823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2556556622650548128411215 3834834933975822192616823)
            ·
              refine ⟨5752252400963733288925235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3834834933975822192616823 5752252400963733288925235)
              ·
                refine ⟨8628378601445599933387853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5752252400963733288925235 8628378601445599933387853)
                ·
                  refine ⟨3235641975542099975020445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8628378601445599933387853 3235641975542099975020445)
                  ·
                    refine ⟨1213365740828287490632667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3235641975542099975020445 1213365740828287490632667)
                    ·
                      rfl

theorem cell22_3544532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 4, 1, 1, 1, 3, 3].length) (baseStart_3544532 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3544532 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3544532 prefixEnd_3544532 := by exact prefixLift 3544532
  have htrace : WordTrace (prefixWord ++ tailWord_3544532) baseStart_3544532 baseEnd_3544532 := by
    simpa [prefixWord, tailWord_3544532, baseEnd_3544532] using wordTrace_append hprefix tailTrace_3544532
  have hstable : (prefixWord ++ tailWord_3544532).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3544532).length < 2 ^ (prefixWord ++ tailWord_3544532).sum := by decide
  have hdescent : baseEnd_3544532 < baseStart_3544532 := by decide
  rcases family_descends (prefixWord ++ tailWord_3544532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3544590 : List Nat := [4, 1, 1, 2, 4, 1, 1, 4, 4]
def baseStart_3544590 : Nat := 118140960795 + 3544590 * 2 ^ 59
def prefixEnd_3544590 : Nat := 4983230072969 + 3 ^ 40 * 3544590 * 2
def baseEnd_3544590 : Nat := 404461865137864890894163

theorem tailTrace_3544590 : CollatzResearch.WordTrace tailWord_3544590 prefixEnd_3544590 404461865137864890894163 := by
  unfold tailWord_3544590
  simp only [CollatzResearch.WordTrace]
  refine ⟨16160227278570409077664903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 86187878819042181747546149 16160227278570409077664903)
  ·
    refine ⟨24240340917855613616497355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16160227278570409077664903 24240340917855613616497355)
    ·
      refine ⟨36360511376783420424746033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24240340917855613616497355 36360511376783420424746033)
      ·
        refine ⟨27270383532587565318559525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36360511376783420424746033 27270383532587565318559525)
        ·
          refine ⟨5113196912360168497229911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27270383532587565318559525 5113196912360168497229911)
          ·
            refine ⟨7669795368540252745844867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5113196912360168497229911 7669795368540252745844867)
            ·
              refine ⟨11504693052810379118767301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7669795368540252745844867 11504693052810379118767301)
              ·
                refine ⟨2157129947401946084768869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11504693052810379118767301 2157129947401946084768869)
                ·
                  refine ⟨404461865137864890894163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2157129947401946084768869 404461865137864890894163)
                  ·
                    rfl

theorem cell22_3544590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 1, 4, 4].length) (baseStart_3544590 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3544590 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3544590 prefixEnd_3544590 := by exact prefixLift 3544590
  have htrace : WordTrace (prefixWord ++ tailWord_3544590) baseStart_3544590 baseEnd_3544590 := by
    simpa [prefixWord, tailWord_3544590, baseEnd_3544590] using wordTrace_append hprefix tailTrace_3544590
  have hstable : (prefixWord ++ tailWord_3544590).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3544590).length < 2 ^ (prefixWord ++ tailWord_3544590).sum := by decide
  have hdescent : baseEnd_3544590 < baseStart_3544590 := by decide
  rcases family_descends (prefixWord ++ tailWord_3544590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3544618 : List Nat := [3, 1, 4, 1, 1, 1, 5, 6]
def baseStart_3544618 : Nat := 118140960795 + 3544618 * 2 ^ 59
def prefixEnd_3544618 : Nat := 4983230072969 + 3 ^ 40 * 3544618 * 2
def baseEnd_3544618 : Nat := 134821686709534659220267

theorem tailTrace_3544618 : CollatzResearch.WordTrace tailWord_3544618 prefixEnd_3544618 134821686709534659220267 := by
  unfold tailWord_3544618
  simp only [CollatzResearch.WordTrace]
  refine ⟨32320709868115458350834627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86188559648307888935559005 32320709868115458350834627)
  ·
    refine ⟨48481064802173187526251941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32320709868115458350834627 48481064802173187526251941)
    ·
      refine ⟨9090199650407472661172239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48481064802173187526251941 9090199650407472661172239)
      ·
        refine ⟨13635299475611208991758359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9090199650407472661172239 13635299475611208991758359)
        ·
          refine ⟨20452949213416813487637539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13635299475611208991758359 20452949213416813487637539)
          ·
            refine ⟨30679423820125220231456309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20452949213416813487637539 30679423820125220231456309)
            ·
              refine ⟨2876195983136739396699029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30679423820125220231456309 2876195983136739396699029)
              ·
                refine ⟨134821686709534659220267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2876195983136739396699029 134821686709534659220267)
                ·
                  rfl

theorem cell22_3544618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 5, 6].length) (baseStart_3544618 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3544618 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3544618 prefixEnd_3544618 := by exact prefixLift 3544618
  have htrace : WordTrace (prefixWord ++ tailWord_3544618) baseStart_3544618 baseEnd_3544618 := by
    simpa [prefixWord, tailWord_3544618, baseEnd_3544618] using wordTrace_append hprefix tailTrace_3544618
  have hstable : (prefixWord ++ tailWord_3544618).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3544618).length < 2 ^ (prefixWord ++ tailWord_3544618).sum := by decide
  have hdescent : baseEnd_3544618 < baseStart_3544618 := by decide
  rcases family_descends (prefixWord ++ tailWord_3544618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3544650 : List Nat := [3, 1, 2, 1, 1, 3, 1, 6, 1, 3]
def baseStart_3544650 : Nat := 118140960795 + 3544650 * 2 ^ 59
def prefixEnd_3544650 : Nat := 4983230072969 + 3 ^ 40 * 3544650 * 2
def baseEnd_3544650 : Nat := 1213406134639774516182305

theorem tailTrace_3544650 : CollatzResearch.WordTrace tailWord_3544650 prefixEnd_3544650 1213406134639774516182305 := by
  unfold tailWord_3544650
  simp only [CollatzResearch.WordTrace]
  refine ⟨32321001652086475717125851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86189337738897268579002269 32321001652086475717125851)
  ·
    refine ⟨48481502478129713575688777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32321001652086475717125851 48481502478129713575688777)
    ·
      refine ⟨36361126858597285181766583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48481502478129713575688777 36361126858597285181766583)
      ·
        refine ⟨54541690287895927772649875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36361126858597285181766583 54541690287895927772649875)
        ·
          refine ⟨81812535431843891658974813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54541690287895927772649875 81812535431843891658974813)
          ·
            refine ⟨30679700786941459372115555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81812535431843891658974813 30679700786941459372115555)
            ·
              refine ⟨46019551180412189058173333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30679700786941459372115555 46019551180412189058173333)
              ·
                refine ⟨2157166461581821362101875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 46019551180412189058173333 2157166461581821362101875)
                ·
                  refine ⟨3235749692372732043152813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2157166461581821362101875 3235749692372732043152813)
                  ·
                    refine ⟨1213406134639774516182305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3235749692372732043152813 1213406134639774516182305)
                    ·
                      rfl

theorem cell22_3544650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 6, 1, 3].length) (baseStart_3544650 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3544650 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3544650 prefixEnd_3544650 := by exact prefixLift 3544650
  have htrace : WordTrace (prefixWord ++ tailWord_3544650) baseStart_3544650 baseEnd_3544650 := by
    simpa [prefixWord, tailWord_3544650, baseEnd_3544650] using wordTrace_append hprefix tailTrace_3544650
  have hstable : (prefixWord ++ tailWord_3544650).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3544650).length < 2 ^ (prefixWord ++ tailWord_3544650).sum := by decide
  have hdescent : baseEnd_3544650 < baseStart_3544650 := by decide
  rcases family_descends (prefixWord ++ tailWord_3544650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3544669 : List Nat := [1, 4, 4, 2, 2, 1, 2, 6]
def baseStart_3544669 : Nat := 118140960795 + 3544669 * 2 ^ 59
def prefixEnd_3544669 : Nat := 4983230072969 + 3 ^ 40 * 3544669 * 2
def baseEnd_3544669 : Nat := 134823626525340533328583

theorem tailTrace_3544669 : CollatzResearch.WordTrace tailWord_3544669 prefixEnd_3544669 134823626525340533328583 := by
  unfold tailWord_3544669
  simp only [CollatzResearch.WordTrace]
  refine ⟨129284699595277069113445061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86189799730184712742296707 129284699595277069113445061)
  ·
    refine ⟨24240881174114450458770949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 129284699595277069113445061 24240881174114450458770949)
    ·
      refine ⟨4545165220146459461019553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24240881174114450458770949 4545165220146459461019553)
      ·
        refine ⟨3408873915109844595764665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4545165220146459461019553 3408873915109844595764665)
        ·
          refine ⟨2556655436332383446823499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3408873915109844595764665 2556655436332383446823499)
          ·
            refine ⟨3834983154498575170235249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2556655436332383446823499 3834983154498575170235249)
            ·
              refine ⟨2876237365873931377676437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3834983154498575170235249 2876237365873931377676437)
              ·
                refine ⟨134823626525340533328583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2876237365873931377676437 134823626525340533328583)
                ·
                  rfl

theorem cell22_3544669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 2, 1, 2, 6].length) (baseStart_3544669 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3544669 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3544669 prefixEnd_3544669 := by exact prefixLift 3544669
  have htrace : WordTrace (prefixWord ++ tailWord_3544669) baseStart_3544669 baseEnd_3544669 := by
    simpa [prefixWord, tailWord_3544669, baseEnd_3544669] using wordTrace_append hprefix tailTrace_3544669
  have hstable : (prefixWord ++ tailWord_3544669).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3544669).length < 2 ^ (prefixWord ++ tailWord_3544669).sum := by decide
  have hdescent : baseEnd_3544669 < baseStart_3544669 := by decide
  rcases family_descends (prefixWord ++ tailWord_3544669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3544721 : List Nat := [1, 2, 2, 1, 1, 1, 1, 6, 1, 6]
def baseStart_3544721 : Nat := 118140960795 + 3544721 * 2 ^ 59
def prefixEnd_3544721 : Nat := 4983230072969 + 3 ^ 40 * 3544721 * 2
def baseEnd_3544721 : Nat := 1213430439390753997657087

theorem tailTrace_3544721 : CollatzResearch.WordTrace tailWord_3544721 prefixEnd_3544721 1213430439390753997657087 := by
  unfold tailWord_3544721
  simp only [CollatzResearch.WordTrace]
  refine ⟨129286596191088681994338017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86191064127392454662892011 129286596191088681994338017)
  ·
    refine ⟨96964947143316511495753513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129286596191088681994338017 96964947143316511495753513)
    ·
      refine ⟨72723710357487383621815135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96964947143316511495753513 72723710357487383621815135)
      ·
        refine ⟨109085565536231075432722703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72723710357487383621815135 109085565536231075432722703)
        ·
          refine ⟨163628348304346613149084055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109085565536231075432722703 163628348304346613149084055)
          ·
            refine ⟨245442522456519919723626083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163628348304346613149084055 245442522456519919723626083)
            ·
              refine ⟨368163783684779879585439125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 245442522456519919723626083 368163783684779879585439125)
              ·
                refine ⟨17257677360224056855567459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 368163783684779879585439125 17257677360224056855567459)
                ·
                  refine ⟨25886516040336085283351189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17257677360224056855567459 25886516040336085283351189)
                  ·
                    refine ⟨1213430439390753997657087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25886516040336085283351189 1213430439390753997657087)
                    ·
                      rfl

theorem cell22_3544721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 6].length) (baseStart_3544721 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3544721 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3544721 prefixEnd_3544721 := by exact prefixLift 3544721
  have htrace : WordTrace (prefixWord ++ tailWord_3544721) baseStart_3544721 baseEnd_3544721 := by
    simpa [prefixWord, tailWord_3544721, baseEnd_3544721] using wordTrace_append hprefix tailTrace_3544721
  have hstable : (prefixWord ++ tailWord_3544721).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3544721).length < 2 ^ (prefixWord ++ tailWord_3544721).sum := by decide
  have hdescent : baseEnd_3544721 < baseStart_3544721 := by decide
  rcases family_descends (prefixWord ++ tailWord_3544721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3544774 : List Nat := [6, 1, 2, 1, 1, 2, 2, 1, 1, 5]
def baseStart_3544774 : Nat := 118140960795 + 3544774 * 2 ^ 59
def prefixEnd_3544774 : Nat := 4983230072969 + 3 ^ 40 * 3544774 * 2
def baseEnd_3544774 : Nat := 1213448582373879526081925

theorem tailTrace_3544774 : CollatzResearch.WordTrace tailWord_3544774 prefixEnd_3544774 1213448582373879526081925 := by
  unfold tailWord_3544774
  simp only [CollatzResearch.WordTrace]
  refine ⟨4040266539371771001438043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 86192352839931114697344917 4040266539371771001438043)
  ·
    refine ⟨6060399809057656502157065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4040266539371771001438043 6060399809057656502157065)
    ·
      refine ⟨4545299856793242376617799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6060399809057656502157065 4545299856793242376617799)
      ·
        refine ⟨6817949785189863564926699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4545299856793242376617799 6817949785189863564926699)
        ·
          refine ⟨10226924677784795347390049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6817949785189863564926699 10226924677784795347390049)
          ·
            refine ⟨7670193508338596510542537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10226924677784795347390049 7670193508338596510542537)
            ·
              refine ⟨5752645131253947382906903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7670193508338596510542537 5752645131253947382906903)
              ·
                refine ⟨8628967696880921074360355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5752645131253947382906903 8628967696880921074360355)
                ·
                  refine ⟨12943451545321381611540533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8628967696880921074360355 12943451545321381611540533)
                  ·
                    refine ⟨1213448582373879526081925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12943451545321381611540533 1213448582373879526081925)
                    ·
                      rfl

theorem cell22_3544774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 2, 1, 1, 5].length) (baseStart_3544774 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3544774 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3544774 prefixEnd_3544774 := by exact prefixLift 3544774
  have htrace : WordTrace (prefixWord ++ tailWord_3544774) baseStart_3544774 baseEnd_3544774 := by
    simpa [prefixWord, tailWord_3544774, baseEnd_3544774] using wordTrace_append hprefix tailTrace_3544774
  have hstable : (prefixWord ++ tailWord_3544774).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3544774).length < 2 ^ (prefixWord ++ tailWord_3544774).sum := by decide
  have hdescent : baseEnd_3544774 < baseStart_3544774 := by decide
  rcases family_descends (prefixWord ++ tailWord_3544774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3544785 : List Nat := [1, 2, 2, 1, 2, 5, 1, 2, 3, 3]
def baseStart_3544785 : Nat := 118140960795 + 3544785 * 2 ^ 59
def prefixEnd_3544785 : Nat := 4983230072969 + 3 ^ 40 * 3544785 * 2
def baseEnd_3544785 : Nat := 1213452347898679164056891

theorem tailTrace_3544785 : CollatzResearch.WordTrace tailWord_3544785 prefixEnd_3544785 1213452347898679164056891 := by
  unfold tailWord_3544785
  simp only [CollatzResearch.WordTrace]
  refine ⟨129288930462856820924667809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86192620308571213949778539 129288930462856820924667809)
  ·
    refine ⟨96966697847142615693500857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129288930462856820924667809 96966697847142615693500857)
    ·
      refine ⟨72725023385356961770125643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96966697847142615693500857 72725023385356961770125643)
      ·
        refine ⟨109087535078035442655188465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72725023385356961770125643 109087535078035442655188465)
        ·
          refine ⟨81815651308526581991391349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109087535078035442655188465 81815651308526581991391349)
          ·
            refine ⟨7670217310174367061692939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 81815651308526581991391349 7670217310174367061692939)
            ·
              refine ⟨11505325965261550592539409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7670217310174367061692939 11505325965261550592539409)
              ·
                refine ⟨8628994473946162944404557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11505325965261550592539409 8628994473946162944404557)
                ·
                  refine ⟨3235872927729811104151709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8628994473946162944404557 3235872927729811104151709)
                  ·
                    refine ⟨1213452347898679164056891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3235872927729811104151709 1213452347898679164056891)
                    ·
                      rfl

theorem cell22_3544785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 1, 2, 3, 3].length) (baseStart_3544785 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3544785 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3544785 prefixEnd_3544785 := by exact prefixLift 3544785
  have htrace : WordTrace (prefixWord ++ tailWord_3544785) baseStart_3544785 baseEnd_3544785 := by
    simpa [prefixWord, tailWord_3544785, baseEnd_3544785] using wordTrace_append hprefix tailTrace_3544785
  have hstable : (prefixWord ++ tailWord_3544785).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3544785).length < 2 ^ (prefixWord ++ tailWord_3544785).sum := by decide
  have hdescent : baseEnd_3544785 < baseStart_3544785 := by decide
  rcases family_descends (prefixWord ++ tailWord_3544785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3544843 : List Nat := [1, 1, 1, 1, 5, 1, 4, 2, 6]
def baseStart_3544843 : Nat := 118140960795 + 3544843 * 2 ^ 59
def prefixEnd_3544843 : Nat := 4983230072969 + 3 ^ 40 * 3544843 * 2
def baseEnd_3544843 : Nat := 404490734161328782035571

theorem tailTrace_3544843 : CollatzResearch.WordTrace tailWord_3544843 prefixEnd_3544843 404490734161328782035571 := by
  unfold tailWord_3544843
  simp only [CollatzResearch.WordTrace]
  refine ⟨129291045896646696830279183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86194030597764464553519455 129291045896646696830279183)
  ·
    refine ⟨193936568844970045245418775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129291045896646696830279183 193936568844970045245418775)
    ·
      refine ⟨290904853267455067868128163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193936568844970045245418775 290904853267455067868128163)
      ·
        refine ⟨436357279901182601802192245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 290904853267455067868128163 436357279901182601802192245)
        ·
          refine ⟨40908494990735868918955523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 436357279901182601802192245 40908494990735868918955523)
          ·
            refine ⟨61362742486103803378433285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40908494990735868918955523 61362742486103803378433285)
            ·
              refine ⟨11505514216144463133456241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 61362742486103803378433285 11505514216144463133456241)
              ·
                refine ⟨8629135662108347350092181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11505514216144463133456241 8629135662108347350092181)
                ·
                  refine ⟨404490734161328782035571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8629135662108347350092181 404490734161328782035571)
                  ·
                    rfl

theorem cell22_3544843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 4, 2, 6].length) (baseStart_3544843 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3544843 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3544843 prefixEnd_3544843 := by exact prefixLift 3544843
  have htrace : WordTrace (prefixWord ++ tailWord_3544843) baseStart_3544843 baseEnd_3544843 := by
    simpa [prefixWord, tailWord_3544843, baseEnd_3544843] using wordTrace_append hprefix tailTrace_3544843
  have hstable : (prefixWord ++ tailWord_3544843).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3544843).length < 2 ^ (prefixWord ++ tailWord_3544843).sum := by decide
  have hdescent : baseEnd_3544843 < baseStart_3544843 := by decide
  rcases family_descends (prefixWord ++ tailWord_3544843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3544888 : List Nat := [2, 1, 2, 1, 3, 3, 1, 9]
def baseStart_3544888 : Nat := 118140960795 + 3544888 * 2 ^ 59
def prefixEnd_3544888 : Nat := 4983230072969 + 3 ^ 40 * 3544888 * 2
def baseEnd_3544888 : Nat := 134831956322624580970175

theorem tailTrace_3544888 : CollatzResearch.WordTrace tailWord_3544888 prefixEnd_3544888 134831956322624580970175 := by
  unfold tailWord_3544888
  simp only [CollatzResearch.WordTrace]
  refine ⟨64646343590741834757833659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86195124787655779677111545 64646343590741834757833659)
  ·
    refine ⟨96969515386112752136750489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64646343590741834757833659 96969515386112752136750489)
    ·
      refine ⟨72727136539584564102562867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96969515386112752136750489 72727136539584564102562867)
      ·
        refine ⟨109090704809376846153844301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72727136539584564102562867 109090704809376846153844301)
        ·
          refine ⟨40909014303516317307691613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 109090704809376846153844301 40909014303516317307691613)
          ·
            refine ⟨15340880363818618990384355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40909014303516317307691613 15340880363818618990384355)
            ·
              refine ⟨23011320545727928485576533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15340880363818618990384355 23011320545727928485576533)
              ·
                refine ⟨134831956322624580970175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 23011320545727928485576533 134831956322624580970175)
                ·
                  rfl

theorem cell22_3544888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 9].length) (baseStart_3544888 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3544888 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3544888 prefixEnd_3544888 := by exact prefixLift 3544888
  have htrace : WordTrace (prefixWord ++ tailWord_3544888) baseStart_3544888 baseEnd_3544888 := by
    simpa [prefixWord, tailWord_3544888, baseEnd_3544888] using wordTrace_append hprefix tailTrace_3544888
  have hstable : (prefixWord ++ tailWord_3544888).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3544888).length < 2 ^ (prefixWord ++ tailWord_3544888).sum := by decide
  have hdescent : baseEnd_3544888 < baseStart_3544888 := by decide
  rcases family_descends (prefixWord ++ tailWord_3544888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3544903 : List Nat := [1, 1, 4, 1, 2, 1, 2, 1, 2, 7]
def baseStart_3544903 : Nat := 118140960795 + 3544903 * 2 ^ 59
def prefixEnd_3544903 : Nat := 4983230072969 + 3 ^ 40 * 3544903 * 2
def baseEnd_3544903 : Nat := 1213492741710166189606529

theorem tailTrace_3544903 : CollatzResearch.WordTrace tailWord_3544903 prefixEnd_3544903 1213492741710166189606529 := by
  unfold tailWord_3544903
  simp only [CollatzResearch.WordTrace]
  refine ⟨129293234276429327077463363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86195489517619551384975575 129293234276429327077463363)
  ·
    refine ⟨193939851414643990616195045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129293234276429327077463363 193939851414643990616195045)
    ·
      refine ⟨36363722140245748240536571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 193939851414643990616195045 36363722140245748240536571)
      ·
        refine ⟨54545583210368622360804857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36363722140245748240536571 54545583210368622360804857)
        ·
          refine ⟨40909187407776466770603643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54545583210368622360804857 40909187407776466770603643)
          ·
            refine ⟨61363781111664700155905465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40909187407776466770603643 61363781111664700155905465)
            ·
              refine ⟨46022835833748525116929099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61363781111664700155905465 46022835833748525116929099)
              ·
                refine ⟨69034253750622787675393649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46022835833748525116929099 69034253750622787675393649)
                ·
                  refine ⟨51775690312967090756545237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69034253750622787675393649 51775690312967090756545237)
                  ·
                    refine ⟨1213492741710166189606529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 51775690312967090756545237 1213492741710166189606529)
                    ·
                      rfl

theorem cell22_3544903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 1, 2, 7].length) (baseStart_3544903 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3544903 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3544903 prefixEnd_3544903 := by exact prefixLift 3544903
  have htrace : WordTrace (prefixWord ++ tailWord_3544903) baseStart_3544903 baseEnd_3544903 := by
    simpa [prefixWord, tailWord_3544903, baseEnd_3544903] using wordTrace_append hprefix tailTrace_3544903
  have hstable : (prefixWord ++ tailWord_3544903).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3544903).length < 2 ^ (prefixWord ++ tailWord_3544903).sum := by decide
  have hdescent : baseEnd_3544903 < baseStart_3544903 := by decide
  rcases family_descends (prefixWord ++ tailWord_3544903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3545044 : List Nat := [2, 4, 1, 2, 1, 1, 2, 4, 2, 3]
def baseStart_3545044 : Nat := 118140960795 + 3545044 * 2 ^ 59
def prefixEnd_3545044 : Nat := 4983230072969 + 3 ^ 40 * 3545044 * 2
def baseEnd_3545044 : Nat := 1213541008891688821831097

theorem tailTrace_3545044 : CollatzResearch.WordTrace tailWord_3545044 prefixEnd_3545044 1213541008891688821831097 := by
  unfold tailWord_3545044
  simp only [CollatzResearch.WordTrace]
  refine ⟨64649188484459254079173093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86198917979279005438897457 64649188484459254079173093)
  ·
    refine ⟨12121722840836110139844955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 64649188484459254079173093 12121722840836110139844955)
    ·
      refine ⟨18182584261254165209767433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12121722840836110139844955 18182584261254165209767433)
      ·
        refine ⟨13636938195940623907325575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18182584261254165209767433 13636938195940623907325575)
        ·
          refine ⟨20455407293910935860988363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13636938195940623907325575 20455407293910935860988363)
          ·
            refine ⟨30683110940866403791482545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20455407293910935860988363 30683110940866403791482545)
            ·
              refine ⟨23012333205649802843611909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30683110940866403791482545 23012333205649802843611909)
              ·
                refine ⟨4314812476059338033177233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23012333205649802843611909 4314812476059338033177233)
                ·
                  refine ⟨3236109357044503524882925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4314812476059338033177233 3236109357044503524882925)
                  ·
                    refine ⟨1213541008891688821831097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3236109357044503524882925 1213541008891688821831097)
                    ·
                      rfl

theorem cell22_3545044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 4, 2, 3].length) (baseStart_3545044 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3545044 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3545044 prefixEnd_3545044 := by exact prefixLift 3545044
  have htrace : WordTrace (prefixWord ++ tailWord_3545044) baseStart_3545044 baseEnd_3545044 := by
    simpa [prefixWord, tailWord_3545044, baseEnd_3545044] using wordTrace_append hprefix tailTrace_3545044
  have hstable : (prefixWord ++ tailWord_3545044).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3545044).length < 2 ^ (prefixWord ++ tailWord_3545044).sum := by decide
  have hdescent : baseEnd_3545044 < baseStart_3545044 := by decide
  rcases family_descends (prefixWord ++ tailWord_3545044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3545046 : List Nat := [5, 2, 1, 1, 3, 2, 1, 1, 6]
def baseStart_3545046 : Nat := 118140960795 + 3545046 * 2 ^ 59
def prefixEnd_3545046 : Nat := 4983230072969 + 3 ^ 40 * 3545046 * 2
def baseEnd_3545046 : Nat := 404513897844187161093697

theorem tailTrace_3545046 : CollatzResearch.WordTrace tailWord_3545046 prefixEnd_3545046 404513897844187161093697 := by
  unfold tailWord_3545046
  simp only [CollatzResearch.WordTrace]
  refine ⟨8081153119681953906244937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 86198966609940841666612661 8081153119681953906244937)
  ·
    refine ⟨6060864839761465429683703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8081153119681953906244937 6060864839761465429683703)
    ·
      refine ⟨9091297259642198144525555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6060864839761465429683703 9091297259642198144525555)
      ·
        refine ⟨13636945889463297216788333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9091297259642198144525555 13636945889463297216788333)
        ·
          refine ⟨5113854708548736456295625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13636945889463297216788333 5113854708548736456295625)
          ·
            refine ⟨3835391031411552342221719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5113854708548736456295625 3835391031411552342221719)
            ·
              refine ⟨5753086547117328513332579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3835391031411552342221719 5753086547117328513332579)
              ·
                refine ⟨8629629820675992769998869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5753086547117328513332579 8629629820675992769998869)
                ·
                  refine ⟨404513897844187161093697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8629629820675992769998869 404513897844187161093697)
                  ·
                    rfl

theorem cell22_3545046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 2, 1, 1, 6].length) (baseStart_3545046 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3545046 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3545046 prefixEnd_3545046 := by exact prefixLift 3545046
  have htrace : WordTrace (prefixWord ++ tailWord_3545046) baseStart_3545046 baseEnd_3545046 := by
    simpa [prefixWord, tailWord_3545046, baseEnd_3545046] using wordTrace_append hprefix tailTrace_3545046
  have hstable : (prefixWord ++ tailWord_3545046).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3545046).length < 2 ^ (prefixWord ++ tailWord_3545046).sum := by decide
  have hdescent : baseEnd_3545046 < baseStart_3545046 := by decide
  rcases family_descends (prefixWord ++ tailWord_3545046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3545072 : List Nat := [2, 1, 1, 1, 3, 2, 2, 4, 3, 3]
def baseStart_3545072 : Nat := 118140960795 + 3545072 * 2 ^ 59
def prefixEnd_3545072 : Nat := 4983230072969 + 3 ^ 40 * 3545072 * 2
def baseEnd_3545072 : Nat := 1213550593863906082131011

theorem tailTrace_3545072 : CollatzResearch.WordTrace tailWord_3545072 prefixEnd_3545072 1213550593863906082131011 := by
  unfold tailWord_3545072
  simp only [CollatzResearch.WordTrace]
  refine ⟨64649699106408534470182735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86199598808544712626910313 64649699106408534470182735)
  ·
    refine ⟨96974548659612801705274103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64649699106408534470182735 96974548659612801705274103)
    ·
      refine ⟨145461822989419202557911155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96974548659612801705274103 145461822989419202557911155)
      ·
        refine ⟨218192734484128803836866733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145461822989419202557911155 218192734484128803836866733)
        ·
          refine ⟨81822275431548301438825025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 218192734484128803836866733 81822275431548301438825025)
          ·
            refine ⟨61366706573661226079118769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81822275431548301438825025 61366706573661226079118769)
            ·
              refine ⟨46025029930245919559339077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61366706573661226079118769 46025029930245919559339077)
              ·
                refine ⟨8629693111921109917376077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46025029930245919559339077 8629693111921109917376077)
                ·
                  refine ⟨3236134916970416219016029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8629693111921109917376077 3236134916970416219016029)
                  ·
                    refine ⟨1213550593863906082131011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3236134916970416219016029 1213550593863906082131011)
                    ·
                      rfl

theorem cell22_3545072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 4, 3, 3].length) (baseStart_3545072 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3545072 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3545072 prefixEnd_3545072 := by exact prefixLift 3545072
  have htrace : WordTrace (prefixWord ++ tailWord_3545072) baseStart_3545072 baseEnd_3545072 := by
    simpa [prefixWord, tailWord_3545072, baseEnd_3545072] using wordTrace_append hprefix tailTrace_3545072
  have hstable : (prefixWord ++ tailWord_3545072).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3545072).length < 2 ^ (prefixWord ++ tailWord_3545072).sum := by decide
  have hdescent : baseEnd_3545072 < baseStart_3545072 := by decide
  rcases family_descends (prefixWord ++ tailWord_3545072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3545085 : List Nat := [1, 4, 1, 1, 1, 2, 2, 1, 9]
def baseStart_3545085 : Nat := 118140960795 + 3545085 * 2 ^ 59
def prefixEnd_3545085 : Nat := 4983230072969 + 3 ^ 40 * 3545085 * 2
def baseEnd_3545085 : Nat := 404518348009859460518657

theorem tailTrace_3545085 : CollatzResearch.WordTrace tailWord_3545085 prefixEnd_3545085 404518348009859460518657 := by
  unfold tailWord_3545085
  simp only [CollatzResearch.WordTrace]
  refine ⟨129299872361769972160588709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86199914907846648107059139 129299872361769972160588709)
  ·
    refine ⟨24243726067831869780110383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 129299872361769972160588709 24243726067831869780110383)
    ·
      refine ⟨36365589101747804670165575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24243726067831869780110383 36365589101747804670165575)
      ·
        refine ⟨54548383652621707005248363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36365589101747804670165575 54548383652621707005248363)
        ·
          refine ⟨81822575478932560507872545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54548383652621707005248363 81822575478932560507872545)
          ·
            refine ⟨61366931609199420380904409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81822575478932560507872545 61366931609199420380904409)
            ·
              refine ⟨46025198706899565285678307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61366931609199420380904409 46025198706899565285678307)
              ·
                refine ⟨69037798060349347928517461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46025198706899565285678307 69037798060349347928517461)
                ·
                  refine ⟨404518348009859460518657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 69037798060349347928517461 404518348009859460518657)
                  ·
                    rfl

theorem cell22_3545085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 1, 9].length) (baseStart_3545085 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3545085 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3545085 prefixEnd_3545085 := by exact prefixLift 3545085
  have htrace : WordTrace (prefixWord ++ tailWord_3545085) baseStart_3545085 baseEnd_3545085 := by
    simpa [prefixWord, tailWord_3545085, baseEnd_3545085] using wordTrace_append hprefix tailTrace_3545085
  have hstable : (prefixWord ++ tailWord_3545085).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3545085).length < 2 ^ (prefixWord ++ tailWord_3545085).sum := by decide
  have hdescent : baseEnd_3545085 < baseStart_3545085 := by decide
  rcases family_descends (prefixWord ++ tailWord_3545085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3545108 : List Nat := [2, 4, 3, 2, 2, 1, 1, 7]
def baseStart_3545108 : Nat := 118140960795 + 3545108 * 2 ^ 59
def prefixEnd_3545108 : Nat := 4983230072969 + 3 ^ 40 * 3545108 * 2
def baseEnd_3545108 : Nat := 134840324155512665358989

theorem tailTrace_3545108 : CollatzResearch.WordTrace tailWord_3545108 prefixEnd_3545108 134840324155512665358989 := by
  unfold tailWord_3545108
  simp only [CollatzResearch.WordTrace]
  refine ⟨64650355620343323544337989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86200474160457764725783985 64650355620343323544337989)
  ·
    refine ⟨12121941678814373164563373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 64650355620343323544337989 12121941678814373164563373)
    ·
      refine ⟨4545728129555389936711265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12121941678814373164563373 4545728129555389936711265)
      ·
        refine ⟨3409296097166542452533449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4545728129555389936711265 3409296097166542452533449)
        ·
          refine ⟨2556972072874906839400087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3409296097166542452533449 2556972072874906839400087)
          ·
            refine ⟨3835458109312360259100131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2556972072874906839400087 3835458109312360259100131)
            ·
              refine ⟨5753187163968540388650197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3835458109312360259100131 5753187163968540388650197)
              ·
                refine ⟨134840324155512665358989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5753187163968540388650197 134840324155512665358989)
                ·
                  rfl

theorem cell22_3545108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 2, 1, 1, 7].length) (baseStart_3545108 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3545108 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3545108 prefixEnd_3545108 := by exact prefixLift 3545108
  have htrace : WordTrace (prefixWord ++ tailWord_3545108) baseStart_3545108 baseEnd_3545108 := by
    simpa [prefixWord, tailWord_3545108, baseEnd_3545108] using wordTrace_append hprefix tailTrace_3545108
  have hstable : (prefixWord ++ tailWord_3545108).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3545108).length < 2 ^ (prefixWord ++ tailWord_3545108).sum := by decide
  have hdescent : baseEnd_3545108 < baseStart_3545108 := by decide
  rcases family_descends (prefixWord ++ tailWord_3545108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3545117 : List Nat := [1, 4, 2, 2, 2, 1, 1, 1, 1, 7]
def baseStart_3545117 : Nat := 118140960795 + 3545117 * 2 ^ 59
def prefixEnd_3545117 : Nat := 4983230072969 + 3 ^ 40 * 3545117 * 2
def baseEnd_3545117 : Nat := 1213565998283540964755873

theorem tailTrace_3545117 : CollatzResearch.WordTrace tailWord_3545117 prefixEnd_3545117 1213565998283540964755873 := by
  unfold tailWord_3545117
  simp only [CollatzResearch.WordTrace]
  refine ⟨129301039497654041625753605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86200692998436027750502403 129301039497654041625753605)
  ·
    refine ⟨24243944905810132804828801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 129301039497654041625753605 24243944905810132804828801)
    ·
      refine ⟨18182958679357599603621601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24243944905810132804828801 18182958679357599603621601)
      ·
        refine ⟨13637219009518199702716201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18182958679357599603621601 13637219009518199702716201)
        ·
          refine ⟨10227914257138649777037151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13637219009518199702716201 10227914257138649777037151)
          ·
            refine ⟨15341871385707974665555727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10227914257138649777037151 15341871385707974665555727)
            ·
              refine ⟨23012807078561961998333591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15341871385707974665555727 23012807078561961998333591)
              ·
                refine ⟨34519210617842942997500387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23012807078561961998333591 34519210617842942997500387)
                ·
                  refine ⟨51778815926764414496250581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34519210617842942997500387 51778815926764414496250581)
                  ·
                    refine ⟨1213565998283540964755873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 51778815926764414496250581 1213565998283540964755873)
                    ·
                      rfl

theorem cell22_3545117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 1, 1, 7].length) (baseStart_3545117 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3545117 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3545117 prefixEnd_3545117 := by exact prefixLift 3545117
  have htrace : WordTrace (prefixWord ++ tailWord_3545117) baseStart_3545117 baseEnd_3545117 := by
    simpa [prefixWord, tailWord_3545117, baseEnd_3545117] using wordTrace_append hprefix tailTrace_3545117
  have hstable : (prefixWord ++ tailWord_3545117).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3545117).length < 2 ^ (prefixWord ++ tailWord_3545117).sum := by decide
  have hdescent : baseEnd_3545117 < baseStart_3545117 := by decide
  rcases family_descends (prefixWord ++ tailWord_3545117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3545140 : List Nat := [2, 5, 1, 2, 2, 1, 2, 3, 1, 3]
def baseStart_3545140 : Nat := 118140960795 + 3545140 * 2 ^ 59
def prefixEnd_3545140 : Nat := 4983230072969 + 3 ^ 40 * 3545140 * 2
def baseEnd_3545140 : Nat := 1213573871653576571430803

theorem tailTrace_3545140 : CollatzResearch.WordTrace tailWord_3545140 prefixEnd_3545140 1213573871653576571430803 := by
  unfold tailWord_3545140
  simp only [CollatzResearch.WordTrace]
  refine ⟨64650939188285358276920437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86201252251047144369227249 64650939188285358276920437)
  ·
    refine ⟨6061025548901752338461291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 64650939188285358276920437 6061025548901752338461291)
    ·
      refine ⟨9091538323352628507691937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6061025548901752338461291 9091538323352628507691937)
      ·
        refine ⟨6818653742514471380768953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9091538323352628507691937 6818653742514471380768953)
        ·
          refine ⟨5113990306885853535576715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6818653742514471380768953 5113990306885853535576715)
          ·
            refine ⟨7670985460328780303365073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5113990306885853535576715 7670985460328780303365073)
            ·
              refine ⟨5753239095246585227523805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7670985460328780303365073 5753239095246585227523805)
              ·
                refine ⟨2157464660717469460321427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5753239095246585227523805 2157464660717469460321427)
                ·
                  refine ⟨3236196991076204190482141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2157464660717469460321427 3236196991076204190482141)
                  ·
                    refine ⟨1213573871653576571430803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3236196991076204190482141 1213573871653576571430803)
                    ·
                      rfl

theorem cell22_3545140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 2, 3, 1, 3].length) (baseStart_3545140 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3545140 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3545140 prefixEnd_3545140 := by exact prefixLift 3545140
  have htrace : WordTrace (prefixWord ++ tailWord_3545140) baseStart_3545140 baseEnd_3545140 := by
    simpa [prefixWord, tailWord_3545140, baseEnd_3545140] using wordTrace_append hprefix tailTrace_3545140
  have hstable : (prefixWord ++ tailWord_3545140).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3545140).length < 2 ^ (prefixWord ++ tailWord_3545140).sum := by decide
  have hdescent : baseEnd_3545140 < baseStart_3545140 := by decide
  rcases family_descends (prefixWord ++ tailWord_3545140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3545149 : List Nat := [1, 4, 1, 3, 1, 1, 3, 3, 1, 4]
def baseStart_3545149 : Nat := 118140960795 + 3545149 * 2 ^ 59
def prefixEnd_3545149 : Nat := 4983230072969 + 3 ^ 40 * 3545149 * 2
def baseEnd_3545149 : Nat := 1213576952537503547955775

theorem tailTrace_3545149 : CollatzResearch.WordTrace tailWord_3545149 prefixEnd_3545149 1213576952537503547955775 := by
  unfold tailWord_3545149
  simp only [CollatzResearch.WordTrace]
  refine ⟨129302206633538111090918501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86201471089025407393945667 129302206633538111090918501)
  ·
    refine ⟨24244163743788395829547219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 129302206633538111090918501 24244163743788395829547219)
    ·
      refine ⟨36366245615682593744320829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24244163743788395829547219 36366245615682593744320829)
      ·
        refine ⟨13637342105880972654120311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36366245615682593744320829 13637342105880972654120311)
        ·
          refine ⟨20456013158821458981180467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13637342105880972654120311 20456013158821458981180467)
          ·
            refine ⟨30684019738232188471770701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20456013158821458981180467 30684019738232188471770701)
            ·
              refine ⟨11506507401837070676914013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30684019738232188471770701 11506507401837070676914013)
              ·
                refine ⟨4314940275688901503842755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11506507401837070676914013 4314940275688901503842755)
                ·
                  refine ⟨6472410413533352255764133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4314940275688901503842755 6472410413533352255764133)
                  ·
                    refine ⟨1213576952537503547955775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6472410413533352255764133 1213576952537503547955775)
                    ·
                      rfl

theorem cell22_3545149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 3, 3, 1, 4].length) (baseStart_3545149 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3545149 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3545149 prefixEnd_3545149 := by exact prefixLift 3545149
  have htrace : WordTrace (prefixWord ++ tailWord_3545149) baseStart_3545149 baseEnd_3545149 := by
    simpa [prefixWord, tailWord_3545149, baseEnd_3545149] using wordTrace_append hprefix tailTrace_3545149
  have hstable : (prefixWord ++ tailWord_3545149).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3545149).length < 2 ^ (prefixWord ++ tailWord_3545149).sum := by decide
  have hdescent : baseEnd_3545149 < baseStart_3545149 := by decide
  rcases family_descends (prefixWord ++ tailWord_3545149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3545164 : List Nat := [2, 2, 1, 3, 1, 1, 4, 4, 4]
def baseStart_3545164 : Nat := 118140960795 + 3545164 * 2 ^ 59
def prefixEnd_3545164 : Nat := 4983230072969 + 3 ^ 40 * 3545164 * 2
def baseEnd_3545164 : Nat := 404527362448016169610243

theorem tailTrace_3545164 : CollatzResearch.WordTrace tailWord_3545164 prefixEnd_3545164 404527362448016169610243 := by
  unfold tailWord_3545164
  simp only [CollatzResearch.WordTrace]
  refine ⟨64651376864241884326357273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86201835818989179101809697 64651376864241884326357273)
  ·
    refine ⟨48488532648181413244767955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64651376864241884326357273 48488532648181413244767955)
    ·
      refine ⟨72732798972272119867151933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48488532648181413244767955 72732798972272119867151933)
      ·
        refine ⟨27274799614602044950181975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72732798972272119867151933 27274799614602044950181975)
        ·
          refine ⟨40912199421903067425272963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27274799614602044950181975 40912199421903067425272963)
          ·
            refine ⟨61368299132854601137909445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40912199421903067425272963 61368299132854601137909445)
            ·
              refine ⟨11506556087410237713358021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 61368299132854601137909445 11506556087410237713358021)
              ·
                refine ⟨2157479266389419571254629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11506556087410237713358021 2157479266389419571254629)
                ·
                  refine ⟨404527362448016169610243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2157479266389419571254629 404527362448016169610243)
                  ·
                    rfl

theorem cell22_3545164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 4, 4, 4].length) (baseStart_3545164 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3545164 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3545164 prefixEnd_3545164 := by exact prefixLift 3545164
  have htrace : WordTrace (prefixWord ++ tailWord_3545164) baseStart_3545164 baseEnd_3545164 := by
    simpa [prefixWord, tailWord_3545164, baseEnd_3545164] using wordTrace_append hprefix tailTrace_3545164
  have hstable : (prefixWord ++ tailWord_3545164).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3545164).length < 2 ^ (prefixWord ++ tailWord_3545164).sum := by decide
  have hdescent : baseEnd_3545164 < baseStart_3545164 := by decide
  rcases family_descends (prefixWord ++ tailWord_3545164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3545230 : List Nat := [4, 1, 1, 3, 3, 2, 2, 1, 2, 3]
def baseStart_3545230 : Nat := 118140960795 + 3545230 * 2 ^ 59
def prefixEnd_3545230 : Nat := 4983230072969 + 3 ^ 40 * 3545230 * 2
def baseEnd_3545230 : Nat := 1213604680492846336680527

theorem tailTrace_3545230 : CollatzResearch.WordTrace tailWord_3545230 prefixEnd_3545230 1213604680492846336680527 := by
  unfold tailWord_3545230
  simp only [CollatzResearch.WordTrace]
  refine ⟨16163145118280582740577143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 86203440630829774616411429 16163145118280582740577143)
  ·
    refine ⟨24244717677420874110865715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16163145118280582740577143 24244717677420874110865715)
    ·
      refine ⟨36367076516131311166298573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24244717677420874110865715 36367076516131311166298573)
      ·
        refine ⟨13637653693549241687361965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36367076516131311166298573 13637653693549241687361965)
        ·
          refine ⟨5114120135080965632760737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13637653693549241687361965 5114120135080965632760737)
          ·
            refine ⟨3835590101310724224570553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5114120135080965632760737 3835590101310724224570553)
            ·
              refine ⟨2876692575983043168427915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3835590101310724224570553 2876692575983043168427915)
              ·
                refine ⟨4315038863974564752641873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2876692575983043168427915 4315038863974564752641873)
                ·
                  refine ⟨3236279147980923564481405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4315038863974564752641873 3236279147980923564481405)
                  ·
                    refine ⟨1213604680492846336680527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3236279147980923564481405 1213604680492846336680527)
                    ·
                      rfl

theorem cell22_3545230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 2, 2, 1, 2, 3].length) (baseStart_3545230 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3545230 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3545230 prefixEnd_3545230 := by exact prefixLift 3545230
  have htrace : WordTrace (prefixWord ++ tailWord_3545230) baseStart_3545230 baseEnd_3545230 := by
    simpa [prefixWord, tailWord_3545230, baseEnd_3545230] using wordTrace_append hprefix tailTrace_3545230
  have hstable : (prefixWord ++ tailWord_3545230).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3545230).length < 2 ^ (prefixWord ++ tailWord_3545230).sum := by decide
  have hdescent : baseEnd_3545230 < baseStart_3545230 := by decide
  rcases family_descends (prefixWord ++ tailWord_3545230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3545329 : List Nat := [1, 2, 2, 2, 2, 1, 2, 4, 2, 4]
def baseStart_3545329 : Nat := 118140960795 + 3545329 * 2 ^ 59
def prefixEnd_3545329 : Nat := 4983230072969 + 3 ^ 40 * 3545329 * 2
def baseEnd_3545329 : Nat := 1213638570216043078455223

theorem tailTrace_3545329 : CollatzResearch.WordTrace tailWord_3545329 prefixEnd_3545329 1213638570216043078455223 := by
  unfold tailWord_3545329
  simp only [CollatzResearch.WordTrace]
  refine ⟨129308771772886001832471041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86205847848590667888314027 129308771772886001832471041)
  ·
    refine ⟨96981578829664501374353281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129308771772886001832471041 96981578829664501374353281)
    ·
      refine ⟨72736184122248376030764961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96981578829664501374353281 72736184122248376030764961)
      ·
        refine ⟨54552138091686282023073721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72736184122248376030764961 54552138091686282023073721)
        ·
          refine ⟨40914103568764711517305291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54552138091686282023073721 40914103568764711517305291)
          ·
            refine ⟨61371155353147067275957937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40914103568764711517305291 61371155353147067275957937)
            ·
              refine ⟨46028366514860300456968453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61371155353147067275957937 46028366514860300456968453)
              ·
                refine ⟨8630318721536306335681585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46028366514860300456968453 8630318721536306335681585)
                ·
                  refine ⟨6472739041152229751761189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8630318721536306335681585 6472739041152229751761189)
                  ·
                    refine ⟨1213638570216043078455223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6472739041152229751761189 1213638570216043078455223)
                    ·
                      rfl

theorem cell22_3545329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 4, 2, 4].length) (baseStart_3545329 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3545329 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3545329 prefixEnd_3545329 := by exact prefixLift 3545329
  have htrace : WordTrace (prefixWord ++ tailWord_3545329) baseStart_3545329 baseEnd_3545329 := by
    simpa [prefixWord, tailWord_3545329, baseEnd_3545329] using wordTrace_append hprefix tailTrace_3545329
  have hstable : (prefixWord ++ tailWord_3545329).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3545329).length < 2 ^ (prefixWord ++ tailWord_3545329).sum := by decide
  have hdescent : baseEnd_3545329 < baseStart_3545329 := by decide
  rcases family_descends (prefixWord ++ tailWord_3545329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3545346 : List Nat := [3, 4, 1, 1, 2, 1, 1, 2, 1, 6]
def baseStart_3545346 : Nat := 118140960795 + 3545346 * 2 ^ 59
def prefixEnd_3545346 : Nat := 4983230072969 + 3 ^ 40 * 3545346 * 2
def baseEnd_3545346 : Nat := 1213644389663460700780171

theorem tailTrace_3545346 : CollatzResearch.WordTrace tailWord_3545346 prefixEnd_3545346 1213644389663460700780171 := by
  unfold tailWord_3545346
  simp only [CollatzResearch.WordTrace]
  refine ⟨32327347953456103433959973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86206261209216275823893261 32327347953456103433959973)
  ·
    refine ⟨6061377741273019393867495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32327347953456103433959973 6061377741273019393867495)
    ·
      refine ⟨9092066611909529090801243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6061377741273019393867495 9092066611909529090801243)
      ·
        refine ⟨13638099917864293636201865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9092066611909529090801243 13638099917864293636201865)
        ·
          refine ⟨10228574938398220227151399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13638099917864293636201865 10228574938398220227151399)
          ·
            refine ⟨15342862407597330340727099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10228574938398220227151399 15342862407597330340727099)
            ·
              refine ⟨23014293611395995511090649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15342862407597330340727099 23014293611395995511090649)
              ·
                refine ⟨17260720208546996633317987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23014293611395995511090649 17260720208546996633317987)
                ·
                  refine ⟨25891080312820494949976981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17260720208546996633317987 25891080312820494949976981)
                  ·
                    refine ⟨1213644389663460700780171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25891080312820494949976981 1213644389663460700780171)
                    ·
                      rfl

theorem cell22_3545346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 2, 1, 6].length) (baseStart_3545346 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3545346 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3545346 prefixEnd_3545346 := by exact prefixLift 3545346
  have htrace : WordTrace (prefixWord ++ tailWord_3545346) baseStart_3545346 baseEnd_3545346 := by
    simpa [prefixWord, tailWord_3545346, baseEnd_3545346] using wordTrace_append hprefix tailTrace_3545346
  have hstable : (prefixWord ++ tailWord_3545346).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3545346).length < 2 ^ (prefixWord ++ tailWord_3545346).sum := by decide
  have hdescent : baseEnd_3545346 < baseStart_3545346 := by decide
  rcases family_descends (prefixWord ++ tailWord_3545346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3545348 : List Nat := [2, 3, 2, 2, 3, 2, 1, 1, 1, 5]
def baseStart_3545348 : Nat := 118140960795 + 3545348 * 2 ^ 59
def prefixEnd_3545348 : Nat := 4983230072969 + 3 ^ 40 * 3545348 * 2
def baseEnd_3545348 : Nat := 1213645074304333362230165

theorem tailTrace_3545348 : CollatzResearch.WordTrace tailWord_3545348 prefixEnd_3545348 1213645074304333362230165 := by
  unfold tailWord_3545348
  simp only [CollatzResearch.WordTrace]
  refine ⟨64654732379908584038706349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86206309839878112051608465 64654732379908584038706349)
  ·
    refine ⟨24245524642465719014514881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64654732379908584038706349 24245524642465719014514881)
    ·
      refine ⟨18184143481849289260886161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24245524642465719014514881 18184143481849289260886161)
      ·
        refine ⟨13638107611386966945664621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18184143481849289260886161 13638107611386966945664621)
        ·
          refine ⟨5114290354270112604624233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13638107611386966945664621 5114290354270112604624233)
          ·
            refine ⟨3835717765702584453468175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5114290354270112604624233 3835717765702584453468175)
            ·
              refine ⟨5753576648553876680202263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3835717765702584453468175 5753576648553876680202263)
              ·
                refine ⟨8630364972830815020303395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5753576648553876680202263 8630364972830815020303395)
                ·
                  refine ⟨12945547459246222530455093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8630364972830815020303395 12945547459246222530455093)
                  ·
                    refine ⟨1213645074304333362230165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12945547459246222530455093 1213645074304333362230165)
                    ·
                      rfl

theorem cell22_3545348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 2, 1, 1, 1, 5].length) (baseStart_3545348 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3545348 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3545348 prefixEnd_3545348 := by exact prefixLift 3545348
  have htrace : WordTrace (prefixWord ++ tailWord_3545348) baseStart_3545348 baseEnd_3545348 := by
    simpa [prefixWord, tailWord_3545348, baseEnd_3545348] using wordTrace_append hprefix tailTrace_3545348
  have hstable : (prefixWord ++ tailWord_3545348).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3545348).length < 2 ^ (prefixWord ++ tailWord_3545348).sum := by decide
  have hdescent : baseEnd_3545348 < baseStart_3545348 := by decide
  rcases family_descends (prefixWord ++ tailWord_3545348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3545361 : List Nat := [1, 2, 2, 1, 1, 7, 2, 6]
def baseStart_3545361 : Nat := 118140960795 + 3545361 * 2 ^ 59
def prefixEnd_3545361 : Nat := 4983230072969 + 3 ^ 40 * 3545361 * 2
def baseEnd_3545361 : Nat := 134849947163333962406125

theorem tailTrace_3545361 : CollatzResearch.WordTrace tailWord_3545361 prefixEnd_3545361 134849947163333962406125 := by
  unfold tailWord_3545361
  simp only [CollatzResearch.WordTrace]
  refine ⟨129309938908770071297635937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86206625939180047531757291 129309938908770071297635937)
  ·
    refine ⟨96982454181577553473226953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129309938908770071297635937 96982454181577553473226953)
    ·
      refine ⟨72736840636183165104920215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96982454181577553473226953 72736840636183165104920215)
      ·
        refine ⟨109105260954274747657380323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72736840636183165104920215 109105260954274747657380323)
        ·
          refine ⟨163657891431412121486070485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109105260954274747657380323 163657891431412121486070485)
          ·
            refine ⟨3835731830423721597329777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 163657891431412121486070485 3835731830423721597329777)
            ·
              refine ⟨2876798872817791197997333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3835731830423721597329777 2876798872817791197997333)
              ·
                refine ⟨134849947163333962406125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2876798872817791197997333 134849947163333962406125)
                ·
                  rfl

theorem cell22_3545361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 7, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 7, 2, 6].length) (baseStart_3545361 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3545361 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3545361 prefixEnd_3545361 := by exact prefixLift 3545361
  have htrace : WordTrace (prefixWord ++ tailWord_3545361) baseStart_3545361 baseEnd_3545361 := by
    simpa [prefixWord, tailWord_3545361, baseEnd_3545361] using wordTrace_append hprefix tailTrace_3545361
  have hstable : (prefixWord ++ tailWord_3545361).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3545361).length < 2 ^ (prefixWord ++ tailWord_3545361).sum := by decide
  have hdescent : baseEnd_3545361 < baseStart_3545361 := by decide
  rcases family_descends (prefixWord ++ tailWord_3545361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3545404 : List Nat := [2, 2, 2, 2, 1, 2, 2, 1, 1, 7]
def baseStart_3545404 : Nat := 118140960795 + 3545404 * 2 ^ 59
def prefixEnd_3545404 : Nat := 4983230072969 + 3 ^ 40 * 3545404 * 2
def baseEnd_3545404 : Nat := 1213664244248767882829993

theorem tailTrace_3545404 : CollatzResearch.WordTrace tailWord_3545404 prefixEnd_3545404 1213664244248767882829993 := by
  unfold tailWord_3545404
  simp only [CollatzResearch.WordTrace]
  refine ⟨64655753623807144820725633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86207671498409526427634177 64655753623807144820725633)
  ·
    refine ⟨48491815217855358615544225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64655753623807144820725633 48491815217855358615544225)
    ·
      refine ⟨36368861413391518961658169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48491815217855358615544225 36368861413391518961658169)
      ·
        refine ⟨27276646060043639221243627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36368861413391518961658169 27276646060043639221243627)
        ·
          refine ⟨40914969090065458831865441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27276646060043639221243627 40914969090065458831865441)
          ·
            refine ⟨30686226817549094123899081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40914969090065458831865441 30686226817549094123899081)
            ·
              refine ⟨23014670113161820592924311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30686226817549094123899081 23014670113161820592924311)
              ·
                refine ⟨34522005169742730889386467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23014670113161820592924311 34522005169742730889386467)
                ·
                  refine ⟨51783007754614096334079701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34522005169742730889386467 51783007754614096334079701)
                  ·
                    refine ⟨1213664244248767882829993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 51783007754614096334079701 1213664244248767882829993)
                    ·
                      rfl

theorem cell22_3545404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 1, 1, 7].length) (baseStart_3545404 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3545404 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3545404 prefixEnd_3545404 := by exact prefixLift 3545404
  have htrace : WordTrace (prefixWord ++ tailWord_3545404) baseStart_3545404 baseEnd_3545404 := by
    simpa [prefixWord, tailWord_3545404, baseEnd_3545404] using wordTrace_append hprefix tailTrace_3545404
  have hstable : (prefixWord ++ tailWord_3545404).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3545404).length < 2 ^ (prefixWord ++ tailWord_3545404).sum := by decide
  have hdescent : baseEnd_3545404 < baseStart_3545404 := by decide
  rcases family_descends (prefixWord ++ tailWord_3545404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3545449 : List Nat := [1, 2, 1, 1, 1, 3, 3, 2, 3, 5]
def baseStart_3545449 : Nat := 118140960795 + 3545449 * 2 ^ 59
def prefixEnd_3545449 : Nat := 4983230072969 + 3 ^ 40 * 3545449 * 2
def baseEnd_3545449 : Nat := 1213679648668402765454855

theorem tailTrace_3545449 : CollatzResearch.WordTrace tailWord_3545449 prefixEnd_3545449 1213679648668402765454855 := by
  unfold tailWord_3545449
  simp only [CollatzResearch.WordTrace]
  refine ⟨129313148532451262326839401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86208765688300841551226267 129313148532451262326839401)
  ·
    refine ⟨96984861399338446745129551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129313148532451262326839401 96984861399338446745129551)
    ·
      refine ⟨145477292099007670117694327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96984861399338446745129551 145477292099007670117694327)
      ·
        refine ⟨218215938148511505176541491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145477292099007670117694327 218215938148511505176541491)
        ·
          refine ⟨327323907222767257764812237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 218215938148511505176541491 327323907222767257764812237)
          ·
            refine ⟨122746465208537721661804589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 327323907222767257764812237 122746465208537721661804589)
            ·
              refine ⟨46029924453201645623176721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 122746465208537721661804589 46029924453201645623176721)
              ·
                refine ⟨34522443339901234217382541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46029924453201645623176721 34522443339901234217382541)
                ·
                  refine ⟨12945916252462962831518453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34522443339901234217382541 12945916252462962831518453)
                  ·
                    refine ⟨1213679648668402765454855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12945916252462962831518453 1213679648668402765454855)
                    ·
                      rfl

theorem cell22_3545449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 2, 3, 5].length) (baseStart_3545449 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3545449 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3545449 prefixEnd_3545449 := by exact prefixLift 3545449
  have htrace : WordTrace (prefixWord ++ tailWord_3545449) baseStart_3545449 baseEnd_3545449 := by
    simpa [prefixWord, tailWord_3545449, baseEnd_3545449] using wordTrace_append hprefix tailTrace_3545449
  have hstable : (prefixWord ++ tailWord_3545449).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3545449).length < 2 ^ (prefixWord ++ tailWord_3545449).sum := by decide
  have hdescent : baseEnd_3545449 < baseStart_3545449 := by decide
  rcases family_descends (prefixWord ++ tailWord_3545449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3545451 : List Nat := [1, 1, 1, 1, 2, 2, 2, 8, 4]
def baseStart_3545451 : Nat := 118140960795 + 3545451 * 2 ^ 59
def prefixEnd_3545451 : Nat := 4983230072969 + 3 ^ 40 * 3545451 * 2
def baseEnd_3545451 : Nat := 404560111103091808968283

theorem tailTrace_3545451 : CollatzResearch.WordTrace tailWord_3545451 prefixEnd_3545451 404560111103091808968283 := by
  unfold tailWord_3545451
  simp only [CollatzResearch.WordTrace]
  refine ⟨129313221478444016668412207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86208814318962677778941471 129313221478444016668412207)
  ·
    refine ⟨193969832217666025002618311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129313221478444016668412207 193969832217666025002618311)
    ·
      refine ⟨290954748326499037503927467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193969832217666025002618311 290954748326499037503927467)
      ·
        refine ⟨436432122489748556255891201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 290954748326499037503927467 436432122489748556255891201)
        ·
          refine ⟨327324091867311417191918401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 436432122489748556255891201 327324091867311417191918401)
          ·
            refine ⟨245493068900483562893938801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 327324091867311417191918401 245493068900483562893938801)
            ·
              refine ⟨184119801675362672170454101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 245493068900483562893938801 184119801675362672170454101)
              ·
                refine ⟨2157653925883156314497509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 184119801675362672170454101 2157653925883156314497509)
                ·
                  refine ⟨404560111103091808968283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2157653925883156314497509 404560111103091808968283)
                  ·
                    rfl

theorem cell22_3545451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 8, 4].length) (baseStart_3545451 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3545451 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3545451 prefixEnd_3545451 := by exact prefixLift 3545451
  have htrace : WordTrace (prefixWord ++ tailWord_3545451) baseStart_3545451 baseEnd_3545451 := by
    simpa [prefixWord, tailWord_3545451, baseEnd_3545451] using wordTrace_append hprefix tailTrace_3545451
  have hstable : (prefixWord ++ tailWord_3545451).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3545451).length < 2 ^ (prefixWord ++ tailWord_3545451).sum := by decide
  have hdescent : baseEnd_3545451 < baseStart_3545451 := by decide
  rcases family_descends (prefixWord ++ tailWord_3545451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3545481 : List Nat := [1, 2, 1, 1, 6, 2, 1, 1, 1, 6]
def baseStart_3545481 : Nat := 118140960795 + 3545481 * 2 ^ 59
def prefixEnd_3545481 : Nat := 4983230072969 + 3 ^ 40 * 3545481 * 2
def baseEnd_3545481 : Nat := 1213690602922365348654757

theorem tailTrace_3545481 : CollatzResearch.WordTrace tailWord_3545481 prefixEnd_3545481 1213690602922365348654757 := by
  unfold tailWord_3545481
  simp only [CollatzResearch.WordTrace]
  refine ⟨129314315668335331792004297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86209543778890221194669531 129314315668335331792004297)
  ·
    refine ⟨96985736751251498844003223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129314315668335331792004297 96985736751251498844003223)
    ·
      refine ⟨145478605126877248266004835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96985736751251498844003223 145478605126877248266004835)
      ·
        refine ⟨218217907690315872399007253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145478605126877248266004835 218217907690315872399007253)
        ·
          refine ⟨10228964422983556518703465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 218217907690315872399007253 10228964422983556518703465)
          ·
            refine ⟨7671723317237667389027599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10228964422983556518703465 7671723317237667389027599)
            ·
              refine ⟨11507584975856501083541399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7671723317237667389027599 11507584975856501083541399)
              ·
                refine ⟨17261377463784751625312099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11507584975856501083541399 17261377463784751625312099)
                ·
                  refine ⟨25892066195677127437968149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17261377463784751625312099 25892066195677127437968149)
                  ·
                    refine ⟨1213690602922365348654757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25892066195677127437968149 1213690602922365348654757)
                    ·
                      rfl

theorem cell22_3545481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 1, 1, 1, 6].length) (baseStart_3545481 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3545481 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3545481 prefixEnd_3545481 := by exact prefixLift 3545481
  have htrace : WordTrace (prefixWord ++ tailWord_3545481) baseStart_3545481 baseEnd_3545481 := by
    simpa [prefixWord, tailWord_3545481, baseEnd_3545481] using wordTrace_append hprefix tailTrace_3545481
  have hstable : (prefixWord ++ tailWord_3545481).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3545481).length < 2 ^ (prefixWord ++ tailWord_3545481).sum := by decide
  have hdescent : baseEnd_3545481 < baseStart_3545481 := by decide
  rcases family_descends (prefixWord ++ tailWord_3545481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3545496 : List Nat := [2, 1, 2, 5, 1, 2, 9]
def baseStart_3545496 : Nat := 118140960795 + 3545496 * 2 ^ 59
def prefixEnd_3545496 : Nat := 4983230072969 + 3 ^ 40 * 3545496 * 2
def baseEnd_3545496 : Nat := 44951693989959641093693

theorem tailTrace_3545496 : CollatzResearch.WordTrace tailWord_3545496 prefixEnd_3545496 44951693989959641093693 := by
  unfold tailWord_3545496
  simp only [CollatzResearch.WordTrace]
  refine ⟨64657431381640494676900171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86209908508853992902533561 64657431381640494676900171)
  ·
    refine ⟨96986147072460742015350257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64657431381640494676900171 96986147072460742015350257)
    ·
      refine ⟨72739610304345556511512693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96986147072460742015350257 72739610304345556511512693)
      ·
        refine ⟨6819338466032395922954315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 72739610304345556511512693 6819338466032395922954315)
        ·
          refine ⟨10229007699048593884431473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6819338466032395922954315 10229007699048593884431473)
          ·
            refine ⟨7671755774286445413323605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10229007699048593884431473 7671755774286445413323605)
            ·
              refine ⟨44951693989959641093693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7671755774286445413323605 44951693989959641093693)
              ·
                rfl

theorem cell22_3545496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 9].length) (baseStart_3545496 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3545496 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3545496 prefixEnd_3545496 := by exact prefixLift 3545496
  have htrace : WordTrace (prefixWord ++ tailWord_3545496) baseStart_3545496 baseEnd_3545496 := by
    simpa [prefixWord, tailWord_3545496, baseEnd_3545496] using wordTrace_append hprefix tailTrace_3545496
  have hstable : (prefixWord ++ tailWord_3545496).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3545496).length < 2 ^ (prefixWord ++ tailWord_3545496).sum := by decide
  have hdescent : baseEnd_3545496 < baseStart_3545496 := by decide
  rcases family_descends (prefixWord ++ tailWord_3545496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3545517 : List Nat := [1, 5, 2, 2, 3, 1, 1, 1, 1, 5]
def baseStart_3545517 : Nat := 118140960795 + 3545517 * 2 ^ 59
def prefixEnd_3545517 : Nat := 4983230072969 + 3 ^ 40 * 3545517 * 2
def baseEnd_3545517 : Nat := 1213702926458073254754647

theorem tailTrace_3545517 : CollatzResearch.WordTrace tailWord_3545517 prefixEnd_3545517 1213702926458073254754647 := by
  unfold tailWord_3545517
  simp only [CollatzResearch.WordTrace]
  refine ⟨129315628696204909940314805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86210419130803273293543203 129315628696204909940314805)
  ·
    refine ⟨12123340190269210306904513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 129315628696204909940314805 12123340190269210306904513)
    ·
      refine ⟨9092505142701907730178385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12123340190269210306904513 9092505142701907730178385)
      ·
        refine ⟨6819378857026430797633789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9092505142701907730178385 6819378857026430797633789)
        ·
          refine ⟨2557267071384911549112671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6819378857026430797633789 2557267071384911549112671)
          ·
            refine ⟨3835900607077367323669007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2557267071384911549112671 3835900607077367323669007)
            ·
              refine ⟨5753850910616050985503511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3835900607077367323669007 5753850910616050985503511)
              ·
                refine ⟨8630776365924076478255267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5753850910616050985503511 8630776365924076478255267)
                ·
                  refine ⟨12946164548886114717382901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8630776365924076478255267 12946164548886114717382901)
                  ·
                    refine ⟨1213702926458073254754647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12946164548886114717382901 1213702926458073254754647)
                    ·
                      rfl

theorem cell22_3545517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 3, 1, 1, 1, 1, 5].length) (baseStart_3545517 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3545517 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3545517 prefixEnd_3545517 := by exact prefixLift 3545517
  have htrace : WordTrace (prefixWord ++ tailWord_3545517) baseStart_3545517 baseEnd_3545517 := by
    simpa [prefixWord, tailWord_3545517, baseEnd_3545517] using wordTrace_append hprefix tailTrace_3545517
  have hstable : (prefixWord ++ tailWord_3545517).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3545517).length < 2 ^ (prefixWord ++ tailWord_3545517).sum := by decide
  have hdescent : baseEnd_3545517 < baseStart_3545517 := by decide
  rcases family_descends (prefixWord ++ tailWord_3545517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3545545 : List Nat := [1, 2, 1, 1, 2, 1, 7, 3, 1, 3]
def baseStart_3545545 : Nat := 118140960795 + 3545545 * 2 ^ 59
def prefixEnd_3545545 : Nat := 4983230072969 + 3 ^ 40 * 3545545 * 2
def baseEnd_3545545 : Nat := 1213712511430290515054561

theorem tailTrace_3545545 : CollatzResearch.WordTrace tailWord_3545545 prefixEnd_3545545 1213712511430290515054561 := by
  unfold tailWord_3545545
  simp only [CollatzResearch.WordTrace]
  refine ⟨129316649940103470722334089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86211099960068980481556059 129316649940103470722334089)
  ·
    refine ⟨96987487455077603041750567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129316649940103470722334089 96987487455077603041750567)
    ·
      refine ⟨145481231182616404562625851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96987487455077603041750567 145481231182616404562625851)
      ·
        refine ⟨218221846773924606843938777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145481231182616404562625851 218221846773924606843938777)
        ·
          refine ⟨163666385080443455132954083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 218221846773924606843938777 163666385080443455132954083)
          ·
            refine ⟨245499577620665182699431125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163666385080443455132954083 245499577620665182699431125)
            ·
              refine ⟨5753896350484340219517917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 245499577620665182699431125 5753896350484340219517917)
              ·
                refine ⟨2157711131431627582319219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5753896350484340219517917 2157711131431627582319219)
                ·
                  refine ⟨3236566697147441373478829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2157711131431627582319219 3236566697147441373478829)
                  ·
                    refine ⟨1213712511430290515054561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3236566697147441373478829 1213712511430290515054561)
                    ·
                      rfl

theorem cell22_3545545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 7, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 7, 3, 1, 3].length) (baseStart_3545545 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3545545 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3545545 prefixEnd_3545545 := by exact prefixLift 3545545
  have htrace : WordTrace (prefixWord ++ tailWord_3545545) baseStart_3545545 baseEnd_3545545 := by
    simpa [prefixWord, tailWord_3545545, baseEnd_3545545] using wordTrace_append hprefix tailTrace_3545545
  have hstable : (prefixWord ++ tailWord_3545545).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3545545).length < 2 ^ (prefixWord ++ tailWord_3545545).sum := by decide
  have hdescent : baseEnd_3545545 < baseStart_3545545 := by decide
  rcases family_descends (prefixWord ++ tailWord_3545545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3545558 : List Nat := [5, 2, 1, 1, 1, 1, 1, 3, 7]
def baseStart_3545558 : Nat := 118140960795 + 3545558 * 2 ^ 59
def prefixEnd_3545558 : Nat := 4983230072969 + 3 ^ 40 * 3545558 * 2
def baseEnd_3545558 : Nat := 404572320531987604826507

theorem tailTrace_3545558 : CollatzResearch.WordTrace tailWord_3545558 prefixEnd_3545558 404572320531987604826507 := by
  unfold tailWord_3545558
  simp only [CollatzResearch.WordTrace]
  refine ⟨8082320255566023371409833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 86211416059370915961704885 8082320255566023371409833)
  ·
    refine ⟨6061740191674517528557375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8082320255566023371409833 6061740191674517528557375)
    ·
      refine ⟨9092610287511776292836063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6061740191674517528557375 9092610287511776292836063)
      ·
        refine ⟨13638915431267664439254095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9092610287511776292836063 13638915431267664439254095)
        ·
          refine ⟨20458373146901496658881143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13638915431267664439254095 20458373146901496658881143)
          ·
            refine ⟨30687559720352244988321715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20458373146901496658881143 30687559720352244988321715)
            ·
              refine ⟨46031339580528367482482573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30687559720352244988321715 46031339580528367482482573)
              ·
                refine ⟨17261752342698137805930965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46031339580528367482482573 17261752342698137805930965)
                ·
                  refine ⟨404572320531987604826507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17261752342698137805930965 404572320531987604826507)
                  ·
                    rfl

theorem cell22_3545558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 3, 7].length) (baseStart_3545558 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3545558 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3545558 prefixEnd_3545558 := by exact prefixLift 3545558
  have htrace : WordTrace (prefixWord ++ tailWord_3545558) baseStart_3545558 baseEnd_3545558 := by
    simpa [prefixWord, tailWord_3545558, baseEnd_3545558] using wordTrace_append hprefix tailTrace_3545558
  have hstable : (prefixWord ++ tailWord_3545558).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3545558).length < 2 ^ (prefixWord ++ tailWord_3545558).sum := by decide
  have hdescent : baseEnd_3545558 < baseStart_3545558 := by decide
  rcases family_descends (prefixWord ++ tailWord_3545558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3545562 : List Nat := [3, 1, 1, 2, 3, 1, 5, 2, 1, 3]
def baseStart_3545562 : Nat := 118140960795 + 3545562 * 2 ^ 59
def prefixEnd_3545562 : Nat := 4983230072969 + 3 ^ 40 * 3545562 * 2
def baseEnd_3545562 : Nat := 1213718330877708137379509

theorem tailTrace_3545562 : CollatzResearch.WordTrace tailWord_3545562 prefixEnd_3545562 1213718330877708137379509 := by
  unfold tailWord_3545562
  simp only [CollatzResearch.WordTrace]
  refine ⟨32329317495260470656425735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86211513320694588417135293 32329317495260470656425735)
  ·
    refine ⟨48493976242890705984638603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32329317495260470656425735 48493976242890705984638603)
    ·
      refine ⟨72740964364336058976957905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48493976242890705984638603 72740964364336058976957905)
      ·
        refine ⟨54555723273252044232718429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72740964364336058976957905 54555723273252044232718429)
        ·
          refine ⟨20458396227469516587269411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54555723273252044232718429 20458396227469516587269411)
          ·
            refine ⟨30687594341204274880904117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20458396227469516587269411 30687594341204274880904117)
            ·
              refine ⟨2876961969487900770084761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30687594341204274880904117 2876961969487900770084761)
              ·
                refine ⟨2157721477115925577563571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2876961969487900770084761 2157721477115925577563571)
                ·
                  refine ⟨3236582215673888366345357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2157721477115925577563571 3236582215673888366345357)
                  ·
                    refine ⟨1213718330877708137379509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3236582215673888366345357 1213718330877708137379509)
                    ·
                      rfl

theorem cell22_3545562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 5, 2, 1, 3].length) (baseStart_3545562 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3545562 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3545562 prefixEnd_3545562 := by exact prefixLift 3545562
  have htrace : WordTrace (prefixWord ++ tailWord_3545562) baseStart_3545562 baseEnd_3545562 := by
    simpa [prefixWord, tailWord_3545562, baseEnd_3545562] using wordTrace_append hprefix tailTrace_3545562
  have hstable : (prefixWord ++ tailWord_3545562).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3545562).length < 2 ^ (prefixWord ++ tailWord_3545562).sum := by decide
  have hdescent : baseEnd_3545562 < baseStart_3545562 := by decide
  rcases family_descends (prefixWord ++ tailWord_3545562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3545603 : List Nat := [1, 1, 1, 3, 2, 1, 4, 5, 4]
def baseStart_3545603 : Nat := 118140960795 + 3545603 * 2 ^ 59
def prefixEnd_3545603 : Nat := 4983230072969 + 3 ^ 40 * 3545603 * 2
def baseEnd_3545603 : Nat := 404577455338532565701461

theorem tailTrace_3545603 : CollatzResearch.WordTrace tailWord_3545603 prefixEnd_3545603 404577455338532565701461 := by
  unfold tailWord_3545603
  simp only [CollatzResearch.WordTrace]
  refine ⟨129318765373893346627945463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86212510249262231085296975 129318765373893346627945463)
  ·
    refine ⟨193978148060840019941918195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129318765373893346627945463 193978148060840019941918195)
    ·
      refine ⟨290967222091260029912877293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193978148060840019941918195 290967222091260029912877293)
      ·
        refine ⟨109112708284222511217328985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 290967222091260029912877293 109112708284222511217328985)
        ·
          refine ⟨81834531213166883412996739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109112708284222511217328985 81834531213166883412996739)
          ·
            refine ⟨122751796819750325119495109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81834531213166883412996739 122751796819750325119495109)
            ·
              refine ⟨23015961903703185959905333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 122751796819750325119495109 23015961903703185959905333)
              ·
                refine ⟨2157746428472173683741125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23015961903703185959905333 2157746428472173683741125)
                ·
                  refine ⟨404577455338532565701461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2157746428472173683741125 404577455338532565701461)
                  ·
                    rfl

theorem cell22_3545603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 5, 4].length) (baseStart_3545603 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3545603 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3545603 prefixEnd_3545603 := by exact prefixLift 3545603
  have htrace : WordTrace (prefixWord ++ tailWord_3545603) baseStart_3545603 baseEnd_3545603 := by
    simpa [prefixWord, tailWord_3545603, baseEnd_3545603] using wordTrace_append hprefix tailTrace_3545603
  have hstable : (prefixWord ++ tailWord_3545603).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3545603).length < 2 ^ (prefixWord ++ tailWord_3545603).sum := by decide
  have hdescent : baseEnd_3545603 < baseStart_3545603 := by decide
  rcases family_descends (prefixWord ++ tailWord_3545603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3545613 : List Nat := [1, 7, 1, 1, 1, 3, 2, 2, 1, 3]
def baseStart_3545613 : Nat := 118140960795 + 3545613 * 2 ^ 59
def prefixEnd_3545613 : Nat := 4983230072969 + 3 ^ 40 * 3545613 * 2
def baseEnd_3545613 : Nat := 1213735789219961004354353

theorem tailTrace_3545613 : CollatzResearch.WordTrace tailWord_3545613 prefixEnd_3545613 1213735789219961004354353 := by
  unfold tailWord_3545613
  simp only [CollatzResearch.WordTrace]
  refine ⟨129319130103857118335809493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86212753402571412223872995 129319130103857118335809493)
  ·
    refine ⟨3030917111809151210995535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 129319130103857118335809493 3030917111809151210995535)
    ·
      refine ⟨4546375667713726816493303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3030917111809151210995535 4546375667713726816493303)
      ·
        refine ⟨6819563501570590224739955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4546375667713726816493303 6819563501570590224739955)
        ·
          refine ⟨10229345252355885337109933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6819563501570590224739955 10229345252355885337109933)
          ·
            refine ⟨3836004469633457001416225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10229345252355885337109933 3836004469633457001416225)
            ·
              refine ⟨2877003352225092751062169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3836004469633457001416225 2877003352225092751062169)
              ·
                refine ⟨2157752514168819563296627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2877003352225092751062169 2157752514168819563296627)
                ·
                  refine ⟨3236628771253229344944941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2157752514168819563296627 3236628771253229344944941)
                  ·
                    refine ⟨1213735789219961004354353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3236628771253229344944941 1213735789219961004354353)
                    ·
                      rfl

theorem cell22_3545613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 3, 2, 2, 1, 3].length) (baseStart_3545613 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3545613 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3545613 prefixEnd_3545613 := by exact prefixLift 3545613
  have htrace : WordTrace (prefixWord ++ tailWord_3545613) baseStart_3545613 baseEnd_3545613 := by
    simpa [prefixWord, tailWord_3545613, baseEnd_3545613] using wordTrace_append hprefix tailTrace_3545613
  have hstable : (prefixWord ++ tailWord_3545613).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3545613).length < 2 ^ (prefixWord ++ tailWord_3545613).sum := by decide
  have hdescent : baseEnd_3545613 < baseStart_3545613 := by decide
  rcases family_descends (prefixWord ++ tailWord_3545613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3545616 : List Nat := [2, 1, 1, 1, 1, 1, 1, 2, 8, 4]
def baseStart_3545616 : Nat := 118140960795 + 3545616 * 2 ^ 59
def prefixEnd_3545616 : Nat := 4983230072969 + 3 ^ 40 * 3545616 * 2
def baseEnd_3545616 : Nat := 1213736816181269996529343

theorem tailTrace_3545616 : CollatzResearch.WordTrace tailWord_3545616 prefixEnd_3545616 1213736816181269996529343 := by
  unfold tailWord_3545616
  simp only [CollatzResearch.WordTrace]
  refine ⟨64659619761423124924084351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86212826348564166565445801 64659619761423124924084351)
  ·
    refine ⟨96989429642134687386126527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64659619761423124924084351 96989429642134687386126527)
    ·
      refine ⟨145484144463202031079189791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96989429642134687386126527 145484144463202031079189791)
      ·
        refine ⟨218226216694803046618784687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145484144463202031079189791 218226216694803046618784687)
        ·
          refine ⟨327339325042204569928177031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 218226216694803046618784687 327339325042204569928177031)
          ·
            refine ⟨491008987563306854892265547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 327339325042204569928177031 491008987563306854892265547)
            ·
              refine ⟨736513481344960282338398321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 491008987563306854892265547 736513481344960282338398321)
              ·
                refine ⟨552385111008720211753798741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 736513481344960282338398321 552385111008720211753798741)
                ·
                  refine ⟨6473263019633439981489829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 552385111008720211753798741 6473263019633439981489829)
                  ·
                    refine ⟨1213736816181269996529343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6473263019633439981489829 1213736816181269996529343)
                    ·
                      rfl

theorem cell22_3545616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 8, 4].length) (baseStart_3545616 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3545616 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3545616 prefixEnd_3545616 := by exact prefixLift 3545616
  have htrace : WordTrace (prefixWord ++ tailWord_3545616) baseStart_3545616 baseEnd_3545616 := by
    simpa [prefixWord, tailWord_3545616, baseEnd_3545616] using wordTrace_append hprefix tailTrace_3545616
  have hstable : (prefixWord ++ tailWord_3545616).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3545616).length < 2 ^ (prefixWord ++ tailWord_3545616).sum := by decide
  have hdescent : baseEnd_3545616 < baseStart_3545616 := by decide
  rcases family_descends (prefixWord ++ tailWord_3545616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3545635 : List Nat := [1, 1, 1, 4, 4, 1, 2, 3, 2, 3]
def baseStart_3545635 : Nat := 118140960795 + 3545635 * 2 ^ 59
def prefixEnd_3545635 : Nat := 4983230072969 + 3 ^ 40 * 3545635 * 2
def baseEnd_3545635 : Nat := 1213743320269560280304285

theorem tailTrace_3545635 : CollatzResearch.WordTrace tailWord_3545635 prefixEnd_3545635 1213743320269560280304285 := by
  unfold tailWord_3545635
  simp only [CollatzResearch.WordTrace]
  refine ⟨129319932509777416093110359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86213288339851610728740239 129319932509777416093110359)
  ·
    refine ⟨193979898764666124139665539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129319932509777416093110359 193979898764666124139665539)
    ·
      refine ⟨290969848146999186209498309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193979898764666124139665539 290969848146999186209498309)
      ·
        refine ⟨54556846527562347414280933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 290969848146999186209498309 54556846527562347414280933)
        ·
          refine ⟨10229408723917940140177675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 54556846527562347414280933 10229408723917940140177675)
          ·
            refine ⟨15344113085876910210266513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10229408723917940140177675 15344113085876910210266513)
            ·
              refine ⟨11508084814407682657699885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15344113085876910210266513 11508084814407682657699885)
              ·
                refine ⟨4315531805402880996637457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11508084814407682657699885 4315531805402880996637457)
                ·
                  refine ⟨3236648854052160747478093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4315531805402880996637457 3236648854052160747478093)
                  ·
                    refine ⟨1213743320269560280304285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3236648854052160747478093 1213743320269560280304285)
                    ·
                      rfl

theorem cell22_3545635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 2, 3, 2, 3].length) (baseStart_3545635 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3545635 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3545635 prefixEnd_3545635 := by exact prefixLift 3545635
  have htrace : WordTrace (prefixWord ++ tailWord_3545635) baseStart_3545635 baseEnd_3545635 := by
    simpa [prefixWord, tailWord_3545635, baseEnd_3545635] using wordTrace_append hprefix tailTrace_3545635
  have hstable : (prefixWord ++ tailWord_3545635).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3545635).length < 2 ^ (prefixWord ++ tailWord_3545635).sum := by decide
  have hdescent : baseEnd_3545635 < baseStart_3545635 := by decide
  rcases family_descends (prefixWord ++ tailWord_3545635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3545663 : List Nat := [1, 1, 2, 2, 3, 2, 1, 2, 5, 3]
def baseStart_3545663 : Nat := 118140960795 + 3545663 * 2 ^ 59
def prefixEnd_3545663 : Nat := 4983230072969 + 3 ^ 40 * 3545663 * 2
def baseEnd_3545663 : Nat := 1213752905241777540604199

theorem tailTrace_3545663 : CollatzResearch.WordTrace tailWord_3545663 prefixEnd_3545663 1213752905241777540604199 := by
  unfold tailWord_3545663
  simp only [CollatzResearch.WordTrace]
  refine ⟨129320953753675976875129643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86213969169117317916753095 129320953753675976875129643)
  ·
    refine ⟨193981430630513965312694465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129320953753675976875129643 193981430630513965312694465)
    ·
      refine ⟨145486072972885473984520849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193981430630513965312694465 145486072972885473984520849)
      ·
        refine ⟨109114554729664105488390637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145486072972885473984520849 109114554729664105488390637)
        ·
          refine ⟨40917958023624039558146489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 109114554729664105488390637 40917958023624039558146489)
          ·
            refine ⟨30688468517718029668609867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40917958023624039558146489 30688468517718029668609867)
            ·
              refine ⟨46032702776577044502914801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30688468517718029668609867 46032702776577044502914801)
              ·
                refine ⟨34524527082432783377186101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46032702776577044502914801 34524527082432783377186101)
                ·
                  refine ⟨3236674413978073441611197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 34524527082432783377186101 3236674413978073441611197)
                  ·
                    refine ⟨1213752905241777540604199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3236674413978073441611197 1213752905241777540604199)
                    ·
                      rfl

theorem cell22_3545663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 2, 5, 3].length) (baseStart_3545663 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3545663 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3545663 prefixEnd_3545663 := by exact prefixLift 3545663
  have htrace : WordTrace (prefixWord ++ tailWord_3545663) baseStart_3545663 baseEnd_3545663 := by
    simpa [prefixWord, tailWord_3545663, baseEnd_3545663] using wordTrace_append hprefix tailTrace_3545663
  have hstable : (prefixWord ++ tailWord_3545663).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3545663).length < 2 ^ (prefixWord ++ tailWord_3545663).sum := by decide
  have hdescent : baseEnd_3545663 < baseStart_3545663 := by decide
  rcases family_descends (prefixWord ++ tailWord_3545663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3545753 : List Nat := [1, 2, 1, 2, 1, 2, 4, 3, 1, 5]
def baseStart_3545753 : Nat := 118140960795 + 3545753 * 2 ^ 59
def prefixEnd_3545753 : Nat := 4983230072969 + 3 ^ 40 * 3545753 * 2
def baseEnd_3545753 : Nat := 1213783714081047305853923

theorem tailTrace_3545753 : CollatzResearch.WordTrace tailWord_3545753 prefixEnd_3545753 1213783714081047305853923 := by
  unfold tailWord_3545753
  simp only [CollatzResearch.WordTrace]
  refine ⟨129324236323349922245905913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86216157548899948163937275 129324236323349922245905913)
  ·
    refine ⟨96993177242512441684429435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129324236323349922245905913 96993177242512441684429435)
    ·
      refine ⟨145489765863768662526644153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96993177242512441684429435 145489765863768662526644153)
      ·
        refine ⟨109117324397826496894983115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145489765863768662526644153 109117324397826496894983115)
        ·
          refine ⟨163675986596739745342474673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109117324397826496894983115 163675986596739745342474673)
          ·
            refine ⟨122756989947554809006856005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 163675986596739745342474673 122756989947554809006856005)
            ·
              refine ⟨23016935615166526688785501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 122756989947554809006856005 23016935615166526688785501)
              ·
                refine ⟨8631350855687447508294563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23016935615166526688785501 8631350855687447508294563)
                ·
                  refine ⟨12947026283531171262441845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8631350855687447508294563 12947026283531171262441845)
                  ·
                    refine ⟨1213783714081047305853923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12947026283531171262441845 1213783714081047305853923)
                    ·
                      rfl

theorem cell22_3545753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 3, 1, 5].length) (baseStart_3545753 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3545753 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3545753 prefixEnd_3545753 := by exact prefixLift 3545753
  have htrace : WordTrace (prefixWord ++ tailWord_3545753) baseStart_3545753 baseEnd_3545753 := by
    simpa [prefixWord, tailWord_3545753, baseEnd_3545753] using wordTrace_append hprefix tailTrace_3545753
  have hstable : (prefixWord ++ tailWord_3545753).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3545753).length < 2 ^ (prefixWord ++ tailWord_3545753).sum := by decide
  have hdescent : baseEnd_3545753 < baseStart_3545753 := by decide
  rcases family_descends (prefixWord ++ tailWord_3545753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3545783 : List Nat := [1, 1, 3, 1, 6, 10]
def baseStart_3545783 : Nat := 118140960795 + 3545783 * 2 ^ 59
def prefixEnd_3545783 : Nat := 4983230072969 + 3 ^ 40 * 3545783 * 2
def baseEnd_3545783 : Nat := 14985110909804163303751

theorem tailTrace_3545783 : CollatzResearch.WordTrace tailWord_3545783 prefixEnd_3545783 14985110909804163303751 := by
  unfold tailWord_3545783
  simp only [CollatzResearch.WordTrace]
  refine ⟨129325330513241237369498003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86216887008827491579665335 129325330513241237369498003)
  ·
    refine ⟨193987995769861856054247005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129325330513241237369498003 193987995769861856054247005)
    ·
      refine ⟨72745498413698196020342627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 193987995769861856054247005 72745498413698196020342627)
      ·
        refine ⟨109118247620547294030513941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72745498413698196020342627 109118247620547294030513941)
        ·
          refine ⟨5114917857213154407680341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 109118247620547294030513941 5114917857213154407680341)
          ·
            refine ⟨14985110909804163303751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 5114917857213154407680341 14985110909804163303751)
            ·
              rfl

theorem cell22_3545783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 10].length) (baseStart_3545783 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3545783 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3545783 prefixEnd_3545783 := by exact prefixLift 3545783
  have htrace : WordTrace (prefixWord ++ tailWord_3545783) baseStart_3545783 baseEnd_3545783 := by
    simpa [prefixWord, tailWord_3545783, baseEnd_3545783] using wordTrace_append hprefix tailTrace_3545783
  have hstable : (prefixWord ++ tailWord_3545783).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3545783).length < 2 ^ (prefixWord ++ tailWord_3545783).sum := by decide
  have hdescent : baseEnd_3545783 < baseStart_3545783 := by decide
  rcases family_descends (prefixWord ++ tailWord_3545783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3545789 : List Nat := [1, 4, 1, 2, 1, 5, 2, 2, 4]
def baseStart_3545789 : Nat := 118140960795 + 3545789 * 2 ^ 59
def prefixEnd_3545789 : Nat := 4983230072969 + 3 ^ 40 * 3545789 * 2
def baseEnd_3545789 : Nat := 404598679205585070651271

theorem tailTrace_3545789 : CollatzResearch.WordTrace tailWord_3545789 prefixEnd_3545789 404598679205585070651271 := by
  unfold tailWord_3545789
  simp only [CollatzResearch.WordTrace]
  refine ⟨129325549351219500394216421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86217032900813000262810947 129325549351219500394216421)
  ·
    refine ⟨24248540503353656323915579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 129325549351219500394216421 24248540503353656323915579)
    ·
      refine ⟨36372810755030484485873369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24248540503353656323915579 36372810755030484485873369)
      ·
        refine ⟨27279608066272863364405027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36372810755030484485873369 27279608066272863364405027)
        ·
          refine ⟨40919412099409295046607541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27279608066272863364405027 40919412099409295046607541)
          ·
            refine ⟨3836194884319621410619457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 40919412099409295046607541 3836194884319621410619457)
            ·
              refine ⟨2877146163239716057964593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3836194884319621410619457 2877146163239716057964593)
              ·
                refine ⟨2157859622429787043473445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2877146163239716057964593 2157859622429787043473445)
                ·
                  refine ⟨404598679205585070651271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2157859622429787043473445 404598679205585070651271)
                  ·
                    rfl

theorem cell22_3545789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 5, 2, 2, 4].length) (baseStart_3545789 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3545789 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3545789 prefixEnd_3545789 := by exact prefixLift 3545789
  have htrace : WordTrace (prefixWord ++ tailWord_3545789) baseStart_3545789 baseEnd_3545789 := by
    simpa [prefixWord, tailWord_3545789, baseEnd_3545789] using wordTrace_append hprefix tailTrace_3545789
  have hstable : (prefixWord ++ tailWord_3545789).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3545789).length < 2 ^ (prefixWord ++ tailWord_3545789).sum := by decide
  have hdescent : baseEnd_3545789 < baseStart_3545789 := by decide
  rcases family_descends (prefixWord ++ tailWord_3545789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3545800 : List Nat := [2, 1, 3, 1, 2, 5, 1, 7]
def baseStart_3545800 : Nat := 118140960795 + 3545800 * 2 ^ 59
def prefixEnd_3545800 : Nat := 4983230072969 + 3 ^ 40 * 3545800 * 2
def baseEnd_3545800 : Nat := 134866644793506094436531

theorem tailTrace_3545800 : CollatzResearch.WordTrace tailWord_3545800 prefixEnd_3545800 134866644793506094436531 := by
  unfold tailWord_3545800
  simp only [CollatzResearch.WordTrace]
  refine ⟨64662975277089824636433427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86217300369453099515244569 64662975277089824636433427)
  ·
    refine ⟨96994462915634736954650141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64662975277089824636433427 96994462915634736954650141)
    ·
      refine ⟨36372923593363026357993803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96994462915634736954650141 36372923593363026357993803)
      ·
        refine ⟨54559385390044539536990705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36372923593363026357993803 54559385390044539536990705)
        ·
          refine ⟨40919539042533404652743029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54559385390044539536990705 40919539042533404652743029)
          ·
            refine ⟨3836206785237506686194659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 40919539042533404652743029 3836206785237506686194659)
            ·
              refine ⟨5754310177856260029291989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3836206785237506686194659 5754310177856260029291989)
              ·
                refine ⟨134866644793506094436531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5754310177856260029291989 134866644793506094436531)
                ·
                  rfl

theorem cell22_3545800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 5, 1, 7].length) (baseStart_3545800 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3545800 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3545800 prefixEnd_3545800 := by exact prefixLift 3545800
  have htrace : WordTrace (prefixWord ++ tailWord_3545800) baseStart_3545800 baseEnd_3545800 := by
    simpa [prefixWord, tailWord_3545800, baseEnd_3545800] using wordTrace_append hprefix tailTrace_3545800
  have hstable : (prefixWord ++ tailWord_3545800).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3545800).length < 2 ^ (prefixWord ++ tailWord_3545800).sum := by decide
  have hdescent : baseEnd_3545800 < baseStart_3545800 := by decide
  rcases family_descends (prefixWord ++ tailWord_3545800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3545815 : List Nat := [1, 1, 3, 2, 1, 4, 1, 1, 5, 3]
def baseStart_3545815 : Nat := 118140960795 + 3545815 * 2 ^ 59
def prefixEnd_3545815 : Nat := 4983230072969 + 3 ^ 40 * 3545815 * 2
def baseEnd_3545815 : Nat := 1213804937948099810803733

theorem tailTrace_3545815 : CollatzResearch.WordTrace tailWord_3545815 prefixEnd_3545815 1213804937948099810803733 := by
  unfold tailWord_3545815
  simp only [CollatzResearch.WordTrace]
  refine ⟨129326497649125306834662899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86217665099416871223108599 129326497649125306834662899)
  ·
    refine ⟨193989746473687960251994349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129326497649125306834662899 193989746473687960251994349)
    ·
      refine ⟨72746154927632985094497881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 193989746473687960251994349 72746154927632985094497881)
      ·
        refine ⟨54559616195724738820873411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72746154927632985094497881 54559616195724738820873411)
        ·
          refine ⟨81839424293587108231310117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54559616195724738820873411 81839424293587108231310117)
          ·
            refine ⟨15344892055047582793370647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 81839424293587108231310117 15344892055047582793370647)
            ·
              refine ⟨23017338082571374190055971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15344892055047582793370647 23017338082571374190055971)
              ·
                refine ⟨34526007123857061285083957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23017338082571374190055971 34526007123857061285083957)
                ·
                  refine ⟨3236813167861599495476621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 34526007123857061285083957 3236813167861599495476621)
                  ·
                    refine ⟨1213804937948099810803733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3236813167861599495476621 1213804937948099810803733)
                    ·
                      rfl

theorem cell22_3545815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 1, 5, 3].length) (baseStart_3545815 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3545815 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3545815 prefixEnd_3545815 := by exact prefixLift 3545815
  have htrace : WordTrace (prefixWord ++ tailWord_3545815) baseStart_3545815 baseEnd_3545815 := by
    simpa [prefixWord, tailWord_3545815, baseEnd_3545815] using wordTrace_append hprefix tailTrace_3545815
  have hstable : (prefixWord ++ tailWord_3545815).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3545815).length < 2 ^ (prefixWord ++ tailWord_3545815).sum := by decide
  have hdescent : baseEnd_3545815 < baseStart_3545815 := by decide
  rcases family_descends (prefixWord ++ tailWord_3545815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3545860 : List Nat := [2, 3, 2, 2, 1, 1, 1, 3, 2, 5]
def baseStart_3545860 : Nat := 118140960795 + 3545860 * 2 ^ 59
def prefixEnd_3545860 : Nat := 4983230072969 + 3 ^ 40 * 3545860 * 2
def baseEnd_3545860 : Nat := 1213820342367734693428595

theorem tailTrace_3545860 : CollatzResearch.WordTrace tailWord_3545860 prefixEnd_3545860 1213820342367734693428595 := by
  unfold tailWord_3545860
  simp only [CollatzResearch.WordTrace]
  refine ⟨64664069466981139760025517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86218759289308186346700689 64664069466981139760025517)
  ·
    refine ⟨24249026050117927410009569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64664069466981139760025517 24249026050117927410009569)
    ·
      refine ⟨18186769537588445557507177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24249026050117927410009569 18186769537588445557507177)
      ·
        refine ⟨13640077153191334168130383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18186769537588445557507177 13640077153191334168130383)
        ·
          refine ⟨20460115729787001252195575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13640077153191334168130383 20460115729787001252195575)
          ·
            refine ⟨30690173594680501878293363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20460115729787001252195575 30690173594680501878293363)
            ·
              refine ⟨46035260392020752817440045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30690173594680501878293363 46035260392020752817440045)
              ·
                refine ⟨17263222647007782306540017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46035260392020752817440045 17263222647007782306540017)
                ·
                  refine ⟨12947416985255836729905013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17263222647007782306540017 12947416985255836729905013)
                  ·
                    refine ⟨1213820342367734693428595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12947416985255836729905013 1213820342367734693428595)
                    ·
                      rfl

theorem cell22_3545860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 3, 2, 5].length) (baseStart_3545860 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3545860 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3545860 prefixEnd_3545860 := by exact prefixLift 3545860
  have htrace : WordTrace (prefixWord ++ tailWord_3545860) baseStart_3545860 baseEnd_3545860 := by
    simpa [prefixWord, tailWord_3545860, baseEnd_3545860] using wordTrace_append hprefix tailTrace_3545860
  have hstable : (prefixWord ++ tailWord_3545860).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3545860).length < 2 ^ (prefixWord ++ tailWord_3545860).sum := by decide
  have hdescent : baseEnd_3545860 < baseStart_3545860 := by decide
  rcases family_descends (prefixWord ++ tailWord_3545860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3545907 : List Nat := [1, 1, 1, 2, 6, 3, 1, 1, 6]
def baseStart_3545907 : Nat := 118140960795 + 3545907 * 2 ^ 59
def prefixEnd_3545907 : Nat := 4983230072969 + 3 ^ 40 * 3545907 * 2
def baseEnd_3545907 : Nat := 404612143809414079167817

theorem tailTrace_3545907 : CollatzResearch.WordTrace tailWord_3545907 prefixEnd_3545907 404612143809414079167817 := by
  unfold tailWord_3545907
  simp only [CollatzResearch.WordTrace]
  refine ⟨129329853164792006547011975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86219902109861337698007983 129329853164792006547011975)
  ·
    refine ⟨193994779747188009820517963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129329853164792006547011975 193994779747188009820517963)
    ·
      refine ⟨290992169620782014730776945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193994779747188009820517963 290992169620782014730776945)
      ·
        refine ⟨218244127215586511048082709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 290992169620782014730776945 218244127215586511048082709)
        ·
          refine ⟨10230193463230617705378877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 218244127215586511048082709 10230193463230617705378877)
          ·
            refine ⟨3836322548711481639517079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10230193463230617705378877 3836322548711481639517079)
            ·
              refine ⟨5754483823067222459275619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3836322548711481639517079 5754483823067222459275619)
              ·
                refine ⟨8631725734600833688913429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5754483823067222459275619 8631725734600833688913429)
                ·
                  refine ⟨404612143809414079167817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8631725734600833688913429 404612143809414079167817)
                  ·
                    rfl

theorem cell22_3545907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 3, 1, 1, 6].length) (baseStart_3545907 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3545907 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3545907 prefixEnd_3545907 := by exact prefixLift 3545907
  have htrace : WordTrace (prefixWord ++ tailWord_3545907) baseStart_3545907 baseEnd_3545907 := by
    simpa [prefixWord, tailWord_3545907, baseEnd_3545907] using wordTrace_append hprefix tailTrace_3545907
  have hstable : (prefixWord ++ tailWord_3545907).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3545907).length < 2 ^ (prefixWord ++ tailWord_3545907).sum := by decide
  have hdescent : baseEnd_3545907 < baseStart_3545907 := by decide
  rcases family_descends (prefixWord ++ tailWord_3545907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3545926 : List Nat := [6, 1, 1, 2, 2, 1, 1, 1, 3, 4]
def baseStart_3545926 : Nat := 118140960795 + 3545926 * 2 ^ 59
def prefixEnd_3545926 : Nat := 4983230072969 + 3 ^ 40 * 3545926 * 2
def baseEnd_3545926 : Nat := 1213842935516532521278393

theorem tailTrace_3545926 : CollatzResearch.WordTrace tailWord_3545926 prefixEnd_3545926 1213842935516532521278393 := by
  unfold tailWord_3545926
  simp only [CollatzResearch.WordTrace]
  refine ⟨4041579567241349149748551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 86220364101148781861302421 4041579567241349149748551)
  ·
    refine ⟨6062369350862023724622827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4041579567241349149748551 6062369350862023724622827)
    ·
      refine ⟨9093554026293035586934241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6062369350862023724622827 9093554026293035586934241)
      ·
        refine ⟨6820165519719776690200681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9093554026293035586934241 6820165519719776690200681)
        ·
          refine ⟨5115124139789832517650511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6820165519719776690200681 5115124139789832517650511)
          ·
            refine ⟨7672686209684748776475767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5115124139789832517650511 7672686209684748776475767)
            ·
              refine ⟨11509029314527123164713651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7672686209684748776475767 11509029314527123164713651)
              ·
                refine ⟨17263543971790684747070477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11509029314527123164713651 17263543971790684747070477)
                ·
                  refine ⟨6473828989421506780151429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17263543971790684747070477 6473828989421506780151429)
                  ·
                    refine ⟨1213842935516532521278393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6473828989421506780151429 1213842935516532521278393)
                    ·
                      rfl

theorem cell22_3545926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 1, 1, 3, 4].length) (baseStart_3545926 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3545926 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3545926 prefixEnd_3545926 := by exact prefixLift 3545926
  have htrace : WordTrace (prefixWord ++ tailWord_3545926) baseStart_3545926 baseEnd_3545926 := by
    simpa [prefixWord, tailWord_3545926, baseEnd_3545926] using wordTrace_append hprefix tailTrace_3545926
  have hstable : (prefixWord ++ tailWord_3545926).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3545926).length < 2 ^ (prefixWord ++ tailWord_3545926).sum := by decide
  have hdescent : baseEnd_3545926 < baseStart_3545926 := by decide
  rcases family_descends (prefixWord ++ tailWord_3545926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3546052 : List Nat := [2, 3, 3, 3, 2, 1, 1, 3, 1, 3]
def baseStart_3546052 : Nat := 118140960795 + 3546052 * 2 ^ 59
def prefixEnd_3546052 : Nat := 4983230072969 + 3 ^ 40 * 3546052 * 2
def baseEnd_3546052 : Nat := 1213886067891510192628007

theorem tailTrace_3546052 : CollatzResearch.WordTrace tailWord_3546052 prefixEnd_3546052 1213886067891510192628007 := by
  unfold tailWord_3546052
  simp only [CollatzResearch.WordTrace]
  refine ⟨64667570874633348155520205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86223427832844464207360273 64667570874633348155520205)
  ·
    refine ⟨24250339077987505558320077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64667570874633348155520205 24250339077987505558320077)
    ·
      refine ⟨9093877154245314584370029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24250339077987505558320077 9093877154245314584370029)
      ·
        refine ⟨3410203932841992969138761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9093877154245314584370029 3410203932841992969138761)
        ·
          refine ⟨2557652949631494726854071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3410203932841992969138761 2557652949631494726854071)
          ·
            refine ⟨3836479424447242090281107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2557652949631494726854071 3836479424447242090281107)
            ·
              refine ⟨5754719136670863135421661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3836479424447242090281107 5754719136670863135421661)
              ·
                refine ⟨2158019676251573675783123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5754719136670863135421661 2158019676251573675783123)
                ·
                  refine ⟨3237029514377360513674685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2158019676251573675783123 3237029514377360513674685)
                  ·
                    refine ⟨1213886067891510192628007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3237029514377360513674685 1213886067891510192628007)
                    ·
                      rfl

theorem cell22_3546052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 2, 1, 1, 3, 1, 3].length) (baseStart_3546052 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3546052 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3546052 prefixEnd_3546052 := by exact prefixLift 3546052
  have htrace : WordTrace (prefixWord ++ tailWord_3546052) baseStart_3546052 baseEnd_3546052 := by
    simpa [prefixWord, tailWord_3546052, baseEnd_3546052] using wordTrace_append hprefix tailTrace_3546052
  have hstable : (prefixWord ++ tailWord_3546052).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3546052).length < 2 ^ (prefixWord ++ tailWord_3546052).sum := by decide
  have hdescent : baseEnd_3546052 < baseStart_3546052 := by decide
  rcases family_descends (prefixWord ++ tailWord_3546052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3546059 : List Nat := [1, 1, 1, 1, 3, 5, 3, 3, 4]
def baseStart_3546059 : Nat := 118140960795 + 3546059 * 2 ^ 59
def prefixEnd_3546059 : Nat := 4983230072969 + 3 ^ 40 * 3546059 * 2
def baseEnd_3546059 : Nat := 404629488044854835900995

theorem tailTrace_3546059 : CollatzResearch.WordTrace tailWord_3546059 prefixEnd_3546059 404629488044854835900995 := by
  unfold tailWord_3546059
  simp only [CollatzResearch.WordTrace]
  refine ⟨129335397060241336506545231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86223598040160891004363487 129335397060241336506545231)
  ·
    refine ⟨194003095590362004759817847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129335397060241336506545231 194003095590362004759817847)
    ·
      refine ⟨291004643385543007139726771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194003095590362004759817847 291004643385543007139726771)
      ·
        refine ⟨436506965078314510709590157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 291004643385543007139726771 436506965078314510709590157)
        ·
          refine ⟨163690111904367941516096309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 436506965078314510709590157 163690111904367941516096309)
          ·
            refine ⟨15345947991034494517134029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 163690111904367941516096309 15345947991034494517134029)
            ·
              refine ⟨5754730496637935443925261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15345947991034494517134029 5754730496637935443925261)
              ·
                refine ⟨2158023936239225791471973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5754730496637935443925261 2158023936239225791471973)
                ·
                  refine ⟨404629488044854835900995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2158023936239225791471973 404629488044854835900995)
                  ·
                    rfl

theorem cell22_3546059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 3, 3, 4].length) (baseStart_3546059 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3546059 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3546059 prefixEnd_3546059 := by exact prefixLift 3546059
  have htrace : WordTrace (prefixWord ++ tailWord_3546059) baseStart_3546059 baseEnd_3546059 := by
    simpa [prefixWord, tailWord_3546059, baseEnd_3546059] using wordTrace_append hprefix tailTrace_3546059
  have hstable : (prefixWord ++ tailWord_3546059).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3546059).length < 2 ^ (prefixWord ++ tailWord_3546059).sum := by decide
  have hdescent : baseEnd_3546059 < baseStart_3546059 := by decide
  rcases family_descends (prefixWord ++ tailWord_3546059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3546072 : List Nat := [2, 1, 2, 2, 2, 3, 1, 1, 4, 4]
def baseStart_3546072 : Nat := 118140960795 + 3546072 * 2 ^ 59
def prefixEnd_3546072 : Nat := 4983230072969 + 3 ^ 40 * 3546072 * 2
def baseEnd_3546072 : Nat := 1213892914300236807127945

theorem tailTrace_3546072 : CollatzResearch.WordTrace tailWord_3546072 prefixEnd_3546072 1213892914300236807127945 := by
  unfold tailWord_3546072
  simp only [CollatzResearch.WordTrace]
  refine ⟨64667935604597119863384235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86223914139462826484512313 64667935604597119863384235)
  ·
    refine ⟨97001903406895679795076353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64667935604597119863384235 97001903406895679795076353)
    ·
      refine ⟨72751427555171759846307265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97001903406895679795076353 72751427555171759846307265)
      ·
        refine ⟨54563570666378819884730449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72751427555171759846307265 54563570666378819884730449)
        ·
          refine ⟨40922677999784114913547837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54563570666378819884730449 40922677999784114913547837)
          ·
            refine ⟨15346004249919043092580439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40922677999784114913547837 15346004249919043092580439)
            ·
              refine ⟨23019006374878564638870659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15346004249919043092580439 23019006374878564638870659)
              ·
                refine ⟨34528509562317846958305989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23019006374878564638870659 34528509562317846958305989)
                ·
                  refine ⟨6474095542934596304682373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34528509562317846958305989 6474095542934596304682373)
                  ·
                    refine ⟨1213892914300236807127945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6474095542934596304682373 1213892914300236807127945)
                    ·
                      rfl

theorem cell22_3546072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 1, 4, 4].length) (baseStart_3546072 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3546072 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3546072 prefixEnd_3546072 := by exact prefixLift 3546072
  have htrace : WordTrace (prefixWord ++ tailWord_3546072) baseStart_3546072 baseEnd_3546072 := by
    simpa [prefixWord, tailWord_3546072, baseEnd_3546072] using wordTrace_append hprefix tailTrace_3546072
  have hstable : (prefixWord ++ tailWord_3546072).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3546072).length < 2 ^ (prefixWord ++ tailWord_3546072).sum := by decide
  have hdescent : baseEnd_3546072 < baseStart_3546072 := by decide
  rcases family_descends (prefixWord ++ tailWord_3546072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3546074 : List Nat := [3, 1, 1, 2, 4, 1, 2, 1, 4, 3]
def baseStart_3546074 : Nat := 118140960795 + 3546074 * 2 ^ 59
def prefixEnd_3546074 : Nat := 4983230072969 + 3 ^ 40 * 3546074 * 2
def baseEnd_3546074 : Nat := 1213893598941109468577939

theorem tailTrace_3546074 : CollatzResearch.WordTrace tailWord_3546074 prefixEnd_3546074 1213893598941109468577939 := by
  unfold tailWord_3546074
  simp only [CollatzResearch.WordTrace]
  refine ⟨32333986038796748517085319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86223962770124662712227517 32333986038796748517085319)
  ·
    refine ⟨48500979058195122775627979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32333986038796748517085319 48500979058195122775627979)
    ·
      refine ⟨72751468587292684163441969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48500979058195122775627979 72751468587292684163441969)
      ·
        refine ⟨54563601440469513122581477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72751468587292684163441969 54563601440469513122581477)
        ·
          refine ⟨10230675270088033710484027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 54563601440469513122581477 10230675270088033710484027)
          ·
            refine ⟨15346012905132050565726041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10230675270088033710484027 15346012905132050565726041)
            ·
              refine ⟨11509509678849037924294531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15346012905132050565726041 11509509678849037924294531)
              ·
                refine ⟨17264264518273556886441797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11509509678849037924294531 17264264518273556886441797)
                ·
                  refine ⟨3237049597176291916207837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17264264518273556886441797 3237049597176291916207837)
                  ·
                    refine ⟨1213893598941109468577939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3237049597176291916207837 1213893598941109468577939)
                    ·
                      rfl

theorem cell22_3546074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 2, 1, 4, 3].length) (baseStart_3546074 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3546074 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3546074 prefixEnd_3546074 := by exact prefixLift 3546074
  have htrace : WordTrace (prefixWord ++ tailWord_3546074) baseStart_3546074 baseEnd_3546074 := by
    simpa [prefixWord, tailWord_3546074, baseEnd_3546074] using wordTrace_append hprefix tailTrace_3546074
  have hstable : (prefixWord ++ tailWord_3546074).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3546074).length < 2 ^ (prefixWord ++ tailWord_3546074).sum := by decide
  have hdescent : baseEnd_3546074 < baseStart_3546074 := by decide
  rcases family_descends (prefixWord ++ tailWord_3546074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3546087 : List Nat := [1, 1, 5, 2, 2, 1, 1, 9]
def baseStart_3546087 : Nat := 118140960795 + 3546087 * 2 ^ 59
def prefixEnd_3546087 : Nat := 4983230072969 + 3 ^ 40 * 3546087 * 2
def baseEnd_3546087 : Nat := 134877561011864640889211

theorem tailTrace_3546087 : CollatzResearch.WordTrace tailWord_3546087 prefixEnd_3546087 134877561011864640889211 := by
  unfold tailWord_3546087
  simp only [CollatzResearch.WordTrace]
  refine ⟨129336418304139897288564515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86224278869426598192376343 129336418304139897288564515)
  ·
    refine ⟨194004627456209845932846773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129336418304139897288564515 194004627456209845932846773)
    ·
      refine ⟨18187933824019673056204385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 194004627456209845932846773 18187933824019673056204385)
      ·
        refine ⟨13640950368014754792153289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18187933824019673056204385 13640950368014754792153289)
        ·
          refine ⟨10230712776011066094114967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13640950368014754792153289 10230712776011066094114967)
          ·
            refine ⟨15346069164016599141172451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10230712776011066094114967 15346069164016599141172451)
            ·
              refine ⟨23019103746024898711758677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15346069164016599141172451 23019103746024898711758677)
              ·
                refine ⟨134877561011864640889211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 23019103746024898711758677 134877561011864640889211)
                ·
                  rfl

theorem cell22_3546087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 9].length) (baseStart_3546087 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3546087 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3546087 prefixEnd_3546087 := by exact prefixLift 3546087
  have htrace : WordTrace (prefixWord ++ tailWord_3546087) baseStart_3546087 baseEnd_3546087 := by
    simpa [prefixWord, tailWord_3546087, baseEnd_3546087] using wordTrace_append hprefix tailTrace_3546087
  have hstable : (prefixWord ++ tailWord_3546087).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3546087).length < 2 ^ (prefixWord ++ tailWord_3546087).sum := by decide
  have hdescent : baseEnd_3546087 < baseStart_3546087 := by decide
  rcases family_descends (prefixWord ++ tailWord_3546087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3546147 : List Nat := [1, 1, 1, 4, 3, 2, 1, 1, 1, 7]
def baseStart_3546147 : Nat := 118140960795 + 3546147 * 2 ^ 59
def prefixEnd_3546147 : Nat := 4983230072969 + 3 ^ 40 * 3546147 * 2
def baseEnd_3546147 : Nat := 1213918588332961611502715

theorem tailTrace_3546147 : CollatzResearch.WordTrace tailWord_3546147 prefixEnd_3546147 1213918588332961611502715 := by
  unfold tailWord_3546147
  simp only [CollatzResearch.WordTrace]
  refine ⟨129338606683922527535748695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86225737789281685023832463 129338606683922527535748695)
  ·
    refine ⟨194007910025883791303623043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129338606683922527535748695 194007910025883791303623043)
    ·
      refine ⟨291011865038825686955434565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194007910025883791303623043 291011865038825686955434565)
      ·
        refine ⟨54564724694779816304143981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 291011865038825686955434565 54564724694779816304143981)
        ·
          refine ⟨20461771760542431114053993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54564724694779816304143981 20461771760542431114053993)
          ·
            refine ⟨15346328820406823335540495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20461771760542431114053993 15346328820406823335540495)
            ·
              refine ⟨23019493230610235003310743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15346328820406823335540495 23019493230610235003310743)
              ·
                refine ⟨34529239845915352504966115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23019493230610235003310743 34529239845915352504966115)
                ·
                  refine ⟨51793859768873028757449173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34529239845915352504966115 51793859768873028757449173)
                  ·
                    refine ⟨1213918588332961611502715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 51793859768873028757449173 1213918588332961611502715)
                    ·
                      rfl

theorem cell22_3546147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 1, 1, 7].length) (baseStart_3546147 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3546147 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3546147 prefixEnd_3546147 := by exact prefixLift 3546147
  have htrace : WordTrace (prefixWord ++ tailWord_3546147) baseStart_3546147 baseEnd_3546147 := by
    simpa [prefixWord, tailWord_3546147, baseEnd_3546147] using wordTrace_append hprefix tailTrace_3546147
  have hstable : (prefixWord ++ tailWord_3546147).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3546147).length < 2 ^ (prefixWord ++ tailWord_3546147).sum := by decide
  have hdescent : baseEnd_3546147 < baseStart_3546147 := by decide
  rcases family_descends (prefixWord ++ tailWord_3546147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3546179 : List Nat := [1, 1, 1, 3, 1, 2, 5, 3, 1, 4]
def baseStart_3546179 : Nat := 118140960795 + 3546179 * 2 ^ 59
def prefixEnd_3546179 : Nat := 4983230072969 + 3 ^ 40 * 3546179 * 2
def baseEnd_3546179 : Nat := 1213929542586924194702617

theorem tailTrace_3546179 : CollatzResearch.WordTrace tailWord_3546179 prefixEnd_3546179 1213929542586924194702617 := by
  unfold tailWord_3546179
  simp only [CollatzResearch.WordTrace]
  refine ⟨129339773819806597000913591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86226515879871064667275727 129339773819806597000913591)
  ·
    refine ⟨194009660729709895501370387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129339773819806597000913591 194009660729709895501370387)
    ·
      refine ⟨291014491094564843252055581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194009660729709895501370387 291014491094564843252055581)
      ·
        refine ⟨109130434160461816219520843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 291014491094564843252055581 109130434160461816219520843)
        ·
          refine ⟨163695651240692724329281265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109130434160461816219520843 163695651240692724329281265)
          ·
            refine ⟨122771738430519543246960949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 163695651240692724329281265 122771738430519543246960949)
            ·
              refine ⟨11509850477861207179402589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 122771738430519543246960949 11509850477861207179402589)
              ·
                refine ⟨4316193929197952692275971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11509850477861207179402589 4316193929197952692275971)
                ·
                  refine ⟨6474290893796929038413957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4316193929197952692275971 6474290893796929038413957)
                  ·
                    refine ⟨1213929542586924194702617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6474290893796929038413957 1213929542586924194702617)
                    ·
                      rfl

theorem cell22_3546179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 5, 3, 1, 4].length) (baseStart_3546179 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3546179 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3546179 prefixEnd_3546179 := by exact prefixLift 3546179
  have htrace : WordTrace (prefixWord ++ tailWord_3546179) baseStart_3546179 baseEnd_3546179 := by
    simpa [prefixWord, tailWord_3546179, baseEnd_3546179] using wordTrace_append hprefix tailTrace_3546179
  have hstable : (prefixWord ++ tailWord_3546179).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3546179).length < 2 ^ (prefixWord ++ tailWord_3546179).sum := by decide
  have hdescent : baseEnd_3546179 < baseStart_3546179 := by decide
  rcases family_descends (prefixWord ++ tailWord_3546179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3546192 : List Nat := [2, 1, 1, 1, 1, 3, 1, 4, 3, 5]
def baseStart_3546192 : Nat := 118140960795 + 3546192 * 2 ^ 59
def prefixEnd_3546192 : Nat := 4983230072969 + 3 ^ 40 * 3546192 * 2
def baseEnd_3546192 : Nat := 1213933992752596494127577

theorem tailTrace_3546192 : CollatzResearch.WordTrace tailWord_3546192 prefixEnd_3546192 1213933992752596494127577 := by
  unfold tailWord_3546192
  simp only [CollatzResearch.WordTrace]
  refine ⟨64670123984379750110568415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86226831979173000147424553 64670123984379750110568415)
  ·
    refine ⟨97005185976569625165852623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64670123984379750110568415 97005185976569625165852623)
    ·
      refine ⟨145507778964854437748778935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97005185976569625165852623 145507778964854437748778935)
      ·
        refine ⟨218261668447281656623168403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145507778964854437748778935 218261668447281656623168403)
        ·
          refine ⟨327392502670922484934752605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 218261668447281656623168403 327392502670922484934752605)
          ·
            refine ⟨122772188501595931850532227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 327392502670922484934752605 122772188501595931850532227)
            ·
              refine ⟨184158282752393897775798341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122772188501595931850532227 184158282752393897775798341)
              ·
                refine ⟨34529678016073855832962189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 184158282752393897775798341 34529678016073855832962189)
                ·
                  refine ⟨12948629256027695937360821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34529678016073855832962189 12948629256027695937360821)
                  ·
                    refine ⟨1213933992752596494127577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12948629256027695937360821 1213933992752596494127577)
                    ·
                      rfl

theorem cell22_3546192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 4, 3, 5].length) (baseStart_3546192 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3546192 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3546192 prefixEnd_3546192 := by exact prefixLift 3546192
  have htrace : WordTrace (prefixWord ++ tailWord_3546192) baseStart_3546192 baseEnd_3546192 := by
    simpa [prefixWord, tailWord_3546192, baseEnd_3546192] using wordTrace_append hprefix tailTrace_3546192
  have hstable : (prefixWord ++ tailWord_3546192).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3546192).length < 2 ^ (prefixWord ++ tailWord_3546192).sum := by decide
  have hdescent : baseEnd_3546192 < baseStart_3546192 := by decide
  rcases family_descends (prefixWord ++ tailWord_3546192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3546194 : List Nat := [3, 2, 2, 1, 3, 1, 1, 3, 6]
def baseStart_3546194 : Nat := 118140960795 + 3546194 * 2 ^ 59
def prefixEnd_3546194 : Nat := 4983230072969 + 3 ^ 40 * 3546194 * 2
def baseEnd_3546194 : Nat := 404644892464489718525857

theorem tailTrace_3546194 : CollatzResearch.WordTrace tailWord_3546194 prefixEnd_3546194 404644892464489718525857 := by
  unfold tailWord_3546194
  simp only [CollatzResearch.WordTrace]
  refine ⟨32335080228688063640677409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86226880609834836375139757 32335080228688063640677409)
  ·
    refine ⟨24251310171516047730508057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32335080228688063640677409 24251310171516047730508057)
    ·
      refine ⟨18188482628637035797881043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24251310171516047730508057 18188482628637035797881043)
      ·
        refine ⟨27282723942955553696821565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18188482628637035797881043 27282723942955553696821565)
        ·
          refine ⟨10231021478608332636308087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27282723942955553696821565 10231021478608332636308087)
          ·
            refine ⟨15346532217912498954462131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10231021478608332636308087 15346532217912498954462131)
            ·
              refine ⟨23019798326868748431693197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15346532217912498954462131 23019798326868748431693197)
              ·
                refine ⟨8632424372575780661884949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23019798326868748431693197 8632424372575780661884949)
                ·
                  refine ⟨404644892464489718525857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8632424372575780661884949 404644892464489718525857)
                  ·
                    rfl

theorem cell22_3546194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 3, 6].length) (baseStart_3546194 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3546194 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3546194 prefixEnd_3546194 := by exact prefixLift 3546194
  have htrace : WordTrace (prefixWord ++ tailWord_3546194) baseStart_3546194 baseEnd_3546194 := by
    simpa [prefixWord, tailWord_3546194, baseEnd_3546194] using wordTrace_append hprefix tailTrace_3546194
  have hstable : (prefixWord ++ tailWord_3546194).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3546194).length < 2 ^ (prefixWord ++ tailWord_3546194).sum := by decide
  have hdescent : baseEnd_3546194 < baseStart_3546194 := by decide
  rcases family_descends (prefixWord ++ tailWord_3546194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3546207 : List Nat := [1, 1, 2, 3, 1, 1, 3, 1, 3, 6]
def baseStart_3546207 : Nat := 118140960795 + 3546207 * 2 ^ 59
def prefixEnd_3546207 : Nat := 4983230072969 + 3 ^ 40 * 3546207 * 2
def baseEnd_3546207 : Nat := 1213939127559141455002531

theorem tailTrace_3546207 : CollatzResearch.WordTrace tailWord_3546207 prefixEnd_3546207 1213939127559141455002531 := by
  unfold tailWord_3546207
  simp only [CollatzResearch.WordTrace]
  refine ⟨129340795063705157782932875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86227196709136771855288583 129340795063705157782932875)
  ·
    refine ⟨194011192595557736674399313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129340795063705157782932875 194011192595557736674399313)
    ·
      refine ⟨145508394446668302505799485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 194011192595557736674399313 145508394446668302505799485)
      ·
        refine ⟨54565647917500613439674807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 145508394446668302505799485 54565647917500613439674807)
        ·
          refine ⟨81848471876250920159512211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54565647917500613439674807 81848471876250920159512211)
          ·
            refine ⟨122772707814376380239268317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81848471876250920159512211 122772707814376380239268317)
            ·
              refine ⟨46039765430391142589725619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 122772707814376380239268317 46039765430391142589725619)
              ·
                refine ⟨69059648145586713884588429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46039765430391142589725619 69059648145586713884588429)
                ·
                  refine ⟨25897368054595017706720661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 69059648145586713884588429 25897368054595017706720661)
                  ·
                    refine ⟨1213939127559141455002531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25897368054595017706720661 1213939127559141455002531)
                    ·
                      rfl

theorem cell22_3546207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 1, 3, 6].length) (baseStart_3546207 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3546207 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3546207 prefixEnd_3546207 := by exact prefixLift 3546207
  have htrace : WordTrace (prefixWord ++ tailWord_3546207) baseStart_3546207 baseEnd_3546207 := by
    simpa [prefixWord, tailWord_3546207, baseEnd_3546207] using wordTrace_append hprefix tailTrace_3546207
  have hstable : (prefixWord ++ tailWord_3546207).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3546207).length < 2 ^ (prefixWord ++ tailWord_3546207).sum := by decide
  have hdescent : baseEnd_3546207 < baseStart_3546207 := by decide
  rcases family_descends (prefixWord ++ tailWord_3546207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3546209 : List Nat := [1, 2, 3, 1, 1, 2, 5, 1, 1, 5]
def baseStart_3546209 : Nat := 118140960795 + 3546209 * 2 ^ 59
def prefixEnd_3546209 : Nat := 4983230072969 + 3 ^ 40 * 3546209 * 2
def baseEnd_3546209 : Nat := 1213939812200014116452525

theorem tailTrace_3546209 : CollatzResearch.WordTrace tailWord_3546209 prefixEnd_3546209 1213939812200014116452525 := by
  unfold tailWord_3546209
  simp only [CollatzResearch.WordTrace]
  refine ⟨129340868009697912124505681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86227245339798608083003787 129340868009697912124505681)
  ·
    refine ⟨97005651007273434093379261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129340868009697912124505681 97005651007273434093379261)
    ·
      refine ⟨36377119127727537785017223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97005651007273434093379261 36377119127727537785017223)
      ·
        refine ⟨54565678691591306677525835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36377119127727537785017223 54565678691591306677525835)
        ·
          refine ⟨81848518037386960016288753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54565678691591306677525835 81848518037386960016288753)
          ·
            refine ⟨61386388528040220012216565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81848518037386960016288753 61386388528040220012216565)
            ·
              refine ⟨5754973924503770626145303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 61386388528040220012216565 5754973924503770626145303)
              ·
                refine ⟨8632460886755655939217955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5754973924503770626145303 8632460886755655939217955)
                ·
                  refine ⟨12948691330133483908826933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8632460886755655939217955 12948691330133483908826933)
                  ·
                    refine ⟨1213939812200014116452525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12948691330133483908826933 1213939812200014116452525)
                    ·
                      rfl

theorem cell22_3546209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 5, 1, 1, 5].length) (baseStart_3546209 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3546209 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3546209 prefixEnd_3546209 := by exact prefixLift 3546209
  have htrace : WordTrace (prefixWord ++ tailWord_3546209) baseStart_3546209 baseEnd_3546209 := by
    simpa [prefixWord, tailWord_3546209, baseEnd_3546209] using wordTrace_append hprefix tailTrace_3546209
  have hstable : (prefixWord ++ tailWord_3546209).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3546209).length < 2 ^ (prefixWord ++ tailWord_3546209).sum := by decide
  have hdescent : baseEnd_3546209 < baseStart_3546209 := by decide
  rcases family_descends (prefixWord ++ tailWord_3546209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3546224 : List Nat := [2, 1, 1, 1, 5, 1, 2, 3, 2, 4]
def baseStart_3546224 : Nat := 118140960795 + 3546224 * 2 ^ 59
def prefixEnd_3546224 : Nat := 4983230072969 + 3 ^ 40 * 3546224 * 2
def baseEnd_3546224 : Nat := 1213944947006559077327479

theorem tailTrace_3546224 : CollatzResearch.WordTrace tailWord_3546224 prefixEnd_3546224 1213944947006559077327479 := by
  unfold tailWord_3546224
  simp only [CollatzResearch.WordTrace]
  refine ⟨64670707552321784843150863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86227610069762379790867817 64670707552321784843150863)
  ·
    refine ⟨97006061328482677264726295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64670707552321784843150863 97006061328482677264726295)
    ·
      refine ⟨145509091992724015897089443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97006061328482677264726295 145509091992724015897089443)
      ·
        refine ⟨218263637989086023845634165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145509091992724015897089443 218263637989086023845634165)
        ·
          refine ⟨20462216061476814735528203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 218263637989086023845634165 20462216061476814735528203)
          ·
            refine ⟨30693324092215222103292305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20462216061476814735528203 30693324092215222103292305)
            ·
              refine ⟨23019993069161416577469229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30693324092215222103292305 23019993069161416577469229)
              ·
                refine ⟨8632497400935531216550961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23019993069161416577469229 8632497400935531216550961)
                ·
                  refine ⟨6474373050701648412413221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8632497400935531216550961 6474373050701648412413221)
                  ·
                    refine ⟨1213944947006559077327479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6474373050701648412413221 1213944947006559077327479)
                    ·
                      rfl

theorem cell22_3546224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 3, 2, 4].length) (baseStart_3546224 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3546224 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3546224 prefixEnd_3546224 := by exact prefixLift 3546224
  have htrace : WordTrace (prefixWord ++ tailWord_3546224) baseStart_3546224 baseEnd_3546224 := by
    simpa [prefixWord, tailWord_3546224, baseEnd_3546224] using wordTrace_append hprefix tailTrace_3546224
  have hstable : (prefixWord ++ tailWord_3546224).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3546224).length < 2 ^ (prefixWord ++ tailWord_3546224).sum := by decide
  have hdescent : baseEnd_3546224 < baseStart_3546224 := by decide
  rcases family_descends (prefixWord ++ tailWord_3546224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3546241 : List Nat := [1, 2, 4, 2, 2, 2, 1, 2, 2, 4]
def baseStart_3546241 : Nat := 118140960795 + 3546241 * 2 ^ 59
def prefixEnd_3546241 : Nat := 4983230072969 + 3 ^ 40 * 3546241 * 2
def baseEnd_3546241 : Nat := 1213950766453976699652427

theorem tailTrace_3546241 : CollatzResearch.WordTrace tailWord_3546241 prefixEnd_3546241 1213950766453976699652427 := by
  unfold tailWord_3546241
  simp only [CollatzResearch.WordTrace]
  refine ⟨129342035145581981589670577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86228023430387987726447051 129342035145581981589670577)
  ·
    refine ⟨97006526359186486192252933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129342035145581981589670577 97006526359186486192252933)
    ·
      refine ⟨18188723692347466161047425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 97006526359186486192252933 18188723692347466161047425)
      ·
        refine ⟨13641542769260599620785569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18188723692347466161047425 13641542769260599620785569)
        ·
          refine ⟨10231157076945449715589177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13641542769260599620785569 10231157076945449715589177)
          ·
            refine ⟨7673367807709087286691883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10231157076945449715589177 7673367807709087286691883)
            ·
              refine ⟨11510051711563630930037825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7673367807709087286691883 11510051711563630930037825)
              ·
                refine ⟨8632538783672723197528369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11510051711563630930037825 8632538783672723197528369)
                ·
                  refine ⟨6474404087754542398146277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8632538783672723197528369 6474404087754542398146277)
                  ·
                    refine ⟨1213950766453976699652427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6474404087754542398146277 1213950766453976699652427)
                    ·
                      rfl

theorem cell22_3546241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 1, 2, 2, 4].length) (baseStart_3546241 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3546241 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3546241 prefixEnd_3546241 := by exact prefixLift 3546241
  have htrace : WordTrace (prefixWord ++ tailWord_3546241) baseStart_3546241 baseEnd_3546241 := by
    simpa [prefixWord, tailWord_3546241, baseEnd_3546241] using wordTrace_append hprefix tailTrace_3546241
  have hstable : (prefixWord ++ tailWord_3546241).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3546241).length < 2 ^ (prefixWord ++ tailWord_3546241).sum := by decide
  have hdescent : baseEnd_3546241 < baseStart_3546241 := by decide
  rcases family_descends (prefixWord ++ tailWord_3546241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3546267 : List Nat := [1, 1, 1, 1, 1, 1, 2, 3, 11]
def baseStart_3546267 : Nat := 118140960795 + 3546267 * 2 ^ 59
def prefixEnd_3546267 : Nat := 4983230072969 + 3 ^ 40 * 3546267 * 2
def baseEnd_3546267 : Nat := 404653222261773766167449

theorem tailTrace_3546267 : CollatzResearch.WordTrace tailWord_3546267 prefixEnd_3546267 404653222261773766167449 := by
  unfold tailWord_3546267
  simp only [CollatzResearch.WordTrace]
  refine ⟨129342983443487788030117055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86228655628991858686744703 129342983443487788030117055)
  ·
    refine ⟨194014475165231682045175583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129342983443487788030117055 194014475165231682045175583)
    ·
      refine ⟨291021712747847523067763375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194014475165231682045175583 291021712747847523067763375)
      ·
        refine ⟨436532569121771284601645063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 291021712747847523067763375 436532569121771284601645063)
        ·
          refine ⟨654798853682656926902467595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 436532569121771284601645063 654798853682656926902467595)
          ·
            refine ⟨982198280523985390353701393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 654798853682656926902467595 982198280523985390353701393)
            ·
              refine ⟨736648710392989042765276045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 982198280523985390353701393 736648710392989042765276045)
              ·
                refine ⟨276243266397370891036978517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 736648710392989042765276045 276243266397370891036978517)
                ·
                  refine ⟨404653222261773766167449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 276243266397370891036978517 404653222261773766167449)
                  ·
                    rfl

theorem cell22_3546267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 11].length) (baseStart_3546267 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3546267 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3546267 prefixEnd_3546267 := by exact prefixLift 3546267
  have htrace : WordTrace (prefixWord ++ tailWord_3546267) baseStart_3546267 baseEnd_3546267 := by
    simpa [prefixWord, tailWord_3546267, baseEnd_3546267] using wordTrace_append hprefix tailTrace_3546267
  have hstable : (prefixWord ++ tailWord_3546267).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3546267).length < 2 ^ (prefixWord ++ tailWord_3546267).sum := by decide
  have hdescent : baseEnd_3546267 < baseStart_3546267 := by decide
  rcases family_descends (prefixWord ++ tailWord_3546267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3546348 : List Nat := [2, 2, 1, 1, 2, 4, 4, 1, 1, 4]
def baseStart_3546348 : Nat := 118140960795 + 3546348 * 2 ^ 59
def prefixEnd_3546348 : Nat := 4983230072969 + 3 ^ 40 * 3546348 * 2
def baseEnd_3546348 : Nat := 1213987394740664087227099

theorem tailTrace_3546348 : CollatzResearch.WordTrace tailWord_3546348 prefixEnd_3546348 1213987394740664087227099 := by
  unfold tailWord_3546348
  simp only [CollatzResearch.WordTrace]
  refine ⟨64672968878097169431907849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86230625170796225909210465 64672968878097169431907849)
  ·
    refine ⟨48504726658572877073930887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64672968878097169431907849 48504726658572877073930887)
    ·
      refine ⟨72757089987859315610896331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48504726658572877073930887 72757089987859315610896331)
      ·
        refine ⟨109135634981788973416344497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72757089987859315610896331 109135634981788973416344497)
        ·
          refine ⟨81851726236341730062258373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109135634981788973416344497 81851726236341730062258373)
          ·
            refine ⟨15347198669314074386673445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 81851726236341730062258373 15347198669314074386673445)
            ·
              refine ⟨2877599750496388947501271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15347198669314074386673445 2877599750496388947501271)
              ·
                refine ⟨4316399625744583421251907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2877599750496388947501271 4316399625744583421251907)
                ·
                  refine ⟨6474599438616875131877861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4316399625744583421251907 6474599438616875131877861)
                  ·
                    refine ⟨1213987394740664087227099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6474599438616875131877861 1213987394740664087227099)
                    ·
                      rfl

theorem cell22_3546348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 4].length) (baseStart_3546348 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3546348 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3546348 prefixEnd_3546348 := by exact prefixLift 3546348
  have htrace : WordTrace (prefixWord ++ tailWord_3546348) baseStart_3546348 baseEnd_3546348 := by
    simpa [prefixWord, tailWord_3546348, baseEnd_3546348] using wordTrace_append hprefix tailTrace_3546348
  have hstable : (prefixWord ++ tailWord_3546348).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3546348).length < 2 ^ (prefixWord ++ tailWord_3546348).sum := by decide
  have hdescent : baseEnd_3546348 < baseStart_3546348 := by decide
  rcases family_descends (prefixWord ++ tailWord_3546348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3546361 : List Nat := [1, 2, 1, 3, 1, 1, 5, 1, 4, 3]
def baseStart_3546361 : Nat := 118140960795 + 3546361 * 2 ^ 59
def prefixEnd_3546361 : Nat := 4983230072969 + 3 ^ 40 * 3546361 * 2
def baseEnd_3546361 : Nat := 1213991844906336386652059

theorem tailTrace_3546361 : CollatzResearch.WordTrace tailWord_3546361 prefixEnd_3546361 1213991844906336386652059 := by
  unfold tailWord_3546361
  simp only [CollatzResearch.WordTrace]
  refine ⟨129346411905147242084038937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86230941270098161389359291 129346411905147242084038937)
  ·
    refine ⟨97009808928860431563029203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129346411905147242084038937 97009808928860431563029203)
    ·
      refine ⟨145514713393290647344543805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97009808928860431563029203 145514713393290647344543805)
      ·
        refine ⟨54568017522483992754203927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 145514713393290647344543805 54568017522483992754203927)
        ·
          refine ⟨81852026283725989131305891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54568017522483992754203927 81852026283725989131305891)
          ·
            refine ⟨122778039425588983696958837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81852026283725989131305891 122778039425588983696958837)
            ·
              refine ⟨11510441196148967221589891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 122778039425588983696958837 11510441196148967221589891)
              ·
                refine ⟨17265661794223450832384837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11510441196148967221589891 17265661794223450832384837)
                ·
                  refine ⟨3237311586416897031072157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17265661794223450832384837 3237311586416897031072157)
                  ·
                    refine ⟨1213991844906336386652059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3237311586416897031072157 1213991844906336386652059)
                    ·
                      rfl

theorem cell22_3546361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 5, 1, 4, 3].length) (baseStart_3546361 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3546361 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3546361 prefixEnd_3546361 := by exact prefixLift 3546361
  have htrace : WordTrace (prefixWord ++ tailWord_3546361) baseStart_3546361 baseEnd_3546361 := by
    simpa [prefixWord, tailWord_3546361, baseEnd_3546361] using wordTrace_append hprefix tailTrace_3546361
  have hstable : (prefixWord ++ tailWord_3546361).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3546361).length < 2 ^ (prefixWord ++ tailWord_3546361).sum := by decide
  have hdescent : baseEnd_3546361 < baseStart_3546361 := by decide
  rcases family_descends (prefixWord ++ tailWord_3546361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3546389 : List Nat := [1, 3, 2, 1, 2, 1, 1, 1, 1, 9]
def baseStart_3546389 : Nat := 118140960795 + 3546389 * 2 ^ 59
def prefixEnd_3546389 : Nat := 4983230072969 + 3 ^ 40 * 3546389 * 2
def baseEnd_3546389 : Nat := 1214001429878553646951973

theorem tailTrace_3546389 : CollatzResearch.WordTrace tailWord_3546389 prefixEnd_3546389 1214001429878553646951973 := by
  unfold tailWord_3546389
  simp only [CollatzResearch.WordTrace]
  refine ⟨129347433149045802866058221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86231622099363868577372147 129347433149045802866058221)
  ·
    refine ⟨48505287430892176074771833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129347433149045802866058221 48505287430892176074771833)
    ·
      refine ⟨36378965573169132056078875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48505287430892176074771833 36378965573169132056078875)
      ·
        refine ⟨54568448359753698084118313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36378965573169132056078875 54568448359753698084118313)
        ·
          refine ⟨40926336269815273563088735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54568448359753698084118313 40926336269815273563088735)
          ·
            refine ⟨61389504404722910344633103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40926336269815273563088735 61389504404722910344633103)
            ·
              refine ⟨92084256607084365516949655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61389504404722910344633103 92084256607084365516949655)
              ·
                refine ⟨138126384910626548275424483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92084256607084365516949655 138126384910626548275424483)
                ·
                  refine ⟨207189577365939822413136725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 138126384910626548275424483 207189577365939822413136725)
                  ·
                    refine ⟨1214001429878553646951973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 207189577365939822413136725 1214001429878553646951973)
                    ·
                      rfl

theorem cell22_3546389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 1, 1, 9].length) (baseStart_3546389 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3546389 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3546389 prefixEnd_3546389 := by exact prefixLift 3546389
  have htrace : WordTrace (prefixWord ++ tailWord_3546389) baseStart_3546389 baseEnd_3546389 := by
    simpa [prefixWord, tailWord_3546389, baseEnd_3546389] using wordTrace_append hprefix tailTrace_3546389
  have hstable : (prefixWord ++ tailWord_3546389).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3546389).length < 2 ^ (prefixWord ++ tailWord_3546389).sum := by decide
  have hdescent : baseEnd_3546389 < baseStart_3546389 := by decide
  rcases family_descends (prefixWord ++ tailWord_3546389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3546429 : List Nat := [1, 4, 1, 5, 1, 2, 2, 1, 2, 3]
def baseStart_3546429 : Nat := 118140960795 + 3546429 * 2 ^ 59
def prefixEnd_3546429 : Nat := 4983230072969 + 3 ^ 40 * 3546429 * 2
def baseEnd_3546429 : Nat := 1214015122696006875951851

theorem tailTrace_3546429 : CollatzResearch.WordTrace tailWord_3546429 prefixEnd_3546429 1214015122696006875951851 := by
  unfold tailWord_3546429
  simp only [CollatzResearch.WordTrace]
  refine ⟨129348892068900889697514341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86232594712600593131676227 129348892068900889697514341)
  ·
    refine ⟨24252917262918916818283939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 129348892068900889697514341 24252917262918916818283939)
    ·
      refine ⟨36379375894378375227425909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24252917262918916818283939 36379375894378375227425909)
      ·
        refine ⟨3410566490097972677571179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 36379375894378375227425909 3410566490097972677571179)
        ·
          refine ⟨5115849735146959016356769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3410566490097972677571179 5115849735146959016356769)
          ·
            refine ⟨3836887301360219262267577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5115849735146959016356769 3836887301360219262267577)
            ·
              refine ⟨2877665476020164446700683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3836887301360219262267577 2877665476020164446700683)
              ·
                refine ⟨4316498214030246670051025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2877665476020164446700683 4316498214030246670051025)
                ·
                  refine ⟨3237373660522685002538269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4316498214030246670051025 3237373660522685002538269)
                  ·
                    refine ⟨1214015122696006875951851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3237373660522685002538269 1214015122696006875951851)
                    ·
                      rfl

theorem cell22_3546429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 2, 2, 1, 2, 3].length) (baseStart_3546429 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3546429 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3546429 prefixEnd_3546429 := by exact prefixLift 3546429
  have htrace : WordTrace (prefixWord ++ tailWord_3546429) baseStart_3546429 baseEnd_3546429 := by
    simpa [prefixWord, tailWord_3546429, baseEnd_3546429] using wordTrace_append hprefix tailTrace_3546429
  have hstable : (prefixWord ++ tailWord_3546429).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3546429).length < 2 ^ (prefixWord ++ tailWord_3546429).sum := by decide
  have hdescent : baseEnd_3546429 < baseStart_3546429 := by decide
  rcases family_descends (prefixWord ++ tailWord_3546429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3546530 : List Nat := [3, 3, 1, 2, 1, 3, 1, 1, 4, 3]
def baseStart_3546530 : Nat := 118140960795 + 3546530 * 2 ^ 59
def prefixEnd_3546530 : Nat := 4983230072969 + 3 ^ 40 * 3546530 * 2
def baseEnd_3546530 : Nat := 1214049697060076279176541

theorem tailTrace_3546530 : CollatzResearch.WordTrace tailWord_3546530 prefixEnd_3546530 1214049697060076279176541 := by
  unfold tailWord_3546530
  simp only [CollatzResearch.WordTrace]
  refine ⟨32338143960383745986735261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86235050561023322631294029 32338143960383745986735261)
  ·
    refine ⟨12126803985143904745025723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32338143960383745986735261 12126803985143904745025723)
    ·
      refine ⟨18190205977715857117538585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12126803985143904745025723 18190205977715857117538585)
      ·
        refine ⟨13642654483286892838153939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18190205977715857117538585 13642654483286892838153939)
        ·
          refine ⟨20463981724930339257230909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13642654483286892838153939 20463981724930339257230909)
          ·
            refine ⟨7673993146848877221461591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20463981724930339257230909 7673993146848877221461591)
            ·
              refine ⟨11510989720273315832192387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7673993146848877221461591 11510989720273315832192387)
              ·
                refine ⟨17266484580409973748288581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11510989720273315832192387 17266484580409973748288581)
                ·
                  refine ⟨3237465858826870077804109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17266484580409973748288581 3237465858826870077804109)
                  ·
                    refine ⟨1214049697060076279176541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3237465858826870077804109 1214049697060076279176541)
                    ·
                      rfl

theorem cell22_3546530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 1, 1, 4, 3].length) (baseStart_3546530 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3546530 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3546530 prefixEnd_3546530 := by exact prefixLift 3546530
  have htrace : WordTrace (prefixWord ++ tailWord_3546530) baseStart_3546530 baseEnd_3546530 := by
    simpa [prefixWord, tailWord_3546530, baseEnd_3546530] using wordTrace_append hprefix tailTrace_3546530
  have hstable : (prefixWord ++ tailWord_3546530).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3546530).length < 2 ^ (prefixWord ++ tailWord_3546530).sum := by decide
  have hdescent : baseEnd_3546530 < baseStart_3546530 := by decide
  rcases family_descends (prefixWord ++ tailWord_3546530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3546571 : List Nat := [1, 1, 1, 1, 3, 3, 3, 2, 7]
def baseStart_3546571 : Nat := 118140960795 + 3546571 * 2 ^ 59
def prefixEnd_3546571 : Nat := 4983230072969 + 3 ^ 40 * 3546571 * 2
def baseEnd_3546571 : Nat := 404687910732655279633805

theorem tailTrace_3546571 : CollatzResearch.WordTrace tailWord_3546571 prefixEnd_3546571 404687910732655279633805 := by
  unfold tailWord_3546571
  simp only [CollatzResearch.WordTrace]
  refine ⟨129354071234386447949183567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86236047489590965299455711 129354071234386447949183567)
  ·
    refine ⟨194031106851579671923775351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129354071234386447949183567 194031106851579671923775351)
    ·
      refine ⟨291046660277369507885663027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194031106851579671923775351 291046660277369507885663027)
      ·
        refine ⟨436569990416054261828494541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 291046660277369507885663027 436569990416054261828494541)
        ·
          refine ⟨163713746406020348185685453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 436569990416054261828494541 163713746406020348185685453)
          ·
            refine ⟨61392654902257630569632045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 163713746406020348185685453 61392654902257630569632045)
            ·
              refine ⟨23022245588346611463612017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61392654902257630569632045 23022245588346611463612017)
              ·
                refine ⟨17266684191259958597709013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23022245588346611463612017 17266684191259958597709013)
                ·
                  refine ⟨404687910732655279633805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17266684191259958597709013 404687910732655279633805)
                  ·
                    rfl

theorem cell22_3546571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 2, 7].length) (baseStart_3546571 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3546571 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3546571 prefixEnd_3546571 := by exact prefixLift 3546571
  have htrace : WordTrace (prefixWord ++ tailWord_3546571) baseStart_3546571 baseEnd_3546571 := by
    simpa [prefixWord, tailWord_3546571, baseEnd_3546571] using wordTrace_append hprefix tailTrace_3546571
  have hstable : (prefixWord ++ tailWord_3546571).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3546571).length < 2 ^ (prefixWord ++ tailWord_3546571).sum := by decide
  have hdescent : baseEnd_3546571 < baseStart_3546571 := by decide
  rcases family_descends (prefixWord ++ tailWord_3546571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3546618 : List Nat := [3, 1, 1, 1, 1, 2, 5, 1, 3, 4]
def baseStart_3546618 : Nat := 118140960795 + 3546618 * 2 ^ 59
def prefixEnd_3546618 : Nat := 4983230072969 + 3 ^ 40 * 3546618 * 2
def baseEnd_3546618 : Nat := 1214079821258473382976271

theorem tailTrace_3546618 : CollatzResearch.WordTrace tailWord_3546618 prefixEnd_3546618 1214079821258473382976271 := by
  unfold tailWord_3546618
  simp only [CollatzResearch.WordTrace]
  refine ⟨32338946366304043744036127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86237190310144116650763005 32338946366304043744036127)
  ·
    refine ⟨48508419549456065616054191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32338946366304043744036127 48508419549456065616054191)
    ·
      refine ⟨72762629324184098424081287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48508419549456065616054191 72762629324184098424081287)
      ·
        refine ⟨109143943986276147636121931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72762629324184098424081287 109143943986276147636121931)
        ·
          refine ⟨163715915979414221454182897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109143943986276147636121931 163715915979414221454182897)
          ·
            refine ⟨122786936984560666090637173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 163715915979414221454182897 122786936984560666090637173)
            ·
              refine ⟨11511275342302562445997235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 122786936984560666090637173 11511275342302562445997235)
              ·
                refine ⟨17266913013453843668995853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11511275342302562445997235 17266913013453843668995853)
                ·
                  refine ⟨6475092380045191375873445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17266913013453843668995853 6475092380045191375873445)
                  ·
                    refine ⟨1214079821258473382976271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6475092380045191375873445 1214079821258473382976271)
                    ·
                      rfl

theorem cell22_3546618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 5, 1, 3, 4].length) (baseStart_3546618 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3546618 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3546618 prefixEnd_3546618 := by exact prefixLift 3546618
  have htrace : WordTrace (prefixWord ++ tailWord_3546618) baseStart_3546618 baseEnd_3546618 := by
    simpa [prefixWord, tailWord_3546618, baseEnd_3546618] using wordTrace_append hprefix tailTrace_3546618
  have hstable : (prefixWord ++ tailWord_3546618).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3546618).length < 2 ^ (prefixWord ++ tailWord_3546618).sum := by decide
  have hdescent : baseEnd_3546618 < baseStart_3546618 := by decide
  rcases family_descends (prefixWord ++ tailWord_3546618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3546680 : List Nat := [2, 1, 2, 1, 4, 2, 3, 1, 2, 4]
def baseStart_3546680 : Nat := 118140960795 + 3546680 * 2 ^ 59
def prefixEnd_3546680 : Nat := 4983230072969 + 3 ^ 40 * 3546680 * 2
def baseEnd_3546680 : Nat := 1214101045125525887926081

theorem tailTrace_3546680 : CollatzResearch.WordTrace tailWord_3546680 prefixEnd_3546680 1214101045125525887926081 := by
  unfold tailWord_3546680
  simp only [CollatzResearch.WordTrace]
  refine ⟨64679023395495779782450747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86238697860661039709934329 64679023395495779782450747)
  ·
    refine ⟨97018535093243669673676121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64679023395495779782450747 97018535093243669673676121)
    ·
      refine ⟨72763901319932752255257091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97018535093243669673676121 72763901319932752255257091)
      ·
        refine ⟨109145851979899128382885637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72763901319932752255257091 109145851979899128382885637)
        ·
          refine ⟨20464847246231086571791057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 109145851979899128382885637 20464847246231086571791057)
          ·
            refine ⟨15348635434673314928843293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20464847246231086571791057 15348635434673314928843293)
            ·
              refine ⟨5755738288002493098316235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15348635434673314928843293 5755738288002493098316235)
              ·
                refine ⟨8633607432003739647474353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5755738288002493098316235 8633607432003739647474353)
                ·
                  refine ⟨6475205574002804735605765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8633607432003739647474353 6475205574002804735605765)
                  ·
                    refine ⟨1214101045125525887926081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6475205574002804735605765 1214101045125525887926081)
                    ·
                      rfl

theorem cell22_3546680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 3, 1, 2, 4].length) (baseStart_3546680 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3546680 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3546680 prefixEnd_3546680 := by exact prefixLift 3546680
  have htrace : WordTrace (prefixWord ++ tailWord_3546680) baseStart_3546680 baseEnd_3546680 := by
    simpa [prefixWord, tailWord_3546680, baseEnd_3546680] using wordTrace_append hprefix tailTrace_3546680
  have hstable : (prefixWord ++ tailWord_3546680).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3546680).length < 2 ^ (prefixWord ++ tailWord_3546680).sum := by decide
  have hdescent : baseEnd_3546680 < baseStart_3546680 := by decide
  rcases family_descends (prefixWord ++ tailWord_3546680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3546800 : List Nat := [2, 1, 1, 1, 2, 1, 4, 1, 6, 3]
def baseStart_3546800 : Nat := 118140960795 + 3546800 * 2 ^ 59
def prefixEnd_3546800 : Nat := 4983230072969 + 3 ^ 40 * 3546800 * 2
def baseEnd_3546800 : Nat := 1214142123577885574925713

theorem tailTrace_3546800 : CollatzResearch.WordTrace tailWord_3546800 prefixEnd_3546800 1214142123577885574925713 := by
  unfold tailWord_3546800
  simp only [CollatzResearch.WordTrace]
  refine ⟨64681211775278410029634927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86241615700371213372846569 64681211775278410029634927)
  ·
    refine ⟨97021817662917615044452391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64681211775278410029634927 97021817662917615044452391)
    ·
      refine ⟨145532726494376422566678587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97021817662917615044452391 145532726494376422566678587)
      ·
        refine ⟨218299089741564633850017881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145532726494376422566678587 218299089741564633850017881)
        ·
          refine ⟨163724317306173475387513411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 218299089741564633850017881 163724317306173475387513411)
          ·
            refine ⟨245586475959260213081270117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163724317306173475387513411 245586475959260213081270117)
            ·
              refine ⟨46047464242361289952738147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 245586475959260213081270117 46047464242361289952738147)
              ·
                refine ⟨69071196363541934929107221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46047464242361289952738147 69071196363541934929107221)
                ·
                  refine ⟨3237712329541028199801901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 69071196363541934929107221 3237712329541028199801901)
                  ·
                    refine ⟨1214142123577885574925713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3237712329541028199801901 1214142123577885574925713)
                    ·
                      rfl

theorem cell22_3546800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 1, 6, 3].length) (baseStart_3546800 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3546800 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3546800 prefixEnd_3546800 := by exact prefixLift 3546800
  have htrace : WordTrace (prefixWord ++ tailWord_3546800) baseStart_3546800 baseEnd_3546800 := by
    simpa [prefixWord, tailWord_3546800, baseEnd_3546800] using wordTrace_append hprefix tailTrace_3546800
  have hstable : (prefixWord ++ tailWord_3546800).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3546800).length < 2 ^ (prefixWord ++ tailWord_3546800).sum := by decide
  have hdescent : baseEnd_3546800 < baseStart_3546800 := by decide
  rcases family_descends (prefixWord ++ tailWord_3546800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3546815 : List Nat := [1, 1, 2, 2, 2, 3, 1, 4, 2, 4]
def baseStart_3546815 : Nat := 118140960795 + 3546815 * 2 ^ 59
def prefixEnd_3546815 : Nat := 4983230072969 + 3 ^ 40 * 3546815 * 2
def baseEnd_3546815 : Nat := 1214147258384430535800667

theorem tailTrace_3546815 : CollatzResearch.WordTrace tailWord_3546815 prefixEnd_3546815 1214147258384430535800667 := by
  unfold tailWord_3546815
  simp only [CollatzResearch.WordTrace]
  refine ⟨129362970645502477621065899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86241980430334985080710599 129362970645502477621065899)
  ·
    refine ⟨194044455968253716431598849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129362970645502477621065899 194044455968253716431598849)
    ·
      refine ⟨145533341976190287323699137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 194044455968253716431598849 145533341976190287323699137)
      ·
        refine ⟨109150006482142715492774353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145533341976190287323699137 109150006482142715492774353)
        ·
          refine ⟨81862504861607036619580765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109150006482142715492774353 81862504861607036619580765)
          ·
            refine ⟨30698439323102638732342787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81862504861607036619580765 30698439323102638732342787)
            ·
              refine ⟨46047658984653958098514181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30698439323102638732342787 46047658984653958098514181)
              ·
                refine ⟨8633936059622617143471409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46047658984653958098514181 8633936059622617143471409)
                ·
                  refine ⟨6475452044716962857603557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8633936059622617143471409 6475452044716962857603557)
                  ·
                    refine ⟨1214147258384430535800667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6475452044716962857603557 1214147258384430535800667)
                    ·
                      rfl

theorem cell22_3546815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 4, 2, 4].length) (baseStart_3546815 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3546815 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3546815 prefixEnd_3546815 := by exact prefixLift 3546815
  have htrace : WordTrace (prefixWord ++ tailWord_3546815) baseStart_3546815 baseEnd_3546815 := by
    simpa [prefixWord, tailWord_3546815, baseEnd_3546815] using wordTrace_append hprefix tailTrace_3546815
  have hstable : (prefixWord ++ tailWord_3546815).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3546815).length < 2 ^ (prefixWord ++ tailWord_3546815).sum := by decide
  have hdescent : baseEnd_3546815 < baseStart_3546815 := by decide
  rcases family_descends (prefixWord ++ tailWord_3546815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3546834 : List Nat := [3, 2, 2, 2, 2, 1, 2, 3, 2, 3]
def baseStart_3546834 : Nat := 118140960795 + 3546834 * 2 ^ 59
def prefixEnd_3546834 : Nat := 4983230072969 + 3 ^ 40 * 3546834 * 2
def baseEnd_3546834 : Nat := 1214153762472720819575609

theorem tailTrace_3546834 : CollatzResearch.WordTrace tailWord_3546834 prefixEnd_3546834 1214153762472720819575609 := by
  unfold tailWord_3546834
  simp only [CollatzResearch.WordTrace]
  refine ⟨32340915908108410966501889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86242442421622429244005037 32340915908108410966501889)
  ·
    refine ⟨24255686931081308224876417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32340915908108410966501889 24255686931081308224876417)
    ·
      refine ⟨18191765198310981168657313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24255686931081308224876417 18191765198310981168657313)
      ·
        refine ⟨13643823898733235876492985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18191765198310981168657313 13643823898733235876492985)
        ·
          refine ⟨10232867924049926907369739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13643823898733235876492985 10232867924049926907369739)
          ·
            refine ⟨15349301886074890361054609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10232867924049926907369739 15349301886074890361054609)
            ·
              refine ⟨11511976414556167770790957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15349301886074890361054609 11511976414556167770790957)
              ·
                refine ⟨4316991155458562914046609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11511976414556167770790957 4316991155458562914046609)
                ·
                  refine ⟨3237743366593922185534957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4316991155458562914046609 3237743366593922185534957)
                  ·
                    refine ⟨1214153762472720819575609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3237743366593922185534957 1214153762472720819575609)
                    ·
                      rfl

theorem cell22_3546834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 2, 3, 2, 3].length) (baseStart_3546834 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3546834 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3546834 prefixEnd_3546834 := by exact prefixLift 3546834
  have htrace : WordTrace (prefixWord ++ tailWord_3546834) baseStart_3546834 baseEnd_3546834 := by
    simpa [prefixWord, tailWord_3546834, baseEnd_3546834] using wordTrace_append hprefix tailTrace_3546834
  have hstable : (prefixWord ++ tailWord_3546834).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3546834).length < 2 ^ (prefixWord ++ tailWord_3546834).sum := by decide
  have hdescent : baseEnd_3546834 < baseStart_3546834 := by decide
  rcases family_descends (prefixWord ++ tailWord_3546834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3546849 : List Nat := [1, 2, 3, 1, 5, 2, 1, 1, 2, 4]
def baseStart_3546849 : Nat := 118140960795 + 3546849 * 2 ^ 59
def prefixEnd_3546849 : Nat := 4983230072969 + 3 ^ 40 * 3546849 * 2
def baseEnd_3546849 : Nat := 1214158897279265780450563

theorem tailTrace_3546849 : CollatzResearch.WordTrace tailWord_3546849 prefixEnd_3546849 1214158897279265780450563 := by
  unfold tailWord_3546849
  simp only [CollatzResearch.WordTrace]
  refine ⟨129364210727379301427803601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86242807151586200951869067 129364210727379301427803601)
  ·
    refine ⟨97023158045534476070852701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129364210727379301427803601 97023158045534476070852701)
    ·
      refine ⟨36383684267075428526569763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97023158045534476070852701 36383684267075428526569763)
      ·
        refine ⟨54575526400613142789854645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36383684267075428526569763 54575526400613142789854645)
        ·
          refine ⟨5116455600057482136548873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 54575526400613142789854645 5116455600057482136548873)
          ·
            refine ⟨3837341700043111602411655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5116455600057482136548873 3837341700043111602411655)
            ·
              refine ⟨5756012550064667403617483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3837341700043111602411655 5756012550064667403617483)
              ·
                refine ⟨8634018825097001105426225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5756012550064667403617483 8634018825097001105426225)
                ·
                  refine ⟨6475514118822750829069669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8634018825097001105426225 6475514118822750829069669)
                  ·
                    refine ⟨1214158897279265780450563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6475514118822750829069669 1214158897279265780450563)
                    ·
                      rfl

theorem cell22_3546849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 2, 1, 1, 2, 4].length) (baseStart_3546849 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3546849 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3546849 prefixEnd_3546849 := by exact prefixLift 3546849
  have htrace : WordTrace (prefixWord ++ tailWord_3546849) baseStart_3546849 baseEnd_3546849 := by
    simpa [prefixWord, tailWord_3546849, baseEnd_3546849] using wordTrace_append hprefix tailTrace_3546849
  have hstable : (prefixWord ++ tailWord_3546849).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3546849).length < 2 ^ (prefixWord ++ tailWord_3546849).sum := by decide
  have hdescent : baseEnd_3546849 < baseStart_3546849 := by decide
  rcases family_descends (prefixWord ++ tailWord_3546849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3546862 : List Nat := [4, 1, 2, 1, 1, 2, 1, 2, 5, 3]
def baseStart_3546862 : Nat := 118140960795 + 3546862 * 2 ^ 59
def prefixEnd_3546862 : Nat := 4983230072969 + 3 ^ 40 * 3546862 * 2
def baseEnd_3546862 : Nat := 1214163347444938079875523

theorem tailTrace_3546862 : CollatzResearch.WordTrace tailWord_3546862 prefixEnd_3546862 1214163347444938079875523 := by
  unfold tailWord_3546862
  simp only [CollatzResearch.WordTrace]
  refine ⟨16170585609541525581003355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 86243123250888136432017893 16170585609541525581003355)
  ·
    refine ⟨24255878414312288371505033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16170585609541525581003355 24255878414312288371505033)
    ·
      refine ⟨18191908810734216278628775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24255878414312288371505033 18191908810734216278628775)
      ·
        refine ⟨27287863216101324417943163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18191908810734216278628775 27287863216101324417943163)
        ·
          refine ⟨40931794824151986626914745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27287863216101324417943163 40931794824151986626914745)
          ·
            refine ⟨30698846118113989970186059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40931794824151986626914745 30698846118113989970186059)
            ·
              refine ⟨46048269177170984955279089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30698846118113989970186059 46048269177170984955279089)
              ·
                refine ⟨34536201882878238716459317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46048269177170984955279089 34536201882878238716459317)
                ·
                  refine ⟨3237768926519834879668061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 34536201882878238716459317 3237768926519834879668061)
                  ·
                    refine ⟨1214163347444938079875523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3237768926519834879668061 1214163347444938079875523)
                    ·
                      rfl

theorem cell22_3546862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 2, 5, 3].length) (baseStart_3546862 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3546862 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3546862 prefixEnd_3546862 := by exact prefixLift 3546862
  have htrace : WordTrace (prefixWord ++ tailWord_3546862) baseStart_3546862 baseEnd_3546862 := by
    simpa [prefixWord, tailWord_3546862, baseEnd_3546862] using wordTrace_append hprefix tailTrace_3546862
  have hstable : (prefixWord ++ tailWord_3546862).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3546862).length < 2 ^ (prefixWord ++ tailWord_3546862).sum := by decide
  have hdescent : baseEnd_3546862 < baseStart_3546862 := by decide
  rcases family_descends (prefixWord ++ tailWord_3546862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3546868 : List Nat := [2, 6, 1, 1, 1, 1, 3, 2, 2, 3]
def baseStart_3546868 : Nat := 118140960795 + 3546868 * 2 ^ 59
def prefixEnd_3546868 : Nat := 4983230072969 + 3 ^ 40 * 3546868 * 2
def baseEnd_3546868 : Nat := 1214165401367556064225505

theorem tailTrace_3546868 : CollatzResearch.WordTrace tailWord_3546868 prefixEnd_3546868 1214165401367556064225505 := by
  unfold tailWord_3546868
  simp only [CollatzResearch.WordTrace]
  refine ⟨64682451857155233836372629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86243269142873645115163505 64682451857155233836372629)
  ·
    refine ⟨3031989930804151586079967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 64682451857155233836372629 3031989930804151586079967)
    ·
      refine ⟨4547984896206227379119951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3031989930804151586079967 4547984896206227379119951)
      ·
        refine ⟨6821977344309341068679927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4547984896206227379119951 6821977344309341068679927)
        ·
          refine ⟨10232966016464011603019891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6821977344309341068679927 10232966016464011603019891)
          ·
            refine ⟨15349449024696017404529837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10232966016464011603019891 15349449024696017404529837)
            ·
              refine ⟨5756043384261006526698689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15349449024696017404529837 5756043384261006526698689)
              ·
                refine ⟨4317032538195754895024017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5756043384261006526698689 4317032538195754895024017)
                ·
                  refine ⟨3237774403646816171268013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4317032538195754895024017 3237774403646816171268013)
                  ·
                    refine ⟨1214165401367556064225505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3237774403646816171268013 1214165401367556064225505)
                    ·
                      rfl

theorem cell22_3546868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 3, 2, 2, 3].length) (baseStart_3546868 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3546868 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3546868 prefixEnd_3546868 := by exact prefixLift 3546868
  have htrace : WordTrace (prefixWord ++ tailWord_3546868) baseStart_3546868 baseEnd_3546868 := by
    simpa [prefixWord, tailWord_3546868, baseEnd_3546868] using wordTrace_append hprefix tailTrace_3546868
  have hstable : (prefixWord ++ tailWord_3546868).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3546868).length < 2 ^ (prefixWord ++ tailWord_3546868).sum := by decide
  have hdescent : baseEnd_3546868 < baseStart_3546868 := by decide
  rcases family_descends (prefixWord ++ tailWord_3546868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3546875 : List Nat := [1, 1, 1, 1, 1, 3, 1, 8, 5]
def baseStart_3546875 : Nat := 118140960795 + 3546875 * 2 ^ 59
def prefixEnd_3546875 : Nat := 4983230072969 + 3 ^ 40 * 3546875 * 2
def baseEnd_3546875 : Nat := 404722599203536793100161

theorem tailTrace_3546875 : CollatzResearch.WordTrace tailWord_3546875 prefixEnd_3546875 404722599203536793100161 := by
  unfold tailWord_3546875
  simp only [CollatzResearch.WordTrace]
  refine ⟨129365159025285107868250079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86243439350190071912166719 129365159025285107868250079)
  ·
    refine ⟨194047738537927661802375119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129365159025285107868250079 194047738537927661802375119)
    ·
      refine ⟨291071607806891492703562679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194047738537927661802375119 291071607806891492703562679)
      ·
        refine ⟨436607411710337239055344019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 291071607806891492703562679 436607411710337239055344019)
        ·
          refine ⟨654911117565505858583016029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 436607411710337239055344019 654911117565505858583016029)
          ·
            refine ⟨245591669087064696968631011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 654911117565505858583016029 245591669087064696968631011)
            ·
              refine ⟨368387503630597045452946517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 245591669087064696968631011 368387503630597045452946517)
              ·
                refine ⟨4317041058171059126401717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 368387503630597045452946517 4317041058171059126401717)
                ·
                  refine ⟨404722599203536793100161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4317041058171059126401717 404722599203536793100161)
                  ·
                    rfl

theorem cell22_3546875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 8, 5].length) (baseStart_3546875 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3546875 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3546875 prefixEnd_3546875 := by exact prefixLift 3546875
  have htrace : WordTrace (prefixWord ++ tailWord_3546875) baseStart_3546875 baseEnd_3546875 := by
    simpa [prefixWord, tailWord_3546875, baseEnd_3546875] using wordTrace_append hprefix tailTrace_3546875
  have hstable : (prefixWord ++ tailWord_3546875).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3546875).length < 2 ^ (prefixWord ++ tailWord_3546875).sum := by decide
  have hdescent : baseEnd_3546875 < baseStart_3546875 := by decide
  rcases family_descends (prefixWord ++ tailWord_3546875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3546879 : List Nat := [1, 1, 2, 2, 1, 3, 4, 4, 1, 3]
def baseStart_3546879 : Nat := 118140960795 + 3546879 * 2 ^ 59
def prefixEnd_3546879 : Nat := 4983230072969 + 3 ^ 40 * 3546879 * 2
def baseEnd_3546879 : Nat := 1214169166892355702200471

theorem tailTrace_3546879 : CollatzResearch.WordTrace tailWord_3546879 prefixEnd_3546879 1214169166892355702200471 := by
  unfold tailWord_3546879
  simp only [CollatzResearch.WordTrace]
  refine ⟨129365304917270616551395691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86243536611513744367597127 129365304917270616551395691)
  ·
    refine ⟨194047957375905924827093537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129365304917270616551395691 194047957375905924827093537)
    ·
      refine ⟨145535968031929443620320153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 194047957375905924827093537 145535968031929443620320153)
      ·
        refine ⟨109151976023947082715240115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145535968031929443620320153 109151976023947082715240115)
        ·
          refine ⟨163727964035920624072860173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109151976023947082715240115 163727964035920624072860173)
          ·
            refine ⟨61397986513470234027322565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 163727964035920624072860173 61397986513470234027322565)
            ·
              refine ⟨11512122471275668880122981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 61397986513470234027322565 11512122471275668880122981)
              ·
                refine ⟨2158522963364187915023059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11512122471275668880122981 2158522963364187915023059)
                ·
                  refine ⟨3237784445046281872534589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2158522963364187915023059 3237784445046281872534589)
                  ·
                    refine ⟨1214169166892355702200471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3237784445046281872534589 1214169166892355702200471)
                    ·
                      rfl

theorem cell22_3546879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 4, 4, 1, 3].length) (baseStart_3546879 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3546879 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3546879 prefixEnd_3546879 := by exact prefixLift 3546879
  have htrace : WordTrace (prefixWord ++ tailWord_3546879) baseStart_3546879 baseEnd_3546879 := by
    simpa [prefixWord, tailWord_3546879, baseEnd_3546879] using wordTrace_append hprefix tailTrace_3546879
  have hstable : (prefixWord ++ tailWord_3546879).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3546879).length < 2 ^ (prefixWord ++ tailWord_3546879).sum := by decide
  have hdescent : baseEnd_3546879 < baseStart_3546879 := by decide
  rcases family_descends (prefixWord ++ tailWord_3546879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3546905 : List Nat := [1, 2, 1, 2, 1, 1, 1, 2, 7, 4]
def baseStart_3546905 : Nat := 118140960795 + 3546905 * 2 ^ 59
def prefixEnd_3546905 : Nat := 4983230072969 + 3 ^ 40 * 3546905 * 2
def baseEnd_3546905 : Nat := 1214178067223700301050391

theorem tailTrace_3546905 : CollatzResearch.WordTrace tailWord_3546905 prefixEnd_3546905 1214178067223700301050391 := by
  unfold tailWord_3546905
  simp only [CollatzResearch.WordTrace]
  refine ⟨129366253215176422991842169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86244168810117615327894779 129366253215176422991842169)
  ·
    refine ⟨97024689911382317243881627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129366253215176422991842169 97024689911382317243881627)
    ·
      refine ⟨145537034867073475865822441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97024689911382317243881627 145537034867073475865822441)
      ·
        refine ⟨109152776150305106899366831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145537034867073475865822441 109152776150305106899366831)
        ·
          refine ⟨163729164225457660349050247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109152776150305106899366831 163729164225457660349050247)
          ·
            refine ⟨245593746338186490523575371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163729164225457660349050247 245593746338186490523575371)
            ·
              refine ⟨368390619507279735785363057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 245593746338186490523575371 368390619507279735785363057)
              ·
                refine ⟨276292964630459801839022293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 368390619507279735785363057 276292964630459801839022293)
                ·
                  refine ⟨6475616358526401605602085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 276292964630459801839022293 6475616358526401605602085)
                  ·
                    refine ⟨1214178067223700301050391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6475616358526401605602085 1214178067223700301050391)
                    ·
                      rfl

theorem cell22_3546905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 2, 7, 4].length) (baseStart_3546905 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3546905 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3546905 prefixEnd_3546905 := by exact prefixLift 3546905
  have htrace : WordTrace (prefixWord ++ tailWord_3546905) baseStart_3546905 baseEnd_3546905 := by
    simpa [prefixWord, tailWord_3546905, baseEnd_3546905] using wordTrace_append hprefix tailTrace_3546905
  have hstable : (prefixWord ++ tailWord_3546905).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3546905).length < 2 ^ (prefixWord ++ tailWord_3546905).sum := by decide
  have hdescent : baseEnd_3546905 < baseStart_3546905 := by decide
  rcases family_descends (prefixWord ++ tailWord_3546905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3546935 : List Nat := [1, 1, 3, 1, 2, 1, 2, 1, 5, 5]
def baseStart_3546935 : Nat := 118140960795 + 3546935 * 2 ^ 59
def prefixEnd_3546935 : Nat := 4983230072969 + 3 ^ 40 * 3546935 * 2
def baseEnd_3546935 : Nat := 1214188336836790222800299

theorem tailTrace_3546935 : CollatzResearch.WordTrace tailWord_3546935 prefixEnd_3546935 1214188336836790222800299 := by
  unfold tailWord_3546935
  simp only [CollatzResearch.WordTrace]
  refine ⟨129367347405067738115434259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86244898270045158743622839 129367347405067738115434259)
  ·
    refine ⟨194051021107601607173151389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129367347405067738115434259 194051021107601607173151389)
    ·
      refine ⟨72769132915350602689931771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 194051021107601607173151389 72769132915350602689931771)
      ·
        refine ⟨109153699373025904034897657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72769132915350602689931771 109153699373025904034897657)
        ·
          refine ⟨81865274529769428026173243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109153699373025904034897657 81865274529769428026173243)
          ·
            refine ⟨122797911794654142039259865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81865274529769428026173243 122797911794654142039259865)
            ·
              refine ⟨92098433845990606529444899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 122797911794654142039259865 92098433845990606529444899)
              ·
                refine ⟨138147650768985909794167349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92098433845990606529444899 138147650768985909794167349)
                ·
                  refine ⟨12951342259592429043203189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 138147650768985909794167349 12951342259592429043203189)
                  ·
                    refine ⟨1214188336836790222800299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12951342259592429043203189 1214188336836790222800299)
                    ·
                      rfl

theorem cell22_3546935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 1, 5, 5].length) (baseStart_3546935 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3546935 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3546935 prefixEnd_3546935 := by exact prefixLift 3546935
  have htrace : WordTrace (prefixWord ++ tailWord_3546935) baseStart_3546935 baseEnd_3546935 := by
    simpa [prefixWord, tailWord_3546935, baseEnd_3546935] using wordTrace_append hprefix tailTrace_3546935
  have hstable : (prefixWord ++ tailWord_3546935).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3546935).length < 2 ^ (prefixWord ++ tailWord_3546935).sum := by decide
  have hdescent : baseEnd_3546935 < baseStart_3546935 := by decide
  rcases family_descends (prefixWord ++ tailWord_3546935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3546956 : List Nat := [2, 2, 1, 3, 4, 2, 1, 2, 1, 4]
def baseStart_3546956 : Nat := 118140960795 + 3546956 * 2 ^ 59
def prefixEnd_3546956 : Nat := 4983230072969 + 3 ^ 40 * 3546956 * 2
def baseEnd_3546956 : Nat := 1214195525565953168025235

theorem tailTrace_3546956 : CollatzResearch.WordTrace tailWord_3546956 prefixEnd_3546956 1214195525565953168025235 := by
  unfold tailWord_3546956
  simp only [CollatzResearch.WordTrace]
  refine ⟨64684056668995829350974361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86245408891994439134632481 64684056668995829350974361)
  ·
    refine ⟨48513042501746872013230771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64684056668995829350974361 48513042501746872013230771)
    ·
      refine ⟨72769563752620308019846157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48513042501746872013230771 72769563752620308019846157)
      ·
        refine ⟨27288586407232615507442309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72769563752620308019846157 27288586407232615507442309)
        ·
          refine ⟨5116609951356115407645433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27288586407232615507442309 5116609951356115407645433)
          ·
            refine ⟨3837457463517086555734075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5116609951356115407645433 3837457463517086555734075)
            ·
              refine ⟨5756186195275629833601113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3837457463517086555734075 5756186195275629833601113)
              ·
                refine ⟨4317139646456722375200835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5756186195275629833601113 4317139646456722375200835)
                ·
                  refine ⟨6475709469685083562801253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4317139646456722375200835 6475709469685083562801253)
                  ·
                    refine ⟨1214195525565953168025235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6475709469685083562801253 1214195525565953168025235)
                    ·
                      rfl

theorem cell22_3546956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 2, 1, 2, 1, 4].length) (baseStart_3546956 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3546956 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3546956 prefixEnd_3546956 := by exact prefixLift 3546956
  have htrace : WordTrace (prefixWord ++ tailWord_3546956) baseStart_3546956 baseEnd_3546956 := by
    simpa [prefixWord, tailWord_3546956, baseEnd_3546956] using wordTrace_append hprefix tailTrace_3546956
  have hstable : (prefixWord ++ tailWord_3546956).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3546956).length < 2 ^ (prefixWord ++ tailWord_3546956).sum := by decide
  have hdescent : baseEnd_3546956 < baseStart_3546956 := by decide
  rcases family_descends (prefixWord ++ tailWord_3546956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3547018 : List Nat := [3, 1, 2, 4, 3, 1, 1, 1, 2, 4]
def baseStart_3547018 : Nat := 118140960795 + 3547018 * 2 ^ 59
def prefixEnd_3547018 : Nat := 4983230072969 + 3 ^ 40 * 3547018 * 2
def baseEnd_3547018 : Nat := 1214216749433005672975045

theorem tailTrace_3547018 : CollatzResearch.WordTrace tailWord_3547018 prefixEnd_3547018 1214216749433005672975045 := by
  unfold tailWord_3547018
  simp only [CollatzResearch.WordTrace]
  refine ⟨32342593665941760822676427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86246916442511362193803805 32342593665941760822676427)
  ·
    refine ⟨48513890498912641234014641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32342593665941760822676427 48513890498912641234014641)
    ·
      refine ⟨36385417874184480925510981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48513890498912641234014641 36385417874184480925510981)
      ·
        refine ⟨6822265851409590173533309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36385417874184480925510981 6822265851409590173533309)
        ·
          refine ⟨2558349694278596315074991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6822265851409590173533309 2558349694278596315074991)
          ·
            refine ⟨3837524541417894472612487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2558349694278596315074991 3837524541417894472612487)
            ·
              refine ⟨5756286812126841708918731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3837524541417894472612487 5756286812126841708918731)
              ·
                refine ⟨8634430218190262563378097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5756286812126841708918731 8634430218190262563378097)
                ·
                  refine ⟨6475822663642696922533573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8634430218190262563378097 6475822663642696922533573)
                  ·
                    refine ⟨1214216749433005672975045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6475822663642696922533573 1214216749433005672975045)
                    ·
                      rfl

theorem cell22_3547018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 3, 1, 1, 1, 2, 4].length) (baseStart_3547018 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3547018 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3547018 prefixEnd_3547018 := by exact prefixLift 3547018
  have htrace : WordTrace (prefixWord ++ tailWord_3547018) baseStart_3547018 baseEnd_3547018 := by
    simpa [prefixWord, tailWord_3547018, baseEnd_3547018] using wordTrace_append hprefix tailTrace_3547018
  have hstable : (prefixWord ++ tailWord_3547018).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3547018).length < 2 ^ (prefixWord ++ tailWord_3547018).sum := by decide
  have hdescent : baseEnd_3547018 < baseStart_3547018 := by decide
  rcases family_descends (prefixWord ++ tailWord_3547018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3547031 : List Nat := [1, 1, 3, 3, 1, 3, 1, 5, 1, 3]
def baseStart_3547031 : Nat := 118140960795 + 3547031 * 2 ^ 59
def prefixEnd_3547031 : Nat := 4983230072969 + 3 ^ 40 * 3547031 * 2
def baseEnd_3547031 : Nat := 1214221199598677972400005

theorem tailTrace_3547031 : CollatzResearch.WordTrace tailWord_3547031 prefixEnd_3547031 1214221199598677972400005 := by
  unfold tailWord_3547031
  simp only [CollatzResearch.WordTrace]
  refine ⟨129370848812719946510928947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86247232541813297673952631 129370848812719946510928947)
  ·
    refine ⟨194056273219079919766393421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129370848812719946510928947 194056273219079919766393421)
    ·
      refine ⟨72771102457154969912397533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 194056273219079919766393421 72771102457154969912397533)
      ·
        refine ⟨27289163421433113717149075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72771102457154969912397533 27289163421433113717149075)
        ·
          refine ⟨40933745132149670575723613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27289163421433113717149075 40933745132149670575723613)
          ·
            refine ⟨15350154424556126465896355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40933745132149670575723613 15350154424556126465896355)
            ·
              refine ⟨23025231636834189698844533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15350154424556126465896355 23025231636834189698844533)
              ·
                refine ⟨2158615465953205284266675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23025231636834189698844533 2158615465953205284266675)
                ·
                  refine ⟨3237923198929807926400013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2158615465953205284266675 3237923198929807926400013)
                  ·
                    refine ⟨1214221199598677972400005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3237923198929807926400013 1214221199598677972400005)
                    ·
                      rfl

theorem cell22_3547031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 5, 1, 3].length) (baseStart_3547031 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3547031 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3547031 prefixEnd_3547031 := by exact prefixLift 3547031
  have htrace : WordTrace (prefixWord ++ tailWord_3547031) baseStart_3547031 baseEnd_3547031 := by
    simpa [prefixWord, tailWord_3547031, baseEnd_3547031] using wordTrace_append hprefix tailTrace_3547031
  have hstable : (prefixWord ++ tailWord_3547031).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3547031).length < 2 ^ (prefixWord ++ tailWord_3547031).sum := by decide
  have hdescent : baseEnd_3547031 < baseStart_3547031 := by decide
  rcases family_descends (prefixWord ++ tailWord_3547031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3547044 : List Nat := [2, 3, 1, 2, 1, 3, 3, 2, 5]
def baseStart_3547044 : Nat := 118140960795 + 3547044 * 2 ^ 59
def prefixEnd_3547044 : Nat := 4983230072969 + 3 ^ 40 * 3547044 * 2
def baseEnd_3547044 : Nat := 404741883254783423941655

theorem tailTrace_3547044 : CollatzResearch.WordTrace tailWord_3547044 prefixEnd_3547044 404741883254783423941655 := by
  unfold tailWord_3547044
  simp only [CollatzResearch.WordTrace]
  refine ⟨64685661480836424865576093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86247548641115233154101457 64685661480836424865576093)
  ·
    refine ⟨24257123055313659324591035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64685661480836424865576093 24257123055313659324591035)
    ·
      refine ⟨36385684582970488986886553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24257123055313659324591035 36385684582970488986886553)
      ·
        refine ⟨27289263437227866740164915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36385684582970488986886553 27289263437227866740164915)
        ·
          refine ⟨40933895155841800110247373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27289263437227866740164915 40933895155841800110247373)
          ·
            refine ⟨15350210683440675041342765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40933895155841800110247373 15350210683440675041342765)
            ·
              refine ⟨5756329006290253140503537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15350210683440675041342765 5756329006290253140503537)
              ·
                refine ⟨4317246754717689855377653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5756329006290253140503537 4317246754717689855377653)
                ·
                  refine ⟨404741883254783423941655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4317246754717689855377653 404741883254783423941655)
                  ·
                    rfl

theorem cell22_3547044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 3, 2, 5].length) (baseStart_3547044 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3547044 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3547044 prefixEnd_3547044 := by exact prefixLift 3547044
  have htrace : WordTrace (prefixWord ++ tailWord_3547044) baseStart_3547044 baseEnd_3547044 := by
    simpa [prefixWord, tailWord_3547044, baseEnd_3547044] using wordTrace_append hprefix tailTrace_3547044
  have hstable : (prefixWord ++ tailWord_3547044).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3547044).length < 2 ^ (prefixWord ++ tailWord_3547044).sum := by decide
  have hdescent : baseEnd_3547044 < baseStart_3547044 := by decide
  rcases family_descends (prefixWord ++ tailWord_3547044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3547061 : List Nat := [1, 3, 3, 2, 1, 3, 3, 1, 5]
def baseStart_3547061 : Nat := 118140960795 + 3547061 * 2 ^ 59
def prefixEnd_3547061 : Nat := 4983230072969 + 3 ^ 40 * 3547061 * 2
def baseEnd_3547061 : Nat := 404743823070589298049971

theorem tailTrace_3547061 : CollatzResearch.WordTrace tailWord_3547061 prefixEnd_3547061 404743823070589298049971 := by
  unfold tailWord_3547061
  simp only [CollatzResearch.WordTrace]
  refine ⟨129371943002611261634521037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86247962001740841089680691 129371943002611261634521037)
  ·
    refine ⟨48514478625979223112945389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129371943002611261634521037 48514478625979223112945389)
    ·
      refine ⟨18192929484742208667354521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48514478625979223112945389 18192929484742208667354521)
      ·
        refine ⟨13644697113556656500515891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18192929484742208667354521 13644697113556656500515891)
        ·
          refine ⟨20467045670334984750773837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13644697113556656500515891 20467045670334984750773837)
          ·
            refine ⟨7675142126375619281540189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20467045670334984750773837 7675142126375619281540189)
            ·
              refine ⟨2878178297390857230577571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7675142126375619281540189 2878178297390857230577571)
              ·
                refine ⟨4317267446086285845866357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2878178297390857230577571 4317267446086285845866357)
                ·
                  refine ⟨404743823070589298049971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4317267446086285845866357 404743823070589298049971)
                  ·
                    rfl

theorem cell22_3547061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 3, 1, 5].length) (baseStart_3547061 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3547061 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3547061 prefixEnd_3547061 := by exact prefixLift 3547061
  have htrace : WordTrace (prefixWord ++ tailWord_3547061) baseStart_3547061 baseEnd_3547061 := by
    simpa [prefixWord, tailWord_3547061, baseEnd_3547061] using wordTrace_append hprefix tailTrace_3547061
  have hstable : (prefixWord ++ tailWord_3547061).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3547061).length < 2 ^ (prefixWord ++ tailWord_3547061).sum := by decide
  have hdescent : baseEnd_3547061 < baseStart_3547061 := by decide
  rcases family_descends (prefixWord ++ tailWord_3547061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3547072 : List Nat := [2, 1, 1, 2, 3, 2, 1, 4, 6]
def baseStart_3547072 : Nat := 118140960795 + 3547072 * 2 ^ 59
def prefixEnd_3547072 : Nat := 4983230072969 + 3 ^ 40 * 3547072 * 2
def baseEnd_3547072 : Nat := 404745078245522510708293

theorem tailTrace_3547072 : CollatzResearch.WordTrace tailWord_3547072 prefixEnd_3547072 404745078245522510708293 := by
  unfold tailWord_3547072
  simp only [CollatzResearch.WordTrace]
  refine ⟨64686172102785705256585735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86248229470380940342114313 64686172102785705256585735)
  ·
    refine ⟨97029258154178557884878603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64686172102785705256585735 97029258154178557884878603)
    ·
      refine ⟨145543887231267836827317905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97029258154178557884878603 145543887231267836827317905)
      ·
        refine ⟨109157915423450877620488429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145543887231267836827317905 109157915423450877620488429)
        ·
          refine ⟨40934218283794079107683161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 109157915423450877620488429 40934218283794079107683161)
          ·
            refine ⟨30700663712845559330762371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40934218283794079107683161 30700663712845559330762371)
            ·
              refine ⟨46050995569268338996143557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30700663712845559330762371 46050995569268338996143557)
              ·
                refine ⟨8634561669237813561776917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46050995569268338996143557 8634561669237813561776917)
                ·
                  refine ⟨404745078245522510708293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8634561669237813561776917 404745078245522510708293)
                  ·
                    rfl

theorem cell22_3547072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 4, 6].length) (baseStart_3547072 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3547072 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3547072 prefixEnd_3547072 := by exact prefixLift 3547072
  have htrace : WordTrace (prefixWord ++ tailWord_3547072) baseStart_3547072 baseEnd_3547072 := by
    simpa [prefixWord, tailWord_3547072, baseEnd_3547072] using wordTrace_append hprefix tailTrace_3547072
  have hstable : (prefixWord ++ tailWord_3547072).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3547072).length < 2 ^ (prefixWord ++ tailWord_3547072).sum := by decide
  have hdescent : baseEnd_3547072 < baseStart_3547072 := by decide
  rcases family_descends (prefixWord ++ tailWord_3547072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3547087 : List Nat := [1, 1, 2, 1, 1, 5, 2, 1, 3, 5]
def baseStart_3547087 : Nat := 118140960795 + 3547087 * 2 ^ 59
def prefixEnd_3547087 : Nat := 4983230072969 + 3 ^ 40 * 3547087 * 2
def baseEnd_3547087 : Nat := 1214240369543112492999833

theorem tailTrace_3547087 : CollatzResearch.WordTrace tailWord_3547087 prefixEnd_3547087 1214240369543112492999833 := by
  unfold tailWord_3547087
  simp only [CollatzResearch.WordTrace]
  refine ⟨129372891300517068074967515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86248594200344712049978343 129372891300517068074967515)
  ·
    refine ⟨194059336950775602112451273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129372891300517068074967515 194059336950775602112451273)
    ·
      refine ⟨145544502713081701584338455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 194059336950775602112451273 145544502713081701584338455)
      ·
        refine ⟨218316754069622552376507683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145544502713081701584338455 218316754069622552376507683)
        ·
          refine ⟨327475131104433828564761525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 218316754069622552376507683 327475131104433828564761525)
          ·
            refine ⟨30700793541040671427946393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 327475131104433828564761525 30700793541040671427946393)
            ·
              refine ⟨23025595155780503570959795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30700793541040671427946393 23025595155780503570959795)
              ·
                refine ⟨34538392733670755356439693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23025595155780503570959795 34538392733670755356439693)
                ·
                  refine ⟨12951897275126533258664885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34538392733670755356439693 12951897275126533258664885)
                  ·
                    refine ⟨1214240369543112492999833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12951897275126533258664885 1214240369543112492999833)
                    ·
                      rfl

theorem cell22_3547087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 1, 3, 5].length) (baseStart_3547087 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3547087 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3547087 prefixEnd_3547087 := by exact prefixLift 3547087
  have htrace : WordTrace (prefixWord ++ tailWord_3547087) baseStart_3547087 baseEnd_3547087 := by
    simpa [prefixWord, tailWord_3547087, baseEnd_3547087] using wordTrace_append hprefix tailTrace_3547087
  have hstable : (prefixWord ++ tailWord_3547087).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3547087).length < 2 ^ (prefixWord ++ tailWord_3547087).sum := by decide
  have hdescent : baseEnd_3547087 < baseStart_3547087 := by decide
  rcases family_descends (prefixWord ++ tailWord_3547087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3547089 : List Nat := [1, 2, 2, 1, 2, 1, 2, 7, 4]
def baseStart_3547089 : Nat := 118140960795 + 3547089 * 2 ^ 59
def prefixEnd_3547089 : Nat := 4983230072969 + 3 ^ 40 * 3547089 * 2
def baseEnd_3547089 : Nat := 404747018061328384816609

theorem tailTrace_3547089 : CollatzResearch.WordTrace tailWord_3547089 prefixEnd_3547089 404747018061328384816609 := by
  unfold tailWord_3547089
  simp only [CollatzResearch.WordTrace]
  refine ⟨129372964246509822416540321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86248642831006548277693547 129372964246509822416540321)
  ·
    refine ⟨97029723184882366812405241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129372964246509822416540321 97029723184882366812405241)
    ·
      refine ⟨72772292388661775109303931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97029723184882366812405241 72772292388661775109303931)
      ·
        refine ⟨109158438582992662663955897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72772292388661775109303931 109158438582992662663955897)
        ·
          refine ⟨81868828937244496997966923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109158438582992662663955897 81868828937244496997966923)
          ·
            refine ⟨122803243405866745496950385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81868828937244496997966923 122803243405866745496950385)
            ·
              refine ⟨92102432554400059122712789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 122803243405866745496950385 92102432554400059122712789)
              ·
                refine ⟨2158650762993751385688581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 92102432554400059122712789 2158650762993751385688581)
                ·
                  refine ⟨404747018061328384816609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2158650762993751385688581 404747018061328384816609)
                  ·
                    rfl

theorem cell22_3547089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 7, 4].length) (baseStart_3547089 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3547089 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3547089 prefixEnd_3547089 := by exact prefixLift 3547089
  have htrace : WordTrace (prefixWord ++ tailWord_3547089) baseStart_3547089 baseEnd_3547089 := by
    simpa [prefixWord, tailWord_3547089, baseEnd_3547089] using wordTrace_append hprefix tailTrace_3547089
  have hstable : (prefixWord ++ tailWord_3547089).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3547089).length < 2 ^ (prefixWord ++ tailWord_3547089).sum := by decide
  have hdescent : baseEnd_3547089 < baseStart_3547089 := by decide
  rcases family_descends (prefixWord ++ tailWord_3547089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3547164 : List Nat := [2, 2, 3, 1, 3, 1, 1, 1, 2, 6]
def baseStart_3547164 : Nat := 118140960795 + 3547164 * 2 ^ 59
def prefixEnd_3547164 : Nat := 4983230072969 + 3 ^ 40 * 3547164 * 2
def baseEnd_3547164 : Nat := 1214266728216709958824597

theorem tailTrace_3547164 : CollatzResearch.WordTrace tailWord_3547164 prefixEnd_3547164 1214266728216709958824597 := by
  unfold tailWord_3547164
  simp only [CollatzResearch.WordTrace]
  refine ⟨64687849860619055112760273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86250466480825406817013697 64687849860619055112760273)
  ·
    refine ⟨48515887395464291334570205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64687849860619055112760273 48515887395464291334570205)
    ·
      refine ⟨18193457773299109250463827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48515887395464291334570205 18193457773299109250463827)
      ·
        refine ⟨27290186659948663875695741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18193457773299109250463827 27290186659948663875695741)
        ·
          refine ⟨10233819997480748953385903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27290186659948663875695741 10233819997480748953385903)
          ·
            refine ⟨15350729996221123430078855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10233819997480748953385903 15350729996221123430078855)
            ·
              refine ⟨23026094994331685145118283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15350729996221123430078855 23026094994331685145118283)
              ·
                refine ⟨34539142491497527717677425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23026094994331685145118283 34539142491497527717677425)
                ·
                  refine ⟨25904356868623145788258069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34539142491497527717677425 25904356868623145788258069)
                  ·
                    refine ⟨1214266728216709958824597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25904356868623145788258069 1214266728216709958824597)
                    ·
                      rfl

theorem cell22_3547164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 1, 2, 6].length) (baseStart_3547164 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3547164 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3547164 prefixEnd_3547164 := by exact prefixLift 3547164
  have htrace : WordTrace (prefixWord ++ tailWord_3547164) baseStart_3547164 baseEnd_3547164 := by
    simpa [prefixWord, tailWord_3547164, baseEnd_3547164] using wordTrace_append hprefix tailTrace_3547164
  have hstable : (prefixWord ++ tailWord_3547164).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3547164).length < 2 ^ (prefixWord ++ tailWord_3547164).sum := by decide
  have hdescent : baseEnd_3547164 < baseStart_3547164 := by decide
  rcases family_descends (prefixWord ++ tailWord_3547164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3547224 : List Nat := [2, 1, 2, 2, 1, 4, 1, 3, 6]
def baseStart_3547224 : Nat := 118140960795 + 3547224 * 2 ^ 59
def prefixEnd_3547224 : Nat := 4983230072969 + 3 ^ 40 * 3547224 * 2
def baseEnd_3547224 : Nat := 404762422480963267441471

theorem tailTrace_3547224 : CollatzResearch.WordTrace tailWord_3547224 prefixEnd_3547224 404762422480963267441471 := by
  unfold tailWord_3547224
  simp only [CollatzResearch.WordTrace]
  refine ⟨64688944050510370236352363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86251925400680493648469817 64688944050510370236352363)
  ·
    refine ⟨97033416075765555354528545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64688944050510370236352363 97033416075765555354528545)
    ·
      refine ⟨72775062056824166515896409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97033416075765555354528545 72775062056824166515896409)
      ·
        refine ⟨54581296542618124886922307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72775062056824166515896409 54581296542618124886922307)
        ·
          refine ⟨81871944813927187330383461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54581296542618124886922307 81871944813927187330383461)
          ·
            refine ⟨15350989652611347624446899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 81871944813927187330383461 15350989652611347624446899)
            ·
              refine ⟨23026484478917021436670349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15350989652611347624446899 23026484478917021436670349)
              ·
                refine ⟨8634931679593883038751381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23026484478917021436670349 8634931679593883038751381)
                ·
                  refine ⟨404762422480963267441471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8634931679593883038751381 404762422480963267441471)
                  ·
                    rfl

theorem cell22_3547224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 3, 6].length) (baseStart_3547224 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3547224 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3547224 prefixEnd_3547224 := by exact prefixLift 3547224
  have htrace : WordTrace (prefixWord ++ tailWord_3547224) baseStart_3547224 baseEnd_3547224 := by
    simpa [prefixWord, tailWord_3547224, baseEnd_3547224] using wordTrace_append hprefix tailTrace_3547224
  have hstable : (prefixWord ++ tailWord_3547224).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3547224).length < 2 ^ (prefixWord ++ tailWord_3547224).sum := by decide
  have hdescent : baseEnd_3547224 < baseStart_3547224 := by decide
  rcases family_descends (prefixWord ++ tailWord_3547224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3547269 : List Nat := [1, 3, 1, 1, 5, 1, 10]
def baseStart_3547269 : Nat := 118140960795 + 3547269 * 2 ^ 59
def prefixEnd_3547269 : Nat := 4983230072969 + 3 ^ 40 * 3547269 * 2
def baseEnd_3547269 : Nat := 44974173031945358701825

theorem tailTrace_3547269 : CollatzResearch.WordTrace tailWord_3547269 prefixEnd_3547269 44974173031945358701825 := by
  unfold tailWord_3547269
  simp only [CollatzResearch.WordTrace]
  refine ⟨129379529385857713158092861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86253019590571808772061907 129379529385857713158092861)
  ·
    refine ⟨48517323519696642434284823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129379529385857713158092861 48517323519696642434284823)
    ·
      refine ⟨72775985279544963651427235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48517323519696642434284823 72775985279544963651427235)
      ·
        refine ⟨109163977919317445477140853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72775985279544963651427235 109163977919317445477140853)
        ·
          refine ⟨10234122929936010513481955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 109163977919317445477140853 10234122929936010513481955)
          ·
            refine ⟨15351184394904015770222933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10234122929936010513481955 15351184394904015770222933)
            ·
              refine ⟨44974173031945358701825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 15351184394904015770222933 44974173031945358701825)
              ·
                rfl

theorem cell22_3547269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 10].length) (baseStart_3547269 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3547269 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3547269 prefixEnd_3547269 := by exact prefixLift 3547269
  have htrace : WordTrace (prefixWord ++ tailWord_3547269) baseStart_3547269 baseEnd_3547269 := by
    simpa [prefixWord, tailWord_3547269, baseEnd_3547269] using wordTrace_append hprefix tailTrace_3547269
  have hstable : (prefixWord ++ tailWord_3547269).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3547269).length < 2 ^ (prefixWord ++ tailWord_3547269).sum := by decide
  have hdescent : baseEnd_3547269 < baseStart_3547269 := by decide
  rcases family_descends (prefixWord ++ tailWord_3547269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3547290 : List Nat := [3, 1, 1, 5, 2, 1, 1, 3, 2, 3]
def baseStart_3547290 : Nat := 118140960795 + 3547290 * 2 ^ 59
def prefixEnd_3547290 : Nat := 4983230072969 + 3 ^ 40 * 3547290 * 2
def baseEnd_3547290 : Nat := 1214309860591687630174211

theorem tailTrace_3547290 : CollatzResearch.WordTrace tailWord_3547290 prefixEnd_3547290 1214309860591687630174211 := by
  unfold tailWord_3547290
  simp only [CollatzResearch.WordTrace]
  refine ⟨32345073829695408436151831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86253530212521089163071549 32345073829695408436151831)
  ·
    refine ⟨48517610744543112654227747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32345073829695408436151831 48517610744543112654227747)
    ·
      refine ⟨72776416116814668981341621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48517610744543112654227747 72776416116814668981341621)
      ·
        refine ⟨6822789010951375217000777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 72776416116814668981341621 6822789010951375217000777)
        ·
          refine ⟨5117091758213531412750583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6822789010951375217000777 5117091758213531412750583)
          ·
            refine ⟨7675637637320297119125875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5117091758213531412750583 7675637637320297119125875)
            ·
              refine ⟨11513456455980445678688813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7675637637320297119125875 11513456455980445678688813)
              ·
                refine ⟨4317546170992667129508305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11513456455980445678688813 4317546170992667129508305)
                ·
                  refine ⟨3238159628244500347131229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4317546170992667129508305 3238159628244500347131229)
                  ·
                    refine ⟨1214309860591687630174211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3238159628244500347131229 1214309860591687630174211)
                    ·
                      rfl

theorem cell22_3547290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 1, 3, 2, 3].length) (baseStart_3547290 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3547290 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3547290 prefixEnd_3547290 := by exact prefixLift 3547290
  have htrace : WordTrace (prefixWord ++ tailWord_3547290) baseStart_3547290 baseEnd_3547290 := by
    simpa [prefixWord, tailWord_3547290, baseEnd_3547290] using wordTrace_append hprefix tailTrace_3547290
  have hstable : (prefixWord ++ tailWord_3547290).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3547290).length < 2 ^ (prefixWord ++ tailWord_3547290).sum := by decide
  have hdescent : baseEnd_3547290 < baseStart_3547290 := by decide
  rcases family_descends (prefixWord ++ tailWord_3547290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3547301 : List Nat := [1, 3, 1, 2, 1, 3, 2, 1, 5, 3]
def baseStart_3547301 : Nat := 118140960795 + 3547301 * 2 ^ 59
def prefixEnd_3547301 : Nat := 4983230072969 + 3 ^ 40 * 3547301 * 2
def baseEnd_3547301 : Nat := 1214313626116487268149177

theorem tailTrace_3547301 : CollatzResearch.WordTrace tailWord_3547301 prefixEnd_3547301 1214313626116487268149177 := by
  unfold tailWord_3547301
  simp only [CollatzResearch.WordTrace]
  refine ⟨129380696521741782623257757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86253797681161188415505171 129380696521741782623257757)
  ·
    refine ⟨48517761195653168483721659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129380696521741782623257757 48517761195653168483721659)
    ·
      refine ⟨72776641793479752725582489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48517761195653168483721659 72776641793479752725582489)
      ·
        refine ⟨54582481345109814544186867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72776641793479752725582489 54582481345109814544186867)
        ·
          refine ⟨81873722017664721816280301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54582481345109814544186867 81873722017664721816280301)
          ·
            refine ⟨30702645756624270681105113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81873722017664721816280301 30702645756624270681105113)
            ·
              refine ⟨23026984317468203010828835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30702645756624270681105113 23026984317468203010828835)
              ·
                refine ⟨34540476476202304516243253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23026984317468203010828835 34540476476202304516243253)
                ·
                  refine ⟨3238169669643966048397805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 34540476476202304516243253 3238169669643966048397805)
                  ·
                    refine ⟨1214313626116487268149177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3238169669643966048397805 1214313626116487268149177)
                    ·
                      rfl

theorem cell22_3547301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 1, 5, 3].length) (baseStart_3547301 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3547301 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3547301 prefixEnd_3547301 := by exact prefixLift 3547301
  have htrace : WordTrace (prefixWord ++ tailWord_3547301) baseStart_3547301 baseEnd_3547301 := by
    simpa [prefixWord, tailWord_3547301, baseEnd_3547301] using wordTrace_append hprefix tailTrace_3547301
  have hstable : (prefixWord ++ tailWord_3547301).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3547301).length < 2 ^ (prefixWord ++ tailWord_3547301).sum := by decide
  have hdescent : baseEnd_3547301 < baseStart_3547301 := by decide
  rcases family_descends (prefixWord ++ tailWord_3547301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3547346 : List Nat := [3, 2, 2, 2, 1, 2, 1, 1, 1, 7]
def baseStart_3547346 : Nat := 118140960795 + 3547346 * 2 ^ 59
def prefixEnd_3547346 : Nat := 4983230072969 + 3 ^ 40 * 3547346 * 2
def baseEnd_3547346 : Nat := 1214329030536122150774039

theorem tailTrace_3547346 : CollatzResearch.WordTrace tailWord_3547346 prefixEnd_3547346 1214329030536122150774039 := by
  unfold tailWord_3547346
  simp only [CollatzResearch.WordTrace]
  refine ⟨32345584451644688827161473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86254891871052503539097261 32345584451644688827161473)
  ·
    refine ⟨24259188338733516620371105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32345584451644688827161473 24259188338733516620371105)
    ·
      refine ⟨18194391254050137465278329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24259188338733516620371105 18194391254050137465278329)
      ·
        refine ⟨13645793440537603098958747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18194391254050137465278329 13645793440537603098958747)
        ·
          refine ⟨20468690160806404648438121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13645793440537603098958747 20468690160806404648438121)
          ·
            refine ⟨15351517620604803486328591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20468690160806404648438121 15351517620604803486328591)
            ·
              refine ⟨23027276430907205229492887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15351517620604803486328591 23027276430907205229492887)
              ·
                refine ⟨34540914646360807844239331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23027276430907205229492887 34540914646360807844239331)
                ·
                  refine ⟨51811371969541211766358997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34540914646360807844239331 51811371969541211766358997)
                  ·
                    refine ⟨1214329030536122150774039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 51811371969541211766358997 1214329030536122150774039)
                    ·
                      rfl

theorem cell22_3547346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 1, 1, 7].length) (baseStart_3547346 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3547346 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3547346 prefixEnd_3547346 := by exact prefixLift 3547346
  have htrace : WordTrace (prefixWord ++ tailWord_3547346) baseStart_3547346 baseEnd_3547346 := by
    simpa [prefixWord, tailWord_3547346, baseEnd_3547346] using wordTrace_append hprefix tailTrace_3547346
  have hstable : (prefixWord ++ tailWord_3547346).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3547346).length < 2 ^ (prefixWord ++ tailWord_3547346).sum := by decide
  have hdescent : baseEnd_3547346 < baseStart_3547346 := by decide
  rcases family_descends (prefixWord ++ tailWord_3547346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3547361 : List Nat := [1, 2, 3, 1, 3, 1, 1, 3, 3, 4]
def baseStart_3547361 : Nat := 118140960795 + 3547361 * 2 ^ 59
def prefixEnd_3547361 : Nat := 4983230072969 + 3 ^ 40 * 3547361 * 2
def baseEnd_3547361 : Nat := 1214334165342667111648993

theorem tailTrace_3547361 : CollatzResearch.WordTrace tailWord_3547361 prefixEnd_3547361 1214334165342667111648993 := by
  unfold tailWord_3547361
  simp only [CollatzResearch.WordTrace]
  refine ⟨129382884901524412870441937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86255256601016275246961291 129382884901524412870441937)
  ·
    refine ⟨97037163676143309652831453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129382884901524412870441937 97037163676143309652831453)
    ·
      refine ⟨36388936378553741119811795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97037163676143309652831453 36388936378553741119811795)
      ·
        refine ⟨54583404567830611679717693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36388936378553741119811795 54583404567830611679717693)
        ·
          refine ⟨20468776712936479379894135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54583404567830611679717693 20468776712936479379894135)
          ·
            refine ⟨30703165069404719069841203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20468776712936479379894135 30703165069404719069841203)
            ·
              refine ⟨46054747604107078604761805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30703165069404719069841203 46054747604107078604761805)
              ·
                refine ⟨17270530351540154476785677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46054747604107078604761805 17270530351540154476785677)
                ·
                  refine ⟨6476448881827557928794629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17270530351540154476785677 6476448881827557928794629)
                  ·
                    refine ⟨1214334165342667111648993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6476448881827557928794629 1214334165342667111648993)
                    ·
                      rfl

theorem cell22_3547361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 3, 3, 4].length) (baseStart_3547361 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3547361 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3547361 prefixEnd_3547361 := by exact prefixLift 3547361
  have htrace : WordTrace (prefixWord ++ tailWord_3547361) baseStart_3547361 baseEnd_3547361 := by
    simpa [prefixWord, tailWord_3547361, baseEnd_3547361] using wordTrace_append hprefix tailTrace_3547361
  have hstable : (prefixWord ++ tailWord_3547361).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3547361).length < 2 ^ (prefixWord ++ tailWord_3547361).sum := by decide
  have hdescent : baseEnd_3547361 < baseStart_3547361 := by decide
  rcases family_descends (prefixWord ++ tailWord_3547361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3547393 : List Nat := [1, 2, 4, 1, 1, 2, 1, 6, 4]
def baseStart_3547393 : Nat := 118140960795 + 3547393 * 2 ^ 59
def prefixEnd_3547393 : Nat := 4983230072969 + 3 ^ 40 * 3547393 * 2
def baseEnd_3547393 : Nat := 404781706532209898282965

theorem tailTrace_3547393 : CollatzResearch.WordTrace tailWord_3547393 prefixEnd_3547393 404781706532209898282965 := by
  unfold tailWord_3547393
  simp only [CollatzResearch.WordTrace]
  refine ⟨129384052037408482335606833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86256034691605654890404555 129384052037408482335606833)
  ·
    refine ⟨97038039028056361751705125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129384052037408482335606833 97038039028056361751705125)
    ·
      refine ⟨18194632317760567828444711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 97038039028056361751705125 18194632317760567828444711)
      ·
        refine ⟨27291948476640851742667067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18194632317760567828444711 27291948476640851742667067)
        ·
          refine ⟨40937922714961277614000601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27291948476640851742667067 40937922714961277614000601)
          ·
            refine ⟨30703442036220958210500451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40937922714961277614000601 30703442036220958210500451)
            ·
              refine ⟨46055163054331437315750677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30703442036220958210500451 46055163054331437315750677)
              ·
                refine ⟨2158835768171786124175813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 46055163054331437315750677 2158835768171786124175813)
                ·
                  refine ⟨404781706532209898282965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2158835768171786124175813 404781706532209898282965)
                  ·
                    rfl

theorem cell22_3547393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 6, 4].length) (baseStart_3547393 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3547393 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3547393 prefixEnd_3547393 := by exact prefixLift 3547393
  have htrace : WordTrace (prefixWord ++ tailWord_3547393) baseStart_3547393 baseEnd_3547393 := by
    simpa [prefixWord, tailWord_3547393, baseEnd_3547393] using wordTrace_append hprefix tailTrace_3547393
  have hstable : (prefixWord ++ tailWord_3547393).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3547393).length < 2 ^ (prefixWord ++ tailWord_3547393).sum := by decide
  have hdescent : baseEnd_3547393 < baseStart_3547393 := by decide
  rcases family_descends (prefixWord ++ tailWord_3547393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3547406 : List Nat := [4, 1, 1, 2, 1, 2, 1, 1, 3, 6]
def baseStart_3547406 : Nat := 118140960795 + 3547406 * 2 ^ 59
def prefixEnd_3547406 : Nat := 4983230072969 + 3 ^ 40 * 3547406 * 2
def baseEnd_3547406 : Nat := 1214349569762301994273855

theorem tailTrace_3547406 : CollatzResearch.WordTrace tailWord_3547406 prefixEnd_3547406 1214349569762301994273855 := by
  unfold tailWord_3547406
  simp only [CollatzResearch.WordTrace]
  refine ⟨16173065773295173194478759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 86256350790907590370553381 16173065773295173194478759)
  ·
    refine ⟨24259598659942759791718139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16173065773295173194478759 24259598659942759791718139)
    ·
      refine ⟨36389397989914139687577209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24259598659942759791718139 36389397989914139687577209)
      ·
        refine ⟨27292048492435604765682907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36389397989914139687577209 27292048492435604765682907)
        ·
          refine ⟨40938072738653407148524361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27292048492435604765682907 40938072738653407148524361)
          ·
            refine ⟨30703554553990055361393271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40938072738653407148524361 30703554553990055361393271)
            ·
              refine ⟨46055331830985083042089907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30703554553990055361393271 46055331830985083042089907)
              ·
                refine ⟨69082997746477624563134861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46055331830985083042089907 69082997746477624563134861)
                ·
                  refine ⟨25906124154929109211175573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 69082997746477624563134861 25906124154929109211175573)
                  ·
                    refine ⟨1214349569762301994273855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25906124154929109211175573 1214349569762301994273855)
                    ·
                      rfl

theorem cell22_3547406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 1, 3, 6].length) (baseStart_3547406 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3547406 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3547406 prefixEnd_3547406 := by exact prefixLift 3547406
  have htrace : WordTrace (prefixWord ++ tailWord_3547406) baseStart_3547406 baseEnd_3547406 := by
    simpa [prefixWord, tailWord_3547406, baseEnd_3547406] using wordTrace_append hprefix tailTrace_3547406
  have hstable : (prefixWord ++ tailWord_3547406).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3547406).length < 2 ^ (prefixWord ++ tailWord_3547406).sum := by decide
  have hdescent : baseEnd_3547406 < baseStart_3547406 := by decide
  rcases family_descends (prefixWord ++ tailWord_3547406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3547481 : List Nat := [1, 2, 1, 2, 2, 2, 1, 2, 4, 5]
def baseStart_3547481 : Nat := 118140960795 + 3547481 * 2 ^ 59
def prefixEnd_3547481 : Nat := 4983230072969 + 3 ^ 40 * 3547481 * 2
def baseEnd_3547481 : Nat := 1214375243795026798648625

theorem tailTrace_3547481 : CollatzResearch.WordTrace tailWord_3547481 prefixEnd_3547481 1214375243795026798648625 := by
  unfold tailWord_3547481
  simp only [CollatzResearch.WordTrace]
  refine ⟨129387261661089673364810297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86258174440726448909873531 129387261661089673364810297)
  ·
    refine ⟨97040446245817255023607723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129387261661089673364810297 97040446245817255023607723)
    ·
      refine ⟨145560669368725882535411585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97040446245817255023607723 145560669368725882535411585)
      ·
        refine ⟨109170502026544411901558689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145560669368725882535411585 109170502026544411901558689)
        ·
          refine ⟨81877876519908308926169017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109170502026544411901558689 81877876519908308926169017)
          ·
            refine ⟨61408407389931231694626763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81877876519908308926169017 61408407389931231694626763)
            ·
              refine ⟨92112611084896847541940145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61408407389931231694626763 92112611084896847541940145)
              ·
                refine ⟨69084458313672635656455109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 92112611084896847541940145 69084458313672635656455109)
                ·
                  refine ⟨12953335933813619185585333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 69084458313672635656455109 12953335933813619185585333)
                  ·
                    refine ⟨1214375243795026798648625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12953335933813619185585333 1214375243795026798648625)
                    ·
                      rfl

theorem cell22_3547481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 2, 4, 5].length) (baseStart_3547481 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3547481 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3547481 prefixEnd_3547481 := by exact prefixLift 3547481
  have htrace : WordTrace (prefixWord ++ tailWord_3547481) baseStart_3547481 baseEnd_3547481 := by
    simpa [prefixWord, tailWord_3547481, baseEnd_3547481] using wordTrace_append hprefix tailTrace_3547481
  have hstable : (prefixWord ++ tailWord_3547481).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3547481).length < 2 ^ (prefixWord ++ tailWord_3547481).sum := by decide
  have hdescent : baseEnd_3547481 < baseStart_3547481 := by decide
  rcases family_descends (prefixWord ++ tailWord_3547481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3547500 : List Nat := [2, 2, 1, 1, 6, 1, 2, 2, 5]
def baseStart_3547500 : Nat := 118140960795 + 3547500 * 2 ^ 59
def prefixEnd_3547500 : Nat := 4983230072969 + 3 ^ 40 * 3547500 * 2
def baseEnd_3547500 : Nat := 404793915961105694141189

theorem tailTrace_3547500 : CollatzResearch.WordTrace tailWord_3547500 prefixEnd_3547500 404793915961105694141189 := by
  unfold tailWord_3547500
  simp only [CollatzResearch.WordTrace]
  refine ⟨64693977324010419804875977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86258636432013893073167969 64693977324010419804875977)
  ·
    refine ⟨48520482993007814853656983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64693977324010419804875977 48520482993007814853656983)
    ·
      refine ⟨72780724489511722280485475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48520482993007814853656983 72780724489511722280485475)
      ·
        refine ⟨109171086734267583420728213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72780724489511722280485475 109171086734267583420728213)
        ·
          refine ⟨5117394690668792972846635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 109171086734267583420728213 5117394690668792972846635)
          ·
            refine ⟨7676092036003189459269953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5117394690668792972846635 7676092036003189459269953)
            ·
              refine ⟨5757069027002392094452465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7676092036003189459269953 5757069027002392094452465)
              ·
                refine ⟨4317801770251794070839349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5757069027002392094452465 4317801770251794070839349)
                ·
                  refine ⟨404793915961105694141189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4317801770251794070839349 404793915961105694141189)
                  ·
                    rfl

theorem cell22_3547500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 5].length) (baseStart_3547500 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3547500 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3547500 prefixEnd_3547500 := by exact prefixLift 3547500
  have htrace : WordTrace (prefixWord ++ tailWord_3547500) baseStart_3547500 baseEnd_3547500 := by
    simpa [prefixWord, tailWord_3547500, baseEnd_3547500] using wordTrace_append hprefix tailTrace_3547500
  have hstable : (prefixWord ++ tailWord_3547500).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3547500).length < 2 ^ (prefixWord ++ tailWord_3547500).sum := by decide
  have hdescent : baseEnd_3547500 < baseStart_3547500 := by decide
  rcases family_descends (prefixWord ++ tailWord_3547500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3547504 : List Nat := [2, 1, 1, 1, 4, 5, 2, 2, 1, 3]
def baseStart_3547504 : Nat := 118140960795 + 3547504 * 2 ^ 59
def prefixEnd_3547504 : Nat := 4983230072969 + 3 ^ 40 * 3547504 * 2
def baseEnd_3547504 : Nat := 1214383117165062405323555

theorem tailTrace_3547504 : CollatzResearch.WordTrace tailWord_3547504 prefixEnd_3547504 1214383117165062405323555 := by
  unfold tailWord_3547504
  simp only [CollatzResearch.WordTrace]
  refine ⟨64694050270003174146448783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86258733693337565528598377 64694050270003174146448783)
  ·
    refine ⟨97041075405004761219673175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64694050270003174146448783 97041075405004761219673175)
    ·
      refine ⟨145561613107507141829509763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97041075405004761219673175 145561613107507141829509763)
      ·
        refine ⟨218342419661260712744264645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145561613107507141829509763 218342419661260712744264645)
        ·
          refine ⟨40939203686486383639549621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 218342419661260712744264645 40939203686486383639549621)
          ·
            refine ⟨3838050345608098466207777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 40939203686486383639549621 3838050345608098466207777)
            ·
              refine ⟨2878537759206073849655833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3838050345608098466207777 2878537759206073849655833)
              ·
                refine ⟨2158903319404555387241875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2878537759206073849655833 2158903319404555387241875)
                ·
                  refine ⟨3238354979106833080862813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2158903319404555387241875 3238354979106833080862813)
                  ·
                    refine ⟨1214383117165062405323555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3238354979106833080862813 1214383117165062405323555)
                    ·
                      rfl

theorem cell22_3547504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 5, 2, 2, 1, 3].length) (baseStart_3547504 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3547504 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3547504 prefixEnd_3547504 := by exact prefixLift 3547504
  have htrace : WordTrace (prefixWord ++ tailWord_3547504) baseStart_3547504 baseEnd_3547504 := by
    simpa [prefixWord, tailWord_3547504, baseEnd_3547504] using wordTrace_append hprefix tailTrace_3547504
  have hstable : (prefixWord ++ tailWord_3547504).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3547504).length < 2 ^ (prefixWord ++ tailWord_3547504).sum := by decide
  have hdescent : baseEnd_3547504 < baseStart_3547504 := by decide
  rcases family_descends (prefixWord ++ tailWord_3547504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3547528 : List Nat := [2, 1, 3, 3, 1, 1, 3, 2, 6]
def baseStart_3547528 : Nat := 118140960795 + 3547528 * 2 ^ 59
def prefixEnd_3547528 : Nat := 4983230072969 + 3 ^ 40 * 3547528 * 2
def baseEnd_3547528 : Nat := 404797110951844780907827

theorem tailTrace_3547528 : CollatzResearch.WordTrace tailWord_3547528 prefixEnd_3547528 404797110951844780907827 := by
  unfold tailWord_3547528
  simp only [CollatzResearch.WordTrace]
  refine ⟨64694487945959700195885619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86259317261279600261180825 64694487945959700195885619)
  ·
    refine ⟨97041731918939550293828429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64694487945959700195885619 97041731918939550293828429)
    ·
      refine ⟨36390649469602331360185661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97041731918939550293828429 36390649469602331360185661)
      ·
        refine ⟨13646493551100874260069623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36390649469602331360185661 13646493551100874260069623)
        ·
          refine ⟨20469740326651311390104435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13646493551100874260069623 20469740326651311390104435)
          ·
            refine ⟨30704610489976967085156653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20469740326651311390104435 30704610489976967085156653)
            ·
              refine ⟨11514228933741362656933745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30704610489976967085156653 11514228933741362656933745)
              ·
                refine ⟨8635671700306021992700309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11514228933741362656933745 8635671700306021992700309)
                ·
                  refine ⟨404797110951844780907827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8635671700306021992700309 404797110951844780907827)
                  ·
                    rfl

theorem cell22_3547528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 3, 2, 6].length) (baseStart_3547528 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3547528 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3547528 prefixEnd_3547528 := by exact prefixLift 3547528
  have htrace : WordTrace (prefixWord ++ tailWord_3547528) baseStart_3547528 baseEnd_3547528 := by
    simpa [prefixWord, tailWord_3547528, baseEnd_3547528] using wordTrace_append hprefix tailTrace_3547528
  have hstable : (prefixWord ++ tailWord_3547528).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3547528).length < 2 ^ (prefixWord ++ tailWord_3547528).sum := by decide
  have hdescent : baseEnd_3547528 < baseStart_3547528 := by decide
  rcases family_descends (prefixWord ++ tailWord_3547528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3547543 : List Nat := [1, 1, 3, 3, 1, 1, 4, 2, 1, 5]
def baseStart_3547543 : Nat := 118140960795 + 3547543 * 2 ^ 59
def prefixEnd_3547543 : Nat := 4983230072969 + 3 ^ 40 * 3547543 * 2
def baseEnd_3547543 : Nat := 1214396467662079303598435

theorem tailTrace_3547543 : CollatzResearch.WordTrace tailWord_3547543 prefixEnd_3547543 1214396467662079303598435 := by
  unfold tailWord_3547543
  simp only [CollatzResearch.WordTrace]
  refine ⟨129389522986865057953567283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86259681991243371969044855 129389522986865057953567283)
  ·
    refine ⟨194084284480297586930350925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129389522986865057953567283 194084284480297586930350925)
    ·
      refine ⟨72781606680111595098881597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 194084284480297586930350925 72781606680111595098881597)
      ·
        refine ⟨27293102505041848162080599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72781606680111595098881597 27293102505041848162080599)
        ·
          refine ⟨40939653757562772243120899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27293102505041848162080599 40939653757562772243120899)
          ·
            refine ⟨61409480636344158364681349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40939653757562772243120899 61409480636344158364681349)
            ·
              refine ⟨11514277619314529693377753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 61409480636344158364681349 11514277619314529693377753)
              ·
                refine ⟨8635708214485897270033315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11514277619314529693377753 8635708214485897270033315)
                ·
                  refine ⟨12953562321728845905049973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8635708214485897270033315 12953562321728845905049973)
                  ·
                    refine ⟨1214396467662079303598435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12953562321728845905049973 1214396467662079303598435)
                    ·
                      rfl

theorem cell22_3547543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 4, 2, 1, 5].length) (baseStart_3547543 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3547543 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3547543 prefixEnd_3547543 := by exact prefixLift 3547543
  have htrace : WordTrace (prefixWord ++ tailWord_3547543) baseStart_3547543 baseEnd_3547543 := by
    simpa [prefixWord, tailWord_3547543, baseEnd_3547543] using wordTrace_append hprefix tailTrace_3547543
  have hstable : (prefixWord ++ tailWord_3547543).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3547543).length < 2 ^ (prefixWord ++ tailWord_3547543).sum := by decide
  have hdescent : baseEnd_3547543 < baseStart_3547543 := by decide
  rcases family_descends (prefixWord ++ tailWord_3547543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3547545 : List Nat := [1, 2, 1, 2, 1, 4, 4, 3, 4]
def baseStart_3547545 : Nat := 118140960795 + 3547545 * 2 ^ 59
def prefixEnd_3547545 : Nat := 4983230072969 + 3 ^ 40 * 3547545 * 2
def baseEnd_3547545 : Nat := 404799050767650655016143

theorem tailTrace_3547545 : CollatzResearch.WordTrace tailWord_3547545 prefixEnd_3547545 404799050767650655016143 := by
  unfold tailWord_3547545
  simp only [CollatzResearch.WordTrace]
  refine ⟨129389595932857812295140089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86259730621905208196760059 129389595932857812295140089)
  ·
    refine ⟨97042196949643359221355067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129389595932857812295140089 97042196949643359221355067)
    ·
      refine ⟨145563295424465038832032601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97042196949643359221355067 145563295424465038832032601)
      ·
        refine ⟨109172471568348779124024451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145563295424465038832032601 109172471568348779124024451)
        ·
          refine ⟨163758707352523168686036677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109172471568348779124024451 163758707352523168686036677)
          ·
            refine ⟨30704757628598094128631877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 163758707352523168686036677 30704757628598094128631877)
            ·
              refine ⟨5757142055362142649118477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30704757628598094128631877 5757142055362142649118477)
              ·
                refine ⟨2158928270760803493419429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5757142055362142649118477 2158928270760803493419429)
                ·
                  refine ⟨404799050767650655016143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2158928270760803493419429 404799050767650655016143)
                  ·
                    rfl

theorem cell22_3547545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 4, 3, 4].length) (baseStart_3547545 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3547545 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3547545 prefixEnd_3547545 := by exact prefixLift 3547545
  have htrace : WordTrace (prefixWord ++ tailWord_3547545) baseStart_3547545 baseEnd_3547545 := by
    simpa [prefixWord, tailWord_3547545, baseEnd_3547545] using wordTrace_append hprefix tailTrace_3547545
  have hstable : (prefixWord ++ tailWord_3547545).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3547545).length < 2 ^ (prefixWord ++ tailWord_3547545).sum := by decide
  have hdescent : baseEnd_3547545 < baseStart_3547545 := by decide
  rcases family_descends (prefixWord ++ tailWord_3547545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3547633 : List Nat := [1, 2, 2, 2, 3, 1, 2, 1, 1, 7]
def baseStart_3547633 : Nat := 118140960795 + 3547633 * 2 ^ 59
def prefixEnd_3547633 : Nat := 4983230072969 + 3 ^ 40 * 3547633 * 2
def baseEnd_3547633 : Nat := 1214427276501349068848159

theorem tailTrace_3547633 : CollatzResearch.WordTrace tailWord_3547633 prefixEnd_3547633 1214427276501349068848159 := by
  unfold tailWord_3547633
  simp only [CollatzResearch.WordTrace]
  refine ⟨129392805556539003324343553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86261870371026002216229035 129392805556539003324343553)
  ·
    refine ⟨97044604167404252493257665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129392805556539003324343553 97044604167404252493257665)
    ·
      refine ⟨72783453125553189369943249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97044604167404252493257665 72783453125553189369943249)
      ·
        refine ⟨54587589844164892027457437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72783453125553189369943249 54587589844164892027457437)
        ·
          refine ⟨20470346191561834510296539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54587589844164892027457437 20470346191561834510296539)
          ·
            refine ⟨30705519287342751765444809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20470346191561834510296539 30705519287342751765444809)
            ·
              refine ⟨23029139465507063824083607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30705519287342751765444809 23029139465507063824083607)
              ·
                refine ⟨34543709198260595736125411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23029139465507063824083607 34543709198260595736125411)
                ·
                  refine ⟨51815563797390893604188117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34543709198260595736125411 51815563797390893604188117)
                  ·
                    refine ⟨1214427276501349068848159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 51815563797390893604188117 1214427276501349068848159)
                    ·
                      rfl

theorem cell22_3547633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 1, 1, 7].length) (baseStart_3547633 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3547633 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3547633 prefixEnd_3547633 := by exact prefixLift 3547633
  have htrace : WordTrace (prefixWord ++ tailWord_3547633) baseStart_3547633 baseEnd_3547633 := by
    simpa [prefixWord, tailWord_3547633, baseEnd_3547633] using wordTrace_append hprefix tailTrace_3547633
  have hstable : (prefixWord ++ tailWord_3547633).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3547633).length < 2 ^ (prefixWord ++ tailWord_3547633).sum := by decide
  have hdescent : baseEnd_3547633 < baseStart_3547633 := by decide
  rcases family_descends (prefixWord ++ tailWord_3547633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3547729 : List Nat := [1, 2, 2, 1, 3, 5, 1, 2, 2, 3]
def baseStart_3547729 : Nat := 118140960795 + 3547729 * 2 ^ 59
def prefixEnd_3547729 : Nat := 4983230072969 + 3 ^ 40 * 3547729 * 2
def baseEnd_3547729 : Nat := 1214460139263236818447865

theorem tailTrace_3547729 : CollatzResearch.WordTrace tailWord_3547729 prefixEnd_3547729 1214460139263236818447865 := by
  unfold tailWord_3547729
  simp only [CollatzResearch.WordTrace]
  refine ⟨129396306964191211719838241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86264204642794141146558827 129396306964191211719838241)
  ·
    refine ⟨97047230223143408789878681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129396306964191211719838241 97047230223143408789878681)
    ·
      refine ⟨72785422667357556592409011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97047230223143408789878681 72785422667357556592409011)
      ·
        refine ⟨109178134001036334888613517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72785422667357556592409011 109178134001036334888613517)
        ·
          refine ⟨40941800250388625583230069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 109178134001036334888613517 40941800250388625583230069)
          ·
            refine ⟨3838293773473933648427819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 40941800250388625583230069 3838293773473933648427819)
            ·
              refine ⟨5757440660210900472641729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3838293773473933648427819 5757440660210900472641729)
              ·
                refine ⟨4318080495158175354481297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5757440660210900472641729 4318080495158175354481297)
                ·
                  refine ⟨3238560371368631515860973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4318080495158175354481297 3238560371368631515860973)
                  ·
                    refine ⟨1214460139263236818447865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3238560371368631515860973 1214460139263236818447865)
                    ·
                      rfl

theorem cell22_3547729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 5, 1, 2, 2, 3].length) (baseStart_3547729 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3547729 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3547729 prefixEnd_3547729 := by exact prefixLift 3547729
  have htrace : WordTrace (prefixWord ++ tailWord_3547729) baseStart_3547729 baseEnd_3547729 := by
    simpa [prefixWord, tailWord_3547729, baseEnd_3547729] using wordTrace_append hprefix tailTrace_3547729
  have hstable : (prefixWord ++ tailWord_3547729).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3547729).length < 2 ^ (prefixWord ++ tailWord_3547729).sum := by decide
  have hdescent : baseEnd_3547729 < baseStart_3547729 := by decide
  rcases family_descends (prefixWord ++ tailWord_3547729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3547746 : List Nat := [3, 3, 2, 3, 1, 2, 1, 1, 1, 5]
def baseStart_3547746 : Nat := 118140960795 + 3547746 * 2 ^ 59
def prefixEnd_3547746 : Nat := 4983230072969 + 3 ^ 40 * 3547746 * 2
def baseEnd_3547746 : Nat := 1214465958710654440772813

theorem tailTrace_3547746 : CollatzResearch.WordTrace tailWord_3547746 prefixEnd_3547746 1214465958710654440772813 := by
  unfold tailWord_3547746
  simp only [CollatzResearch.WordTrace]
  refine ⟨32349231751282405905801773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86264618003419749082138061 32349231751282405905801773)
  ·
    refine ⟨12130961906730902214675665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32349231751282405905801773 12130961906730902214675665)
    ·
      refine ⟨9098221430048176661006749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12130961906730902214675665 9098221430048176661006749)
      ·
        refine ⟨3411833036268066247877531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9098221430048176661006749 3411833036268066247877531)
        ·
          refine ⟨5117749554402099371816297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3411833036268066247877531 5117749554402099371816297)
          ·
            refine ⟨3838312165801574528862223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5117749554402099371816297 3838312165801574528862223)
            ·
              refine ⟨5757468248702361793293335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3838312165801574528862223 5757468248702361793293335)
              ·
                refine ⟨8636202373053542689940003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5757468248702361793293335 8636202373053542689940003)
                ·
                  refine ⟨12954303559580314034910005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8636202373053542689940003 12954303559580314034910005)
                  ·
                    refine ⟨1214465958710654440772813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12954303559580314034910005 1214465958710654440772813)
                    ·
                      rfl

theorem cell22_3547746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 2, 1, 1, 1, 5].length) (baseStart_3547746 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3547746 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3547746 prefixEnd_3547746 := by exact prefixLift 3547746
  have htrace : WordTrace (prefixWord ++ tailWord_3547746) baseStart_3547746 baseEnd_3547746 := by
    simpa [prefixWord, tailWord_3547746, baseEnd_3547746] using wordTrace_append hprefix tailTrace_3547746
  have hstable : (prefixWord ++ tailWord_3547746).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3547746).length < 2 ^ (prefixWord ++ tailWord_3547746).sum := by decide
  have hdescent : baseEnd_3547746 < baseStart_3547746 := by decide
  rcases family_descends (prefixWord ++ tailWord_3547746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3547778 : List Nat := [3, 4, 3, 1, 1, 1, 1, 2, 2, 4]
def baseStart_3547778 : Nat := 118140960795 + 3547778 * 2 ^ 59
def prefixEnd_3547778 : Nat := 4983230072969 + 3 ^ 40 * 3547778 * 2
def baseEnd_3547778 : Nat := 1214476912964617023972715

theorem tailTrace_3547778 : CollatzResearch.WordTrace tailWord_3547778 prefixEnd_3547778 1214476912964617023972715 := by
  unfold tailWord_3547778
  simp only [CollatzResearch.WordTrace]
  refine ⟨32349523535253423272092997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86265396094009128725581325 32349523535253423272092997)
  ·
    refine ⟨6065535662860016863517437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32349523535253423272092997 6065535662860016863517437)
    ·
      refine ⟨2274575873572506323819039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6065535662860016863517437 2274575873572506323819039)
      ·
        refine ⟨3411863810358759485728559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2274575873572506323819039 3411863810358759485728559)
        ·
          refine ⟨5117795715538139228592839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3411863810358759485728559 5117795715538139228592839)
          ·
            refine ⟨7676693573307208842889259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5117795715538139228592839 7676693573307208842889259)
            ·
              refine ⟨11515040359960813264333889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7676693573307208842889259 11515040359960813264333889)
              ·
                refine ⟨8636280269970609948250417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11515040359960813264333889 8636280269970609948250417)
                ·
                  refine ⟨6477210202477957461187813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8636280269970609948250417 6477210202477957461187813)
                  ·
                    refine ⟨1214476912964617023972715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6477210202477957461187813 1214476912964617023972715)
                    ·
                      rfl

theorem cell22_3547778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 1, 2, 2, 4].length) (baseStart_3547778 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3547778 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3547778 prefixEnd_3547778 := by exact prefixLift 3547778
  have htrace : WordTrace (prefixWord ++ tailWord_3547778) baseStart_3547778 baseEnd_3547778 := by
    simpa [prefixWord, tailWord_3547778, baseEnd_3547778] using wordTrace_append hprefix tailTrace_3547778
  have hstable : (prefixWord ++ tailWord_3547778).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3547778).length < 2 ^ (prefixWord ++ tailWord_3547778).sum := by decide
  have hdescent : baseEnd_3547778 < baseStart_3547778 := by decide
  rcases family_descends (prefixWord ++ tailWord_3547778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3547804 : List Nat := [2, 2, 3, 2, 2, 1, 4, 1, 5]
def baseStart_3547804 : Nat := 118140960795 + 3547804 * 2 ^ 59
def prefixEnd_3547804 : Nat := 4983230072969 + 3 ^ 40 * 3547804 * 2
def baseEnd_3547804 : Nat := 404828604431987207607545

theorem tailTrace_3547804 : CollatzResearch.WordTrace tailWord_3547804 prefixEnd_3547804 404828604431987207607545 := by
  unfold tailWord_3547804
  simp only [CollatzResearch.WordTrace]
  refine ⟨64699521219459749764409233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86266028292612999685878977 64699521219459749764409233)
  ·
    refine ⟨48524640914594812323306925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64699521219459749764409233 48524640914594812323306925)
    ·
      refine ⟨18196740342973054621240097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48524640914594812323306925 18196740342973054621240097)
      ·
        refine ⟨13647555257229790965930073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18196740342973054621240097 13647555257229790965930073)
        ·
          refine ⟨10235666442922343224447555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13647555257229790965930073 10235666442922343224447555)
          ·
            refine ⟨15353499664383514836671333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10235666442922343224447555 15353499664383514836671333)
            ·
              refine ⟨2878781187071909031875875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15353499664383514836671333 2878781187071909031875875)
              ·
                refine ⟨4318171780607863547813813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2878781187071909031875875 4318171780607863547813813)
                ·
                  refine ⟨404828604431987207607545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4318171780607863547813813 404828604431987207607545)
                  ·
                    rfl

theorem cell22_3547804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 4, 1, 5].length) (baseStart_3547804 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3547804 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3547804 prefixEnd_3547804 := by exact prefixLift 3547804
  have htrace : WordTrace (prefixWord ++ tailWord_3547804) baseStart_3547804 baseEnd_3547804 := by
    simpa [prefixWord, tailWord_3547804, baseEnd_3547804] using wordTrace_append hprefix tailTrace_3547804
  have hstable : (prefixWord ++ tailWord_3547804).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3547804).length < 2 ^ (prefixWord ++ tailWord_3547804).sum := by decide
  have hdescent : baseEnd_3547804 < baseStart_3547804 := by decide
  rcases family_descends (prefixWord ++ tailWord_3547804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3547834 : List Nat := [3, 1, 1, 1, 2, 3, 5, 1, 1, 4]
def baseStart_3547834 : Nat := 118140960795 + 3547834 * 2 ^ 59
def prefixEnd_3547834 : Nat := 4983230072969 + 3 ^ 40 * 3547834 * 2
def baseEnd_3547834 : Nat := 1214496082909051544572543

theorem tailTrace_3547834 : CollatzResearch.WordTrace tailWord_3547834 prefixEnd_3547834 1214496082909051544572543 := by
  unfold tailWord_3547834
  simp only [CollatzResearch.WordTrace]
  refine ⟨32350034157202703663102639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86266757752540543101607037 32350034157202703663102639)
  ·
    refine ⟨48525051235804055494653959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32350034157202703663102639 48525051235804055494653959)
    ·
      refine ⟨72787576853706083241980939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48525051235804055494653959 72787576853706083241980939)
      ·
        refine ⟨109181365280559124862971409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72787576853706083241980939 109181365280559124862971409)
        ·
          refine ⟨81886023960419343647228557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109181365280559124862971409 81886023960419343647228557)
          ·
            refine ⟨30707258985157253867710709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81886023960419343647228557 30707258985157253867710709)
            ·
              refine ⟨2878805529858492550097879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30707258985157253867710709 2878805529858492550097879)
              ·
                refine ⟨4318208294787738825146819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2878805529858492550097879 4318208294787738825146819)
                ·
                  refine ⟨6477312442181608237720229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4318208294787738825146819 6477312442181608237720229)
                  ·
                    refine ⟨1214496082909051544572543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6477312442181608237720229 1214496082909051544572543)
                    ·
                      rfl

theorem cell22_3547834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 5, 1, 1, 4].length) (baseStart_3547834 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3547834 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3547834 prefixEnd_3547834 := by exact prefixLift 3547834
  have htrace : WordTrace (prefixWord ++ tailWord_3547834) baseStart_3547834 baseEnd_3547834 := by
    simpa [prefixWord, tailWord_3547834, baseEnd_3547834] using wordTrace_append hprefix tailTrace_3547834
  have hstable : (prefixWord ++ tailWord_3547834).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3547834).length < 2 ^ (prefixWord ++ tailWord_3547834).sum := by decide
  have hdescent : baseEnd_3547834 < baseStart_3547834 := by decide
  rcases family_descends (prefixWord ++ tailWord_3547834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3547864 : List Nat := [2, 1, 2, 2, 3, 2, 2, 3, 2, 3]
def baseStart_3547864 : Nat := 118140960795 + 3547864 * 2 ^ 59
def prefixEnd_3547864 : Nat := 4983230072969 + 3 ^ 40 * 3547864 * 2
def baseEnd_3547864 : Nat := 1214506352522141466322451

theorem tailTrace_3547864 : CollatzResearch.WordTrace tailWord_3547864 prefixEnd_3547864 1214506352522141466322451 := by
  unfold tailWord_3547864
  simp only [CollatzResearch.WordTrace]
  refine ⟨64700615409351064888001323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86267487212468086517335097 64700615409351064888001323)
  ·
    refine ⟨97050923114026597332001985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64700615409351064888001323 97050923114026597332001985)
    ·
      refine ⟨72788192335519947999001489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97050923114026597332001985 72788192335519947999001489)
      ·
        refine ⟨54591144251639960999251117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72788192335519947999001489 54591144251639960999251117)
        ·
          refine ⟨20471679094364985374719169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54591144251639960999251117 20471679094364985374719169)
          ·
            refine ⟨15353759320773739031039377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20471679094364985374719169 15353759320773739031039377)
            ·
              refine ⟨11515319490580304273279533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15353759320773739031039377 11515319490580304273279533)
              ·
                refine ⟨4318244808967614102479825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11515319490580304273279533 4318244808967614102479825)
                ·
                  refine ⟨3238683606725710576859869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4318244808967614102479825 3238683606725710576859869)
                  ·
                    refine ⟨1214506352522141466322451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3238683606725710576859869 1214506352522141466322451)
                    ·
                      rfl

theorem cell22_3547864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 2, 3, 2, 3].length) (baseStart_3547864 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3547864 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3547864 prefixEnd_3547864 := by exact prefixLift 3547864
  have htrace : WordTrace (prefixWord ++ tailWord_3547864) baseStart_3547864 baseEnd_3547864 := by
    simpa [prefixWord, tailWord_3547864, baseEnd_3547864] using wordTrace_append hprefix tailTrace_3547864
  have hstable : (prefixWord ++ tailWord_3547864).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3547864).length < 2 ^ (prefixWord ++ tailWord_3547864).sum := by decide
  have hdescent : baseEnd_3547864 < baseStart_3547864 := by decide
  rcases family_descends (prefixWord ++ tailWord_3547864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3547982 : List Nat := [4, 1, 1, 1, 1, 1, 1, 2, 5, 5]
def baseStart_3547982 : Nat := 118140960795 + 3547982 * 2 ^ 59
def prefixEnd_3547982 : Nat := 4983230072969 + 3 ^ 40 * 3547982 * 2
def baseEnd_3547982 : Nat := 1214546746333628491872089

theorem tailTrace_3547982 : CollatzResearch.WordTrace tailWord_3547982 prefixEnd_3547982 1214546746333628491872089 := by
  unfold tailWord_3547982
  simp only [CollatzResearch.WordTrace]
  refine ⟨16175691829034329491099775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 86270356421516423952532133 16175691829034329491099775)
  ·
    refine ⟨24263537743551494236649663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16175691829034329491099775 24263537743551494236649663)
    ·
      refine ⟨36395306615327241354974495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24263537743551494236649663 36395306615327241354974495)
      ·
        refine ⟨54592959922990862032461743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36395306615327241354974495 54592959922990862032461743)
        ·
          refine ⟨81889439884486293048692615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54592959922990862032461743 81889439884486293048692615)
          ·
            refine ⟨122834159826729439573038923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81889439884486293048692615 122834159826729439573038923)
            ·
              refine ⟨184251239740094159359558385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122834159826729439573038923 184251239740094159359558385)
              ·
                refine ⟨138188429805070619519668789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 184251239740094159359558385 138188429805070619519668789)
                ·
                  refine ⟨12955165294225370579968949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 138188429805070619519668789 12955165294225370579968949)
                  ·
                    refine ⟨1214546746333628491872089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12955165294225370579968949 1214546746333628491872089)
                    ·
                      rfl

theorem cell22_3547982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 2, 5, 5].length) (baseStart_3547982 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3547982 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3547982 prefixEnd_3547982 := by exact prefixLift 3547982
  have htrace : WordTrace (prefixWord ++ tailWord_3547982) baseStart_3547982 baseEnd_3547982 := by
    simpa [prefixWord, tailWord_3547982, baseEnd_3547982] using wordTrace_append hprefix tailTrace_3547982
  have hstable : (prefixWord ++ tailWord_3547982).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3547982).length < 2 ^ (prefixWord ++ tailWord_3547982).sum := by decide
  have hdescent : baseEnd_3547982 < baseStart_3547982 := by decide
  rcases family_descends (prefixWord ++ tailWord_3547982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3548044 : List Nat := [2, 2, 1, 2, 1, 2, 3, 1, 5, 3]
def baseStart_3548044 : Nat := 118140960795 + 3548044 * 2 ^ 59
def prefixEnd_3548044 : Nat := 4983230072969 + 3 ^ 40 * 3548044 * 2
def baseEnd_3548044 : Nat := 1214567970200680996821899

theorem tailTrace_3548044 : CollatzResearch.WordTrace tailWord_3548044 prefixEnd_3548044 1214567970200680996821899 := by
  unfold tailWord_3548044
  simp only [CollatzResearch.WordTrace]
  refine ⟨64703897979025010258777593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86271863972033347011703457 64703897979025010258777593)
  ·
    refine ⟨48527923484268757694083195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64703897979025010258777593 48527923484268757694083195)
    ·
      refine ⟨72791885226403136541124793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48527923484268757694083195 72791885226403136541124793)
      ·
        refine ⟨54593913919802352405843595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72791885226403136541124793 54593913919802352405843595)
        ·
          refine ⟨81890870879703528608765393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54593913919802352405843595 81890870879703528608765393)
          ·
            refine ⟨61418153159777646456574045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81890870879703528608765393 61418153159777646456574045)
            ·
              refine ⟨23031807434916617421215267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61418153159777646456574045 23031807434916617421215267)
              ·
                refine ⟨34547711152374926131822901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23031807434916617421215267 34547711152374926131822901)
                ·
                  refine ⟨3238847920535149324858397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 34547711152374926131822901 3238847920535149324858397)
                  ·
                    refine ⟨1214567970200680996821899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3238847920535149324858397 1214567970200680996821899)
                    ·
                      rfl

theorem cell22_3548044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 1, 5, 3].length) (baseStart_3548044 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3548044 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3548044 prefixEnd_3548044 := by exact prefixLift 3548044
  have htrace : WordTrace (prefixWord ++ tailWord_3548044) baseStart_3548044 baseEnd_3548044 := by
    simpa [prefixWord, tailWord_3548044, baseEnd_3548044] using wordTrace_append hprefix tailTrace_3548044
  have hstable : (prefixWord ++ tailWord_3548044).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3548044).length < 2 ^ (prefixWord ++ tailWord_3548044).sum := by decide
  have hdescent : baseEnd_3548044 < baseStart_3548044 := by decide
  rcases family_descends (prefixWord ++ tailWord_3548044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3548057 : List Nat := [1, 2, 1, 2, 1, 3, 1, 4, 7]
def baseStart_3548057 : Nat := 118140960795 + 3548057 * 2 ^ 59
def prefixEnd_3548057 : Nat := 4983230072969 + 3 ^ 40 * 3548057 * 2
def baseEnd_3548057 : Nat := 404857473455451098748953

theorem tailTrace_3548057 : CollatzResearch.WordTrace tailWord_3548057 prefixEnd_3548057 404857473455451098748953 := by
  unfold tailWord_3548057
  simp only [CollatzResearch.WordTrace]
  refine ⟨129408270107002923737778425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86272180071335282491852283 129408270107002923737778425)
  ·
    refine ⟨97056202580252192803333819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129408270107002923737778425 97056202580252192803333819)
    ·
      refine ⟨145584303870378289205000729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97056202580252192803333819 145584303870378289205000729)
      ·
        refine ⟨109188227902783716903750547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145584303870378289205000729 109188227902783716903750547)
        ·
          refine ⟨163782341854175575355625821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109188227902783716903750547 163782341854175575355625821)
          ·
            refine ⟨61418378195315840758359683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 163782341854175575355625821 61418378195315840758359683)
            ·
              refine ⟨92127567292973761137539525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61418378195315840758359683 92127567292973761137539525)
              ·
                refine ⟨17273918867432580213288661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 92127567292973761137539525 17273918867432580213288661)
                ·
                  refine ⟨404857473455451098748953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17273918867432580213288661 404857473455451098748953)
                  ·
                    rfl

theorem cell22_3548057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 4, 7].length) (baseStart_3548057 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3548057 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3548057 prefixEnd_3548057 := by exact prefixLift 3548057
  have htrace : WordTrace (prefixWord ++ tailWord_3548057) baseStart_3548057 baseEnd_3548057 := by
    simpa [prefixWord, tailWord_3548057, baseEnd_3548057] using wordTrace_append hprefix tailTrace_3548057
  have hstable : (prefixWord ++ tailWord_3548057).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3548057).length < 2 ^ (prefixWord ++ tailWord_3548057).sum := by decide
  have hdescent : baseEnd_3548057 < baseStart_3548057 := by decide
  rcases family_descends (prefixWord ++ tailWord_3548057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3548089 : List Nat := [1, 2, 1, 4, 2, 2, 2, 1, 2, 5]
def baseStart_3548089 : Nat := 118140960795 + 3548089 * 2 ^ 59
def prefixEnd_3548089 : Nat := 4983230072969 + 3 ^ 40 * 3548089 * 2
def baseEnd_3548089 : Nat := 1214583374620315879446761

theorem tailTrace_3548089 : CollatzResearch.WordTrace tailWord_3548089 prefixEnd_3548089 1214583374620315879446761 := by
  unfold tailWord_3548089
  simp only [CollatzResearch.WordTrace]
  refine ⟨129409437242886993202943321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86272958161924662135295547 129409437242886993202943321)
  ·
    refine ⟨97057077932165244902207491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129409437242886993202943321 97057077932165244902207491)
    ·
      refine ⟨145585616898247867353311237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97057077932165244902207491 145585616898247867353311237)
      ·
        refine ⟨27297303168421475128745857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 145585616898247867353311237 27297303168421475128745857)
        ·
          refine ⟨20472977376316106346559393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27297303168421475128745857 20472977376316106346559393)
          ·
            refine ⟨15354733032237079759919545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20472977376316106346559393 15354733032237079759919545)
            ·
              refine ⟨11516049774177809819939659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15354733032237079759919545 11516049774177809819939659)
              ·
                refine ⟨17274074661266714729909489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11516049774177809819939659 17274074661266714729909489)
                ·
                  refine ⟨12955555995950036047432117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17274074661266714729909489 12955555995950036047432117)
                  ·
                    refine ⟨1214583374620315879446761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12955555995950036047432117 1214583374620315879446761)
                    ·
                      rfl

theorem cell22_3548089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 2, 1, 2, 5].length) (baseStart_3548089 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3548089 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3548089 prefixEnd_3548089 := by exact prefixLift 3548089
  have htrace : WordTrace (prefixWord ++ tailWord_3548089) baseStart_3548089 baseEnd_3548089 := by
    simpa [prefixWord, tailWord_3548089, baseEnd_3548089] using wordTrace_append hprefix tailTrace_3548089
  have hstable : (prefixWord ++ tailWord_3548089).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3548089).length < 2 ^ (prefixWord ++ tailWord_3548089).sum := by decide
  have hdescent : baseEnd_3548089 < baseStart_3548089 := by decide
  rcases family_descends (prefixWord ++ tailWord_3548089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3548121 : List Nat := [1, 2, 1, 2, 5, 1, 2, 3, 1, 4]
def baseStart_3548121 : Nat := 118140960795 + 3548121 * 2 ^ 59
def prefixEnd_3548121 : Nat := 4983230072969 + 3 ^ 40 * 3548121 * 2
def baseEnd_3548121 : Nat := 1214594328874278462646663

theorem tailTrace_3548121 : CollatzResearch.WordTrace tailWord_3548121 prefixEnd_3548121 1214594328874278462646663 := by
  unfold tailWord_3548121
  simp only [CollatzResearch.WordTrace]
  refine ⟨129410604378771062668108217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86273736252514041778738811 129410604378771062668108217)
  ·
    refine ⟨97057953284078297001081163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129410604378771062668108217 97057953284078297001081163)
    ·
      refine ⟨145586929926117445501621745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97057953284078297001081163 145586929926117445501621745)
      ·
        refine ⟨109190197444588084126216309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145586929926117445501621745 109190197444588084126216309)
        ·
          refine ⟨10236581010430132886832779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 109190197444588084126216309 10236581010430132886832779)
          ·
            refine ⟨15354871515645199330249169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10236581010430132886832779 15354871515645199330249169)
            ·
              refine ⟨11516153636733899497686877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15354871515645199330249169 11516153636733899497686877)
              ·
                refine ⟨4318557613775212311632579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11516153636733899497686877 4318557613775212311632579)
                ·
                  refine ⟨6477836420662818467448869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4318557613775212311632579 6477836420662818467448869)
                  ·
                    refine ⟨1214594328874278462646663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6477836420662818467448869 1214594328874278462646663)
                    ·
                      rfl

theorem cell22_3548121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 2, 3, 1, 4].length) (baseStart_3548121 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3548121 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3548121 prefixEnd_3548121 := by exact prefixLift 3548121
  have htrace : WordTrace (prefixWord ++ tailWord_3548121) baseStart_3548121 baseEnd_3548121 := by
    simpa [prefixWord, tailWord_3548121, baseEnd_3548121] using wordTrace_append hprefix tailTrace_3548121
  have hstable : (prefixWord ++ tailWord_3548121).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3548121).length < 2 ^ (prefixWord ++ tailWord_3548121).sum := by decide
  have hdescent : baseEnd_3548121 < baseStart_3548121 := by decide
  rcases family_descends (prefixWord ++ tailWord_3548121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3548136 : List Nat := [2, 1, 4, 1, 1, 1, 2, 6, 4]
def baseStart_3548136 : Nat := 118140960795 + 3548136 * 2 ^ 59
def prefixEnd_3548136 : Nat := 4983230072969 + 3 ^ 40 * 3548136 * 2
def baseEnd_3548136 : Nat := 404866487893607807840539

theorem tailTrace_3548136 : CollatzResearch.WordTrace tailWord_3548136 prefixEnd_3548136 404866487893607807840539 := by
  unfold tailWord_3548136
  simp only [CollatzResearch.WordTrace]
  refine ⟨64705575736858360114952131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86274100982477813486602841 64705575736858360114952131)
  ·
    refine ⟨97058363605287540172428197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64705575736858360114952131 97058363605287540172428197)
    ·
      refine ⟨18198443175991413782330287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 97058363605287540172428197 18198443175991413782330287)
      ·
        refine ⟨27297664763987120673495431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18198443175991413782330287 27297664763987120673495431)
        ·
          refine ⟨40946497145980681010243147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27297664763987120673495431 40946497145980681010243147)
          ·
            refine ⟨61419745718971021515364721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40946497145980681010243147 61419745718971021515364721)
            ·
              refine ⟨46064809289228266136523541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61419745718971021515364721 46064809289228266136523541)
              ·
                refine ⟨2159287935432574975149541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 46064809289228266136523541 2159287935432574975149541)
                ·
                  refine ⟨404866487893607807840539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2159287935432574975149541 404866487893607807840539)
                  ·
                    rfl

theorem cell22_3548136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 6, 4].length) (baseStart_3548136 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3548136 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3548136 prefixEnd_3548136 := by exact prefixLift 3548136
  have htrace : WordTrace (prefixWord ++ tailWord_3548136) baseStart_3548136 baseEnd_3548136 := by
    simpa [prefixWord, tailWord_3548136, baseEnd_3548136] using wordTrace_append hprefix tailTrace_3548136
  have hstable : (prefixWord ++ tailWord_3548136).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3548136).length < 2 ^ (prefixWord ++ tailWord_3548136).sum := by decide
  have hdescent : baseEnd_3548136 < baseStart_3548136 := by decide
  rcases family_descends (prefixWord ++ tailWord_3548136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3548224 : List Nat := [2, 1, 1, 2, 2, 3, 1, 2, 1, 7]
def baseStart_3548224 : Nat := 118140960795 + 3548224 * 2 ^ 59
def prefixEnd_3548224 : Nat := 4983230072969 + 3 ^ 40 * 3548224 * 2
def baseEnd_3548224 : Nat := 1214629587879220527321347

theorem tailTrace_3548224 : CollatzResearch.WordTrace tailWord_3548224 prefixEnd_3548224 1214629587879220527321347 := by
  unfold tailWord_3548224
  simp only [CollatzResearch.WordTrace]
  refine ⟨64707180548698955629553863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86276240731598607506071817 64707180548698955629553863)
  ·
    refine ⟨97060770823048433444330795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64707180548698955629553863 97060770823048433444330795)
    ·
      refine ⟨145591156234572650166496193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97060770823048433444330795 145591156234572650166496193)
      ·
        refine ⟨109193367175929487624872145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145591156234572650166496193 109193367175929487624872145)
        ·
          refine ⟨81895025381947115718654109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109193367175929487624872145 81895025381947115718654109)
          ·
            refine ⟨30710634518230168394495291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81895025381947115718654109 30710634518230168394495291)
            ·
              refine ⟨46065951777345252591742937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30710634518230168394495291 46065951777345252591742937)
              ·
                refine ⟨34549463833008939443807203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46065951777345252591742937 34549463833008939443807203)
                ·
                  refine ⟨51824195749513409165710805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34549463833008939443807203 51824195749513409165710805)
                  ·
                    refine ⟨1214629587879220527321347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 51824195749513409165710805 1214629587879220527321347)
                    ·
                      rfl

theorem cell22_3548224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 2, 1, 7].length) (baseStart_3548224 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3548224 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3548224 prefixEnd_3548224 := by exact prefixLift 3548224
  have htrace : WordTrace (prefixWord ++ tailWord_3548224) baseStart_3548224 baseEnd_3548224 := by
    simpa [prefixWord, tailWord_3548224, baseEnd_3548224] using wordTrace_append hprefix tailTrace_3548224
  have hstable : (prefixWord ++ tailWord_3548224).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3548224).length < 2 ^ (prefixWord ++ tailWord_3548224).sum := by decide
  have hdescent : baseEnd_3548224 < baseStart_3548224 := by decide
  rcases family_descends (prefixWord ++ tailWord_3548224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3548258 : List Nat := [3, 3, 2, 2, 1, 1, 2, 1, 2, 5]
def baseStart_3548258 : Nat := 118140960795 + 3548258 * 2 ^ 59
def prefixEnd_3548258 : Nat := 4983230072969 + 3 ^ 40 * 3548258 * 2
def baseEnd_3548258 : Nat := 1214641226774055771971243

theorem tailTrace_3548258 : CollatzResearch.WordTrace tailWord_3548258 prefixEnd_3548258 1214641226774055771971243 := by
  unfold tailWord_3548258
  simp only [CollatzResearch.WordTrace]
  refine ⟨32353900294818683766461357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86277067452849823377230285 32353900294818683766461357)
  ·
    refine ⟨12132712610557006412423009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32353900294818683766461357 12132712610557006412423009)
    ·
      refine ⟨9099534457917754809317257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12132712610557006412423009 9099534457917754809317257)
      ·
        refine ⟨6824650843438316106987943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9099534457917754809317257 6824650843438316106987943)
        ·
          refine ⟨10236976265157474160481915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6824650843438316106987943 10236976265157474160481915)
          ·
            refine ⟨15355464397736211240722873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10236976265157474160481915 15355464397736211240722873)
            ·
              refine ⟨11516598298302158430542155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15355464397736211240722873 11516598298302158430542155)
              ·
                refine ⟨17274897447453237645813233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11516598298302158430542155 17274897447453237645813233)
                ·
                  refine ⟨12956173085589928234359925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17274897447453237645813233 12956173085589928234359925)
                  ·
                    refine ⟨1214641226774055771971243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12956173085589928234359925 1214641226774055771971243)
                    ·
                      rfl

theorem cell22_3548258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 2, 1, 2, 5].length) (baseStart_3548258 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3548258 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3548258 prefixEnd_3548258 := by exact prefixLift 3548258
  have htrace : WordTrace (prefixWord ++ tailWord_3548258) baseStart_3548258 baseEnd_3548258 := by
    simpa [prefixWord, tailWord_3548258, baseEnd_3548258] using wordTrace_append hprefix tailTrace_3548258
  have hstable : (prefixWord ++ tailWord_3548258).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3548258).length < 2 ^ (prefixWord ++ tailWord_3548258).sum := by decide
  have hdescent : baseEnd_3548258 < baseStart_3548258 := by decide
  rcases family_descends (prefixWord ++ tailWord_3548258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3548288 : List Nat := [2, 1, 1, 2, 1, 3, 5, 3, 4]
def baseStart_3548288 : Nat := 118140960795 + 3548288 * 2 ^ 59
def prefixEnd_3548288 : Nat := 4983230072969 + 3 ^ 40 * 3548288 * 2
def baseEnd_3548288 : Nat := 404883832129048564573717

theorem tailTrace_3548288 : CollatzResearch.WordTrace tailWord_3548288 prefixEnd_3548288 404883832129048564573717 := by
  unfold tailWord_3548288
  simp only [CollatzResearch.WordTrace]
  refine ⟨64708347684583025094718759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86277796912777366792958345 64708347684583025094718759)
  ·
    refine ⟨97062521526874537642078139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64708347684583025094718759 97062521526874537642078139)
    ·
      refine ⟨145593782290311806463117209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97062521526874537642078139 145593782290311806463117209)
      ·
        refine ⟨109195336717733854847337907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145593782290311806463117209 109195336717733854847337907)
        ·
          refine ⟨163793005076600782271006861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109195336717733854847337907 163793005076600782271006861)
          ·
            refine ⟨61422376903725293351627573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 163793005076600782271006861 61422376903725293351627573)
            ·
              refine ⟨5758347834724246251715085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 61422376903725293351627573 5758347834724246251715085)
              ·
                refine ⟨2159380438021592344393157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5758347834724246251715085 2159380438021592344393157)
                ·
                  refine ⟨404883832129048564573717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2159380438021592344393157 404883832129048564573717)
                  ·
                    rfl

theorem cell22_3548288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 5, 3, 4].length) (baseStart_3548288 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3548288 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3548288 prefixEnd_3548288 := by exact prefixLift 3548288
  have htrace : WordTrace (prefixWord ++ tailWord_3548288) baseStart_3548288 baseEnd_3548288 := by
    simpa [prefixWord, tailWord_3548288, baseEnd_3548288] using wordTrace_append hprefix tailTrace_3548288
  have hstable : (prefixWord ++ tailWord_3548288).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3548288).length < 2 ^ (prefixWord ++ tailWord_3548288).sum := by decide
  have hdescent : baseEnd_3548288 < baseStart_3548288 := by decide
  rcases family_descends (prefixWord ++ tailWord_3548288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3548316 : List Nat := [2, 2, 3, 2, 1, 2, 1, 9]
def baseStart_3548316 : Nat := 118140960795 + 3548316 * 2 ^ 59
def prefixEnd_3548316 : Nat := 4983230072969 + 3 ^ 40 * 3548316 * 2
def baseEnd_3548316 : Nat := 134962342373262550446785

theorem tailTrace_3548316 : CollatzResearch.WordTrace tailWord_3548316 prefixEnd_3548316 134962342373262550446785 := by
  unfold tailWord_3548316
  simp only [CollatzResearch.WordTrace]
  refine ⟨64708858306532305485728401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86278477742043073980971201 64708858306532305485728401)
  ·
    refine ⟨48531643729899229114296301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64708858306532305485728401 48531643729899229114296301)
    ·
      refine ⟨18199366398712210917861113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48531643729899229114296301 18199366398712210917861113)
      ·
        refine ⟨13649524799034158188395835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18199366398712210917861113 13649524799034158188395835)
        ·
          refine ⟨20474287198551237282593753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13649524799034158188395835 20474287198551237282593753)
          ·
            refine ⟨15355715398913427961945315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20474287198551237282593753 15355715398913427961945315)
            ·
              refine ⟨23033573098370141942917973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15355715398913427961945315 23033573098370141942917973)
              ·
                refine ⟨134962342373262550446785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 23033573098370141942917973 134962342373262550446785)
                ·
                  rfl

theorem cell22_3548316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 9].length) (baseStart_3548316 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3548316 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3548316 prefixEnd_3548316 := by exact prefixLift 3548316
  have htrace : WordTrace (prefixWord ++ tailWord_3548316) baseStart_3548316 baseEnd_3548316 := by
    simpa [prefixWord, tailWord_3548316, baseEnd_3548316] using wordTrace_append hprefix tailTrace_3548316
  have hstable : (prefixWord ++ tailWord_3548316).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3548316).length < 2 ^ (prefixWord ++ tailWord_3548316).sum := by decide
  have hdescent : baseEnd_3548316 < baseStart_3548316 := by decide
  rcases family_descends (prefixWord ++ tailWord_3548316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3548412 : List Nat := [2, 2, 2, 1, 6, 1, 1, 2, 5]
def baseStart_3548412 : Nat := 118140960795 + 3548412 * 2 ^ 59
def prefixEnd_3548412 : Nat := 4983230072969 + 3 ^ 40 * 3548412 * 2
def baseEnd_3548412 : Nat := 404897981373750234540257

theorem tailTrace_3548412 : CollatzResearch.WordTrace tailWord_3548412 prefixEnd_3548412 404897981373750234540257 := by
  unfold tailWord_3548412
  simp only [CollatzResearch.WordTrace]
  refine ⟨64710609010358409683475745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86280812013811212911300993 64710609010358409683475745)
  ·
    refine ⟨48532956757768807262606809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64710609010358409683475745 48532956757768807262606809)
    ·
      refine ⟨36399717568326605446955107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48532956757768807262606809 36399717568326605446955107)
      ·
        refine ⟨54599576352489908170432661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36399717568326605446955107 54599576352489908170432661)
        ·
          refine ⟨2559355141522964445489031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 54599576352489908170432661 2559355141522964445489031)
          ·
            refine ⟨3839032712284446668233547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2559355141522964445489031 3839032712284446668233547)
            ·
              refine ⟨5758549068426670002350321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3839032712284446668233547 5758549068426670002350321)
              ·
                refine ⟨4318911801320002501762741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5758549068426670002350321 4318911801320002501762741)
                ·
                  refine ⟨404897981373750234540257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4318911801320002501762741 404897981373750234540257)
                  ·
                    rfl

theorem cell22_3548412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 6, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 6, 1, 1, 2, 5].length) (baseStart_3548412 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3548412 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3548412 prefixEnd_3548412 := by exact prefixLift 3548412
  have htrace : WordTrace (prefixWord ++ tailWord_3548412) baseStart_3548412 baseEnd_3548412 := by
    simpa [prefixWord, tailWord_3548412, baseEnd_3548412] using wordTrace_append hprefix tailTrace_3548412
  have hstable : (prefixWord ++ tailWord_3548412).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3548412).length < 2 ^ (prefixWord ++ tailWord_3548412).sum := by decide
  have hdescent : baseEnd_3548412 < baseStart_3548412 := by decide
  rcases family_descends (prefixWord ++ tailWord_3548412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3548453 : List Nat := [1, 3, 1, 2, 4, 1, 2, 1, 1, 6]
def baseStart_3548453 : Nat := 118140960795 + 3548453 * 2 ^ 59
def prefixEnd_3548453 : Nat := 4983230072969 + 3 ^ 40 * 3548453 * 2
def baseEnd_3548453 : Nat := 1214707979259140263345645

theorem tailTrace_3548453 : CollatzResearch.WordTrace tailWord_3548453 prefixEnd_3548453 1214707979259140263345645 := by
  unfold tailWord_3548453
  simp only [CollatzResearch.WordTrace]
  refine ⟨129422713413568283369194013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86281808942378855579462675 129422713413568283369194013)
  ·
    refine ⟨48533517530088106263447755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129422713413568283369194013 48533517530088106263447755)
    ·
      refine ⟨72800276295132159395171633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48533517530088106263447755 72800276295132159395171633)
      ·
        refine ⟨54600207221349119546378725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72800276295132159395171633 54600207221349119546378725)
        ·
          refine ⟨10237538854002959914946011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 54600207221349119546378725 10237538854002959914946011)
          ·
            refine ⟨15356308281004439872419017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10237538854002959914946011 15356308281004439872419017)
            ·
              refine ⟨11517231210753329904314263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15356308281004439872419017 11517231210753329904314263)
              ·
                refine ⟨17275846816129994856471395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11517231210753329904314263 17275846816129994856471395)
                ·
                  refine ⟨25913770224194992284707093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17275846816129994856471395 25913770224194992284707093)
                  ·
                    refine ⟨1214707979259140263345645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25913770224194992284707093 1214707979259140263345645)
                    ·
                      rfl

theorem cell22_3548453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 2, 1, 1, 6].length) (baseStart_3548453 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3548453 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3548453 prefixEnd_3548453 := by exact prefixLift 3548453
  have htrace : WordTrace (prefixWord ++ tailWord_3548453) baseStart_3548453 baseEnd_3548453 := by
    simpa [prefixWord, tailWord_3548453, baseEnd_3548453] using wordTrace_append hprefix tailTrace_3548453
  have hstable : (prefixWord ++ tailWord_3548453).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3548453).length < 2 ^ (prefixWord ++ tailWord_3548453).sum := by decide
  have hdescent : baseEnd_3548453 < baseStart_3548453 := by decide
  rcases family_descends (prefixWord ++ tailWord_3548453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3548500 : List Nat := [2, 4, 1, 1, 2, 1, 2, 1, 5, 3]
def baseStart_3548500 : Nat := 118140960795 + 3548500 * 2 ^ 59
def prefixEnd_3548500 : Nat := 4983230072969 + 3 ^ 40 * 3548500 * 2
def baseEnd_3548500 : Nat := 1214724068319647807420501

theorem tailTrace_3548500 : CollatzResearch.WordTrace tailWord_3548500 prefixEnd_3548500 1214724068319647807420501 := by
  unfold tailWord_3548500
  simp only [CollatzResearch.WordTrace]
  refine ⟨64712213822199005198077477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86282951762932006930769969 64712213822199005198077477)
  ·
    refine ⟨12133540091662313474639527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 64712213822199005198077477 12133540091662313474639527)
    ·
      refine ⟨18200310137493470211959291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12133540091662313474639527 18200310137493470211959291)
      ·
        refine ⟨27300465206240205317938937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18200310137493470211959291 27300465206240205317938937)
        ·
          refine ⟨20475348904680153988454203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27300465206240205317938937 20475348904680153988454203)
          ·
            refine ⟨30713023357020230982681305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20475348904680153988454203 30713023357020230982681305)
            ·
              refine ⟨23034767517765173237010979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30713023357020230982681305 23034767517765173237010979)
              ·
                refine ⟨34552151276647759855516469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23034767517765173237010979 34552151276647759855516469)
                ·
                  refine ⟨3239264182185727486454669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 34552151276647759855516469 3239264182185727486454669)
                  ·
                    refine ⟨1214724068319647807420501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3239264182185727486454669 1214724068319647807420501)
                    ·
                      rfl

theorem cell22_3548500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 1, 5, 3].length) (baseStart_3548500 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3548500 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3548500 prefixEnd_3548500 := by exact prefixLift 3548500
  have htrace : WordTrace (prefixWord ++ tailWord_3548500) baseStart_3548500 baseEnd_3548500 := by
    simpa [prefixWord, tailWord_3548500, baseEnd_3548500] using wordTrace_append hprefix tailTrace_3548500
  have hstable : (prefixWord ++ tailWord_3548500).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3548500).length < 2 ^ (prefixWord ++ tailWord_3548500).sum := by decide
  have hdescent : baseEnd_3548500 < baseStart_3548500 := by decide
  rcases family_descends (prefixWord ++ tailWord_3548500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3548517 : List Nat := [1, 3, 1, 3, 1, 2, 2, 5, 1, 3]
def baseStart_3548517 : Nat := 118140960795 + 3548517 * 2 ^ 59
def prefixEnd_3548517 : Nat := 4983230072969 + 3 ^ 40 * 3548517 * 2
def baseEnd_3548517 : Nat := 1214729887767065429745449

theorem tailTrace_3548517 : CollatzResearch.WordTrace tailWord_3548517 prefixEnd_3548517 1214729887767065429745449 := by
  unfold tailWord_3548517
  simp only [CollatzResearch.WordTrace]
  refine ⟨129425047685336422299523805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86283365123557614866349203 129425047685336422299523805)
  ·
    refine ⟨48534392882001158362321427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129425047685336422299523805 48534392882001158362321427)
    ·
      refine ⟨72801589323001737543482141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48534392882001158362321427 72801589323001737543482141)
      ·
        refine ⟨27300595996125651578805803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72801589323001737543482141 27300595996125651578805803)
        ·
          refine ⟨40950893994188477368208705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27300595996125651578805803 40950893994188477368208705)
          ·
            refine ⟨30713170495641358026156529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40950893994188477368208705 30713170495641358026156529)
            ·
              refine ⟨23034877871731018519617397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30713170495641358026156529 23034877871731018519617397)
              ·
                refine ⟨2159519800474782986214131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23034877871731018519617397 2159519800474782986214131)
                ·
                  refine ⟨3239279700712174479321197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2159519800474782986214131 3239279700712174479321197)
                  ·
                    refine ⟨1214729887767065429745449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3239279700712174479321197 1214729887767065429745449)
                    ·
                      rfl

theorem cell22_3548517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 5, 1, 3].length) (baseStart_3548517 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3548517 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3548517 prefixEnd_3548517 := by exact prefixLift 3548517
  have htrace : WordTrace (prefixWord ++ tailWord_3548517) baseStart_3548517 baseEnd_3548517 := by
    simpa [prefixWord, tailWord_3548517, baseEnd_3548517] using wordTrace_append hprefix tailTrace_3548517
  have hstable : (prefixWord ++ tailWord_3548517).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3548517).length < 2 ^ (prefixWord ++ tailWord_3548517).sum := by decide
  have hdescent : baseEnd_3548517 < baseStart_3548517 := by decide
  rcases family_descends (prefixWord ++ tailWord_3548517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3548528 : List Nat := [2, 1, 1, 1, 4, 2, 2, 2, 2, 5]
def baseStart_3548528 : Nat := 118140960795 + 3548528 * 2 ^ 59
def prefixEnd_3548528 : Nat := 4983230072969 + 3 ^ 40 * 3548528 * 2
def baseEnd_3548528 : Nat := 1214733653291865067720415

theorem tailTrace_3548528 : CollatzResearch.WordTrace tailWord_3548528 prefixEnd_3548528 1214733653291865067720415 := by
  unfold tailWord_3548528
  simp only [CollatzResearch.WordTrace]
  refine ⟨64712724444148285589087119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86283632592197714118782825 64712724444148285589087119)
  ·
    refine ⟨97069086666222428383630679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64712724444148285589087119 97069086666222428383630679)
    ·
      refine ⟨145603629999333642575446019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97069086666222428383630679 145603629999333642575446019)
      ·
        refine ⟨218405444999000463863169029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145603629999333642575446019 218405444999000463863169029)
        ·
          refine ⟨40951020937312586974344193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 218405444999000463863169029 40951020937312586974344193)
          ·
            refine ⟨30713265702984440230758145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40951020937312586974344193 30713265702984440230758145)
            ·
              refine ⟨23034949277238330173068609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30713265702984440230758145 23034949277238330173068609)
              ·
                refine ⟨17276211957928747629801457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23034949277238330173068609 17276211957928747629801457)
                ·
                  refine ⟨12957158968446560722351093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17276211957928747629801457 12957158968446560722351093)
                  ·
                    refine ⟨1214733653291865067720415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12957158968446560722351093 1214733653291865067720415)
                    ·
                      rfl

theorem cell22_3548528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 2, 2, 5].length) (baseStart_3548528 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3548528 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3548528 prefixEnd_3548528 := by exact prefixLift 3548528
  have htrace : WordTrace (prefixWord ++ tailWord_3548528) baseStart_3548528 baseEnd_3548528 := by
    simpa [prefixWord, tailWord_3548528, baseEnd_3548528] using wordTrace_append hprefix tailTrace_3548528
  have hstable : (prefixWord ++ tailWord_3548528).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3548528).length < 2 ^ (prefixWord ++ tailWord_3548528).sum := by decide
  have hdescent : baseEnd_3548528 < baseStart_3548528 := by decide
  rcases family_descends (prefixWord ++ tailWord_3548528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3548530 : List Nat := [3, 2, 1, 2, 1, 2, 4, 2, 5]
def baseStart_3548530 : Nat := 118140960795 + 3548530 * 2 ^ 59
def prefixEnd_3548530 : Nat := 4983230072969 + 3 ^ 40 * 3548530 * 2
def baseEnd_3548530 : Nat := 404911445977579243056803

theorem tailTrace_3548530 : CollatzResearch.WordTrace tailWord_3548530 prefixEnd_3548530 404911445977579243056803 := by
  unfold tailWord_3548530
  simp only [CollatzResearch.WordTrace]
  refine ⟨32356380458572331379936761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86283681222859550346498029 32356380458572331379936761)
  ·
    refine ⟨24267285343929248534952571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32356380458572331379936761 24267285343929248534952571)
    ·
      refine ⟨36400928015893872802428857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24267285343929248534952571 36400928015893872802428857)
      ·
        refine ⟨27300696011920404601821643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36400928015893872802428857 27300696011920404601821643)
        ·
          refine ⟨40951044017880606902732465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27300696011920404601821643 40951044017880606902732465)
          ·
            refine ⟨30713283013410455177049349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40951044017880606902732465 30713283013410455177049349)
            ·
              refine ⟨5758740565014460345696753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30713283013410455177049349 5758740565014460345696753)
              ·
                refine ⟨4319055423760845259272565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5758740565014460345696753 4319055423760845259272565)
                ·
                  refine ⟨404911445977579243056803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4319055423760845259272565 404911445977579243056803)
                  ·
                    rfl

theorem cell22_3548530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 4, 2, 5].length) (baseStart_3548530 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3548530 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3548530 prefixEnd_3548530 := by exact prefixLift 3548530
  have htrace : WordTrace (prefixWord ++ tailWord_3548530) baseStart_3548530 baseEnd_3548530 := by
    simpa [prefixWord, tailWord_3548530, baseEnd_3548530] using wordTrace_append hprefix tailTrace_3548530
  have hstable : (prefixWord ++ tailWord_3548530).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3548530).length < 2 ^ (prefixWord ++ tailWord_3548530).sum := by decide
  have hdescent : baseEnd_3548530 < baseStart_3548530 := by decide
  rcases family_descends (prefixWord ++ tailWord_3548530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3548620 : List Nat := [2, 2, 1, 4, 2, 2, 1, 8]
def baseStart_3548620 : Nat := 118140960795 + 3548620 * 2 ^ 59
def prefixEnd_3548620 : Nat := 4983230072969 + 3 ^ 40 * 3548620 * 2
def baseEnd_3548620 : Nat := 134973905196889721602237

theorem tailTrace_3548620 : CollatzResearch.WordTrace tailWord_3548620 prefixEnd_3548620 134973905196889721602237 := by
  unfold tailWord_3548620
  simp only [CollatzResearch.WordTrace]
  refine ⟨64714402201981635445261657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86285869602642180593682209 64714402201981635445261657)
  ·
    refine ⟨48535801651486226583946243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64714402201981635445261657 48535801651486226583946243)
    ·
      refine ⟨72803702477229339875919365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48535801651486226583946243 72803702477229339875919365)
      ·
        refine ⟨13650694214480501226734881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 72803702477229339875919365 13650694214480501226734881)
        ·
          refine ⟨10238020660860375920051161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13650694214480501226734881 10238020660860375920051161)
          ·
            refine ⟨7678515495645281940038371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10238020660860375920051161 7678515495645281940038371)
            ·
              refine ⟨11517773243467922910057557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7678515495645281940038371 11517773243467922910057557)
              ·
                refine ⟨134973905196889721602237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11517773243467922910057557 134973905196889721602237)
                ·
                  rfl

theorem cell22_3548620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 1, 8].length) (baseStart_3548620 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3548620 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3548620 prefixEnd_3548620 := by exact prefixLift 3548620
  have htrace : WordTrace (prefixWord ++ tailWord_3548620) baseStart_3548620 baseEnd_3548620 := by
    simpa [prefixWord, tailWord_3548620, baseEnd_3548620] using wordTrace_append hprefix tailTrace_3548620
  have hstable : (prefixWord ++ tailWord_3548620).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3548620).length < 2 ^ (prefixWord ++ tailWord_3548620).sum := by decide
  have hdescent : baseEnd_3548620 < baseStart_3548620 := by decide
  rcases family_descends (prefixWord ++ tailWord_3548620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3548759 : List Nat := [1, 1, 3, 2, 2, 3, 3, 2, 2, 3]
def baseStart_3548759 : Nat := 118140960795 + 3548759 * 2 ^ 59
def prefixEnd_3548759 : Nat := 4983230072969 + 3 ^ 40 * 3548759 * 2
def baseEnd_3548759 : Nat := 1214812729312657465194707

theorem tailTrace_3548759 : CollatzResearch.WordTrace tailWord_3548759 prefixEnd_3548759 1214812729312657465194707 := by
  unfold tailWord_3548759
  simp only [CollatzResearch.WordTrace]
  refine ⟨129433874150459697629833331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86289249433639798419888887 129433874150459697629833331)
  ·
    refine ⟨194150811225689546444749997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129433874150459697629833331 194150811225689546444749997)
    ·
      refine ⟨72806554209633579916781249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 194150811225689546444749997 72806554209633579916781249)
      ·
        refine ⟨54604915657225184937585937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72806554209633579916781249 54604915657225184937585937)
        ·
          refine ⟨40953686742918888703189453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54604915657225184937585937 40953686742918888703189453)
          ·
            refine ⟨15357632528594583263696045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40953686742918888703189453 15357632528594583263696045)
            ·
              refine ⟨5759112198222968723886017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15357632528594583263696045 5759112198222968723886017)
              ·
                refine ⟨4319334148667226542914513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5759112198222968723886017 4319334148667226542914513)
                ·
                  refine ⟨3239500611500419907185885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4319334148667226542914513 3239500611500419907185885)
                  ·
                    refine ⟨1214812729312657465194707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3239500611500419907185885 1214812729312657465194707)
                    ·
                      rfl

theorem cell22_3548759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 3, 2, 2, 3].length) (baseStart_3548759 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3548759 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3548759 prefixEnd_3548759 := by exact prefixLift 3548759
  have htrace : WordTrace (prefixWord ++ tailWord_3548759) baseStart_3548759 baseEnd_3548759 := by
    simpa [prefixWord, tailWord_3548759, baseEnd_3548759] using wordTrace_append hprefix tailTrace_3548759
  have hstable : (prefixWord ++ tailWord_3548759).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3548759).length < 2 ^ (prefixWord ++ tailWord_3548759).sum := by decide
  have hdescent : baseEnd_3548759 < baseStart_3548759 := by decide
  rcases family_descends (prefixWord ++ tailWord_3548759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3548785 : List Nat := [1, 2, 2, 2, 1, 1, 1, 4, 2, 6]
def baseStart_3548785 : Nat := 118140960795 + 3548785 * 2 ^ 59
def prefixEnd_3548785 : Nat := 4983230072969 + 3 ^ 40 * 3548785 * 2
def baseEnd_3548785 : Nat := 1214821629644002064044627

theorem tailTrace_3548785 : CollatzResearch.WordTrace tailWord_3548785 prefixEnd_3548785 1214821629644002064044627 := by
  unfold tailWord_3548785
  simp only [CollatzResearch.WordTrace]
  refine ⟨129434822448365504070279809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86289881632243669380186539 129434822448365504070279809)
  ·
    refine ⟨97076116836274128052709857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129434822448365504070279809 97076116836274128052709857)
    ·
      refine ⟨72807087627205596039532393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97076116836274128052709857 72807087627205596039532393)
      ·
        refine ⟨54605315720404197029649295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72807087627205596039532393 54605315720404197029649295)
        ·
          refine ⟨81907973580606295544473943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54605315720404197029649295 81907973580606295544473943)
          ·
            refine ⟨122861960370909443316710915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81907973580606295544473943 122861960370909443316710915)
            ·
              refine ⟨184292940556364164975066373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122861960370909443316710915 184292940556364164975066373)
              ·
                refine ⟨34554926354318280932824945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 184292940556364164975066373 34554926354318280932824945)
                ·
                  refine ⟨25916194765738710699618709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34554926354318280932824945 25916194765738710699618709)
                  ·
                    refine ⟨1214821629644002064044627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25916194765738710699618709 1214821629644002064044627)
                    ·
                      rfl

theorem cell22_3548785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 4, 2, 6].length) (baseStart_3548785 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3548785 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3548785 prefixEnd_3548785 := by exact prefixLift 3548785
  have htrace : WordTrace (prefixWord ++ tailWord_3548785) baseStart_3548785 baseEnd_3548785 := by
    simpa [prefixWord, tailWord_3548785, baseEnd_3548785] using wordTrace_append hprefix tailTrace_3548785
  have hstable : (prefixWord ++ tailWord_3548785).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3548785).length < 2 ^ (prefixWord ++ tailWord_3548785).sum := by decide
  have hdescent : baseEnd_3548785 < baseStart_3548785 := by decide
  rcases family_descends (prefixWord ++ tailWord_3548785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3548789 : List Nat := [1, 3, 4, 2, 1, 1, 4, 6]
def baseStart_3548789 : Nat := 118140960795 + 3548789 * 2 ^ 59
def prefixEnd_3548789 : Nat := 4983230072969 + 3 ^ 40 * 3548789 * 2
def baseEnd_3548789 : Nat := 134980333213971931882735

theorem tailTrace_3548789 : CollatzResearch.WordTrace tailWord_3548789 prefixEnd_3548789 134980333213971931882735 := by
  unfold tailWord_3548789
  simp only [CollatzResearch.WordTrace]
  refine ⟨129434968340351012753425421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86289978893567341835616947 129434968340351012753425421)
  ·
    refine ⟨48538113127631629782534533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129434968340351012753425421 48538113127631629782534533)
    ·
      refine ⟨9100896211430930584225225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48538113127631629782534533 9100896211430930584225225)
      ·
        refine ⟨6825672158573197938168919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9100896211430930584225225 6825672158573197938168919)
        ·
          refine ⟨10238508237859796907253379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6825672158573197938168919 10238508237859796907253379)
          ·
            refine ⟨15357762356789695360880069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10238508237859796907253379 15357762356789695360880069)
            ·
              refine ⟨2879580441898067880165013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15357762356789695360880069 2879580441898067880165013)
              ·
                refine ⟨134980333213971931882735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2879580441898067880165013 134980333213971931882735)
                ·
                  rfl

theorem cell22_3548789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 4, 6].length) (baseStart_3548789 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3548789 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3548789 prefixEnd_3548789 := by exact prefixLift 3548789
  have htrace : WordTrace (prefixWord ++ tailWord_3548789) baseStart_3548789 baseEnd_3548789 := by
    simpa [prefixWord, tailWord_3548789, baseEnd_3548789] using wordTrace_append hprefix tailTrace_3548789
  have hstable : (prefixWord ++ tailWord_3548789).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3548789).length < 2 ^ (prefixWord ++ tailWord_3548789).sum := by decide
  have hdescent : baseEnd_3548789 < baseStart_3548789 := by decide
  rcases family_descends (prefixWord ++ tailWord_3548789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3548800 : List Nat := [2, 1, 1, 2, 1, 4, 1, 1, 9]
def baseStart_3548800 : Nat := 118140960795 + 3548800 * 2 ^ 59
def prefixEnd_3548800 : Nat := 4983230072969 + 3 ^ 40 * 3548800 * 2
def baseEnd_3548800 : Nat := 404942254816849008306527

theorem tailTrace_3548800 : CollatzResearch.WordTrace tailWord_3548800 prefixEnd_3548800 404942254816849008306527 := by
  unfold tailWord_3548800
  simp only [CollatzResearch.WordTrace]
  refine ⟨64717684771655580816037927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86290246362207441088050569 64717684771655580816037927)
  ·
    refine ⟨97076527157483371224056891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64717684771655580816037927 97076527157483371224056891)
    ·
      refine ⟨145614790736225056836085337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97076527157483371224056891 145614790736225056836085337)
      ·
        refine ⟨109211093052168792627064003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145614790736225056836085337 109211093052168792627064003)
        ·
          refine ⟨163816639578253188940596005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109211093052168792627064003 163816639578253188940596005)
          ·
            refine ⟨30715619920922472926361751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 163816639578253188940596005 30715619920922472926361751)
            ·
              refine ⟨46073429881383709389542627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30715619920922472926361751 46073429881383709389542627)
              ·
                refine ⟨69110144822075564084313941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46073429881383709389542627 69110144822075564084313941)
                ·
                  refine ⟨404942254816849008306527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 69110144822075564084313941 404942254816849008306527)
                  ·
                    rfl

theorem cell22_3548800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 1, 9].length) (baseStart_3548800 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3548800 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3548800 prefixEnd_3548800 := by exact prefixLift 3548800
  have htrace : WordTrace (prefixWord ++ tailWord_3548800) baseStart_3548800 baseEnd_3548800 := by
    simpa [prefixWord, tailWord_3548800, baseEnd_3548800] using wordTrace_append hprefix tailTrace_3548800
  have hstable : (prefixWord ++ tailWord_3548800).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3548800).length < 2 ^ (prefixWord ++ tailWord_3548800).sum := by decide
  have hdescent : baseEnd_3548800 < baseStart_3548800 := by decide
  rcases family_descends (prefixWord ++ tailWord_3548800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3548847 : List Nat := [1, 1, 2, 1, 2, 4, 3, 1, 3, 4]
def baseStart_3548847 : Nat := 118140960795 + 3548847 * 2 ^ 59
def prefixEnd_3548847 : Nat := 4983230072969 + 3 ^ 40 * 3548847 * 2
def baseEnd_3548847 : Nat := 1214842853511054568994437

theorem tailTrace_3548847 : CollatzResearch.WordTrace tailWord_3548847 prefixEnd_3548847 1214842853511054568994437 := by
  unfold tailWord_3548847
  simp only [CollatzResearch.WordTrace]
  refine ⟨129437083774140888659036795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86291389182760592439357863 129437083774140888659036795)
  ·
    refine ⟨194155625661211332988555193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129437083774140888659036795 194155625661211332988555193)
    ·
      refine ⟨145616719245908499741416395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 194155625661211332988555193 145616719245908499741416395)
      ·
        refine ⟨218425078868862749612124593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145616719245908499741416395 218425078868862749612124593)
        ·
          refine ⟨163818809151647062209093445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 218425078868862749612124593 163818809151647062209093445)
          ·
            refine ⟨30716026715933824164205021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 163818809151647062209093445 30716026715933824164205021)
            ·
              refine ⟨11518510018475184061576883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30716026715933824164205021 11518510018475184061576883)
              ·
                refine ⟨17277765027712776092365325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11518510018475184061576883 17277765027712776092365325)
                ·
                  refine ⟨6479161885392291034636997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17277765027712776092365325 6479161885392291034636997)
                  ·
                    refine ⟨1214842853511054568994437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6479161885392291034636997 1214842853511054568994437)
                    ·
                      rfl

theorem cell22_3548847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 3, 1, 3, 4].length) (baseStart_3548847 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3548847 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3548847 prefixEnd_3548847 := by exact prefixLift 3548847
  have htrace : WordTrace (prefixWord ++ tailWord_3548847) baseStart_3548847 baseEnd_3548847 := by
    simpa [prefixWord, tailWord_3548847, baseEnd_3548847] using wordTrace_append hprefix tailTrace_3548847
  have hstable : (prefixWord ++ tailWord_3548847).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3548847).length < 2 ^ (prefixWord ++ tailWord_3548847).sum := by decide
  have hdescent : baseEnd_3548847 < baseStart_3548847 := by decide
  rcases family_descends (prefixWord ++ tailWord_3548847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3548909 : List Nat := [1, 5, 1, 2, 1, 3, 1, 1, 1, 6]
def baseStart_3548909 : Nat := 118140960795 + 3548909 * 2 ^ 59
def prefixEnd_3548909 : Nat := 4983230072969 + 3 ^ 40 * 3548909 * 2
def baseEnd_3548909 : Nat := 1214864077378107073944247

theorem tailTrace_3548909 : CollatzResearch.WordTrace tailWord_3548909 prefixEnd_3548909 1214864077378107073944247 := by
  unfold tailWord_3548909
  simp only [CollatzResearch.WordTrace]
  refine ⟨129439345099916273247793781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86292896733277515498529187 129439345099916273247793781)
  ·
    refine ⟨12134938603117150616980667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 129439345099916273247793781 12134938603117150616980667)
    ·
      refine ⟨18202407904675725925471001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12134938603117150616980667 18202407904675725925471001)
      ·
        refine ⟨13651805928506794444103251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18202407904675725925471001 13651805928506794444103251)
        ·
          refine ⟨20477708892760191666154877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13651805928506794444103251 20477708892760191666154877)
          ·
            refine ⟨7679140834785071874808079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20477708892760191666154877 7679140834785071874808079)
            ·
              refine ⟨11518711252177607812212119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7679140834785071874808079 11518711252177607812212119)
              ·
                refine ⟨17278066878266411718318179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11518711252177607812212119 17278066878266411718318179)
                ·
                  refine ⟨25917100317399617577477269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17278066878266411718318179 25917100317399617577477269)
                  ·
                    refine ⟨1214864077378107073944247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25917100317399617577477269 1214864077378107073944247)
                    ·
                      rfl

theorem cell22_3548909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 1, 1, 1, 6].length) (baseStart_3548909 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3548909 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3548909 prefixEnd_3548909 := by exact prefixLift 3548909
  have htrace : WordTrace (prefixWord ++ tailWord_3548909) baseStart_3548909 baseEnd_3548909 := by
    simpa [prefixWord, tailWord_3548909, baseEnd_3548909] using wordTrace_append hprefix tailTrace_3548909
  have hstable : (prefixWord ++ tailWord_3548909).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3548909).length < 2 ^ (prefixWord ++ tailWord_3548909).sum := by decide
  have hdescent : baseEnd_3548909 < baseStart_3548909 := by decide
  rcases family_descends (prefixWord ++ tailWord_3548909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3548939 : List Nat := [1, 1, 1, 1, 5, 1, 3, 3, 3, 3]
def baseStart_3548939 : Nat := 118140960795 + 3548939 * 2 ^ 59
def prefixEnd_3548939 : Nat := 4983230072969 + 3 ^ 40 * 3548939 * 2
def baseEnd_3548939 : Nat := 1214874346991196995694155

theorem tailTrace_3548939 : CollatzResearch.WordTrace tailWord_3548939 prefixEnd_3548939 1214874346991196995694155 := by
  unfold tailWord_3548939
  simp only [CollatzResearch.WordTrace]
  refine ⟨129440439289807588371385871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86293626193205058914257247 129440439289807588371385871)
  ·
    refine ⟨194160658934711382557078807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129440439289807588371385871 194160658934711382557078807)
    ·
      refine ⟨291240988402067073835618211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194160658934711382557078807 291240988402067073835618211)
      ·
        refine ⟨436861482603100610753427317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 291240988402067073835618211 436861482603100610753427317)
        ·
          refine ⟨40955763994040682258133811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 436861482603100610753427317 40955763994040682258133811)
          ·
            refine ⟨61433645991061023387200717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40955763994040682258133811 61433645991061023387200717)
            ·
              refine ⟨23037617246647883770200269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61433645991061023387200717 23037617246647883770200269)
              ·
                refine ⟨8639106467492956413825101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23037617246647883770200269 8639106467492956413825101)
                ·
                  refine ⟨3239664925309858655184413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8639106467492956413825101 3239664925309858655184413)
                  ·
                    refine ⟨1214874346991196995694155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3239664925309858655184413 1214874346991196995694155)
                    ·
                      rfl

theorem cell22_3548939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 3, 3, 3].length) (baseStart_3548939 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3548939 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3548939 prefixEnd_3548939 := by exact prefixLift 3548939
  have htrace : WordTrace (prefixWord ++ tailWord_3548939) baseStart_3548939 baseEnd_3548939 := by
    simpa [prefixWord, tailWord_3548939, baseEnd_3548939] using wordTrace_append hprefix tailTrace_3548939
  have hstable : (prefixWord ++ tailWord_3548939).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3548939).length < 2 ^ (prefixWord ++ tailWord_3548939).sum := by decide
  have hdescent : baseEnd_3548939 < baseStart_3548939 := by decide
  rcases family_descends (prefixWord ++ tailWord_3548939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3548958 : List Nat := [4, 3, 2, 2, 1, 1, 1, 8]
def baseStart_3548958 : Nat := 118140960795 + 3548958 * 2 ^ 59
def prefixEnd_3548958 : Nat := 4983230072969 + 3 ^ 40 * 3548958 * 2
def baseEnd_3548958 : Nat := 134986761231054142163233

theorem tailTrace_3548958 : CollatzResearch.WordTrace tailWord_3548958 prefixEnd_3548958 134986761231054142163233 := by
  unfold tailWord_3548958
  simp only [CollatzResearch.WordTrace]
  refine ⟨16180141534592344327040941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 86294088184492503077551685 16180141534592344327040941)
  ·
    refine ⟨6067553075472129122640353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16180141534592344327040941 6067553075472129122640353)
    ·
      refine ⟨4550664806604096841980265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6067553075472129122640353 4550664806604096841980265)
      ·
        refine ⟨3412998604953072631485199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4550664806604096841980265 3412998604953072631485199)
        ·
          refine ⟨5119497907429608947227799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3412998604953072631485199 5119497907429608947227799)
          ·
            refine ⟨7679246861144413420841699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5119497907429608947227799 7679246861144413420841699)
            ·
              refine ⟨11518870291716620131262549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7679246861144413420841699 11518870291716620131262549)
              ·
                refine ⟨134986761231054142163233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11518870291716620131262549 134986761231054142163233)
                ·
                  rfl

theorem cell22_3548958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 1, 8].length) (baseStart_3548958 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3548958 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3548958 prefixEnd_3548958 := by exact prefixLift 3548958
  have htrace : WordTrace (prefixWord ++ tailWord_3548958) baseStart_3548958 baseEnd_3548958 := by
    simpa [prefixWord, tailWord_3548958, baseEnd_3548958] using wordTrace_append hprefix tailTrace_3548958
  have hstable : (prefixWord ++ tailWord_3548958).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3548958).length < 2 ^ (prefixWord ++ tailWord_3548958).sum := by decide
  have hdescent : baseEnd_3548958 < baseStart_3548958 := by decide
  rcases family_descends (prefixWord ++ tailWord_3548958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3549031 : List Nat := [1, 1, 5, 1, 2, 1, 2, 5, 4]
def baseStart_3549031 : Nat := 118140960795 + 3549031 * 2 ^ 59
def prefixEnd_3549031 : Nat := 4983230072969 + 3 ^ 40 * 3549031 * 2
def baseEnd_3549031 : Nat := 404968613490446474131291

theorem tailTrace_3549031 : CollatzResearch.WordTrace tailWord_3549031 prefixEnd_3549031 404968613490446474131291 := by
  unfold tailWord_3549031
  simp only [CollatzResearch.WordTrace]
  refine ⟨129443794805474288083734947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86295863203649525389156631 129443794805474288083734947)
  ·
    refine ⟨194165692208211432125602421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129443794805474288083734947 194165692208211432125602421)
    ·
      refine ⟨18203033644519821761775227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 194165692208211432125602421 18203033644519821761775227)
      ·
        refine ⟨27304550466779732642662841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18203033644519821761775227 27304550466779732642662841)
        ·
          refine ⟨20478412850084799481997131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27304550466779732642662841 20478412850084799481997131)
          ·
            refine ⟨30717619275127199222995697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20478412850084799481997131 30717619275127199222995697)
            ·
              refine ⟨23038214456345399417246773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30717619275127199222995697 23038214456345399417246773)
              ·
                refine ⟨2159832605282381195366885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23038214456345399417246773 2159832605282381195366885)
                ·
                  refine ⟨404968613490446474131291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2159832605282381195366885 404968613490446474131291)
                  ·
                    rfl

theorem cell22_3549031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 5, 4].length) (baseStart_3549031 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3549031 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3549031 prefixEnd_3549031 := by exact prefixLift 3549031
  have htrace : WordTrace (prefixWord ++ tailWord_3549031) baseStart_3549031 baseEnd_3549031 := by
    simpa [prefixWord, tailWord_3549031, baseEnd_3549031] using wordTrace_append hprefix tailTrace_3549031
  have hstable : (prefixWord ++ tailWord_3549031).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3549031).length < 2 ^ (prefixWord ++ tailWord_3549031).sum := by decide
  have hdescent : baseEnd_3549031 < baseStart_3549031 := by decide
  rcases family_descends (prefixWord ++ tailWord_3549031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3549059 : List Nat := [1, 1, 1, 3, 4, 2, 3, 7]
def baseStart_3549059 : Nat := 118140960795 + 3549059 * 2 ^ 59
def prefixEnd_3549059 : Nat := 4983230072969 + 3 ^ 40 * 3549059 * 2
def baseEnd_3549059 : Nat := 134990602827061853632643

theorem tailTrace_3549059 : CollatzResearch.WordTrace tailWord_3549059 prefixEnd_3549059 134990602827061853632643 := by
  unfold tailWord_3549059
  simp only [CollatzResearch.WordTrace]
  refine ⟨129444816049372848865754231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86296544032915232577169487 129444816049372848865754231)
  ·
    refine ⟨194167224074059273298631347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129444816049372848865754231 194167224074059273298631347)
    ·
      refine ⟨291250836111088909947947021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194167224074059273298631347 291250836111088909947947021)
      ·
        refine ⟨109219063541658341230480133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 291250836111088909947947021 109219063541658341230480133)
        ·
          refine ⟨20478574414060938980715025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 109219063541658341230480133 20478574414060938980715025)
          ·
            refine ⟨15358930810545704235536269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20478574414060938980715025 15358930810545704235536269)
            ·
              refine ⟨5759599053954639088326101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15358930810545704235536269 5759599053954639088326101)
              ·
                refine ⟨134990602827061853632643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5759599053954639088326101 134990602827061853632643)
                ·
                  rfl

theorem cell22_3549059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 3, 7].length) (baseStart_3549059 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3549059 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3549059 prefixEnd_3549059 := by exact prefixLift 3549059
  have htrace : WordTrace (prefixWord ++ tailWord_3549059) baseStart_3549059 baseEnd_3549059 := by
    simpa [prefixWord, tailWord_3549059, baseEnd_3549059] using wordTrace_append hprefix tailTrace_3549059
  have hstable : (prefixWord ++ tailWord_3549059).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3549059).length < 2 ^ (prefixWord ++ tailWord_3549059).sum := by decide
  have hdescent : baseEnd_3549059 < baseStart_3549059 := by decide
  rcases family_descends (prefixWord ++ tailWord_3549059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3549119 : List Nat := [1, 1, 2, 2, 2, 1, 3, 3, 2, 5]
def baseStart_3549119 : Nat := 118140960795 + 3549119 * 2 ^ 59
def prefixEnd_3549119 : Nat := 4983230072969 + 3 ^ 40 * 3549119 * 2
def baseEnd_3549119 : Nat := 1214935964669736526193603

theorem tailTrace_3549119 : CollatzResearch.WordTrace tailWord_3549119 prefixEnd_3549119 1214935964669736526193603 := by
  unfold tailWord_3549119
  simp only [CollatzResearch.WordTrace]
  refine ⟨129447004429155479112938411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86298002952770319408625607 129447004429155479112938411)
  ·
    refine ⟨194170506643733218669407617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129447004429155479112938411 194170506643733218669407617)
    ·
      refine ⟨145627879982799914002055713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 194170506643733218669407617 145627879982799914002055713)
      ·
        refine ⟨109220909987099935501541785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145627879982799914002055713 109220909987099935501541785)
        ·
          refine ⟨81915682490324951626156339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109220909987099935501541785 81915682490324951626156339)
          ·
            refine ⟨122873523735487427439234509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81915682490324951626156339 122873523735487427439234509)
            ·
              refine ⟨46077571400807785289712941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 122873523735487427439234509 46077571400807785289712941)
              ·
                refine ⟨17279089275302919483642353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46077571400807785289712941 17279089275302919483642353)
                ·
                  refine ⟨12959316956477189612731765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17279089275302919483642353 12959316956477189612731765)
                  ·
                    refine ⟨1214935964669736526193603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12959316956477189612731765 1214935964669736526193603)
                    ·
                      rfl

theorem cell22_3549119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 3, 2, 5].length) (baseStart_3549119 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3549119 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3549119 prefixEnd_3549119 := by exact prefixLift 3549119
  have htrace : WordTrace (prefixWord ++ tailWord_3549119) baseStart_3549119 baseEnd_3549119 := by
    simpa [prefixWord, tailWord_3549119, baseEnd_3549119] using wordTrace_append hprefix tailTrace_3549119
  have hstable : (prefixWord ++ tailWord_3549119).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3549119).length < 2 ^ (prefixWord ++ tailWord_3549119).sum := by decide
  have hdescent : baseEnd_3549119 < baseStart_3549119 := by decide
  rcases family_descends (prefixWord ++ tailWord_3549119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3549179 : List Nat := [1, 1, 1, 1, 1, 3, 4, 1, 3, 6]
def baseStart_3549179 : Nat := 118140960795 + 3549179 * 2 ^ 59
def prefixEnd_3549179 : Nat := 4983230072969 + 3 ^ 40 * 3549179 * 2
def baseEnd_3549179 : Nat := 1214956503895916369693419

theorem tailTrace_3549179 : CollatzResearch.WordTrace tailWord_3549179 prefixEnd_3549179 1214956503895916369693419 := by
  unfold tailWord_3549179
  simp only [CollatzResearch.WordTrace]
  refine ⟨129449192808938109360122591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86299461872625406240081727 129449192808938109360122591)
  ·
    refine ⟨194173789213407164040183887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129449192808938109360122591 194173789213407164040183887)
    ·
      refine ⟨291260683820110746060275831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194173789213407164040183887 291260683820110746060275831)
      ·
        refine ⟨436891025730166119090413747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 291260683820110746060275831 436891025730166119090413747)
        ·
          refine ⟨655336538595249178635620621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 436891025730166119090413747 655336538595249178635620621)
          ·
            refine ⟨245751201973218441988357733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 655336538595249178635620621 245751201973218441988357733)
            ·
              refine ⟨46078350369978457872817075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 245751201973218441988357733 46078350369978457872817075)
              ·
                refine ⟨69117525554967686809225613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46078350369978457872817075 69117525554967686809225613)
                ·
                  refine ⟨25919072083112882553459605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 69117525554967686809225613 25919072083112882553459605)
                  ·
                    refine ⟨1214956503895916369693419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25919072083112882553459605 1214956503895916369693419)
                    ·
                      rfl

theorem cell22_3549179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 1, 3, 6].length) (baseStart_3549179 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3549179 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3549179 prefixEnd_3549179 := by exact prefixLift 3549179
  have htrace : WordTrace (prefixWord ++ tailWord_3549179) baseStart_3549179 baseEnd_3549179 := by
    simpa [prefixWord, tailWord_3549179, baseEnd_3549179] using wordTrace_append hprefix tailTrace_3549179
  have hstable : (prefixWord ++ tailWord_3549179).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3549179).length < 2 ^ (prefixWord ++ tailWord_3549179).sum := by decide
  have hdescent : baseEnd_3549179 < baseStart_3549179 := by decide
  rcases family_descends (prefixWord ++ tailWord_3549179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3549213 : List Nat := [1, 4, 2, 2, 2, 1, 2, 2, 2, 4]
def baseStart_3549213 : Nat := 118140960795 + 3549213 * 2 ^ 59
def prefixEnd_3549213 : Nat := 4983230072969 + 3 ^ 40 * 3549213 * 2
def baseEnd_3549213 : Nat := 1214968142790751614343315

theorem tailTrace_3549213 : CollatzResearch.WordTrace tailWord_3549213 prefixEnd_3549213 1214968142790751614343315 := by
  unfold tailWord_3549213
  simp only [CollatzResearch.WordTrace]
  refine ⟨129450432890814933166860293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86300288593876622111240195 129450432890814933166860293)
  ·
    refine ⟨24271956167027799968786305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 129450432890814933166860293 24271956167027799968786305)
    ·
      refine ⟨18203967125270849976589729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24271956167027799968786305 18203967125270849976589729)
      ·
        refine ⟨13652975343953137482442297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18203967125270849976589729 13652975343953137482442297)
        ·
          refine ⟨10239731507964853111831723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13652975343953137482442297 10239731507964853111831723)
          ·
            refine ⟨15359597261947279667747585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10239731507964853111831723 15359597261947279667747585)
            ·
              refine ⟨11519697946460459750810689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15359597261947279667747585 11519697946460459750810689)
              ·
                refine ⟨8639773459845344813108017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11519697946460459750810689 8639773459845344813108017)
                ·
                  refine ⟨6479830094884008609831013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8639773459845344813108017 6479830094884008609831013)
                  ·
                    refine ⟨1214968142790751614343315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6479830094884008609831013 1214968142790751614343315)
                    ·
                      rfl

theorem cell22_3549213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 2, 2, 2, 4].length) (baseStart_3549213 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3549213 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3549213 prefixEnd_3549213 := by exact prefixLift 3549213
  have htrace : WordTrace (prefixWord ++ tailWord_3549213) baseStart_3549213 baseEnd_3549213 := by
    simpa [prefixWord, tailWord_3549213, baseEnd_3549213] using wordTrace_append hprefix tailTrace_3549213
  have hstable : (prefixWord ++ tailWord_3549213).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3549213).length < 2 ^ (prefixWord ++ tailWord_3549213).sum := by decide
  have hdescent : baseEnd_3549213 < baseStart_3549213 := by decide
  rcases family_descends (prefixWord ++ tailWord_3549213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3549217 : List Nat := [1, 2, 3, 2, 4, 2, 2, 2, 4]
def baseStart_3549217 : Nat := 118140960795 + 3549217 * 2 ^ 59
def prefixEnd_3549217 : Nat := 4983230072969 + 3 ^ 40 * 3549217 * 2
def baseEnd_3549217 : Nat := 404989837357498979081101

theorem tailTrace_3549217 : CollatzResearch.WordTrace tailWord_3549217 prefixEnd_3549217 404989837357498979081101 := by
  unfold tailWord_3549217
  simp only [CollatzResearch.WordTrace]
  refine ⟨129450578782800441850005905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86300385855200294566670603 129450578782800441850005905)
  ·
    refine ⟨97087934087100331387504429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129450578782800441850005905 97087934087100331387504429)
    ·
      refine ⟨36407975282662624270314161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97087934087100331387504429 36407975282662624270314161)
      ·
        refine ⟨27305981461996968202735621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36407975282662624270314161 27305981461996968202735621)
        ·
          refine ⟨5119871524124431538012929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27305981461996968202735621 5119871524124431538012929)
          ·
            refine ⟨3839903643093323653509697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5119871524124431538012929 3839903643093323653509697)
            ·
              refine ⟨2879927732319992740132273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3839903643093323653509697 2879927732319992740132273)
              ·
                refine ⟨2159945799239994555099205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2879927732319992740132273 2159945799239994555099205)
                ·
                  refine ⟨404989837357498979081101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2159945799239994555099205 404989837357498979081101)
                  ·
                    rfl

theorem cell22_3549217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 2, 2, 2, 4].length) (baseStart_3549217 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3549217 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3549217 prefixEnd_3549217 := by exact prefixLift 3549217
  have htrace : WordTrace (prefixWord ++ tailWord_3549217) baseStart_3549217 baseEnd_3549217 := by
    simpa [prefixWord, tailWord_3549217, baseEnd_3549217] using wordTrace_append hprefix tailTrace_3549217
  have hstable : (prefixWord ++ tailWord_3549217).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3549217).length < 2 ^ (prefixWord ++ tailWord_3549217).sum := by decide
  have hdescent : baseEnd_3549217 < baseStart_3549217 := by decide
  rcases family_descends (prefixWord ++ tailWord_3549217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3549260 : List Nat := [2, 2, 1, 3, 1, 1, 3, 5, 1, 3]
def baseStart_3549260 : Nat := 118140960795 + 3549260 * 2 ^ 59
def prefixEnd_3549260 : Nat := 4983230072969 + 3 ^ 40 * 3549260 * 2
def baseEnd_3549260 : Nat := 1214984231851259158418171

theorem tailTrace_3549260 : CollatzResearch.WordTrace tailWord_3549260 prefixEnd_3549260 1214984231851259158418171 := by
  unfold tailWord_3549260
  simp only [CollatzResearch.WordTrace]
  refine ⟨64726073560822330096910617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86301431414429773462547489 64726073560822330096910617)
  ·
    refine ⟨48544555170616747572682963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64726073560822330096910617 48544555170616747572682963)
    ·
      refine ⟨72816832755925121359024445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48544555170616747572682963 72816832755925121359024445)
      ·
        refine ⟨27306312283471920509634167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72816832755925121359024445 27306312283471920509634167)
        ·
          refine ⟨40959468425207880764451251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27306312283471920509634167 40959468425207880764451251)
          ·
            refine ⟨61439202637811821146676877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40959468425207880764451251 61439202637811821146676877)
            ·
              refine ⟨23039700989179432930003829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61439202637811821146676877 23039700989179432930003829)
              ·
                refine ⟨2159971967735571837187859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23039700989179432930003829 2159971967735571837187859)
                ·
                  refine ⟨3239957951603357755781789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2159971967735571837187859 3239957951603357755781789)
                  ·
                    refine ⟨1214984231851259158418171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3239957951603357755781789 1214984231851259158418171)
                    ·
                      rfl

theorem cell22_3549260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 5, 1, 3].length) (baseStart_3549260 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3549260 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3549260 prefixEnd_3549260 := by exact prefixLift 3549260
  have htrace : WordTrace (prefixWord ++ tailWord_3549260) baseStart_3549260 baseEnd_3549260 := by
    simpa [prefixWord, tailWord_3549260, baseEnd_3549260] using wordTrace_append hprefix tailTrace_3549260
  have hstable : (prefixWord ++ tailWord_3549260).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3549260).length < 2 ^ (prefixWord ++ tailWord_3549260).sum := by decide
  have hdescent : baseEnd_3549260 < baseStart_3549260 := by decide
  rcases family_descends (prefixWord ++ tailWord_3549260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3549271 : List Nat := [1, 1, 3, 2, 2, 1, 3, 2, 2, 5]
def baseStart_3549271 : Nat := 118140960795 + 3549271 * 2 ^ 59
def prefixEnd_3549271 : Nat := 4983230072969 + 3 ^ 40 * 3549271 * 2
def baseEnd_3549271 : Nat := 1214987997376058796393137

theorem tailTrace_3549271 : CollatzResearch.WordTrace tailWord_3549271 prefixEnd_3549271 1214987997376058796393137 := by
  unfold tailWord_3549271
  simp only [CollatzResearch.WordTrace]
  refine ⟨129452548324604809072471667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86301698883069872714981111 129452548324604809072471667)
  ·
    refine ⟨194178822486907213608707501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129452548324604809072471667 194178822486907213608707501)
    ·
      refine ⟨72817058432590205103265313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 194178822486907213608707501 72817058432590205103265313)
      ·
        refine ⟨54612793824442653827448985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72817058432590205103265313 54612793824442653827448985)
        ·
          refine ⟨40959595368331990370586739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54612793824442653827448985 40959595368331990370586739)
          ·
            refine ⟨61439393052497985555880109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40959595368331990370586739 61439393052497985555880109)
            ·
              refine ⟨23039772394686744583455041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61439393052497985555880109 23039772394686744583455041)
              ·
                refine ⟨17279829296015058437591281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23039772394686744583455041 17279829296015058437591281)
                ·
                  refine ⟨12959871972011293828193461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17279829296015058437591281 12959871972011293828193461)
                  ·
                    refine ⟨1214987997376058796393137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12959871972011293828193461 1214987997376058796393137)
                    ·
                      rfl

theorem cell22_3549271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 2, 2, 5].length) (baseStart_3549271 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3549271 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3549271 prefixEnd_3549271 := by exact prefixLift 3549271
  have htrace : WordTrace (prefixWord ++ tailWord_3549271) baseStart_3549271 baseEnd_3549271 := by
    simpa [prefixWord, tailWord_3549271, baseEnd_3549271] using wordTrace_append hprefix tailTrace_3549271
  have hstable : (prefixWord ++ tailWord_3549271).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3549271).length < 2 ^ (prefixWord ++ tailWord_3549271).sum := by decide
  have hdescent : baseEnd_3549271 < baseStart_3549271 := by decide
  rcases family_descends (prefixWord ++ tailWord_3549271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3549277 : List Nat := [1, 4, 4, 1, 1, 2, 2, 1, 3, 3]
def baseStart_3549277 : Nat := 118140960795 + 3549277 * 2 ^ 59
def prefixEnd_3549277 : Nat := 4983230072969 + 3 ^ 40 * 3549277 * 2
def baseEnd_3549277 : Nat := 1214990051298676780743119

theorem tailTrace_3549277 : CollatzResearch.WordTrace tailWord_3549277 prefixEnd_3549277 1214990051298676780743119 := by
  unfold tailWord_3549277
  simp only [CollatzResearch.WordTrace]
  refine ⟨129452767162583072097190085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86301844775055381398126723 129452767162583072097190085)
  ·
    refine ⟨24272393842984326018223141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 129452767162583072097190085 24272393842984326018223141)
    ·
      refine ⟨4551073845559561128416839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24272393842984326018223141 4551073845559561128416839)
      ·
        refine ⟨6826610768339341692625259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4551073845559561128416839 6826610768339341692625259)
        ·
          refine ⟨10239916152509012538937889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6826610768339341692625259 10239916152509012538937889)
          ·
            refine ⟨7679937114381759404203417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10239916152509012538937889 7679937114381759404203417)
            ·
              refine ⟨5759952835786319553152563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7679937114381759404203417 5759952835786319553152563)
              ·
                refine ⟨8639929253679479329728845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5759952835786319553152563 8639929253679479329728845)
                ·
                  refine ⟨3239973470129804748648317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8639929253679479329728845 3239973470129804748648317)
                  ·
                    refine ⟨1214990051298676780743119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3239973470129804748648317 1214990051298676780743119)
                    ·
                      rfl

theorem cell22_3549277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 2, 1, 3, 3].length) (baseStart_3549277 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3549277 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3549277 prefixEnd_3549277 := by exact prefixLift 3549277
  have htrace : WordTrace (prefixWord ++ tailWord_3549277) baseStart_3549277 baseEnd_3549277 := by
    simpa [prefixWord, tailWord_3549277, baseEnd_3549277] using wordTrace_append hprefix tailTrace_3549277
  have hstable : (prefixWord ++ tailWord_3549277).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3549277).length < 2 ^ (prefixWord ++ tailWord_3549277).sum := by decide
  have hdescent : baseEnd_3549277 < baseStart_3549277 := by decide
  rcases family_descends (prefixWord ++ tailWord_3549277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3549303 : List Nat := [1, 1, 3, 1, 1, 5, 1, 4, 1, 4]
def baseStart_3549303 : Nat := 118140960795 + 3549303 * 2 ^ 59
def prefixEnd_3549303 : Nat := 4983230072969 + 3 ^ 40 * 3549303 * 2
def baseEnd_3549303 : Nat := 1214998951630021379593039

theorem tailTrace_3549303 : CollatzResearch.WordTrace tailWord_3549303 prefixEnd_3549303 1214998951630021379593039 := by
  unfold tailWord_3549303
  simp only [CollatzResearch.WordTrace]
  refine ⟨129453715460488878537636563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86302476973659252358424375 129453715460488878537636563)
  ·
    refine ⟨194180573190733317806454845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129453715460488878537636563 194180573190733317806454845)
    ·
      refine ⟨72817714946524994177420567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 194180573190733317806454845 72817714946524994177420567)
      ·
        refine ⟨109226572419787491266130851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72817714946524994177420567 109226572419787491266130851)
        ·
          refine ⟨163839858629681236899196277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109226572419787491266130851 163839858629681236899196277)
          ·
            refine ⟨15359986746532615959299651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 163839858629681236899196277 15359986746532615959299651)
            ·
              refine ⟨23039980119798923938949477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15359986746532615959299651 23039980119798923938949477)
              ·
                refine ⟨4319996272462298238553027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23039980119798923938949477 4319996272462298238553027)
                ·
                  refine ⟨6479994408693447357829541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4319996272462298238553027 6479994408693447357829541)
                  ·
                    refine ⟨1214998951630021379593039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6479994408693447357829541 1214998951630021379593039)
                    ·
                      rfl

theorem cell22_3549303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 4, 1, 4].length) (baseStart_3549303 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3549303 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3549303 prefixEnd_3549303 := by exact prefixLift 3549303
  have htrace : WordTrace (prefixWord ++ tailWord_3549303) baseStart_3549303 baseEnd_3549303 := by
    simpa [prefixWord, tailWord_3549303, baseEnd_3549303] using wordTrace_append hprefix tailTrace_3549303
  have hstable : (prefixWord ++ tailWord_3549303).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3549303).length < 2 ^ (prefixWord ++ tailWord_3549303).sum := by decide
  have hdescent : baseEnd_3549303 < baseStart_3549303 := by decide
  rcases family_descends (prefixWord ++ tailWord_3549303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3549320 : List Nat := [2, 1, 3, 4, 1, 1, 2, 3, 1, 4]
def baseStart_3549320 : Nat := 118140960795 + 3549320 * 2 ^ 59
def prefixEnd_3549320 : Nat := 4983230072969 + 3 ^ 40 * 3549320 * 2
def baseEnd_3549320 : Nat := 1215004771077439001917987

theorem tailTrace_3549320 : CollatzResearch.WordTrace tailWord_3549320 prefixEnd_3549320 1215004771077439001917987 := by
  unfold tailWord_3549320
  simp only [CollatzResearch.WordTrace]
  refine ⟨64727167750713645220502707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86302890334284860294003609 64727167750713645220502707)
  ·
    refine ⟨97090751626070467830754061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64727167750713645220502707 97090751626070467830754061)
    ·
      refine ⟨36409031859776425436532773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97090751626070467830754061 36409031859776425436532773)
      ·
        refine ⟨6826693473708079769349895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36409031859776425436532773 6826693473708079769349895)
        ·
          refine ⟨10240040210562119654024843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6826693473708079769349895 10240040210562119654024843)
          ·
            refine ⟨15360060315843179481037265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10240040210562119654024843 15360060315843179481037265)
            ·
              refine ⟨11520045236882384610777949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15360060315843179481037265 11520045236882384610777949)
              ·
                refine ⟨4320016963830894229041731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11520045236882384610777949 4320016963830894229041731)
                ·
                  refine ⟨6480025445746341343562597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4320016963830894229041731 6480025445746341343562597)
                  ·
                    refine ⟨1215004771077439001917987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6480025445746341343562597 1215004771077439001917987)
                    ·
                      rfl

theorem cell22_3549320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 2, 3, 1, 4].length) (baseStart_3549320 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3549320 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3549320 prefixEnd_3549320 := by exact prefixLift 3549320
  have htrace : WordTrace (prefixWord ++ tailWord_3549320) baseStart_3549320 baseEnd_3549320 := by
    simpa [prefixWord, tailWord_3549320, baseEnd_3549320] using wordTrace_append hprefix tailTrace_3549320
  have hstable : (prefixWord ++ tailWord_3549320).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3549320).length < 2 ^ (prefixWord ++ tailWord_3549320).sum := by decide
  have hdescent : baseEnd_3549320 < baseStart_3549320 := by decide
  rcases family_descends (prefixWord ++ tailWord_3549320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3549333 : List Nat := [1, 3, 2, 1, 1, 1, 3, 3, 4, 3]
def baseStart_3549333 : Nat := 118140960795 + 3549333 * 2 ^ 59
def prefixEnd_3549333 : Nat := 4983230072969 + 3 ^ 40 * 3549333 * 2
def baseEnd_3549333 : Nat := 1215009221243111301342947

theorem tailTrace_3549333 : CollatzResearch.WordTrace tailWord_3549333 prefixEnd_3549333 1215009221243111301342947 := by
  unfold tailWord_3549333
  simp only [CollatzResearch.WordTrace]
  refine ⟨129454809650380193661228653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86303206433586795774152435 129454809650380193661228653)
  ·
    refine ⟨48545553618892572622960745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129454809650380193661228653 48545553618892572622960745)
    ·
      refine ⟨36409165214169429467220559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48545553618892572622960745 36409165214169429467220559)
      ·
        refine ⟨54613747821254144200830839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36409165214169429467220559 54613747821254144200830839)
        ·
          refine ⟨81920621731881216301246259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54613747821254144200830839 81920621731881216301246259)
          ·
            refine ⟨122880932597821824451869389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81920621731881216301246259 122880932597821824451869389)
            ·
              refine ⟨46080349724183184169451021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 122880932597821824451869389 46080349724183184169451021)
              ·
                refine ⟨17280131146568694063544133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46080349724183184169451021 17280131146568694063544133)
                ·
                  refine ⟨3240024589981630136914525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17280131146568694063544133 3240024589981630136914525)
                  ·
                    refine ⟨1215009221243111301342947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3240024589981630136914525 1215009221243111301342947)
                    ·
                      rfl

theorem cell22_3549333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 3, 4, 3].length) (baseStart_3549333 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3549333 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3549333 prefixEnd_3549333 := by exact prefixLift 3549333
  have htrace : WordTrace (prefixWord ++ tailWord_3549333) baseStart_3549333 baseEnd_3549333 := by
    simpa [prefixWord, tailWord_3549333, baseEnd_3549333] using wordTrace_append hprefix tailTrace_3549333
  have hstable : (prefixWord ++ tailWord_3549333).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3549333).length < 2 ^ (prefixWord ++ tailWord_3549333).sum := by decide
  have hdescent : baseEnd_3549333 < baseStart_3549333 := by decide
  rcases family_descends (prefixWord ++ tailWord_3549333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3549335 : List Nat := [1, 1, 3, 3, 4, 2, 1, 1, 6]
def baseStart_3549335 : Nat := 118140960795 + 3549335 * 2 ^ 59
def prefixEnd_3549335 : Nat := 4983230072969 + 3 ^ 40 * 3549335 * 2
def baseEnd_3549335 : Nat := 405003301961327987597647

theorem tailTrace_3549335 : CollatzResearch.WordTrace tailWord_3549335 prefixEnd_3549335 405003301961327987597647 := by
  unfold tailWord_3549335
  simp only [CollatzResearch.WordTrace]
  refine ⟨129454882596372948002801459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86303255064248632001867639 129454882596372948002801459)
  ·
    refine ⟨194182323894559422004202189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129454882596372948002801459 194182323894559422004202189)
    ·
      refine ⟨72818371460459783251575821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 194182323894559422004202189 72818371460459783251575821)
      ·
        refine ⟨27306889297672418719340933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72818371460459783251575821 27306889297672418719340933)
        ·
          refine ⟨5120041743313578509876425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27306889297672418719340933 5120041743313578509876425)
          ·
            refine ⟨3840031307485183882407319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5120041743313578509876425 3840031307485183882407319)
            ·
              refine ⟨5760046961227775823610979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3840031307485183882407319 5760046961227775823610979)
              ·
                refine ⟨8640070441841663735416469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5760046961227775823610979 8640070441841663735416469)
                ·
                  refine ⟨405003301961327987597647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8640070441841663735416469 405003301961327987597647)
                  ·
                    rfl

theorem cell22_3549335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 2, 1, 1, 6].length) (baseStart_3549335 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3549335 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3549335 prefixEnd_3549335 := by exact prefixLift 3549335
  have htrace : WordTrace (prefixWord ++ tailWord_3549335) baseStart_3549335 baseEnd_3549335 := by
    simpa [prefixWord, tailWord_3549335, baseEnd_3549335] using wordTrace_append hprefix tailTrace_3549335
  have hstable : (prefixWord ++ tailWord_3549335).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3549335).length < 2 ^ (prefixWord ++ tailWord_3549335).sum := by decide
  have hdescent : baseEnd_3549335 < baseStart_3549335 := by decide
  rcases family_descends (prefixWord ++ tailWord_3549335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3549354 : List Nat := [3, 1, 5, 1, 2, 2, 1, 2, 1, 4]
def baseStart_3549354 : Nat := 118140960795 + 3549354 * 2 ^ 59
def prefixEnd_3549354 : Nat := 4983230072969 + 3 ^ 40 * 3549354 * 2
def baseEnd_3549354 : Nat := 1215016409972274246567883

theorem tailTrace_3549354 : CollatzResearch.WordTrace tailWord_3549354 prefixEnd_3549354 1215016409972274246567883 := by
  unfold tailWord_3549354
  simp only [CollatzResearch.WordTrace]
  refine ⟨32363893895826028561935779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86303717055536076165162077 32363893895826028561935779)
  ·
    refine ⟨48545840843739042842903669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32363893895826028561935779 48545840843739042842903669)
    ·
      refine ⟨4551172579100535266522219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 48545840843739042842903669 4551172579100535266522219)
      ·
        refine ⟨6826758868650802899783329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4551172579100535266522219 6826758868650802899783329)
        ·
          refine ⟨5120069151488102174837497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6826758868650802899783329 5120069151488102174837497)
          ·
            refine ⟨3840051863616076631128123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5120069151488102174837497 3840051863616076631128123)
            ·
              refine ⟨5760077795424114946692185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3840051863616076631128123 5760077795424114946692185)
              ·
                refine ⟨4320058346568086210019139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5760077795424114946692185 4320058346568086210019139)
                ·
                  refine ⟨6480087519852129315028709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4320058346568086210019139 6480087519852129315028709)
                  ·
                    refine ⟨1215016409972274246567883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6480087519852129315028709 1215016409972274246567883)
                    ·
                      rfl

theorem cell22_3549354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 2, 1, 2, 1, 4].length) (baseStart_3549354 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3549354 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3549354 prefixEnd_3549354 := by exact prefixLift 3549354
  have htrace : WordTrace (prefixWord ++ tailWord_3549354) baseStart_3549354 baseEnd_3549354 := by
    simpa [prefixWord, tailWord_3549354, baseEnd_3549354] using wordTrace_append hprefix tailTrace_3549354
  have hstable : (prefixWord ++ tailWord_3549354).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3549354).length < 2 ^ (prefixWord ++ tailWord_3549354).sum := by decide
  have hdescent : baseEnd_3549354 < baseStart_3549354 := by decide
  rcases family_descends (prefixWord ++ tailWord_3549354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3549397 : List Nat := [1, 3, 2, 4, 3, 1, 1, 7]
def baseStart_3549397 : Nat := 118140960795 + 3549397 * 2 ^ 59
def prefixEnd_3549397 : Nat := 4983230072969 + 3 ^ 40 * 3549397 * 2
def baseEnd_3549397 : Nat := 135003458861226274193639

theorem tailTrace_3549397 : CollatzResearch.WordTrace tailWord_3549397 prefixEnd_3549397 135003458861226274193639 := by
  unfold tailWord_3549397
  simp only [CollatzResearch.WordTrace]
  refine ⟨129457143922148332591558445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86304762614765555061038963 129457143922148332591558445)
  ·
    refine ⟨48546428970805624721834417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129457143922148332591558445 48546428970805624721834417)
    ·
      refine ⟨36409821728104218541375813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48546428970805624721834417 36409821728104218541375813)
      ·
        refine ⟨6826841574019540976507965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36409821728104218541375813 6826841574019540976507965)
        ·
          refine ⟨2560065590257327866190487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6826841574019540976507965 2560065590257327866190487)
          ·
            refine ⟨3840098385385991799285731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2560065590257327866190487 3840098385385991799285731)
            ·
              refine ⟨5760147578078987698928597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3840098385385991799285731 5760147578078987698928597)
              ·
                refine ⟨135003458861226274193639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5760147578078987698928597 135003458861226274193639)
                ·
                  rfl

theorem cell22_3549397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 3, 1, 1, 7].length) (baseStart_3549397 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3549397 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3549397 prefixEnd_3549397 := by exact prefixLift 3549397
  have htrace : WordTrace (prefixWord ++ tailWord_3549397) baseStart_3549397 baseEnd_3549397 := by
    simpa [prefixWord, tailWord_3549397, baseEnd_3549397] using wordTrace_append hprefix tailTrace_3549397
  have hstable : (prefixWord ++ tailWord_3549397).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3549397).length < 2 ^ (prefixWord ++ tailWord_3549397).sum := by decide
  have hdescent : baseEnd_3549397 < baseStart_3549397 := by decide
  rcases family_descends (prefixWord ++ tailWord_3549397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3549408 : List Nat := [2, 1, 1, 3, 1, 3, 1, 5, 5]
def baseStart_3549408 : Nat := 118140960795 + 3549408 * 2 ^ 59
def prefixEnd_3549408 : Nat := 4983230072969 + 3 ^ 40 * 3549408 * 2
def baseEnd_3549408 : Nat := 405011631758612035239239

theorem tailTrace_3549408 : CollatzResearch.WordTrace tailWord_3549408 prefixEnd_3549408 405011631758612035239239 := by
  unfold tailWord_3549408
  simp only [CollatzResearch.WordTrace]
  refine ⟨64728772562554240735104439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86305030083405654313472585 64728772562554240735104439)
  ·
    refine ⟨97093158843831361102656659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64728772562554240735104439 97093158843831361102656659)
    ·
      refine ⟨145639738265747041653984989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97093158843831361102656659 145639738265747041653984989)
      ·
        refine ⟨54614901849655140620244371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 145639738265747041653984989 54614901849655140620244371)
        ·
          refine ⟨81922352774482710930366557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54614901849655140620244371 81922352774482710930366557)
          ·
            refine ⟨30720882290431016598887459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81922352774482710930366557 30720882290431016598887459)
            ·
              refine ⟨46081323435646524898331189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30720882290431016598887459 46081323435646524898331189)
              ·
                refine ⟨4320124072091861709218549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 46081323435646524898331189 4320124072091861709218549)
                ·
                  refine ⟨405011631758612035239239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4320124072091861709218549 405011631758612035239239)
                  ·
                    rfl

theorem cell22_3549408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 5, 5].length) (baseStart_3549408 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3549408 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3549408 prefixEnd_3549408 := by exact prefixLift 3549408
  have htrace : WordTrace (prefixWord ++ tailWord_3549408) baseStart_3549408 baseEnd_3549408 := by
    simpa [prefixWord, tailWord_3549408, baseEnd_3549408] using wordTrace_append hprefix tailTrace_3549408
  have hstable : (prefixWord ++ tailWord_3549408).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3549408).length < 2 ^ (prefixWord ++ tailWord_3549408).sum := by decide
  have hdescent : baseEnd_3549408 < baseStart_3549408 := by decide
  rcases family_descends (prefixWord ++ tailWord_3549408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3549442 : List Nat := [3, 4, 1, 1, 2, 1, 3, 2, 5]
def baseStart_3549442 : Nat := 118140960795 + 3549442 * 2 ^ 59
def prefixEnd_3549442 : Nat := 4983230072969 + 3 ^ 40 * 3549442 * 2
def baseEnd_3549442 : Nat := 405015511390223783455871

theorem tailTrace_3549442 : CollatzResearch.WordTrace tailWord_3549442 prefixEnd_3549442 405015511390223783455871 := by
  unfold tailWord_3549442
  simp only [CollatzResearch.WordTrace]
  refine ⟨32364696301746326319236645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86305856804656870184631053 32364696301746326319236645)
  ·
    refine ⟨6068380556577436184856871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32364696301746326319236645 6068380556577436184856871)
    ·
      refine ⟨9102570834866154277285307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6068380556577436184856871 9102570834866154277285307)
      ·
        refine ⟨13653856252299231415927961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9102570834866154277285307 13653856252299231415927961)
        ·
          refine ⟨10240392189224423561945971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13653856252299231415927961 10240392189224423561945971)
          ·
            refine ⟨15360588283836635342918957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10240392189224423561945971 15360588283836635342918957)
            ·
              refine ⟨5760220606438738253594609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15360588283836635342918957 5760220606438738253594609)
              ·
                refine ⟨4320165454829053690195957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5760220606438738253594609 4320165454829053690195957)
                ·
                  refine ⟨405015511390223783455871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4320165454829053690195957 405015511390223783455871)
                  ·
                    rfl

theorem cell22_3549442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 3, 2, 5].length) (baseStart_3549442 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3549442 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3549442 prefixEnd_3549442 := by exact prefixLift 3549442
  have htrace : WordTrace (prefixWord ++ tailWord_3549442) baseStart_3549442 baseEnd_3549442 := by
    simpa [prefixWord, tailWord_3549442, baseEnd_3549442] using wordTrace_append hprefix tailTrace_3549442
  have hstable : (prefixWord ++ tailWord_3549442).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3549442).length < 2 ^ (prefixWord ++ tailWord_3549442).sum := by decide
  have hdescent : baseEnd_3549442 < baseStart_3549442 := by decide
  rcases family_descends (prefixWord ++ tailWord_3549442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
